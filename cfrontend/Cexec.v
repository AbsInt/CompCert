(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Animating the CompCert C semantics *)

Require Import Axioms.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Determinism.
Require Import Csyntax.
Require Import Csem.
Require Cstrategy.

Lemma type_eq: forall (ty1 ty2: type), {ty1=ty2} + {ty1<>ty2}
with typelist_eq: forall (tyl1 tyl2: typelist), {tyl1=tyl2} + {tyl1<>tyl2}
with fieldlist_eq: forall (fld1 fld2: fieldlist), {fld1=fld2} + {fld1<>fld2}.
Proof.
  assert (forall (x y: intsize), {x=y} + {x<>y}). decide equality.
  assert (forall (x y: signedness), {x=y} + {x<>y}). decide equality.
  assert (forall (x y: floatsize), {x=y} + {x<>y}). decide equality.
  generalize ident_eq zeq. intros E1 E2. 
  decide equality.
  decide equality.
  generalize ident_eq. intros E1.
  decide equality.
Defined.

Opaque type_eq.

(** Error monad with options or lists *)

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation " 'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => nil end)
  (at level 200, X ident, A at level 100, B at level 200)
  : list_monad_scope.

Notation " 'check' A ; B" := (if A then B else nil)
  (at level 200, A at level 100, B at level 200)
  : list_monad_scope.

Definition is_val (a: expr) : option (val * type) :=
  match a with
  | Eval v ty => Some(v, ty)
  | _ => None
  end.

Lemma is_val_inv:
  forall a v ty, is_val a = Some(v, ty) -> a = Eval v ty.
Proof.
  intros until ty. destruct a; simpl; congruence.
Qed.

Definition is_loc (a: expr) : option (block * int * type) :=
  match a with
  | Eloc b ofs ty => Some(b, ofs, ty)
  | _ => None
  end.

Lemma is_loc_inv:
  forall a b ofs ty, is_loc a = Some(b, ofs, ty) -> a = Eloc b ofs ty.
Proof.
  intros until ty. destruct a; simpl; congruence.
Qed.

Local Open Scope option_monad_scope. 

Fixpoint is_val_list (al: exprlist) : option (list (val * type)) :=
  match al with
  | Enil => Some nil
  | Econs a1 al => do vt1 <- is_val a1; do vtl <- is_val_list al; Some(vt1::vtl)
  end.

Definition is_skip (s: statement) : {s = Sskip} + {s <> Sskip}.
Proof.
  destruct s; (left; congruence) || (right; congruence).
Qed.

(** * Reduction of expressions *)

Section EXEC.

Variable ge: genv.

Inductive reduction: Type :=
  | Lred (l': expr) (m': mem)
  | Rred (r': expr) (m': mem)
  | Callred (fd: fundef) (args: list val) (tyres: type) (m': mem).

Section EXPRS.

Variable e: env.

Fixpoint sem_cast_arguments (vtl: list (val * type)) (tl: typelist) : option (list val) :=
  match vtl, tl with
  | nil, Tnil => Some nil
  | (v1,t1)::vtl, Tcons t1' tl =>
      do v <- sem_cast v1 t1 t1'; do vl <- sem_cast_arguments vtl tl; Some(v::vl)
  | _, _ => None
  end.

(** The result of stepping an expression can be
- [None] denoting that the expression is stuck;
- [Some nil] meaning that the expression is fully reduced
   (it's [Eval] for a r-value and [Eloc] for a l-value);
- [Some ll] meaning that the expression can reduce to any of
   the elements of [ll].  Each element is a pair of a context
   and a reduction inside this context (see type [reduction] above).
*)

Definition reducts (A: Type): Type := option (list ((expr -> A) * reduction)).

Definition topred (r: reduction) : reducts expr :=
  Some (((fun (x: expr) => x), r) :: nil).

Definition incontext {A B: Type} (ctx: A -> B) (r: reducts A) : reducts B :=
  match r with
  | None => None
  | Some l => Some (map (fun z => ((fun (x: expr) => ctx(fst z x)), snd z)) l)
  end.

Definition incontext2 {A1 A2 B: Type}
                     (ctx1: A1 -> B) (r1: reducts A1)
                     (ctx2: A2 -> B) (r2: reducts A2) : reducts B :=
  match r1, r2 with
  | None, _ => None
  | _, None => None
  | Some l1, Some l2 =>
      Some (map (fun z => ((fun (x: expr) => ctx1(fst z x)), snd z)) l1
            ++ map (fun z => ((fun (x: expr) => ctx2(fst z x)), snd z)) l2)
  end.

Fixpoint step_expr (k: kind) (a: expr) (m: mem): reducts expr :=
  match k, a with
  | LV, Eloc b ofs ty =>
      Some nil
  | LV, Evar x ty =>
      match e!x with
      | Some(b, ty') =>
          check type_eq ty ty';
          topred (Lred (Eloc b Int.zero ty) m)
      | None =>
          do b <- Genv.find_symbol ge x;
          do ty' <- type_of_global ge b;
          check type_eq ty ty';
          topred (Lred (Eloc b Int.zero ty) m)
      end
  | LV, Ederef r ty =>
      match is_val r with
      | Some(Vptr b ofs, ty') =>
          topred (Lred (Eloc b ofs ty) m)
      | Some _ =>
          None
      | None =>
          incontext (fun x => Ederef x ty) (step_expr RV r m)
      end
  | LV, Efield l f ty =>
      match is_loc l with
      | Some(b, ofs, ty') =>
          match ty' with
          | Tstruct id fList =>
              match field_offset f fList with
              | Error _ => None
              | OK delta => topred (Lred (Eloc b (Int.add ofs (Int.repr delta)) ty) m)
              end
          | Tunion id fList =>
              topred (Lred (Eloc b ofs ty) m)
          | _ => None
          end
      | None =>
          incontext (fun x => Efield x f ty) (step_expr LV l m)
      end
  | RV, Eval v ty =>
      Some nil
  | RV, Evalof l ty =>
      match is_loc l with
      | Some(b, ofs, ty') =>
          check type_eq ty ty';
          do v <- load_value_of_type ty m b ofs;
          topred (Rred (Eval v ty) m)
      | None =>
          incontext (fun x => Evalof x ty) (step_expr LV l m)
      end
  | RV, Eaddrof l ty =>
      match is_loc l with
      | Some(b, ofs, ty') => topred (Rred (Eval (Vptr b ofs) ty) m)
      | None => incontext (fun x => Eaddrof x ty) (step_expr LV l m)
      end
  | RV, Eunop op r1 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do v <- sem_unary_operation op v1 ty1;
          topred (Rred (Eval v ty) m)
      | None =>
          incontext (fun x => Eunop op x ty) (step_expr RV r1 m)
      end
  | RV, Ebinop op r1 r2 ty =>
      match is_val r1, is_val r2 with
      | Some(v1, ty1), Some(v2, ty2) =>
          do v <- sem_binary_operation op v1 ty1 v2 ty2 m;
          topred (Rred (Eval v ty) m)
      | _, _ =>
         incontext2 (fun x => Ebinop op x r2 ty) (step_expr RV r1 m)
                    (fun x => Ebinop op r1 x ty) (step_expr RV r2 m)
      end
  | RV, Ecast r1 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do v <- sem_cast v1 ty1 ty;
          topred (Rred (Eval v ty) m)
      | None =>
          incontext (fun x => Ecast x ty) (step_expr RV r1 m)
      end
  | RV, Econdition r1 r2 r3 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do b <- bool_val v1 ty1;
          topred (Rred (Eparen (if b then r2 else r3) ty) m)
      | None =>
          incontext (fun x => Econdition x r2 r3 ty) (step_expr RV r1 m)
      end
  | RV, Esizeof ty' ty =>
      topred (Rred (Eval (Vint (Int.repr (sizeof ty'))) ty) m)
  | RV, Eassign l1 r2 ty =>
      match is_loc l1, is_val r2 with
      | Some(b, ofs, ty1), Some(v2, ty2) =>
          check type_eq ty1 ty;
          do v <- sem_cast v2 ty2 ty1;
          do m' <- store_value_of_type ty1 m b ofs v;
          topred (Rred (Eval v ty) m')
      | _, _ =>
         incontext2 (fun x => Eassign x r2 ty) (step_expr LV l1 m)
                    (fun x => Eassign l1 x ty) (step_expr RV r2 m)
      end
  | RV, Eassignop op l1 r2 tyres ty =>
      match is_loc l1, is_val r2 with
      | Some(b, ofs, ty1), Some(v2, ty2) =>
          check type_eq ty1 ty;
          do v1 <- load_value_of_type ty1 m b ofs;
          do v <- sem_binary_operation op v1 ty1 v2 ty2 m;
          do v' <- sem_cast v tyres ty1;
          do m' <- store_value_of_type ty1 m b ofs v';
          topred (Rred (Eval v' ty) m')
      | _, _ =>
         incontext2 (fun x => Eassignop op x r2 tyres ty) (step_expr LV l1 m)
                    (fun x => Eassignop op l1 x tyres ty) (step_expr RV r2 m)
      end
  | RV, Epostincr id l ty =>
      match is_loc l with
      | Some(b, ofs, ty1) =>
          check type_eq ty1 ty;
          do v1 <- load_value_of_type ty m b ofs;
          do v2 <- sem_incrdecr id v1 ty;
          do v3 <- sem_cast v2 (typeconv ty) ty;
          do m' <- store_value_of_type ty m b ofs v3;
          topred (Rred (Eval v1 ty) m')
      | None =>
          incontext (fun x => Epostincr id x ty) (step_expr LV l m)
      end
  | RV, Ecomma r1 r2 ty =>
      match is_val r1 with
      | Some _ =>
          check type_eq (typeof r2) ty;
          topred (Rred r2 m)
      | None =>
          incontext (fun x => Ecomma x r2 ty) (step_expr RV r1 m)
      end
  | RV, Eparen r1 ty =>
      match is_val r1 with
      | Some (v1, ty1) =>
          do v <- sem_cast v1 ty1 ty;
          topred (Rred (Eval v ty) m)
      | None =>
          incontext (fun x => Eparen x ty) (step_expr RV r1 m)
      end
  | RV, Ecall r1 rargs ty =>
      match is_val r1, is_val_list rargs with
      | Some(vf, tyf), Some vtl =>
          match classify_fun tyf with
          | fun_case_f tyargs tyres =>
              do fd <- Genv.find_funct ge vf;
              do vargs <- sem_cast_arguments vtl tyargs;
              check type_eq (type_of_fundef fd) (Tfunction tyargs tyres);
              topred (Callred fd vargs ty m)
          | _ => None
          end
      | _, _ =>
          incontext2 (fun x => Ecall x rargs ty) (step_expr RV r1 m)
                     (fun x => Ecall r1 x ty) (step_exprlist rargs m)
      end
  | _, _ => None
  end

with step_exprlist (rl: exprlist) (m: mem): reducts exprlist :=
  match rl with
  | Enil =>
      Some nil
  | Econs r1 rs =>
      incontext2 (fun x => Econs x rs) (step_expr RV r1 m)
                 (fun x => Econs r1 x) (step_exprlist rs m)
  end.

(** Soundness: if [step_expr] returns [Some ll], then every element
  of [ll] is a reduct. *)

Lemma context_compose:
  forall k2 k3 C2, context k2 k3 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  context k1 k3 (fun x => C2(C1 x))
with contextlist_compose:
  forall k2 C2, contextlist k2 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  contextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Hint Constructors context contextlist.
Hint Resolve context_compose contextlist_compose.

Definition reduction_ok (a: expr) (m: mem) (rd: reduction) : Prop :=
  match rd with
  | Lred l' m' => lred ge e a m l' m'
  | Rred r' m' => rred a m r' m'
  | Callred fd args tyres m' => callred ge a fd args tyres /\ m' = m
  end.

Definition reduction_kind (rd: reduction): kind :=
  match rd with
  | Lred l' m' => LV
  | Rred r' m' => RV
  | Callred fd args tyres m' => RV
  end.

Ltac monadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some ?y |- _ ] =>
      destruct x as []_eqn; [monadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some ?y |- _ ] =>
      destruct x; [monadInv|discriminate]
  | _ => idtac
  end.

Lemma sem_cast_arguments_sound:
  forall rargs vtl tyargs vargs,
  is_val_list rargs = Some vtl ->
  sem_cast_arguments vtl tyargs = Some vargs ->
  cast_arguments rargs tyargs vargs.
Proof.
  induction rargs; simpl; intros.
  inv H. destruct tyargs; simpl in H0; inv H0. constructor.
  monadInv. inv H. simpl in H0. destruct p as [v1 t1]. destruct tyargs; try congruence. monadInv.
  inv H0. rewrite (is_val_inv _ _ _ Heqo). constructor. auto. eauto. 
Qed.

Definition reducts_ok (k: kind) (a: expr) (m: mem) (res: reducts expr) : Prop :=
  match res with
  | None => True
  | Some nil => match k with LV => is_loc a <> None | RV => is_val a <> None end
  | Some ll =>
      forall C rd,
      In (C, rd) ll ->
      context (reduction_kind rd) k C /\ exists a', a = C a' /\ reduction_ok a' m rd
  end.

Definition list_reducts_ok (al: exprlist) (m: mem) (res: reducts exprlist) : Prop :=
  match res with
  | None => True
  | Some nil => is_val_list al <> None
  | Some ll =>
      forall C rd,
      In (C, rd) ll ->
      contextlist (reduction_kind rd) C /\ exists a', al = C a' /\ reduction_ok a' m rd
  end.

Lemma topred_ok:
  forall k a m rd,
  reduction_ok a m rd ->
  k = reduction_kind rd ->
  reducts_ok k a m (topred rd).
Proof.
  intros. unfold topred; red. simpl; intros. destruct H1; try contradiction.
  inv H1. split. auto. exists a; auto.
Qed.

Lemma incontext_ok:
  forall k a m C res k' a',
  reducts_ok k' a' m res ->
  a = C a' ->
  context k' k C ->
  match k' with LV => is_loc a' = None | RV => is_val a' = None end ->
  reducts_ok k a m (incontext C res).
Proof.
  unfold reducts_ok; intros. destruct res; simpl. destruct l.
(* res = Some nil *)
  destruct k'; congruence.
(* res = Some nonempty-list *)
  simpl map at 1. hnf. intros. 
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [U [a'' [V W]]].
  split. eapply context_compose; eauto. exists a''; split; auto. congruence. 
(* res = None *)
  auto.
Qed.

Remark incontext2_inv:
  forall {A1 A2 B: Type} (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  match incontext2 C1 res1 C2 res2 with
  | None => res1 = None \/ res2 = None
  | Some nil => res1 = Some nil /\ res2 = Some nil
  | Some ll => 
      exists ll1, exists ll2,
      res1 = Some ll1 /\ res2 = Some ll2 /\
      forall C rd, In (C, rd) ll ->
      (exists C', C = (fun x => C1(C' x)) /\ In (C', rd) ll1)
      \/ (exists C', C = (fun x => C2(C' x)) /\ In (C', rd) ll2)
  end.
Proof.
  intros. unfold incontext2. destruct res1 as [ll1|]; auto. destruct res2 as [ll2|]; auto.
  set (ll := map
    (fun z : (expr -> A1) * reduction =>
     (fun x : expr => C1 (fst z x), snd z)) ll1 ++
  map
    (fun z : (expr -> A2) * reduction =>
     (fun x : expr => C2 (fst z x), snd z)) ll2).
  destruct ll as []_eqn.
  destruct (app_eq_nil _ _ Heql). 
  split. destruct ll1; auto || discriminate. destruct ll2; auto || discriminate.
  rewrite <- Heql. exists ll1; exists ll2. split. auto. split. auto.
  unfold ll; intros.
  rewrite in_app in H. destruct H.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  left; exists C'; auto. 
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  right; exists C'; auto.
Qed.

Lemma incontext2_ok:
  forall k a m k1 a1 res1 k2 a2 res2 C1 C2,
  reducts_ok k1 a1 m res1 ->
  reducts_ok k2 a2 m res2 ->
  a = C1 a1 -> a = C2 a2 ->
  context k1 k C1 -> context k2 k C2 ->
  match k1 with LV => is_loc a1 = None | RV => is_val a1 = None end
  \/ match k2 with LV => is_loc a2 = None | RV => is_val a2 = None end ->
  reducts_ok k a m (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_ok; intros.
  generalize (incontext2_inv C1 res1 C2 res2). 
  destruct (incontext2 C1 res1 C2 res2) as [ll|]; auto.
  destruct ll. 
  intros [EQ1 EQ2]. subst. destruct H5. destruct k1; congruence. destruct k2; congruence.
  intros [ll1 [ll2 [EQ1 [EQ2 IN]]]]. subst. intros. 
  exploit IN; eauto. intros [[C' [P Q]] | [C' [P Q]]]; subst.
  destruct ll1; try contradiction. exploit H; eauto.
  intros [U [a' [V W]]]. split. eauto. exists a'; split. congruence. auto. 
  destruct ll2; try contradiction. exploit H0; eauto.
  intros [U [a' [V W]]]. split. eauto. exists a'; split. congruence. auto.
Qed.

Lemma incontext2_list_ok:
  forall a1 a2 ty m res1 res2,
  reducts_ok RV a1 m res1 ->
  list_reducts_ok a2 m res2 ->
  is_val a1 = None \/ is_val_list a2 = None ->
  reducts_ok RV (Ecall a1 a2 ty) m 
               (incontext2 (fun x => Ecall x a2 ty) res1
                           (fun x => Ecall a1 x ty) res2).
Proof.
  unfold reducts_ok, list_reducts_ok; intros.
  set (C1 := fun x => Ecall x a2 ty). set (C2 := fun x => Ecall a1 x ty). 
  generalize (incontext2_inv C1 res1 C2 res2). 
  destruct (incontext2 C1 res1 C2 res2) as [ll|]; auto.
  destruct ll. 
  intros [EQ1 EQ2]. subst. intuition congruence.
  intros [ll1 [ll2 [EQ1 [EQ2 IN]]]]. subst. intros. 
  exploit IN; eauto. intros [[C' [P Q]] | [C' [P Q]]]; subst.
  destruct ll1; try contradiction. exploit H; eauto.
  intros [U [a' [V W]]]. split. unfold C1. auto. exists a'; split. unfold C1; congruence. auto. 
  destruct ll2; try contradiction. exploit H0; eauto.
  intros [U [a' [V W]]]. split. unfold C2. auto. exists a'; split. unfold C2; congruence. auto.
Qed.

Lemma incontext2_list_ok':
  forall a1 a2 m res1 res2,
  reducts_ok RV a1 m res1 ->
  list_reducts_ok a2 m res2 ->
  list_reducts_ok (Econs a1 a2) m
               (incontext2 (fun x => Econs x a2) res1
                           (fun x => Econs a1 x) res2).
Proof.
  unfold reducts_ok, list_reducts_ok; intros.
  set (C1 := fun x => Econs x a2). set (C2 := fun x => Econs a1 x). 
  generalize (incontext2_inv C1 res1 C2 res2). 
  destruct (incontext2 C1 res1 C2 res2) as [ll|]; auto.
  destruct ll. 
  intros [EQ1 EQ2]. subst.
  simpl. destruct (is_val a1); try congruence. destruct (is_val_list a2); congruence.
  intros [ll1 [ll2 [EQ1 [EQ2 IN]]]]. subst. intros. 
  exploit IN; eauto. intros [[C' [P Q]] | [C' [P Q]]]; subst.
  destruct ll1; try contradiction. exploit H; eauto.
  intros [U [a' [V W]]]. split. unfold C1. auto. exists a'; split. unfold C1; congruence. auto. 
  destruct ll2; try contradiction. exploit H0; eauto.
  intros [U [a' [V W]]]. split. unfold C2. auto. exists a'; split. unfold C2; congruence. auto.
Qed.

Ltac mysimpl :=
  match goal with
  | [ |- reducts_ok _ _ _ (match ?x with Some _ => _ | None => None end) ] =>
      destruct x as []_eqn; [mysimpl|exact I]
  | [ |- reducts_ok _ _ _ (match ?x with left _ => _ | right _ => None end) ] =>
      destruct x as []_eqn; [subst;mysimpl|exact I]
  | _ =>
      idtac
  end.

Theorem step_expr_sound:
  forall a k m, reducts_ok k a m (step_expr k a m)
with step_exprlist_sound:
  forall al m, list_reducts_ok al m (step_exprlist al m).
Proof with try (exact I).
  induction a; destruct k; intros; simpl...
(* Eval *)
  congruence.
(* Evar *)
  destruct (e!x) as [[b ty'] | ]_eqn; mysimpl.
  apply topred_ok; auto. apply red_var_local; auto.
  apply topred_ok; auto. apply red_var_global; auto.
(* Efield *)
  destruct (is_loc a) as [[[b ofs] ty'] | ]_eqn.
  destruct ty'... 
  (* top struct *)
  destruct (field_offset f f0) as [delta|]_eqn...
  rewrite (is_loc_inv _ _ _ _ Heqo). apply topred_ok; auto. apply red_field_struct; auto.
  (* top union *)
  rewrite (is_loc_inv _ _ _ _ Heqo). apply topred_ok; auto. apply red_field_union; auto.
  (* in depth *)
  eapply incontext_ok; eauto. 
(* Evalof *)
  destruct (is_loc a) as [[[b ofs] ty'] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto. rewrite (is_loc_inv _ _ _ _ Heqo). apply red_rvalof; auto. 
  (* depth *)
  eapply incontext_ok; eauto.
(* Ederef *)
  destruct (is_val a) as [[v ty'] | ]_eqn.
  (* top *)
  destruct v... mysimpl. apply topred_ok; auto. rewrite (is_val_inv _ _ _ Heqo). apply red_deref; auto. 
  (* depth *)
  eapply incontext_ok; eauto.
(* Eaddrof *)
  destruct (is_loc a) as [[[b ofs] ty'] | ]_eqn.
  (* top *)
  apply topred_ok; auto. rewrite (is_loc_inv _ _ _ _ Heqo). apply red_addrof; auto. 
  (* depth *)
  eapply incontext_ok; eauto.
(* unop *)
  destruct (is_val a) as [[v ty'] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto. rewrite (is_val_inv _ _ _ Heqo). apply red_unop; auto. 
  (* depth *)
  eapply incontext_ok; eauto.
(* binop *)
  destruct (is_val a1) as [[v1 ty1] | ]_eqn.
  destruct (is_val a2) as [[v2 ty2] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto. 
  rewrite (is_val_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0). apply red_binop; auto.
  (* depth *)
  eapply incontext2_ok; eauto. 
  eapply incontext2_ok; eauto. 
(* cast *)
  destruct (is_val a) as [[v ty'] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto. 
  rewrite (is_val_inv _ _ _ Heqo). apply red_cast; auto. 
  (* depth *)
  eapply incontext_ok; eauto.
(* condition *)
  destruct (is_val a1) as [[v ty'] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto.
  rewrite (is_val_inv _ _ _ Heqo). eapply red_condition; eauto.
  (* depth *)
  eapply incontext_ok; eauto.
(* sizeof *)
  apply topred_ok; auto. apply red_sizeof.
(* assign *)
  destruct (is_loc a1) as [[[b ofs] ty1] | ]_eqn.
  destruct (is_val a2) as [[v2 ty2] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto.
  rewrite (is_loc_inv _ _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0). apply red_assign; auto.
  (* depth *)
  eapply incontext2_ok; eauto.
  eapply incontext2_ok; eauto.
(* assignop *)
  destruct (is_loc a1) as [[[b ofs] ty1] | ]_eqn.
  destruct (is_val a2) as [[v2 ty2] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto.
  rewrite (is_loc_inv _ _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0). eapply red_assignop; eauto.
  (* depth *)
  eapply incontext2_ok; eauto.
  eapply incontext2_ok; eauto.
(* postincr *)
  destruct (is_loc a) as [[[b ofs] ty'] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto.
  rewrite (is_loc_inv _ _ _ _ Heqo). eapply red_postincr; eauto. 
  (* depth *)
  eapply incontext_ok; eauto.
(* comma *)
  destruct (is_val a1) as [[v ty'] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto.
  rewrite (is_val_inv _ _ _ Heqo). apply red_comma; auto. 
  (* depth *)
  eapply incontext_ok; eauto.
(* call *)
  destruct (is_val a) as [[vf tyf] | ]_eqn.
  destruct (is_val_list rargs) as [vtl | ]_eqn.
  (* top *)
  destruct (classify_fun tyf) as [tyargs tyres|]_eqn...
  mysimpl. apply topred_ok; auto.
  rewrite (is_val_inv _ _ _ Heqo). red. split; auto. eapply red_Ecall; eauto. 
  eapply sem_cast_arguments_sound; eauto. 
  (* depth *)
  eapply incontext2_list_ok; eauto.
  eapply incontext2_list_ok; eauto. 
(* loc *)
  congruence.
(* paren *)
  destruct (is_val a) as [[v ty'] | ]_eqn.
  (* top *)
  mysimpl. apply topred_ok; auto.
  rewrite (is_val_inv _ _ _ Heqo). apply red_paren; auto. 
  (* depth *)
  eapply incontext_ok; eauto.

  induction al; simpl; intros.
(* nil *)
  congruence.
(* cons *)
  eapply incontext2_list_ok'; eauto.
Qed.


Lemma step_exprlist_val_list:
  forall m al, is_val_list al <> None -> step_exprlist al m = Some nil.
Proof.
  induction al; simpl; intros. 
  auto.
  destruct (is_val r1) as [[v1 ty1]|]_eqn; try congruence.
  destruct (is_val_list al) as []_eqn; try congruence.
  rewrite (is_val_inv _ _ _ Heqo).
  rewrite IHal. auto. congruence.
Qed.

(** Completeness, part 1: if [step_expr] returns [Some ll],
  then [ll] contains all possible reducts. *)

Lemma lred_topred:
  forall l1 m1 l2 m2,
  lred ge e l1 m1 l2 m2 ->
  step_expr LV l1 m1 = topred (Lred l2 m2).
Proof.
  induction 1; simpl.
(* var local *)
  rewrite H. rewrite dec_eq_true; auto.
(* var global *)
  rewrite H; rewrite H0; rewrite H1. rewrite dec_eq_true; auto.
(* deref *) 
  auto.
(* field struct *)
  rewrite H; auto.
(* field union *)
  auto.
Qed.

Lemma rred_topred:
  forall r1 m1 r2 m2,
  rred r1 m1 r2 m2 ->
  step_expr RV r1 m1 = topred (Rred r2 m2).
Proof.
  induction 1; simpl.
(* valof *)
  rewrite dec_eq_true; auto. rewrite H; auto.
(* addrof *)
  auto.
(* unop *)
  rewrite H; auto.
(* binop *)
  rewrite H; auto.
(* cast *)
  rewrite H; auto.
(* condition *)
  rewrite H; auto.
(* sizeof *)
  auto.
(* assign *)
  rewrite dec_eq_true; auto. rewrite H; rewrite H0; auto.
(* assignop *)
  rewrite dec_eq_true; auto. rewrite H; rewrite H0; rewrite H1; rewrite H2; auto.
(* postincr *)
  rewrite dec_eq_true; auto. rewrite H; rewrite H0; rewrite H1; rewrite H2; auto.
(* comma *)
  rewrite H; rewrite dec_eq_true; auto.
(* paren *)
  rewrite H; auto.
Qed.

Lemma sem_cast_arguments_complete:
  forall al tyl vl,
  cast_arguments al tyl vl ->
  exists vtl, is_val_list al = Some vtl /\ sem_cast_arguments vtl tyl = Some vl.
Proof.
  induction 1.
  exists (@nil (val * type)); auto.
  destruct IHcast_arguments as [vtl [A B]]. 
  exists ((v, ty) :: vtl); simpl. rewrite A; rewrite B; rewrite H. auto.
Qed.

Lemma callred_topred:
  forall a fd args ty m,
  callred ge a fd args ty ->
  step_expr RV a m = topred (Callred fd args ty m).
Proof.
  induction 1; simpl.
  rewrite H2. exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
  rewrite A; rewrite H; rewrite B; rewrite H1; rewrite dec_eq_true. auto.
Qed.

Definition reducts_incl {A B: Type} (C: A -> B) (res1: reducts A) (res2: reducts B) : Prop :=
  match res1, res2 with
  | Some ll1, Some ll2 =>
      forall C1 rd, In (C1, rd) ll1 -> In ((fun x => C(C1 x)), rd) ll2
  | None, Some ll2 => False
  | _, None => True
  end.

Lemma reducts_incl_trans:
  forall (A1 A2: Type) (C: A1 -> A2) res1 res2, reducts_incl C res1 res2 ->
  forall (A3: Type) (C': A2 -> A3) res3,
  reducts_incl C' res2 res3 ->
  reducts_incl (fun x => C'(C x)) res1 res3.
Proof.
  unfold reducts_incl; intros. destruct res1; destruct res2; destruct res3; auto. contradiction.
Qed.

Lemma reducts_incl_nil:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C (Some nil) res.
Proof.
  intros; red. destruct res; auto. intros; contradiction.
Qed.

Lemma reducts_incl_val:
  forall (A: Type) a m v ty (C: expr -> A) res,
  is_val a = Some(v, ty) -> reducts_incl C (step_expr RV a m) res.
Proof.
  intros. rewrite (is_val_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_loc:
  forall (A: Type) a m b ofs ty (C: expr -> A) res,
  is_loc a = Some(b, ofs, ty) -> reducts_incl C (step_expr LV a m) res.
Proof.
  intros. rewrite (is_loc_inv _ _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_listval:
  forall (A: Type) a m vtl (C: exprlist -> A) res,
  is_val_list a = Some vtl -> reducts_incl C (step_exprlist a m) res.
Proof.
  intros. rewrite step_exprlist_val_list. apply reducts_incl_nil. congruence.
Qed.

Lemma reducts_incl_incontext:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C res (incontext C res).
Proof.
  intros; unfold reducts_incl. destruct res; simpl; auto.
  intros. set (f := fun z : (expr -> A) * reduction => (fun x : expr => C (fst z x), snd z)).
  change (In (f (C1, rd)) (map f l)). apply in_map. auto.
Qed.

Lemma reducts_incl_incontext2_left:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C1 res1 (incontext2 C1 res1 C2 res2).
Proof.
  intros. destruct res1; simpl; auto. destruct res2; auto. 
  intros. rewrite in_app_iff. left.
  set (f := fun z : (expr -> A1) * reduction => (fun x : expr => C1 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f l)). apply in_map; auto.
Qed.

Lemma reducts_incl_incontext2_right:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C2 res2 (incontext2 C1 res1 C2 res2).
Proof.
  intros. destruct res1; destruct res2; simpl; auto.
  intros. rewrite in_app_iff. right.
  set (f := fun z : (expr -> A2) * reduction => (fun x : expr => C2 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f l0)). apply in_map; auto.
Qed.

Hint Resolve reducts_incl_val reducts_incl_loc reducts_incl_listval
             reducts_incl_incontext reducts_incl_incontext2_left reducts_incl_incontext2_right.

Lemma step_expr_context:
  forall from to C, context from to C ->
  forall a m, reducts_incl C (step_expr from a m) (step_expr to (C a) m)
with step_exprlist_context:
  forall from C, contextlist from C ->
  forall a m, reducts_incl C (step_expr from a m) (step_exprlist (C a) m).
Proof.
  induction 1; simpl; intros.
(* top *)
  red. destruct (step_expr k a m); auto. intros. 
  replace (fun x => C1 x) with C1; auto. apply extensionality; auto.
(* deref *)
  eapply reducts_incl_trans with (C' := fun x => Ederef x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|]_eqn; eauto.
(* field *)
  eapply reducts_incl_trans with (C' := fun x => Efield x f ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|]_eqn; eauto.
(* valof *)
  eapply reducts_incl_trans with (C' := fun x => Evalof x ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|]_eqn; eauto.
(* addrof *)
  eapply reducts_incl_trans with (C' := fun x => Eaddrof x ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|]_eqn; eauto.
(* unop *)
  eapply reducts_incl_trans with (C' := fun x => Eunop op x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|]_eqn; eauto.
(* binop left *)
  eapply reducts_incl_trans with (C' := fun x => Ebinop op x e2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|]_eqn; eauto.
(* binop right *)
  eapply reducts_incl_trans with (C' := fun x => Ebinop op e1 x ty); eauto.
  destruct (is_val e1) as [[v1 ty1]|]_eqn; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|]_eqn; eauto.
(* cast *)
  eapply reducts_incl_trans with (C' := fun x => Ecast x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|]_eqn; eauto.
(* condition *)
  eapply reducts_incl_trans with (C' := fun x => Econdition x r2 r3 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|]_eqn; eauto.
(* assign left *)
  eapply reducts_incl_trans with (C' := fun x => Eassign x e2 ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|]_eqn; eauto.
(* assign right *)
  eapply reducts_incl_trans with (C' := fun x => Eassign e1 x ty); eauto.
  destruct (is_loc e1) as [[[b ofs] ty1]|]_eqn; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|]_eqn; eauto.
(* assignop left *)
  eapply reducts_incl_trans with (C' := fun x => Eassignop op x e2 tyres ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|]_eqn; eauto.
(* assignop right *)
  eapply reducts_incl_trans with (C' := fun x => Eassignop op e1 x tyres ty); eauto.
  destruct (is_loc e1) as [[[b ofs] ty1]|]_eqn; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|]_eqn; eauto.
(* postincr *)
  eapply reducts_incl_trans with (C' := fun x => Epostincr id x ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|]_eqn; eauto.
(* call left *)
  eapply reducts_incl_trans with (C' := fun x => Ecall x el ty); eauto.
  destruct (is_val (C a)) as [[v ty']|]_eqn; eauto.
(* call right *)
  eapply reducts_incl_trans with (C' := fun x => Ecall e1 x ty). apply step_exprlist_context. auto. 
  destruct (is_val e1) as [[v1 ty1]|]_eqn; eauto.
  destruct (is_val_list (C a)) as [vl|]_eqn; eauto.
(* comma *)
  eapply reducts_incl_trans with (C' := fun x => Ecomma x e2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|]_eqn; eauto.
(* paren *)
  eapply reducts_incl_trans with (C' := fun x => Eparen x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|]_eqn; eauto.

  induction 1; simpl; intros.
(* cons left *)
  eapply reducts_incl_trans with (C' := fun x => Econs x el).
  apply step_expr_context; eauto. eauto.
(* binop right *)
  eapply reducts_incl_trans with (C' := fun x => Econs e1 x).
  apply step_exprlist_context; eauto. eauto.
Qed.

(** Completeness, part 2: given a safe expression, [step_expr] does not return [None]. *)

Lemma topred_none:
  forall rd, topred rd <> None.
Proof.
  intros; unfold topred; congruence.
Qed.

Lemma incontext_none:
  forall (A B: Type) (C: A -> B) rds,
  rds <> None -> incontext C rds <> None.
Proof.
  unfold incontext; intros. destruct rds; congruence.
Qed.

Lemma incontext2_none:
  forall (A1 A2 B: Type) (C1: A1 -> B) rds1 (C2: A2 -> B) rds2,
  rds1 <> None -> rds2 <> None -> incontext2 C1 rds1 C2 rds2 <> None.
Proof.
  unfold incontext2; intros. destruct rds1; destruct rds2; congruence.
Qed.

Lemma safe_expr_kind:
  forall k C a m,
  context k RV C ->
  not_stuck ge e (C a) m ->
  k = Cstrategy.expr_kind a.
Proof.
  intros.
  symmetry. eapply Cstrategy.not_imm_stuck_kind; eauto.
Qed.

Lemma safe_inversion:
  forall k C a m,
  context k RV C ->
  not_stuck ge e (C a) m ->
  match a with
  | Eloc _ _ _ => True
  | Eval _ _ => True
  | _ => Cstrategy.invert_expr_prop ge e a m
  end.
Proof.
  intros. eapply Cstrategy.not_imm_stuck_inv; eauto.
Qed. 

Lemma is_val_list_all_values:
  forall al vtl, is_val_list al = Some vtl -> Cstrategy.exprlist_all_values al.
Proof.
  induction al; simpl; intros. auto. 
  destruct (is_val r1) as [[v ty]|]_eqn; try discriminate.
  destruct (is_val_list al) as [vtl'|]_eqn; try discriminate.
  rewrite (is_val_inv _ _ _ Heqo). eauto.
Qed.

Theorem step_expr_defined:
  forall a k m C,
  context k RV C ->
  not_stuck ge e (C a) m ->
  step_expr k a m <> None
with step_exprlist_defined:
  forall al m C,
  Cstrategy.contextlist' C ->
  not_stuck ge e (C al) m ->
  step_exprlist al m <> None.
Proof.
  induction a; intros k m C CTX NS; 
  rewrite (safe_expr_kind _ _ _ _ CTX NS);
  rewrite (safe_expr_kind _ _ _ _ CTX NS) in CTX;
  simpl in *;
  generalize (safe_inversion _ _ _ _ CTX NS); intro INV.
(* val *)
  congruence.
(* var *)
  red in INV. destruct INV as [b [P | [P [Q R]]]].
  rewrite P; rewrite dec_eq_true. apply topred_none.
  rewrite P; rewrite Q; rewrite R; rewrite dec_eq_true. apply topred_none.
(* field *)
  destruct (is_loc a) as [[[b ofs] ty']|]_eqn. 
  rewrite (is_loc_inv _ _ _ _ Heqo) in INV. red in INV. 
  destruct ty'; try contradiction. destruct INV as [delta EQ]. rewrite EQ. apply topred_none.
  apply topred_none.
  apply incontext_none. apply IHa with (C := fun x => C(Efield x f ty)); eauto.
(* valof *)
  destruct (is_loc a) as [[[b ofs] ty']|]_eqn. 
  rewrite (is_loc_inv _ _ _ _ Heqo) in INV. red in INV. destruct INV as [EQ [v LD]]. subst.
  rewrite dec_eq_true; rewrite LD; apply topred_none.
  apply incontext_none. apply IHa with (C := fun x => C(Evalof x ty)); eauto.
(* deref *)
  destruct (is_val a) as [[v ty']|]_eqn. 
  rewrite (is_val_inv _ _ _ Heqo) in INV. red in INV. destruct INV as [b [ofs EQ]]. subst. 
  apply topred_none.
  apply incontext_none. apply IHa with (C := fun x => C(Ederef x ty)); eauto.
(* addrof *) 
  destruct (is_loc a) as [[[b ofs] ty']|]_eqn. 
  apply topred_none.
  apply incontext_none. apply IHa with (C := fun x => C(Eaddrof x ty)); eauto.
(* unop *)
  destruct (is_val a) as [[v1 ty1]|]_eqn. 
  rewrite (is_val_inv _ _ _ Heqo) in INV. red in INV. destruct INV as [v EQ].
  rewrite EQ; apply topred_none.
  apply incontext_none. apply IHa with (C := fun x => C(Eunop op x ty)); eauto.
(* binop *)
  destruct (is_val a1) as [[v1 ty1]|]_eqn. 
  destruct (is_val a2) as [[v2 ty2]|]_eqn. 
  rewrite (is_val_inv _ _ _ Heqo) in INV.
  rewrite (is_val_inv _ _ _ Heqo0) in INV. red in INV. destruct INV as [v EQ].
  rewrite EQ; apply topred_none.
  apply incontext2_none. apply IHa1 with (C := fun x => C(Ebinop op x a2 ty)); eauto. apply IHa2 with (C := fun x => C(Ebinop op a1 x ty)); eauto.
  apply incontext2_none. apply IHa1 with (C := fun x => C(Ebinop op x a2 ty)); eauto. apply IHa2 with (C := fun x => C(Ebinop op a1 x ty)); eauto.
(* cast *)
  destruct (is_val a) as [[v1 ty1]|]_eqn. 
  rewrite (is_val_inv _ _ _ Heqo) in INV. red in INV. destruct INV as [v EQ].
  rewrite EQ; apply topred_none.
  apply incontext_none. apply IHa with (C := fun x => C(Ecast x ty)); eauto.
(* condition *)
  destruct (is_val a1) as [[v1 ty1]|]_eqn. 
  rewrite (is_val_inv _ _ _ Heqo) in INV. red in INV. destruct INV as [v EQ].
  rewrite EQ; apply topred_none.
  apply incontext_none. apply IHa1 with (C := fun x => C(Econdition x a2 a3 ty)); eauto.
(* sizeof *)
  apply topred_none.
(* assign *)
  destruct (is_loc a1) as [[[b ofs] ty1]|]_eqn. 
  destruct (is_val a2) as [[v2 ty2]|]_eqn. 
  rewrite (is_loc_inv _ _ _ _ Heqo) in INV.
  rewrite (is_val_inv _ _ _ Heqo0) in INV. red in INV. 
  destruct INV as [v [m' [P [Q R]]]]. 
  subst. rewrite dec_eq_true; rewrite Q; rewrite R; apply topred_none.
  apply incontext2_none. apply IHa1 with (C := fun x => C(Eassign x a2 ty)); eauto. apply IHa2 with (C := fun x => C(Eassign a1 x ty)); eauto.
  apply incontext2_none. apply IHa1 with (C := fun x => C(Eassign x a2 ty)); eauto. apply IHa2 with (C := fun x => C(Eassign a1 x ty)); eauto.
(* assignop *)
  destruct (is_loc a1) as [[[b ofs] ty1]|]_eqn. 
  destruct (is_val a2) as [[v2 ty2]|]_eqn. 
  rewrite (is_loc_inv _ _ _ _ Heqo) in INV.
  rewrite (is_val_inv _ _ _ Heqo0) in INV. red in INV. 
  destruct INV as [v1 [v [v' [m' [P [Q [R [S T]]]]]]]]. 
  subst. rewrite dec_eq_true; rewrite Q; rewrite R; rewrite S; rewrite T; apply topred_none.
  apply incontext2_none. apply IHa1 with (C := fun x => C(Eassignop op x a2 tyres ty)); eauto. apply IHa2 with (C := fun x => C(Eassignop op a1 x tyres ty)); eauto.
  apply incontext2_none. apply IHa1 with (C := fun x => C(Eassignop op x a2 tyres ty)); eauto. apply IHa2 with (C := fun x => C(Eassignop op a1 x tyres ty)); eauto.
(* postincr *)
  destruct (is_loc a) as [[[b ofs] ty1]|]_eqn. 
  rewrite (is_loc_inv _ _ _ _ Heqo) in INV. red in INV. 
  destruct INV as [v1 [v2 [v3 [m' [P [Q [R [S T]]]]]]]]. 
  subst. rewrite dec_eq_true; rewrite Q; rewrite R; rewrite S; rewrite T; apply topred_none.
  apply incontext_none. apply IHa with (C := fun x => C(Epostincr id x ty)); eauto.
(* comma *)
  destruct (is_val a1) as [[v1 ty1]|]_eqn. 
  rewrite (is_val_inv _ _ _ Heqo) in INV. red in INV. rewrite INV.
  rewrite dec_eq_true; apply topred_none.
  apply incontext_none. apply IHa1 with (C := fun x => C(Ecomma x a2 ty)); eauto.
(* call *)
  destruct (is_val a) as [[vf tyf]|]_eqn. 
  destruct (is_val_list rargs) as [vtl|]_eqn. 
  rewrite (is_val_inv _ _ _ Heqo) in INV. red in INV. 
  destruct INV as [tyargs [tyres [fd [vl [P [Q [R S]]]]]]].
  eapply is_val_list_all_values; eauto.
  rewrite P; rewrite Q. 
  exploit sem_cast_arguments_complete; eauto. intros [vtl' [U V]]. 
  assert (vtl' = vtl) by congruence. subst. rewrite V. rewrite S. rewrite dec_eq_true. 
  apply topred_none.
  apply incontext2_none. apply IHa with (C := fun x => C(Ecall x rargs ty)); eauto.
  apply step_exprlist_defined with (C := fun x => C(Ecall a x ty)); auto.
  apply Cstrategy.contextlist'_intro with (rl0 := Enil). auto.
  apply incontext2_none. apply IHa with (C := fun x => C(Ecall x rargs ty)); eauto.
  apply step_exprlist_defined with (C := fun x => C(Ecall a x ty)); auto.
  apply Cstrategy.contextlist'_intro with (rl0 := Enil). auto.
(* loc *)
  congruence.
(* paren *)
  destruct (is_val a) as [[v1 ty1]|]_eqn. 
  rewrite (is_val_inv _ _ _ Heqo) in INV. red in INV. destruct INV as [v EQ].
  rewrite EQ; apply topred_none.
  apply incontext_none. apply IHa with (C := fun x => C(Eparen x ty)); eauto.

  induction al; intros; simpl.
(* nil *)
  congruence.
(* cons *)
  apply incontext2_none.
  apply step_expr_defined with (C := fun x => C(Econs x al)); eauto. 
  apply Cstrategy.contextlist'_head; auto.
  apply IHal with (C := fun x => C(Econs r1 x)); auto.
  apply Cstrategy.contextlist'_tail; auto.
Qed.

(** Connections between [not_stuck] and [step_expr]. *)

Lemma step_expr_not_imm_stuck:
  forall k a m,
  step_expr k a m <> None ->
  not_imm_stuck ge e k a m.
Proof.
  intros. generalize (step_expr_sound a k m). unfold reducts_ok. 
  destruct (step_expr k a m) as [ll|]. destruct ll.
(* value or location *)
  destruct k; destruct a; simpl; intros; try congruence. 
  apply not_stuck_loc.
  apply Csem.not_stuck_val.
(* reducible *)
  intros R. destruct p as [C1 rd1]. destruct (R C1 rd1) as [P [a' [U V]]]; auto with coqlib.
  subst a. red in V. destruct rd1. 
  eapply not_stuck_lred; eauto. 
  eapply not_stuck_rred; eauto.
  destruct V. subst m'. eapply not_stuck_callred; eauto.
(* stuck *)
  congruence.
Qed.

Lemma step_expr_not_stuck:
  forall a m,
  step_expr RV a m <> None ->
  not_stuck ge e a m.
Proof.
  intros; red; intros. subst a. 
  apply step_expr_not_imm_stuck.
  generalize (step_expr_context _ _ C H0 e' m). unfold reducts_incl. 
  destruct (step_expr k e' m). congruence.
  destruct (step_expr RV (C e') m). tauto. congruence.
Qed.

Lemma not_stuck_step_expr:
  forall a m,
  not_stuck ge e a m ->
  step_expr RV a m <> None.
Proof.
  intros. apply step_expr_defined with (C := fun x => x); auto. 
Qed.

End EXPRS.

(** * External functions and events. *)

Section EVENTS.

Variable F V: Type.
Variable genv: Genv.t F V.

Definition eventval_of_val (v: val) (t: typ) : option eventval :=
  match v, t with
  | Vint i, AST.Tint => Some (EVint i)
  | Vfloat f, AST.Tfloat => Some (EVfloat f)
  | Vptr b ofs, AST.Tint => do id <- Genv.invert_symbol genv b; Some (EVptr_global id ofs)
  | _, _ => None
  end.

Fixpoint list_eventval_of_val (vl: list val) (tl: list typ) : option (list eventval) :=
  match vl, tl with
  | nil, nil => Some nil
  | v1::vl, t1::tl =>
      do ev1 <- eventval_of_val v1 t1;
      do evl <- list_eventval_of_val vl tl;
      Some (ev1 :: evl)
  | _, _ => None
  end.

Definition val_of_eventval (ev: eventval) (t: typ) : option val :=
  match ev, t with
  | EVint i, AST.Tint => Some (Vint i)
  | EVfloat f, AST.Tfloat => Some (Vfloat f)
  | EVptr_global id ofs, AST.Tint => do b <- Genv.find_symbol genv id; Some (Vptr b ofs)
  | _, _ => None
  end.

Lemma eventval_of_val_sound:
  forall v t ev, eventval_of_val v t = Some ev -> eventval_match genv ev t v.
Proof.
  intros. destruct v; destruct t; simpl in H; inv H.
  constructor.
  constructor.
  destruct (Genv.invert_symbol genv b) as [id|]_eqn; inv H1. 
  constructor. apply Genv.invert_find_symbol; auto.
Qed.

Lemma eventval_of_val_complete:
  forall ev t v, eventval_match genv ev t v -> eventval_of_val v t = Some ev.
Proof.
  induction 1; simpl; auto.
  rewrite (Genv.find_invert_symbol _ _ H). auto. 
Qed.

Lemma list_eventval_of_val_sound:
  forall vl tl evl, list_eventval_of_val vl tl = Some evl -> eventval_list_match genv evl tl vl.
Proof with try discriminate.
  induction vl; destruct tl; simpl; intros; inv H.
  constructor.
  destruct (eventval_of_val a t) as [ev1|]_eqn...
  destruct (list_eventval_of_val vl tl) as [evl'|]_eqn...
  inv H1. constructor. apply eventval_of_val_sound; auto. eauto.
Qed.

Lemma list_eventval_of_val_complete:
  forall evl tl vl, eventval_list_match genv evl tl vl -> list_eventval_of_val vl tl = Some evl.
Proof.
  induction 1; simpl. auto. 
  rewrite (eventval_of_val_complete _ _ _ H). rewrite IHeventval_list_match. auto.
Qed.

Lemma val_of_eventval_sound:
  forall ev t v, val_of_eventval ev t = Some v -> eventval_match genv ev t v.
Proof.
  intros. destruct ev; destruct t; simpl in H; inv H.
  constructor.
  constructor.
  destruct (Genv.find_symbol genv i) as [b|]_eqn; inv H1.
  constructor. auto.
Qed.

Lemma val_of_eventval_complete:
  forall ev t v, eventval_match genv ev t v -> val_of_eventval ev t = Some v.
Proof.
  induction 1; simpl; auto. rewrite H; auto.
Qed.

(** System calls and library functions *)

Definition do_ef_external (name: ident) (sg: signature)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do args <- list_eventval_of_val vargs (sig_args sg);
  match nextworld_io w name args with
  | None => None
  | Some(res, w') =>
      do vres <- val_of_eventval res (proj_sig_res sg);
      Some(w', Event_syscall name args res :: E0, vres, m)
  end.

Definition do_ef_volatile_load (chunk: memory_chunk)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b ofs :: nil =>
      if block_is_volatile genv b then
        do id <- Genv.invert_symbol genv b;
        match nextworld_vload w chunk id ofs with
        | None => None
        | Some(res, w') =>
            do vres <- val_of_eventval res (type_of_chunk chunk);
            Some(w', Event_vload chunk id ofs res :: nil, Val.load_result chunk vres, m)
        end
      else
        do v <- Mem.load chunk m b (Int.unsigned ofs);
        Some(w, E0, v, m)
  | _ => None
  end.

Definition do_ef_volatile_store (chunk: memory_chunk)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b ofs :: v :: nil =>
      if block_is_volatile genv b then
        do id <- Genv.invert_symbol genv b;
        do ev <- eventval_of_val v (type_of_chunk chunk);
        do w' <- nextworld_vstore w chunk id ofs ev;
        Some(w', Event_vstore chunk id ofs ev :: nil, Vundef, m)
      else
        do m' <- Mem.store chunk m b (Int.unsigned ofs) v;
        Some(w, E0, Vundef, m')
  | _ => None
  end.

Definition do_ef_volatile_load_global (chunk: memory_chunk) (id: ident) (ofs: int)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match Genv.find_symbol genv id with
  | Some b => do_ef_volatile_load chunk w (Vptr b ofs :: vargs) m
  | None => None
  end.

Definition do_ef_volatile_store_global (chunk: memory_chunk) (id: ident) (ofs: int)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match Genv.find_symbol genv id with
  | Some b => do_ef_volatile_store chunk w (Vptr b ofs :: vargs) m
  | None => None
  end.

Definition do_ef_malloc
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vint n :: nil =>
      let (m', b) := Mem.alloc m (-4) (Int.unsigned n) in
      do m'' <- Mem.store Mint32 m' b (-4) (Vint n);
      Some(w, E0, Vptr b Int.zero, m'')
  | _ => None
  end.

Definition do_ef_free
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b lo :: nil =>
      do vsz <- Mem.load Mint32 m b (Int.unsigned lo - 4);
      match vsz with
      | Vint sz =>
          check (zlt 0 (Int.unsigned sz));
          do m' <- Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz);
          Some(w, E0, Vundef, m')
      | _ => None
      end
  | _ => None
  end.

Definition memcpy_args_ok
  (sz al: Z) (bdst: block) (odst: Z) (bsrc: block) (osrc: Z) : Prop :=
      (al = 1 \/ al = 2 \/ al = 4)
   /\ sz > 0
   /\ (al | sz) /\ (al | osrc) /\ (al | odst)
   /\ (bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc).

Remark memcpy_check_args:
  forall sz al bdst odst bsrc osrc,
  {memcpy_args_ok sz al bdst odst bsrc osrc} + {~memcpy_args_ok sz al bdst odst bsrc osrc}.
Proof with try (right; intuition omega).
  intros. 
  assert (X: {al = 1 \/ al = 2 \/ al = 4} + {~(al = 1 \/ al = 2 \/ al = 4)}).
    destruct (zeq al 1); auto. destruct (zeq al 2); auto. destruct (zeq al 4); auto...
  unfold memcpy_args_ok. destruct X...
  assert (al > 0) by (intuition omega).
  destruct (zlt 0 sz)...
  destruct (Zdivide_dec al sz); auto...
  destruct (Zdivide_dec al osrc); auto...
  destruct (Zdivide_dec al odst); auto...
  assert (Y: {bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc}
           +{~(bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc)}).
    destruct (eq_block bsrc bdst); auto.
    destruct (zeq osrc odst); auto.
    destruct (zle (osrc + sz) odst); auto.
    destruct (zle (odst + sz) osrc); auto.
    right; intuition omega.
  destruct Y... left; intuition omega.
Qed.

Definition do_ef_memcpy (sz al: Z)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr bdst odst :: Vptr bsrc osrc :: nil =>
      if memcpy_check_args sz al bdst (Int.unsigned odst) bsrc (Int.unsigned osrc) then
        do bytes <- Mem.loadbytes m bsrc (Int.unsigned osrc) sz;
        do m' <- Mem.storebytes m bdst (Int.unsigned odst) bytes;
        Some(w, E0, Vundef, m')
      else None
  | _ => None
  end.

Definition do_ef_annot (text: ident) (targs: list typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do args <- list_eventval_of_val vargs targs;
  Some(w, Event_annot text args :: E0, Vundef, m).

Definition do_ef_annot_val (text: ident) (targ: typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | varg :: nil =>
      do arg <- eventval_of_val varg targ;
      Some(w, Event_annot text (arg :: nil) :: E0, varg, m)
  | _ => None
  end.

Definition do_external (ef: external_function):
       world -> list val -> mem -> option (world * trace * val * mem) :=
  match ef with
  | EF_external name sg => do_ef_external name sg
  | EF_builtin name sg => do_ef_external name sg
  | EF_vload chunk => do_ef_volatile_load chunk
  | EF_vstore chunk => do_ef_volatile_store chunk
  | EF_vload_global chunk id ofs => do_ef_volatile_load_global chunk id ofs
  | EF_vstore_global chunk id ofs => do_ef_volatile_store_global chunk id ofs
  | EF_malloc => do_ef_malloc
  | EF_free => do_ef_free
  | EF_memcpy sz al => do_ef_memcpy sz al
  | EF_annot text targs => do_ef_annot text targs
  | EF_annot_val text targ => do_ef_annot_val text targ
  end.

Ltac mydestr :=
  match goal with
  | [ |- None = Some _ -> _ ] => intro X; discriminate
  | [ |- Some _ = Some _ -> _ ] => intro X; inv X
  | [ |- match ?x with Some _ => _ | None => _ end = Some _ -> _ ] => destruct x as []_eqn; mydestr
  | [ |- match ?x with true => _ | false => _ end = Some _ -> _ ] => destruct x as []_eqn; mydestr
  | [ |- match ?x with left _ => _ | right _ => _ end = Some _ -> _ ] => destruct x; mydestr
  | _ => idtac
  end.

Lemma do_ef_external_sound:
  forall ef w vargs m w' t vres m',
  do_external ef w vargs m = Some(w', t, vres, m') ->
  external_call ef genv vargs m t vres m' /\ possible_trace w t w'.
Proof with try congruence.
  intros until m'.
  assert (IO: forall name sg,
             do_ef_external name sg w vargs m = Some(w', t, vres, m') ->
             extcall_io_sem name sg genv vargs m t vres m' /\ possible_trace w t w').
    intros until sg. unfold do_ef_external. mydestr. destruct p as [res w'']; mydestr.
    split. econstructor. apply list_eventval_of_val_sound; auto. 
    apply val_of_eventval_sound; auto. 
    econstructor. constructor; eauto. constructor.

  assert (VLOAD: forall chunk vargs,
    do_ef_volatile_load chunk w vargs m = Some (w', t, vres, m') ->
    volatile_load_sem chunk genv vargs m t vres m' /\ possible_trace w t w').
  intros chunk vargs'.
  unfold do_ef_volatile_load. destruct vargs'... destruct v... destruct vargs'... 
  mydestr. destruct p as [res w'']; mydestr.
  split. constructor. apply Genv.invert_find_symbol; auto. auto. 
  apply val_of_eventval_sound; auto. 
  econstructor. constructor; eauto. constructor.
  split. constructor; auto. constructor.

  assert (VSTORE: forall chunk vargs,
    do_ef_volatile_store chunk w vargs m = Some (w', t, vres, m') ->
    volatile_store_sem chunk genv vargs m t vres m' /\ possible_trace w t w').
  intros chunk vargs'.
  unfold do_ef_volatile_store. destruct vargs'... destruct v... destruct vargs'... destruct vargs'... 
  mydestr.
  split. constructor. apply Genv.invert_find_symbol; auto. auto. 
  apply eventval_of_val_sound; auto. 
  econstructor. constructor; eauto. constructor.
  split. constructor; auto. constructor.

  destruct ef; simpl.
(* EF_external *)
  auto. 
(* EF_builtin *)
  auto.
(* EF_vload *)
  auto.
(* EF_vstore *)
  auto.
(* EF_vload_global *)
  rewrite volatile_load_global_charact.
  unfold do_ef_volatile_load_global. destruct (Genv.find_symbol genv)...
  intros. exploit VLOAD; eauto. intros [A B]. split; auto. exists b; auto.
(* EF_vstore_global *)
  rewrite volatile_store_global_charact.
  unfold do_ef_volatile_store_global. destruct (Genv.find_symbol genv)...
  intros. exploit VSTORE; eauto. intros [A B]. split; auto. exists b; auto.
(* EF_malloc *)
  unfold do_ef_malloc. destruct vargs... destruct v... destruct vargs...
  destruct (Mem.alloc m (-4) (Int.unsigned i)) as [m1 b]_eqn. mydestr.
  split. econstructor; eauto. constructor.
(* EF_free *)
  unfold do_ef_free. destruct vargs... destruct v... destruct vargs... 
  mydestr. destruct v... mydestr. 
  split. econstructor; eauto. omega. constructor.
(* EF_memcpy *)
  unfold do_ef_memcpy. destruct vargs... destruct v... destruct vargs... 
  destruct v... destruct vargs... mydestr. red in m0. 
  split. econstructor; eauto; tauto. constructor.
(* EF_annot *)
  unfold do_ef_annot. mydestr. 
  split. constructor. apply list_eventval_of_val_sound; auto.
  econstructor. constructor; eauto. constructor.
(* EF_annot_val *)
  unfold do_ef_annot_val. destruct vargs... destruct vargs... mydestr. 
  split. constructor. apply eventval_of_val_sound; auto.
  econstructor. constructor; eauto. constructor.
Qed.

Lemma do_ef_external_complete:
  forall ef w vargs m w' t vres m',
  external_call ef genv vargs m t vres m' -> possible_trace w t w' ->
  do_external ef w vargs m = Some(w', t, vres, m').
Proof.
  intros.
  assert (IO: forall name sg,
             extcall_io_sem name sg genv vargs m t vres m' ->
             do_ef_external name sg w vargs m = Some (w', t, vres, m')).
    intros. inv H1. inv H0. inv H8. inv H6. 
    unfold do_ef_external. rewrite (list_eventval_of_val_complete _ _ _ H2). rewrite H8. 
    rewrite (val_of_eventval_complete _ _ _ H3). auto.
 
  assert (VLOAD: forall chunk vargs,
             volatile_load_sem chunk genv vargs m t vres m' ->
             do_ef_volatile_load chunk w vargs m = Some (w', t, vres, m')).
  intros. inv H1; unfold do_ef_volatile_load.
  inv H0. inv H9. inv H7. 
  rewrite H3. rewrite (Genv.find_invert_symbol _ _ H2). rewrite H10. 
  rewrite (val_of_eventval_complete _ _ _ H4). auto.
  inv H0. rewrite H2. rewrite H3. auto.

  assert (VSTORE: forall chunk vargs,
             volatile_store_sem chunk genv vargs m t vres m' ->
             do_ef_volatile_store chunk w vargs m = Some (w', t, vres, m')).
  intros. inv H1; unfold do_ef_volatile_store.
  inv H0. inv H9. inv H7. 
  rewrite H3. rewrite (Genv.find_invert_symbol _ _ H2).
  rewrite (eventval_of_val_complete _ _ _ H4). rewrite H10. auto.
  inv H0. rewrite H2. rewrite H3. auto.

  destruct ef; simpl in *.
(* EF_external *)
  auto.
(* EF_builtin *)
  auto.
(* EF_vload *)
  auto.
(* EF_vstore *)
  auto.
(* EF_vload_global *)
  rewrite volatile_load_global_charact in H. destruct H as [b [P Q]]. 
  unfold do_ef_volatile_load_global. rewrite P. auto. 
(* EF_vstore *)
  rewrite volatile_store_global_charact in H. destruct H as [b [P Q]]. 
  unfold do_ef_volatile_store_global. rewrite P. auto. 
(* EF_malloc *)
  inv H; unfold do_ef_malloc. 
  inv H0. rewrite H1. rewrite H2. auto.
(* EF_free *)
  inv H; unfold do_ef_free.
  inv H0. rewrite H1. rewrite zlt_true. rewrite H3. auto. omega.
(* EF_memcpy *)
  inv H; unfold do_ef_memcpy.
  inv H0. rewrite pred_dec_true. rewrite H7; rewrite H8; auto.
  red. tauto. 
(* EF_annot *)
  inv H; unfold do_ef_annot. inv H0. inv H6. inv H4. 
  rewrite (list_eventval_of_val_complete _ _ _ H1). auto.
(* EF_annot_val *)
  inv H; unfold do_ef_annot_val. inv H0. inv H6. inv H4. 
  rewrite (eventval_of_val_complete _ _ _ H1). auto.
Qed.

End EVENTS.

(** * Transitions over states. *)

Fixpoint do_alloc_variables (e: env) (m: mem) (l: list (ident * type)) {struct l} : env * mem :=
  match l with
  | nil => (e,m)
  | (id, ty) :: l' =>
      let (m1,b1) := Mem.alloc m 0 (sizeof ty) in 
      do_alloc_variables (PTree.set id (b1, ty) e) m1 l'
end.

Lemma do_alloc_variables_sound:
  forall l e m, alloc_variables e m l (fst (do_alloc_variables e m l)) (snd (do_alloc_variables e m l)).
Proof.
  induction l; intros; simpl. 
  constructor.
  destruct a as [id ty]. destruct (Mem.alloc m 0 (sizeof ty)) as [m1 b1]_eqn; simpl.
  econstructor; eauto.
Qed.

Lemma do_alloc_variables_complete:
  forall e1 m1 l e2 m2, alloc_variables e1 m1 l e2 m2 ->
  do_alloc_variables e1 m1 l = (e2, m2).
Proof.
  induction 1; simpl. 
  auto.
  rewrite H; rewrite IHalloc_variables; auto. 
Qed.

Function sem_bind_parameters (e: env) (m: mem) (l: list (ident * type)) (lv: list val) 
                          {struct l} : option mem :=
  match l, lv  with
  | nil, nil => Some m
  | (id, ty) :: params, v1::lv =>
      match PTree.get id e with
         | Some (b, ty') =>
             check (type_eq ty ty');
             do m1 <- store_value_of_type ty m b Int.zero v1;
             sem_bind_parameters e m1 params lv
        | None => None
      end
   | _, _ => None
end.

Lemma sem_bind_parameters_sound : forall e m l lv m',
  sem_bind_parameters e m l lv = Some m' -> 
  bind_parameters e m l lv m'.
Proof.
   intros; functional induction (sem_bind_parameters e m l lv); try discriminate.
   inversion H; constructor; auto.  
   econstructor; eauto.
Qed.

Lemma sem_bind_parameters_complete : forall e m l lv m',
  bind_parameters e m l lv m' ->
  sem_bind_parameters e m l lv = Some m'.
Proof.
   induction 1; simpl; auto.
   rewrite H. rewrite dec_eq_true. 
   destruct (store_value_of_type ty m b Int.zero v1); try discriminate.
   inv H0; auto.
Qed.

Definition expr_final_state (f: function) (k: cont) (e: env) (C_rd: (expr -> expr) * reduction) :=
  match snd C_rd with
  | Lred a m => (E0, ExprState f (fst C_rd a) k e m)
  | Rred a m => (E0, ExprState f (fst C_rd a) k e m)
  | Callred fd vargs ty m => (E0, Callstate fd vargs (Kcall f e (fst C_rd) ty k) m)
  end.

Local Open Scope list_monad_scope.

Definition ret (S: state) : list (trace * state) := (E0, S) :: nil.

Definition do_step (w: world) (s: state) : list (trace * state) :=
  match s with

  | ExprState f a k e m =>
      match is_val a with
      | Some(v, ty) =>
        match k with
        | Kdo k => ret (State f Sskip k e m )
        | Kifthenelse s1 s2 k =>
            do b <- bool_val v ty; ret (State f (if b then s1 else s2) k e m)
        | Kwhile1 x s k =>
            do b <- bool_val v ty; 
            if b then ret (State f s (Kwhile2 x s k) e m) else ret (State f Sskip k e m)
        | Kdowhile2 x s k =>
            do b <- bool_val v ty;
            if b then ret (State f (Sdowhile x s) k e m) else ret (State f Sskip k e m)
        | Kfor2 a2 a3 s k =>
            do b <- bool_val v ty;
            if b then ret (State f s (Kfor3 a2 a3 s k) e m) else ret (State f Sskip k e m)
        | Kreturn k =>
            do v' <- sem_cast v ty f.(fn_return);
            do m' <- Mem.free_list m (blocks_of_env e);
            ret (Returnstate v' (call_cont k) m')
        | Kswitch1 sl k =>
            match v with
            | Vint n => ret (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m)
            | _ => nil
            end
        | _ => nil
        end

      | None =>
          match step_expr e RV a m with
          | None => nil
          | Some ll => map (expr_final_state f k e) ll
          end
      end

  | State f (Sdo x) k e m => ret(ExprState f x (Kdo k) e m)

  | State f (Ssequence s1 s2) k e m => ret(State f s1 (Kseq s2 k) e m)
  | State f Sskip (Kseq s k) e m => ret (State f s k e m)
  | State f Scontinue (Kseq s k) e m => ret (State f Scontinue k e m)
  | State f Sbreak (Kseq s k) e m => ret (State f Sbreak k e m)

  | State f (Sifthenelse a s1 s2) k e m => ret (ExprState f a (Kifthenelse s1 s2 k) e m)

  | State f (Swhile x s) k e m => ret (ExprState f x (Kwhile1 x s k) e m)
  | State f (Sskip|Scontinue) (Kwhile2 x s k) e m => ret (State f (Swhile x s) k e m)
  | State f Sbreak (Kwhile2 x s k) e m => ret (State f Sskip k e m)

  | State f (Sdowhile a s) k e m => ret (State f s (Kdowhile1 a s k) e m)
  | State f (Sskip|Scontinue) (Kdowhile1 x s k) e m => ret (ExprState f x (Kdowhile2 x s k) e m)
  | State f Sbreak (Kdowhile1 x s k) e m => ret (State f Sskip k e m)

  | State f (Sfor a1 a2 a3 s) k e m =>
      if is_skip a1
      then ret (ExprState f a2 (Kfor2 a2 a3 s k) e m)
      else ret (State f a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
  | State f Sskip (Kfor3 a2 a3 s k) e m => ret (State f a3 (Kfor4 a2 a3 s k) e m)
  | State f Scontinue (Kfor3 a2 a3 s k) e m => ret (State f a3 (Kfor4 a2 a3 s k) e m)
  | State f Sbreak (Kfor3 a2 a3 s k) e m => ret (State f Sskip k e m)
  | State f Sskip (Kfor4 a2 a3 s k) e m => ret (State f (Sfor Sskip a2 a3 s) k e m)

  | State f (Sreturn None) k e m =>
      do m' <- Mem.free_list m (blocks_of_env e);
      ret (Returnstate Vundef (call_cont k) m')
  | State f (Sreturn (Some x)) k e m => ret (ExprState f x (Kreturn k) e m)
  | State f Sskip ((Kstop | Kcall _ _ _ _ _) as k) e m => 
     check (type_eq f.(fn_return) Tvoid);
     do m' <- Mem.free_list m (blocks_of_env e);
     ret (Returnstate Vundef k m')

  | State f (Sswitch x sl) k e m => ret (ExprState f x (Kswitch1 sl k) e m)
  | State f (Sskip|Sbreak) (Kswitch2 k) e m => ret (State f Sskip k e m)
  | State f Scontinue (Kswitch2 k) e m => ret (State f Scontinue k e m)

  | State f (Slabel lbl s) k e m => ret (State f s k e m)
  | State f (Sgoto lbl) k e m =>
      match find_label lbl f.(fn_body) (call_cont k) with
      | Some(s', k') => ret (State f s' k' e m)
      | None => nil
      end

  | Callstate (Internal f) vargs k m =>
      check (list_norepet_dec ident_eq (var_names (fn_params f) ++ var_names (fn_vars f)));
      let (e,m1) := do_alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) in
      do m2 <- sem_bind_parameters e m1 f.(fn_params) vargs;
      ret (State f f.(fn_body) k e m2)
  | Callstate (External ef _ _) vargs k m =>
      match do_external _ _ ge ef w vargs m with
      | None => nil
      | Some(w',t,v,m') => (t, Returnstate v k m') :: nil
      end

  | Returnstate v (Kcall f e C ty k) m => ret (ExprState f (C (Eval v ty)) k e m)

  | _ => nil
  end.

Ltac myinv :=
  match goal with
  | [ |- In _ nil -> _ ] => intro X; elim X
  | [ |- In _ (ret _) -> _ ] => 
        intro X; elim X; clear X;
        [intro EQ; unfold ret in EQ; inv EQ; myinv | myinv]
  | [ |- In _ (_ :: nil) -> _ ] => 
        intro X; elim X; clear X; [intro EQ; inv EQ; myinv | myinv]
  | [ |- In _ (match ?x with Some _ => _ | None => _ end) -> _ ] => destruct x as []_eqn; myinv
  | [ |- In _ (match ?x with false => _ | true => _ end) -> _ ] => destruct x as []_eqn; myinv
  | [ |- In _ (match ?x with left _ => _ | right _ => _ end) -> _ ] => destruct x; myinv
  | _ => idtac
  end.

Hint Extern 3 => exact I.

Lemma do_step_sound:
  forall w S t S', In (t, S') (do_step w S) -> Csem.step ge S t S'.
Proof with try (right; econstructor; eauto; fail).
  intros until S'. destruct S; simpl.
(* State *)
  destruct s; myinv...
  (* skip *)
  destruct k; myinv...
  (* break *)
  destruct k; myinv...
  (* continue *)
  destruct k; myinv...
  (* goto *)
  destruct p as [s' k']. myinv...
(* ExprState *)
  destruct (is_val r) as [[v ty]|]_eqn.
  (* expression is a value *)
  rewrite (is_val_inv _ _ _ Heqo).
  destruct k; myinv...
  destruct v; myinv...
  (* expression reduces *)
  destruct (step_expr e RV r m) as [ll|]_eqn; try contradiction. intros.
  exploit list_in_map_inv; eauto. intros [[C rd] [A B]].
  generalize (step_expr_sound e r RV m). unfold reducts_ok. rewrite Heqr0. 
  destruct ll; try contradiction. intros SOUND. 
  exploit SOUND; eauto. intros [CTX [a [EQ RD]]]. subst r. 
  unfold expr_final_state in A. simpl in A. left.
  destruct rd; inv A; simpl in RD. 
  apply step_lred. auto. apply step_expr_not_stuck; congruence. auto. 
  apply step_rred. auto. apply step_expr_not_stuck; congruence. auto.
  destruct RD; subst m'. apply Csem.step_call. auto.  apply step_expr_not_stuck; congruence. auto.
(* callstate *)
  destruct fd; myinv.
  (* internal *)
  destruct (do_alloc_variables empty_env m (fn_params f ++ fn_vars f)) as [e m1]_eqn.
  myinv. right; apply step_internal_function with m1. auto. 
  change e with (fst (e,m1)). change m1 with (snd (e,m1)) at 2. rewrite <- Heqp. 
  apply do_alloc_variables_sound. apply sem_bind_parameters_sound; auto.
  (* external *)
  destruct p as [[[w' tr] v] m']. myinv. right; constructor. 
  eapply do_ef_external_sound; eauto.
(* returnstate *)
  destruct k; myinv...
Qed.

Remark estep_not_val:
  forall f a k e m t S, estep ge (ExprState f a k e m) t S -> is_val a = None.
Proof.
  intros. 
  assert (forall b from to C, context from to C -> (C = fun x => x) \/ is_val (C b) = None).
    induction 1; simpl; auto. 
  inv H. 
  destruct (H0 a0 _ _ _ H10). subst. inv H8; auto. auto.
  destruct (H0 a0 _ _ _ H10). subst. inv H8; auto. auto.
  destruct (H0 a0 _ _ _ H10). subst. inv H8; auto. auto.
Qed.

Lemma do_step_complete:
  forall w S t S' w', possible_trace w t w' -> Csem.step ge S t S' -> In (t, S') (do_step w S).
Proof with (unfold ret; auto with coqlib).
  intros until w'; intro PT; intros. 
  destruct H. 
  (* Expression step *)
  inversion H; subst; exploit estep_not_val; eauto; intro NOTVAL.
(* lred *)
  unfold do_step; rewrite NOTVAL.
  destruct (step_expr e RV (C a) m) as [ll|]_eqn.
  change (E0, ExprState f (C a') k e m') with (expr_final_state f k e (C, Lred a' m')).
  apply in_map.
  generalize (step_expr_context e _ _ _ H2 a m). unfold reducts_incl.
  rewrite Heqr. destruct (step_expr e LV a m) as [ll'|]_eqn; try tauto.
  intro. replace C with (fun x => C x). apply H3. 
  rewrite (lred_topred _ _ _ _ _ H0) in Heqr0. inv Heqr0. auto with coqlib.
  apply extensionality; auto.
  exploit not_stuck_step_expr; eauto.
(* rred *)
  unfold do_step; rewrite NOTVAL.
  destruct (step_expr e RV (C a) m) as [ll|]_eqn.
  change (E0, ExprState f (C a') k e m') with (expr_final_state f k e (C, Rred a' m')).
  apply in_map.
  generalize (step_expr_context e _ _ _ H2 a m). unfold reducts_incl.
  rewrite Heqr. destruct (step_expr e RV a m) as [ll'|]_eqn; try tauto.
  intro. replace C with (fun x => C x). apply H3. 
  rewrite (rred_topred _ _ _ _ _ H0) in Heqr0. inv Heqr0. auto with coqlib.
  apply extensionality; auto.
  exploit not_stuck_step_expr; eauto.
(* callred *)
  unfold do_step; rewrite NOTVAL.
  destruct (step_expr e RV (C a) m) as [ll|]_eqn.
  change (E0, Callstate fd vargs (Kcall f e C ty k) m) with (expr_final_state f k e (C, Callred fd vargs ty m)).
  apply in_map.
  generalize (step_expr_context e _ _ _ H2 a m). unfold reducts_incl.
  rewrite Heqr. destruct (step_expr e RV a m) as [ll'|]_eqn; try tauto.
  intro. replace C with (fun x => C x). apply H3. 
  rewrite (callred_topred _ _ _ _ _ _ H0) in Heqr0. inv Heqr0. auto with coqlib.
  apply extensionality; auto.
  exploit not_stuck_step_expr; eauto.

  (* Statement step *)
  inv H; simpl...
  rewrite H0...
  rewrite H0...
  rewrite H0...
  destruct H0; subst s0...
  destruct H0; subst s0...
  rewrite H0...
  rewrite H0...
  rewrite pred_dec_false...
  rewrite pred_dec_true...
  rewrite H0...
  rewrite H0...
  destruct H0; subst x...
  rewrite H0...
  rewrite H0; rewrite H1...
  rewrite pred_dec_true; auto. rewrite H2. red in H0. destruct k; try contradiction...
  destruct H0; subst x...
  rewrite H0...

  (* Call step *)
  rewrite pred_dec_true; auto. rewrite (do_alloc_variables_complete _ _ _ _ _ H1).
  rewrite (sem_bind_parameters_complete _ _ _ _ _ H2)...
  exploit do_ef_external_complete; eauto. intro EQ; rewrite EQ. auto with coqlib.
Qed.

End EXEC.

Local Open Scope option_monad_scope.

Definition do_initial_state (p: program): option (genv * state) :=
  let ge := Genv.globalenv p in
  do m0 <- Genv.init_mem p;
  do b <- Genv.find_symbol ge p.(prog_main);
  do f <- Genv.find_funct_ptr ge b;
  check (type_eq (type_of_fundef f) (Tfunction Tnil (Tint I32 Signed)));
  Some (ge, Callstate f nil Kstop m0).

Definition at_final_state (S: state): option int :=
  match S with
  | Returnstate (Vint r) Kstop m => Some r
  | _ => None
  end.

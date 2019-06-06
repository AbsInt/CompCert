(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Maps Errors.
Require Import AST Integers Floats Values Memory Globalenvs Events Smallstep.
Require Import Cminor.
Require Import Unityping.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(** * Type inference algorithm *)

Definition type_constant (c: constant) : typ :=
  match c with
  | Ointconst _ => Tint
  | Ofloatconst _ => Tfloat
  | Osingleconst _ => Tsingle
  | Olongconst _ => Tlong
  | Oaddrsymbol _ _ => Tptr
  | Oaddrstack _ => Tptr
  end.

Definition type_unop (op: unary_operation) : typ * typ :=
  match op with
  | Ocast8unsigned | Ocast8signed | Ocast16unsigned | Ocast16signed
  | Onegint | Onotint => (Tint, Tint)
  | Onegf | Oabsf => (Tfloat, Tfloat)
  | Onegfs | Oabsfs => (Tsingle, Tsingle)
  | Osingleoffloat => (Tfloat, Tsingle)
  | Ofloatofsingle => (Tsingle, Tfloat)
  | Ointoffloat | Ointuoffloat => (Tfloat, Tint)
  | Ofloatofint | Ofloatofintu => (Tint, Tfloat)
  | Ointofsingle | Ointuofsingle => (Tsingle, Tint)
  | Osingleofint | Osingleofintu => (Tint, Tsingle)
  | Onegl | Onotl => (Tlong, Tlong)
  | Ointoflong => (Tlong, Tint)
  | Olongofint | Olongofintu => (Tint, Tlong)
  | Olongoffloat | Olonguoffloat => (Tfloat, Tlong)
  | Ofloatoflong | Ofloatoflongu => (Tlong, Tfloat)
  | Olongofsingle | Olonguofsingle => (Tsingle, Tlong)
  | Osingleoflong | Osingleoflongu => (Tlong, Tsingle)
  end.

Definition type_binop (op: binary_operation) : typ * typ * typ :=
  match op with
  | Oadd  | Osub  | Omul  | Odiv  | Odivu  | Omod  | Omodu
  | Oand  | Oor   | Oxor  | Oshl  | Oshr   | Oshru => (Tint, Tint, Tint)
  | Oaddf | Osubf | Omulf | Odivf  => (Tfloat, Tfloat, Tfloat)
  | Oaddfs| Osubfs| Omulfs| Odivfs => (Tsingle, Tsingle, Tsingle)
  | Oaddl | Osubl | Omull | Odivl | Odivlu | Omodl | Omodlu
  | Oandl | Oorl  | Oxorl => (Tlong, Tlong, Tlong)
  | Oshll | Oshrl | Oshrlu => (Tlong, Tint, Tlong)
  | Ocmp _ | Ocmpu _ => (Tint, Tint, Tint)
  | Ocmpf _ => (Tfloat, Tfloat, Tint)
  | Ocmpfs _ => (Tsingle, Tsingle, Tint)
  | Ocmpl _ | Ocmplu _ => (Tlong, Tlong, Tint)
  end.

Module RTLtypes <: TYPE_ALGEBRA.

Definition t := typ.
Definition eq := typ_eq.
Definition default := Tint.

End RTLtypes.

Module S := UniSolver(RTLtypes).

Definition expect (e: S.typenv) (t1 t2: typ) : res S.typenv :=
  if typ_eq t1 t2 then OK e else Error (msg "type mismatch").

Fixpoint type_expr (e: S.typenv) (a: expr) (t: typ) : res S.typenv :=
  match a with
  | Evar id => S.set e id t
  | Econst c => expect e (type_constant c) t
  | Eunop op a1 =>
      let '(targ1, tres) := type_unop op in
      do e1 <- type_expr e a1 targ1;
      expect e1 tres t
  | Ebinop op a1 a2 =>
      let '(targ1, targ2, tres) := type_binop op in
      do e1 <- type_expr e a1 targ1;
      do e2 <- type_expr e1 a2 targ2;
      expect e2 tres t
  | Eload chunk a1 =>
      do e1 <- type_expr e a1 Tptr;
      expect e1 (type_of_chunk chunk) t
  end.

Fixpoint type_exprlist (e: S.typenv) (al: list expr) (tl: list typ) : res S.typenv :=
  match al, tl with
  | nil, nil => OK e
  | a :: al, t :: tl => do e1 <- type_expr e a t; type_exprlist e1 al tl
  | _, _ => Error (msg "arity mismatch")
  end.

Definition type_assign (e: S.typenv) (id: ident) (a: expr) : res S.typenv :=
  match a with
  | Evar id' =>
      do (changed, e1) <- S.move e id id'; OK e1
  | Econst c =>
      S.set e id (type_constant c)
  | Eunop op a1 =>
      let '(targ1, tres) := type_unop op in
      do e1 <- type_expr e a1 targ1;
      S.set e1 id tres
  | Ebinop op a1 a2 =>
      let '(targ1, targ2, tres) := type_binop op in
      do e1 <- type_expr e a1 targ1;
      do e2 <- type_expr e1 a2 targ2;
      S.set e2 id tres
  | Eload chunk a1 =>
      do e1 <- type_expr e a1 Tptr;
      S.set e1 id (type_of_chunk chunk)
  end.

Definition opt_set (e: S.typenv) (optid: option ident) (ty: typ) : res S.typenv :=
  match optid with
  | None => OK e
  | Some id => S.set e id ty
  end.

Fixpoint type_stmt (tret: option typ) (e: S.typenv) (s: stmt) : res S.typenv :=
  match s with
  | Sskip => OK e
  | Sassign id a => type_assign e id a
  | Sstore chunk a1 a2 =>
      do e1 <- type_expr e a1 Tptr; type_expr e1 a2 (type_of_chunk chunk)
  | Scall optid sg fn args =>
      do e1 <- type_expr e fn Tptr;
      do e2 <- type_exprlist e1 args sg.(sig_args);
      opt_set e2 optid (proj_sig_res sg)
  | Stailcall sg fn args =>
      assertion (opt_typ_eq sg.(sig_res) tret);
      do e1 <- type_expr e fn Tptr;
      type_exprlist e1 args sg.(sig_args)
  | Sbuiltin optid ef args =>
      let sg := ef_sig ef in
      do e1 <- type_exprlist e args sg.(sig_args);
      opt_set e1 optid (proj_sig_res sg)
  | Sseq s1 s2 =>
      do e1 <- type_stmt tret e s1; type_stmt tret e1 s2
  | Sifthenelse a s1 s2 =>
      do e1 <- type_expr e a Tint;
      do e2 <- type_stmt tret e1 s1;
      type_stmt tret e2 s2
  | Sloop s1 =>
      type_stmt tret e s1
  | Sblock s1 =>
      type_stmt tret e s1
  | Sexit n =>
      OK e
  | Sswitch sz a tbl dfl =>
      type_expr e a (if sz then Tlong else Tint)
  | Sreturn opta =>
      match opta, tret with
      | None, _ => OK e
      | Some a, Some t => type_expr e a t
      | _, _ => Error (msg "inconsistent return")
      end
  | Slabel lbl s1 =>
      type_stmt tret e s1
  | Sgoto lbl =>
      OK e
  end.

Definition typenv := ident -> typ.

Definition type_function (f: function) : res typenv :=
  do e1 <- S.set_list S.initial f.(fn_params) f.(fn_sig).(sig_args);
  do e2 <- type_stmt f.(fn_sig).(sig_res) e1 f.(fn_body);
  S.solve e2.

(** * Relational specification of the type system *)

Section SPEC.

Variable env: ident -> typ.
Variable tret: option typ.

Inductive wt_expr: expr -> typ -> Prop :=
  | wt_Evar: forall id,
      wt_expr (Evar id) (env id)
  | wt_Econst: forall c,
      wt_expr (Econst c) (type_constant c)
  | wt_Eunop: forall op a1 targ1 tres,
      type_unop op = (targ1, tres) ->
      wt_expr a1 targ1 ->
      wt_expr (Eunop op a1) tres
  | wt_Ebinop: forall op a1 a2 targ1 targ2 tres,
      type_binop op = (targ1, targ2, tres) ->
      wt_expr a1 targ1 -> wt_expr a2 targ2 ->
      wt_expr (Ebinop op a1 a2) tres
  | wt_Eload: forall chunk a1,
      wt_expr a1 Tptr ->
      wt_expr (Eload chunk a1) (type_of_chunk chunk).

Definition wt_opt_assign (optid: option ident) (optty: option typ) : Prop :=
  match optid with
  | Some id => match optty with Some ty => ty | None => Tint end = env id
  | _ => True
  end.

Inductive wt_stmt: stmt -> Prop :=
  | wt_Sskip:
      wt_stmt Sskip
  | wt_Sassign: forall id a,
      wt_expr a (env id) ->
      wt_stmt (Sassign id a)
  | wt_Sstore: forall chunk a1 a2,
      wt_expr a1 Tptr -> wt_expr a2 (type_of_chunk chunk) ->
      wt_stmt (Sstore chunk a1 a2)
  | wt_Scall: forall optid sg a1 al,
      wt_expr a1 Tptr -> list_forall2 wt_expr al sg.(sig_args) ->
      wt_opt_assign optid sg.(sig_res) ->
      wt_stmt (Scall optid sg a1 al)
  | wt_Stailcall: forall sg a1 al,
      wt_expr a1 Tptr -> list_forall2 wt_expr al sg.(sig_args) ->
      sg.(sig_res) = tret ->
      wt_stmt (Stailcall sg a1 al)
  | wt_Sbuiltin: forall optid ef al,
      list_forall2 wt_expr al (ef_sig ef).(sig_args) ->
      wt_opt_assign optid (ef_sig ef).(sig_res) ->
      wt_stmt (Sbuiltin optid ef al)
  | wt_Sseq: forall s1 s2,
      wt_stmt s1 -> wt_stmt s2 ->
      wt_stmt (Sseq s1 s2)
  | wt_Sifthenelse: forall a s1 s2,
      wt_expr a Tint -> wt_stmt s1 -> wt_stmt s2 ->
      wt_stmt (Sifthenelse a s1 s2)
  | wt_Sloop: forall s1,
      wt_stmt s1 ->
      wt_stmt (Sloop s1)
  | wt_Sblock: forall s1,
      wt_stmt s1 ->
      wt_stmt (Sblock s1)
  | wt_Sexit: forall n,
      wt_stmt (Sexit n)
  | wt_Sswitch: forall (sz: bool) a tbl dfl,
      wt_expr a (if sz then Tlong else Tint) ->
      wt_stmt (Sswitch sz a tbl dfl)
  | wt_Sreturn_none:
      wt_stmt (Sreturn None)
  | wt_Sreturn_some: forall a t,
      tret = Some t -> wt_expr a t ->
      wt_stmt (Sreturn (Some a))
  | wt_Slabel: forall lbl s1,
      wt_stmt s1 ->
      wt_stmt (Slabel lbl s1)
  | wt_Sgoto: forall lbl,
      wt_stmt (Sgoto lbl).

End SPEC.

Inductive wt_function (env: typenv) (f: function) : Prop :=
  wt_function_intro:
    type_function f = OK env ->     (**r to ensure uniqueness of [env] *)
    List.map env f.(fn_params) = f.(fn_sig).(sig_args) ->
    wt_stmt env f.(fn_sig).(sig_res) f.(fn_body) ->
    wt_function env f.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_internal: forall env f,
      wt_function env f ->
      wt_fundef (Internal f)
  | wt_fundef_external: forall ef,
      wt_fundef (External ef).

Definition wt_program (p: program): Prop :=
  forall i f, In (i, Gfun f) (prog_defs p) -> wt_fundef f.

(** * Soundness of type inference *)

Lemma expect_incr: forall te e t1 t2 e',
  expect e t1 t2 = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  unfold expect; intros. destruct (typ_eq t1 t2); inv H; auto.
Qed.
Hint Resolve expect_incr: ty.

Lemma expect_sound: forall e t1 t2 e',
  expect e t1 t2 = OK e' -> t1 = t2.
Proof.
  unfold expect; intros. destruct (typ_eq t1 t2); inv H; auto.
Qed.

Lemma type_expr_incr: forall te a t e e',
  type_expr e a t = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  induction a; simpl; intros until e'; intros T SAT; try (monadInv T); eauto with ty.
- destruct (type_unop u) as [targ1 tres]; monadInv T; eauto with ty.
- destruct (type_binop b) as [[targ1 targ2] tres]; monadInv T; eauto with ty.
Qed.
Hint Resolve type_expr_incr: ty.

Lemma type_expr_sound: forall te a t e e',
    type_expr e a t = OK e' -> S.satisf te e' -> wt_expr te a t.
Proof.
  induction a; simpl; intros until e'; intros T SAT; try (monadInv T).
- erewrite <- S.set_sound by eauto. constructor.
- erewrite <- expect_sound by eauto. constructor.
- destruct (type_unop u) as [targ1 tres] eqn:TU; monadInv T.
  erewrite <- expect_sound by eauto. econstructor; eauto with ty.
- destruct (type_binop b) as [[targ1 targ2] tres] eqn:TB; monadInv T.
  erewrite <- expect_sound by eauto. econstructor; eauto with ty.
- erewrite <- expect_sound by eauto. econstructor; eauto with ty.
Qed.

Lemma type_exprlist_incr: forall te al tl e e',
  type_exprlist e al tl = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  induction al; destruct tl; simpl; intros until e'; intros T SAT; monadInv T; eauto with ty.
Qed.
Hint Resolve type_exprlist_incr: ty.

Lemma type_exprlist_sound: forall te al tl e e',
    type_exprlist e al tl = OK e' -> S.satisf te e' -> list_forall2 (wt_expr te) al tl.
Proof.
  induction al; destruct tl; simpl; intros until e'; intros T SAT; monadInv T.
- constructor.
- constructor; eauto using type_expr_sound with ty.
Qed.

Lemma type_assign_incr: forall te id a e e',
    type_assign e id a = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  induction a; simpl; intros until e'; intros T SAT; try (monadInv T); eauto with ty.
- destruct (type_unop u) as [targ1 tres]; monadInv T; eauto with ty.
- destruct (type_binop b) as [[targ1 targ2] tres]; monadInv T; eauto with ty.
Qed.
Hint Resolve type_assign_incr: ty.

Lemma type_assign_sound: forall te id a e e',
    type_assign e id a = OK e' -> S.satisf te e' -> wt_expr te a (te id).
Proof.
  induction a; simpl; intros until e'; intros T SAT; try (monadInv T).
- erewrite S.move_sound by eauto. constructor.
- erewrite S.set_sound by eauto. constructor.
- destruct (type_unop u) as [targ1 tres] eqn:TU; monadInv T.
  erewrite S.set_sound by eauto. econstructor; eauto using type_expr_sound with ty.
- destruct (type_binop b) as [[targ1 targ2] tres] eqn:TB; monadInv T.
  erewrite S.set_sound by eauto. econstructor; eauto using type_expr_sound with ty.
- erewrite S.set_sound by eauto. econstructor; eauto using type_expr_sound with ty.
Qed.

Lemma opt_set_incr: forall te optid optty e e',
    opt_set e optid optty = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  unfold opt_set; intros. destruct optid, optty; try (monadInv H); eauto with ty.
Qed.
Hint Resolve opt_set_incr: ty.

Lemma opt_set_sound: forall te optid sg e e',
    opt_set e optid (proj_sig_res sg) = OK e' -> S.satisf te e' ->
    wt_opt_assign te optid sg.(sig_res).
Proof.
  unfold opt_set; intros; red. destruct optid.
- erewrite S.set_sound by eauto. auto.
- inv H. auto.
Qed.

Lemma type_stmt_incr: forall te tret s e e',
    type_stmt tret e s = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  induction s; simpl; intros e1 e2 T SAT; try (monadInv T); eauto with ty.
- destruct tret, o; try (monadInv T); eauto with ty.
Qed.
Hint Resolve type_stmt_incr: ty.

Lemma type_stmt_sound: forall te tret s e e',
    type_stmt tret e s = OK e' -> S.satisf te e' -> wt_stmt te tret s.
Proof.
  induction s; simpl; intros e1 e2 T SAT; try (monadInv T).
- constructor.
- constructor; eauto using type_assign_sound.
- constructor; eauto using type_expr_sound with ty.
- constructor; eauto using type_expr_sound, type_exprlist_sound, opt_set_sound with ty.
- constructor; eauto using type_expr_sound, type_exprlist_sound with ty.
- constructor; eauto using type_exprlist_sound, opt_set_sound with ty.
- constructor; eauto with ty.
- constructor; eauto using type_expr_sound with ty.
- constructor; eauto.
- constructor; eauto.
- constructor.
- constructor; eauto using type_expr_sound with ty.
- destruct tret, o; try (monadInv T); econstructor; eauto using type_expr_sound with ty.
- constructor; eauto.
- constructor.
Qed.

Theorem type_function_sound: forall f env,
  type_function f = OK env -> wt_function env f.
Proof.
  intros. generalize H; unfold type_function; intros T; monadInv T.
  assert (S.satisf env x0) by (apply S.solve_sound; auto).
  constructor; eauto using S.set_list_sound, type_stmt_sound with ty.
Qed.

(** * Semantic soundness of the type system *)

Definition wt_env (env: typenv) (e: Cminor.env) : Prop :=
  forall id v, e!id = Some v -> Val.has_type v (env id).

Definition def_env (f: function) (e: Cminor.env) : Prop :=
  forall id, In id f.(fn_params) \/ In id f.(fn_vars) -> exists v, e!id = Some v.

Inductive wt_cont_call: cont -> option typ -> Prop :=
  | wt_cont_Kstop:
      wt_cont_call Kstop (Some Tint)
  | wt_cont_Kcall: forall optid f sp e k tret env
        (WT_FN: wt_function env f)
        (WT_CONT: wt_cont env f.(fn_sig).(sig_res) k)
        (WT_ENV: wt_env env e)
        (DEF_ENV: def_env f e)
        (WT_DEST: wt_opt_assign env optid tret),
      wt_cont_call (Kcall optid f sp e k) tret

with wt_cont: typenv -> option typ -> cont -> Prop :=
  | wt_cont_Kseq: forall env tret s k,
      wt_stmt env tret s ->
      wt_cont env tret k ->
      wt_cont env tret (Kseq s k)
  | wt_cont_Kblock: forall env tret k,
      wt_cont env tret k ->
      wt_cont env tret (Kblock k)
  | wt_cont_other: forall env tret k,
      wt_cont_call k tret ->
      wt_cont env tret k.

Inductive wt_state: state -> Prop :=
  | wt_normal_state: forall f s k sp e m env
        (WT_FN: wt_function env f)
        (WT_STMT: wt_stmt env f.(fn_sig).(sig_res) s)
        (WT_CONT: wt_cont env f.(fn_sig).(sig_res) k)
        (WT_ENV: wt_env env e)
        (DEF_ENV: def_env f e),
      wt_state (State f s k sp e m)
  | wt_call_state: forall f args k m
        (WT_FD: wt_fundef f)
        (WT_ARGS: Val.has_type_list args (funsig f).(sig_args))
        (WT_CONT: wt_cont_call k (funsig f).(sig_res)),
      wt_state (Callstate f args k m)
  | wt_return_state: forall v k m tret
        (WT_RES: Val.has_type v (match tret with None => Tint | Some t => t end))
        (WT_CONT: wt_cont_call k tret),
      wt_state (Returnstate v k m).

Lemma wt_is_call_cont:
  forall env tret k, wt_cont env tret k -> is_call_cont k -> wt_cont_call k tret.
Proof.
  destruct 1; intros ICC; contradiction || auto.
Qed.

Lemma call_cont_wt:
  forall env tret k, wt_cont env tret k -> wt_cont_call (call_cont k) tret.
Proof.
  induction 1; simpl; auto. inversion H; subst; auto.
Qed.

Lemma wt_env_assign: forall env id e v,
  wt_env env e -> Val.has_type v (env id) -> wt_env env (PTree.set id v e).
Proof.
  intros; red; intros. rewrite PTree.gsspec in H1; destruct (peq id0 id).
- congruence.
- auto.
Qed.

Lemma def_env_assign: forall f e id v,
  def_env f e -> def_env f (PTree.set id v e).
Proof.
  intros; red; intros i IN. rewrite PTree.gsspec. destruct (peq i id).
  exists v; auto.
  auto.
Qed.

Lemma wt_env_set_params: forall env il vl,
  Val.has_type_list vl (map env il) -> wt_env env (set_params vl il).
Proof.
  induction il as [ | i il]; destruct vl as [ | vl]; simpl; intros; try contradiction.
- red; intros. rewrite PTree.gempty in H0; discriminate.
- destruct H. apply wt_env_assign; auto.
Qed.

Lemma def_set_params: forall id il vl,
  In id il -> exists v, PTree.get id (set_params vl il) = Some v.
Proof.
  induction il as [ | i il]; simpl; intros.
- contradiction.
- destruct vl as [ | v vl]; rewrite PTree.gsspec; destruct (peq id i).
  econstructor; eauto.
  apply IHil; intuition congruence.
  econstructor; eauto.
  apply IHil; intuition congruence.
Qed.

Lemma wt_env_set_locals: forall env il e,
  wt_env env e -> wt_env env (set_locals il e).
Proof.
  induction il as [ | i il]; simpl; intros.
- auto.
- apply wt_env_assign; auto. exact I.
Qed.

Lemma def_set_locals: forall id il e,
  (exists v, PTree.get id e = Some v) \/ In id il ->
  exists v, PTree.get id (set_locals il e) = Some v.
Proof.
  induction il as [ | i il]; simpl; intros.
- tauto.
- rewrite PTree.gsspec; destruct (peq id i).
  econstructor; eauto.
  apply IHil; intuition congruence.
Qed.

Lemma wt_find_label: forall env tret lbl s k,
  wt_stmt env tret s -> wt_cont env tret k ->
  match find_label lbl s k with
  | Some (s', k') => wt_stmt env tret s' /\ wt_cont env tret k'
  | None => True
  end.
Proof.
  induction s; intros k WS WK; simpl; auto.
- inv WS. assert (wt_cont env tret (Kseq s2 k)) by (constructor; auto).
  specialize (IHs1 _ H1 H). destruct (find_label lbl s1 (Kseq s2 k)).
  auto. apply IHs2; auto.
- inv WS. specialize (IHs1 _ H3 WK). destruct (find_label lbl s1 k).
  auto. apply IHs2; auto.
- inversion WS; subst. apply IHs; auto. constructor; auto.
- inv WS. apply IHs; auto. constructor; auto.
- inv WS. destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.

Section SUBJECT_REDUCTION.

Variable p: program.

Hypothesis wt_p: wt_program p.

Let ge := Genv.globalenv p.

Ltac VHT :=
  match goal with
  | [ |- Val.has_type (if Archi.ptr64 then _ else _) _] => unfold Val.has_type; destruct Archi.ptr64 eqn:?; VHT
  | [ |- Val.has_type (match ?v with _ => _ end) _] => destruct v; VHT
  | [ |- Val.has_type (Vptr _ _) Tptr ] => apply Val.Vptr_has_type
  | [ |- Val.has_type _ _ ] => exact I
  | [ |- Val.has_type (?f _ _ _ _ _) _ ] => unfold f; VHT
  | [ |- Val.has_type (?f _ _ _ _) _ ] => unfold f; VHT
  | [ |- Val.has_type (?f _ _) _ ] => unfold f; VHT
  | [ |- Val.has_type (?f _ _ _) _ ] => unfold f; VHT
  | [ |- Val.has_type (?f _) _ ] => unfold f; VHT
  | [ |- True ] => exact I
  | [ |- ?x = ?x ] => reflexivity
  | _ => idtac
  end.

Ltac VHT' :=
  match goal with
  | [ H: None = Some _ |- _ ] => discriminate
  | [ H: Some _ = Some _ |- _ ] => inv H; VHT
  | [ H: match ?x with _ => _ end = Some _ |- _ ] => destruct x; VHT'
  | [ H: ?f _ _ _ _ = Some _ |- _ ] => unfold f in H; VHT'
  | [ H: ?f _ _ _ = Some _ |- _ ] => unfold f in H; VHT'
  | [ H: ?f _ _ = Some _ |- _ ] => unfold f in H; VHT'
  | [ H: ?f _ = Some _ |- _ ] => unfold f in H; VHT'
  | _ => idtac
  end.

Lemma type_constant_sound: forall sp cst v,
  eval_constant ge sp cst = Some v ->
  Val.has_type v (type_constant cst).
Proof.
  intros until v; intros EV. destruct cst; simpl in *; inv EV; VHT.
Qed.

Lemma type_unop_sound: forall op v1 v,
  eval_unop op v1 = Some v -> Val.has_type v (snd (type_unop op)).
Proof.
  unfold eval_unop; intros op v1 v EV; destruct op; simpl; VHT'.
Qed.

Lemma type_binop_sound: forall op v1 v2 m v,
  eval_binop op v1 v2 m = Some v -> Val.has_type v (snd (type_binop op)).
Proof.
  unfold eval_binop; intros op v1 v2 m v EV; destruct op; simpl; VHT';
  destruct (eq_block b b0); VHT.
Qed.

Lemma wt_eval_expr: forall env sp e m a v,
  eval_expr ge sp e m a v ->
  forall t,
  wt_expr env a t ->
  wt_env env e ->
  Val.has_type v t.
Proof.
  induction 1; intros t WT ENV.
- inv WT. apply ENV; auto.
- inv WT. eapply type_constant_sound; eauto.
- inv WT. replace t with (snd (type_unop op)) by (rewrite H3; auto). eapply type_unop_sound; eauto.
- inv WT. replace t with (snd (type_binop op)) by (rewrite H5; auto). eapply type_binop_sound; eauto.
- inv WT. destruct vaddr; try discriminate. eapply Mem.load_type; eauto.
Qed.

Lemma wt_eval_exprlist: forall env sp e m al vl,
  eval_exprlist ge sp e m al vl ->
  forall tl,
  list_forall2 (wt_expr env) al tl ->
  wt_env env e ->
  Val.has_type_list vl tl.
Proof.
  induction 1; intros tl WT ENV; inv WT; simpl.
- auto.
- split. eapply wt_eval_expr; eauto. eauto.
Qed.

Lemma wt_find_funct: forall v fd,
  Genv.find_funct ge v = Some fd -> wt_fundef fd.
Proof.
  intros. eapply Genv.find_funct_prop; eauto.
Qed.

Lemma subject_reduction:
  forall st1 t st2, step ge st1 t st2 ->
  forall (WT: wt_state st1), wt_state st2.
Proof.
  destruct 1; intros; inv WT.
- inv WT_CONT. econstructor; eauto. inv H.
- inv WT_CONT. econstructor; eauto. inv H.
- econstructor; eauto using wt_is_call_cont. exact I.
- inv WT_STMT. econstructor; eauto using wt_Sskip.
  apply wt_env_assign; auto. eapply wt_eval_expr; eauto.
  apply def_env_assign; auto.
- econstructor; eauto using wt_Sskip.
- inv WT_STMT. econstructor; eauto.
  eapply wt_find_funct; eauto.
  eapply wt_eval_exprlist; eauto.
  econstructor; eauto.
- inv WT_STMT. econstructor; eauto.
  eapply wt_find_funct; eauto.
  eapply wt_eval_exprlist; eauto.
  rewrite H8; eapply call_cont_wt; eauto.
- inv WT_STMT. exploit external_call_well_typed; eauto. intros TRES.
  econstructor; eauto using wt_Sskip.
  unfold proj_sig_res in TRES; red in H5.
  destruct optid. rewrite H5 in TRES. apply wt_env_assign; auto. assumption.
  destruct optid. apply def_env_assign; auto. assumption.
- inv WT_STMT. econstructor; eauto. econstructor; eauto.
- inv WT_STMT. destruct b; econstructor; eauto.
- inv WT_STMT. econstructor; eauto. econstructor; eauto. constructor; auto.
- inv WT_STMT. econstructor; eauto. econstructor; eauto.
- inv WT_CONT. econstructor; eauto. inv H.
- inv WT_CONT. econstructor; eauto using wt_Sskip. inv H.
- inv WT_CONT. econstructor; eauto using wt_Sexit. inv H.
- econstructor; eauto using wt_Sexit.
- inv WT_STMT. econstructor; eauto using call_cont_wt. exact I.
- inv WT_STMT. econstructor; eauto using call_cont_wt.
  rewrite H2. eapply wt_eval_expr; eauto.
- inv WT_STMT. econstructor; eauto.
- inversion WT_FN; subst.
  assert (WT_CK: wt_cont env (sig_res (fn_sig f)) (call_cont k)).
  { constructor. eapply call_cont_wt; eauto. }
  generalize (wt_find_label _ _ lbl _ _ H2 WT_CK).
  rewrite H. intros [WT_STMT' WT_CONT']. econstructor; eauto.
- inv WT_FD. inversion H1; subst. econstructor; eauto.
  constructor; auto.
  apply wt_env_set_locals. apply wt_env_set_params. rewrite H2; auto.
  red; intros. apply def_set_locals. destruct H4; auto. left; apply def_set_params; auto.
- exploit external_call_well_typed; eauto. unfold proj_sig_res. simpl in *. intros.
  econstructor; eauto.
- inv WT_CONT. econstructor; eauto using wt_Sskip.
  red in WT_DEST.
  destruct optid. rewrite WT_DEST in WT_RES. apply wt_env_assign; auto. assumption.
  destruct optid. apply def_env_assign; auto. assumption.
Qed.

Lemma subject_reduction_star:
  forall st1 t st2, star step ge st1 t st2 ->
  forall (WT: wt_state st1), wt_state st2.
Proof.
  induction 1; eauto using subject_reduction.
Qed.

Lemma wt_initial_state:
  forall S, initial_state p S -> wt_state S.
Proof.
  intros. inv H. constructor. eapply Genv.find_funct_ptr_prop; eauto.
  rewrite H3; constructor.
  rewrite H3; constructor.
Qed.

End SUBJECT_REDUCTION.

(** * Safe expressions *)

(** Function parameters and declared local variables are always defined
  throughout the execution of a function.  The following [known_idents]
  data structure represents the set of those variables, with efficient membership. *)

Definition known_idents := PTree.t unit.

Definition is_known (ki: known_idents) (id: ident) :=
  match ki!id with Some _ => true | None => false end.

Definition known_id (f: function) : known_idents :=
  let add (ki: known_idents) (id: ident) := PTree.set id tt ki in
  List.fold_left add f.(fn_vars)
      (List.fold_left add f.(fn_params) (PTree.empty unit)).

(** A Cminor expression is safe if it always evaluates to a value,
    never causing a run-time error. *)

Definition safe_unop (op: unary_operation) : bool :=
  match op with
  | Ointoffloat | Ointuoffloat | Ofloatofint | Ofloatofintu => false
  | Ointofsingle | Ointuofsingle | Osingleofint | Osingleofintu => false
  | Olongoffloat | Olonguoffloat | Ofloatoflong | Ofloatoflongu => false
  | Olongofsingle | Olonguofsingle | Osingleoflong | Osingleoflongu => false
  | _ => true
  end.

Definition safe_binop (op: binary_operation) : bool :=
  match op with
  | Odiv | Odivu | Omod | Omodu => false
  | Odivl | Odivlu | Omodl | Omodlu => false
  | Ocmpl _ | Ocmplu _ => false
  | _ => true
  end.

Fixpoint safe_expr (ki: known_idents) (a: expr) : bool :=
  match a with
  | Evar v => is_known ki v
  | Econst c => true
  | Eunop op e1 => safe_unop op && safe_expr ki e1
  | Ebinop op e1 e2 => safe_binop op && safe_expr ki e1 && safe_expr ki e2
  | Eload chunk e => false
  end.

(** Soundness of [known_id]. *)

Lemma known_id_sound_1:
  forall f id x, (known_id f)!id = Some x -> In id f.(fn_params) \/ In id f.(fn_vars).
Proof.
  unfold known_id.
  set (add := fun (ki: known_idents) (id: ident) => PTree.set id tt ki).
  intros.
  assert (REC: forall l ki, (fold_left add l ki)!id = Some x -> In id l \/ ki!id = Some x).
  { induction l as [ | i l ]; simpl; intros.
    - auto.
    - apply IHl in H0. destruct H0; auto. unfold add in H0; rewrite PTree.gsspec in H0.
      destruct (peq id i); auto. }
  apply REC in H. destruct H; auto. apply REC in H. destruct H; auto.
  rewrite PTree.gempty in H; discriminate.
Qed.

Lemma known_id_sound_2:
  forall f id, is_known (known_id f) id = true -> In id f.(fn_params) \/ In id f.(fn_vars).
Proof.
  unfold is_known; intros. destruct (known_id f)!id eqn:E; try discriminate.
  eapply known_id_sound_1; eauto.
Qed.

(** Expressions that satisfy [safe_expr] always evaluate to a value. *)

Lemma eval_safe_expr:
  forall ge f sp e m a,
  def_env f e ->
  safe_expr (known_id f) a = true ->
  exists v, eval_expr ge sp e m a v.
Proof.
  induction a; simpl; intros.
  - apply known_id_sound_2 in H0.
    destruct (H i H0) as [v E].
    exists v; constructor; auto.
  - destruct (eval_constant ge sp c) as [v|] eqn:E.
    exists v; constructor; auto.
    destruct c; discriminate.
  - InvBooleans. destruct IHa as [v1 E1]; auto.
    destruct (eval_unop u v1) as [v|] eqn:E.
    exists v; econstructor; eauto.
    destruct u; discriminate.
  - InvBooleans.
    destruct IHa1 as [v1 E1]; auto.
    destruct IHa2 as [v2 E2]; auto.
    destruct (eval_binop b v1 v2 m) as [v|] eqn:E.
    exists v; econstructor; eauto.
    destruct b; discriminate.
  - discriminate.
Qed.



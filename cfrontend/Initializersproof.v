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

(** Compile-time evaluation of initializers for global C variables. *)

Require Import Coq.Program.Equality.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Csyntax.
Require Import Csem.
Require Import Initializers.

Open Scope error_monad_scope.

Section SOUNDNESS.

Variable ge: genv.

(** * Simple expressions and their big-step semantics *)

(** An expression is simple if it contains no assignments and no
  function calls. *)

Fixpoint simple (a: expr) : Prop :=
  match a with
  | Eloc _ _ _ => True
  | Evar _ _ => True
  | Ederef r _ => simple r
  | Efield l1 _ _ => simple l1
  | Eval _ _ => True
  | Evalof l _ => simple l
  | Eaddrof l _ => simple l
  | Eunop _ r1 _ => simple r1
  | Ebinop _ r1 r2 _ => simple r1 /\ simple r2
  | Ecast r1 _ => simple r1
  | Econdition r1 r2 r3 _ => simple r1 /\ simple r2 /\ simple r3
  | Esizeof _ _ => True
  | Eassign _ _ _ => False
  | Eassignop _ _ _ _ _ => False
  | Epostincr _ _ _ => False
  | Ecomma r1 r2 _ => simple r1 /\ simple r2
  | Ecall _ _ _ => False
  | Eparen r1 _ => simple r1
  end.

(** A big-step semantics for simple expressions.  Similar to the
  big-step semantics from [Cstrategy], with the addition of
  conditionals, comma and paren operators.  It is a pity we do not
  share definitions with [Cstrategy], but such sharing raises
  technical difficulties. *)

Section SIMPLE_EXPRS.

Variable e: env.
Variable m: mem.

Inductive eval_simple_lvalue: expr -> block -> int -> Prop :=
  | esl_loc: forall b ofs ty,
      eval_simple_lvalue (Eloc b ofs ty) b ofs
  | esl_var_local: forall x ty b,
      e!x = Some(b, ty) ->
      eval_simple_lvalue (Evar x ty) b Int.zero
  | esl_var_global: forall x ty b,
      e!x = None ->
      Genv.find_symbol ge x = Some b ->
      type_of_global ge b = Some ty ->
      eval_simple_lvalue (Evar x ty) b Int.zero
  | esl_deref: forall r ty b ofs,
      eval_simple_rvalue r (Vptr b ofs) ->
      eval_simple_lvalue (Ederef r ty) b ofs
  | esl_field_struct: forall l f ty b ofs id fList delta,
      eval_simple_lvalue l b ofs ->
      typeof l = Tstruct id fList -> field_offset f fList = OK delta ->
      eval_simple_lvalue (Efield l f ty) b (Int.add ofs (Int.repr delta))
  | esl_field_union: forall l f ty b ofs id fList,
      eval_simple_lvalue l b ofs ->
      typeof l = Tunion id fList ->
      eval_simple_lvalue (Efield l f ty) b ofs

with eval_simple_rvalue: expr -> val -> Prop :=
  | esr_val: forall v ty,
      eval_simple_rvalue (Eval v ty) v
  | esr_rvalof: forall b ofs l ty v,
      eval_simple_lvalue l b ofs ->
      ty = typeof l ->
      load_value_of_type ty m b ofs = Some v ->
      eval_simple_rvalue (Evalof l ty) v
  | esr_addrof: forall b ofs l ty,
      eval_simple_lvalue l b ofs ->
      eval_simple_rvalue (Eaddrof l ty) (Vptr b ofs)
  | esr_unop: forall op r1 ty v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_unary_operation op v1 (typeof r1) = Some v ->
      eval_simple_rvalue (Eunop op r1 ty) v
  | esr_binop: forall op r1 r2 ty v1 v2 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v2 ->
      sem_binary_operation op v1 (typeof r1) v2 (typeof r2) m = Some v ->
      eval_simple_rvalue (Ebinop op r1 r2 ty) v
  | esr_cast: forall ty r1 v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_cast v1 (typeof r1) ty = Some v ->
      eval_simple_rvalue (Ecast r1 ty) v
  | esr_sizeof: forall ty1 ty,
      eval_simple_rvalue (Esizeof ty1 ty) (Vint (Int.repr (sizeof ty1)))
  | esr_condition: forall r1 r2 r3 ty v v1 b v',
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) = Some b -> 
      eval_simple_rvalue (if b then r2 else r3) v' ->
      sem_cast v' (typeof (if b then r2 else r3)) ty = Some v ->
      eval_simple_rvalue (Econdition r1 r2 r3 ty) v
  | esr_comma: forall r1 r2 ty v1 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v ->
      eval_simple_rvalue (Ecomma r1 r2 ty) v
  | esr_paren: forall r ty v v',
      eval_simple_rvalue r v -> sem_cast v (typeof r) ty = Some v' ->
      eval_simple_rvalue (Eparen r ty) v'.

End SIMPLE_EXPRS.

(** * Correctness of the big-step semantics with respect to reduction sequences *)

(** In this section, we show that if a simple expression [a] reduces to
  some value (with the transition semantics from module [Csem]),
  then it evaluates to this value (with the big-step semantics above). *)

Definition compat_eval (k: kind) (e: env) (a a': expr) (m: mem) : Prop :=
  typeof a = typeof a' /\
  match k with
  | LV => forall b ofs, eval_simple_lvalue e m a' b ofs -> eval_simple_lvalue e m a b ofs
  | RV => forall v, eval_simple_rvalue e m a' v -> eval_simple_rvalue e m a v
  end.

Lemma lred_simple:
  forall e l m l' m', lred ge e l m l' m' -> simple l -> simple l'.
Proof.
  induction 1; simpl; tauto.
Qed.

Lemma lred_compat:
  forall e l m l' m', lred ge e l m l' m' ->
  m = m' /\ compat_eval LV e l l' m.
Proof.
  induction 1; simpl; split; auto; split; auto; intros bx ofsx EV; inv EV.
  apply esl_var_local; auto.
  apply esl_var_global; auto.
  constructor. constructor.
  eapply esl_field_struct; eauto. constructor. simpl; eauto.
  eapply esl_field_union; eauto. constructor. simpl; eauto.
Qed.

Lemma rred_simple:
  forall r m r' m', rred r m r' m' -> simple r -> simple r'.
Proof.
  induction 1; simpl; intuition. destruct b; auto. 
Qed.

Lemma rred_compat:
  forall e r m r' m', rred r m r' m' ->
  simple r ->
  m = m' /\ compat_eval RV e r r' m.
Proof.
  induction 1; simpl; intro SIMP; try contradiction; split; auto; split; auto; intros vx EV.
  inv EV. econstructor. constructor. auto. auto. 
  inv EV. econstructor. constructor.
  inv EV. econstructor; eauto. constructor. 
  inv EV. econstructor; eauto. constructor. constructor.
  inv EV. econstructor; eauto. constructor.
  inv EV. eapply esr_condition; eauto. constructor. 
  inv EV. constructor.
  econstructor; eauto. constructor.
  inv EV. econstructor. constructor. auto. 
Qed.

Lemma compat_eval_context:
  forall e a a' m from to C,
  context from to C ->
  compat_eval from e a a' m ->
  compat_eval to e (C a) (C a') m.
Proof.
  induction 1; intros CE; auto;
  try (generalize (IHcontext CE); intros [TY EV]; red; split; simpl; auto; intros).
  inv H0. constructor; auto.
  inv H0.
    eapply esl_field_struct; eauto. rewrite TY; eauto. 
    eapply esl_field_union; eauto. rewrite TY; eauto.
  inv H0. econstructor. eauto. auto. auto.
  inv H0. econstructor; eauto. 
  inv H0. econstructor; eauto. congruence.
  inv H0. econstructor; eauto. congruence.
  inv H0. econstructor; eauto. congruence.
  inv H0. econstructor; eauto. congruence.
  inv H0. eapply esr_condition; eauto. congruence.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  red; split; intros. auto. inv H0.
  inv H0. econstructor; eauto.
  inv H0. econstructor; eauto. congruence. 
Qed.

Lemma simple_context_1:
  forall a from to C, context from to C -> simple (C a) -> simple a.
Proof.
  induction 1; simpl; tauto. 
Qed.

Lemma simple_context_2:
  forall a a', simple a' -> forall from to C, context from to C -> simple (C a) -> simple (C a').
Proof.
  induction 2; simpl; tauto. 
Qed.

Lemma compat_eval_steps:
  forall f r e m w r' m',
  star step ge (ExprState f r Kstop e m) w (ExprState f r' Kstop e m') ->
  simple r -> 
  m' = m /\ compat_eval RV e r r' m.
Proof.
  intros. dependent induction H.
  (* base case *) 
  split. auto. red; auto.
  (* inductive case *)
  destruct H.
  (* expression step *)
  assert (X: exists r1, s2 = ExprState f r1 Kstop e m /\ compat_eval RV e r r1 m /\ simple r1).
    inv H.
    (* lred *)
    assert (S: simple a) by (eapply simple_context_1; eauto).
    exploit lred_compat; eauto. intros [A B]. subst m'0.
    econstructor; split. eauto. split.
    eapply compat_eval_context; eauto.
    eapply simple_context_2; eauto. eapply lred_simple; eauto.
    (* rred *)
    assert (S: simple a) by (eapply simple_context_1; eauto).
    exploit rred_compat; eauto. intros [A B]. subst m'0.
    econstructor; split. eauto. split.
    eapply compat_eval_context; eauto.
    eapply simple_context_2; eauto. eapply rred_simple; eauto.
    (* callred *)
    assert (S: simple a) by (eapply simple_context_1; eauto).
    inv H10; simpl in S; contradiction.
  destruct X as [r1 [A [B C]]]. subst s2. 
  exploit IHstar; eauto. intros [D E]. 
  split. auto. destruct B; destruct E. split. congruence. auto. 
  (* statement steps *)
  inv H.
Qed.

Theorem eval_simple_steps:
  forall f r e m w v ty m',
  star step ge (ExprState f r Kstop e m) w (ExprState f (Eval v ty) Kstop e m') ->
  simple r ->
  m' = m /\ ty = typeof r /\ eval_simple_rvalue e m r v.
Proof.
  intros. exploit compat_eval_steps; eauto. intros [A [B C]]. 
  intuition. apply C. constructor.
Qed.

(** * Soundness of the compile-time evaluator *)

(** [match_val v v'] holds if the compile-time value [v]
  (with symbolic pointers) matches the run-time value [v']
  (with concrete pointers). *)

Inductive match_val: val -> val -> Prop :=
  | match_vint: forall n,
      match_val (Vint n) (Vint n)
  | match_vfloat: forall f,
      match_val (Vfloat f) (Vfloat f)
  | match_vptr: forall id b ofs,
      Genv.find_symbol ge id = Some b ->
      match_val (Vptr (Zpos id) ofs) (Vptr b ofs)
  | match_vundef:
      match_val Vundef Vundef.

Lemma match_val_of_bool:
  forall b, match_val (Val.of_bool b) (Val.of_bool b).
Proof.
  destruct b; constructor.
Qed.

Hint Constructors match_val: mval.
Hint Resolve match_val_of_bool: mval.

(** The [match_val] relation commutes with the evaluation functions
  from [Csem]. *)

Lemma sem_unary_match:
  forall op ty v1 v v1' v',
  sem_unary_operation op v1 ty = Some v ->
  sem_unary_operation op v1' ty = Some v' ->
  match_val v1 v1' ->
  match_val v v'.
Proof.
  intros. destruct op; simpl in *.
  unfold sem_notbool in *. destruct (classify_bool ty); inv H1; inv H; inv H0; auto with mval. constructor.
  unfold sem_notint in *. destruct (classify_notint ty); inv H1; inv H; inv H0; auto with mval.
  unfold sem_neg in *. destruct (classify_neg ty); inv H1; inv H; inv H0; auto with mval.
Qed.

Lemma mem_empty_not_valid_pointer:
  forall b ofs, Mem.valid_pointer Mem.empty b ofs = false.
Proof.
  intros. unfold Mem.valid_pointer. destruct (Mem.perm_dec Mem.empty b ofs Nonempty); auto.
  red in p. simpl in p. contradiction.
Qed.

Lemma sem_cmp_match:
  forall c v1 ty1 v2 ty2 m v v1' v2' v',
  sem_cmp c v1 ty1 v2 ty2 Mem.empty = Some v ->
  sem_cmp c v1' ty1 v2' ty2 m = Some v' ->
  match_val v1 v1' -> match_val v2 v2' ->
  match_val v v'.
Proof.
Opaque zeq.
  intros. unfold sem_cmp in *.
  destruct (classify_cmp ty1 ty2); try (destruct s); inv H1; inv H2; inv H; inv H0; auto with mval.
  destruct (Int.eq n Int.zero); try discriminate. 
  unfold sem_cmp_mismatch in *. destruct c; inv H3; inv H2; constructor.
  destruct (Int.eq n Int.zero); try discriminate. 
  unfold sem_cmp_mismatch in *. destruct c; inv H2; inv H1; constructor.
  rewrite (mem_empty_not_valid_pointer (Zpos id) (Int.unsigned ofs)) in H4. discriminate.
Qed.

Lemma sem_binary_match:
  forall op v1 ty1 v2 ty2 m v v1' v2' v',
  sem_binary_operation op v1 ty1 v2 ty2 Mem.empty = Some v ->
  sem_binary_operation op v1' ty1 v2' ty2 m = Some v' ->
  match_val v1 v1' -> match_val v2 v2' ->
  match_val v v'.
Proof.
  intros. unfold sem_binary_operation in *; destruct op.
(* add *)
  unfold sem_add in *. destruct (classify_add ty1 ty2); inv H1; inv H2; inv H; inv H0; auto with mval.
(* sub *)
  unfold sem_sub in *. destruct (classify_sub ty1 ty2); inv H1; inv H2; try (inv H; inv H0; auto with mval; fail).
  destruct (zeq (Zpos id) (Zpos id0)); try discriminate.
  assert (b0 = b) by congruence. subst b0. rewrite zeq_true in H0. 
  destruct (Int.eq (Int.repr (sizeof ty)) Int.zero); inv H; inv H0; auto with mval.
(* mul *)
  unfold sem_mul in *. destruct (classify_mul ty1 ty2); inv H1; inv H2; inv H; inv H0; auto with mval.
(* div *)
  unfold sem_div in H0. functional inversion H; rewrite H4 in H0; inv H1; inv H2; inv H0.
  rewrite H11 in H2. inv H2. inv H12. constructor.
  rewrite H11 in H2. inv H2. inv H12. constructor.
  inv H11. constructor.
  inv H11. constructor.
  inv H11. constructor.
(* mod *)
  unfold sem_mod in H0. functional inversion H; rewrite H4 in H0; inv H1; inv H2; inv H0.
  rewrite H11 in H2. inv H2. inv H12. constructor.
  rewrite H11 in H2. inv H2. inv H12. constructor.
(* and *)
  unfold sem_and in *. destruct (classify_binint ty1 ty2); inv H1; inv H2; inv H; inv H0; auto with mval.
(* or *)
  unfold sem_or in *. destruct (classify_binint ty1 ty2); inv H1; inv H2; inv H; inv H0; auto with mval.
(* xor *)
  unfold sem_xor in *. destruct (classify_binint ty1 ty2); inv H1; inv H2; inv H; inv H0; auto with mval.
(* shl *)
  unfold sem_shl in *. destruct (classify_shift ty1 ty2); inv H1; inv H2; try discriminate.
  destruct (Int.ltu n0 Int.iwordsize); inv H0; inv H; constructor.
(* shr *)
  unfold sem_shr in *. destruct (classify_shift ty1 ty2); try discriminate;
  destruct s; inv H1; inv H2; try discriminate.
  destruct (Int.ltu n0 Int.iwordsize); inv H0; inv H; constructor.
  destruct (Int.ltu n0 Int.iwordsize); inv H0; inv H; constructor.
(* comparisons *)
  eapply sem_cmp_match; eauto.
  eapply sem_cmp_match; eauto.
  eapply sem_cmp_match; eauto.
  eapply sem_cmp_match; eauto.
  eapply sem_cmp_match; eauto.
  eapply sem_cmp_match; eauto.
Qed.

Lemma sem_cast_match:
  forall v1 ty1 ty2 v2, sem_cast v1 ty1 ty2 = Some v2 ->
  forall v1' v2',  match_val v1' v1 -> do_cast v1' ty1 ty2 = OK v2' ->
  match_val v2' v2.
Proof.
  intros. unfold do_cast in H1. destruct (sem_cast v1' ty1 ty2) as [v2''|] _eqn; inv H1.
  inv H0.
  replace v2' with v2 by congruence.
  functional inversion H; subst; constructor.
  replace v2' with v2 by congruence.
  functional inversion H; subst; constructor.
  simpl in H; simpl in Heqo. 
  destruct (neutral_for_cast ty1 && neutral_for_cast ty2); inv H; inv Heqo. 
  constructor; auto.
  functional inversion H. 
Qed.

Lemma bool_val_match:
  forall v v' ty,
  match_val v v' ->
  bool_val v ty = bool_val v' ty.
Proof.
  intros. inv H; auto.
Qed.
  
(** Soundness of [constval] with respect to the big-step semantics *)

Lemma constval_rvalue:
  forall m a v,
  eval_simple_rvalue empty_env m a v ->
  forall v',
  constval a = OK v' ->
  match_val v' v
with constval_lvalue:
  forall m a b ofs,
  eval_simple_lvalue empty_env m a b ofs ->
  forall v',
  constval a = OK v' ->
  match_val v' (Vptr b ofs).
Proof.
  (* rvalue *)
  induction 1; intros vres CV; simpl in CV; try (monadInv CV).
  (* val *)
  destruct v; monadInv CV; constructor.
  (* rval *)
  unfold load_value_of_type in H1. destruct (access_mode ty); try congruence. inv H1. 
  eauto.
  (* addrof *)
  eauto.
  (* unop *)
  revert EQ0. caseEq (sem_unary_operation op x (typeof r1)); intros; inv EQ0.
  eapply sem_unary_match; eauto. 
  (* binop *)
  revert EQ2. caseEq (sem_binary_operation op x (typeof r1) x0 (typeof r2) Mem.empty); intros; inv EQ2.
  eapply sem_binary_match; eauto.
  (* cast *)
  eapply sem_cast_match; eauto. 
  (* sizeof *)
  constructor.
  (* conditional *)
  rewrite (bool_val_match x v1 (typeof r1)) in EQ3; auto.
  rewrite H0 in EQ3. destruct b; eapply sem_cast_match; eauto.
  (* comma *)
  auto.
  (* paren *)
  eapply sem_cast_match; eauto.

  (* lvalue *)
  induction 1; intros v' CV; simpl in CV; try (monadInv CV).
  (* var local *)
  unfold empty_env in H. rewrite PTree.gempty in H. congruence.
  (* var_global *)
  constructor; auto.
  (* deref *)
  eauto.
  (* field struct *)
  rewrite H0 in CV. monadInv CV. exploit IHeval_simple_lvalue; eauto. intro MV. inv MV.
  simpl. replace x with delta by congruence. constructor. auto.
  (* field union *)
  rewrite H0 in CV. auto.
Qed.

Lemma constval_simple:
  forall a v, constval a = OK v -> simple a.
Proof.
  induction a; simpl; intros vx CV; try (monadInv CV); eauto.
  destruct (typeof a); discriminate || eauto.
  monadInv CV. eauto.
  destruct (access_mode ty); discriminate || eauto.
  intuition eauto.
Qed.
  
(** Soundness of [constval] with respect to the reduction semantics. *)

Theorem constval_steps:
  forall f r m w v v' ty m',
  star step ge (ExprState f r Kstop empty_env m) w (ExprState f (Eval v' ty) Kstop empty_env m') ->
  constval r = OK v ->
  m' = m /\ ty = typeof r /\ match_val v v'.
Proof.
  intros. exploit eval_simple_steps; eauto. eapply constval_simple; eauto. 
  intros [A [B C]]. intuition. eapply constval_rvalue; eauto.
Qed.

(** * Soundness of the translation of initializers *)

(** Soundness for single initializers. *)

Theorem transl_init_single_steps:
  forall ty a data f m w v1 ty1 m' v chunk b ofs m'',
  transl_init_single ty a = OK data ->
  star step ge (ExprState f a Kstop empty_env m) w (ExprState f (Eval v1 ty1) Kstop empty_env m') ->
  sem_cast v1 ty1 ty = Some v ->
  access_mode ty = By_value chunk ->
  Mem.store chunk m' b ofs v = Some m'' ->
  Genv.store_init_data ge m b ofs data = Some m''.
Proof.
  intros. monadInv H. 
  exploit constval_steps; eauto. intros [A [B C]]. subst m' ty1.
  exploit sem_cast_match; eauto. intros D.
  unfold Genv.store_init_data. 
  inv D. 
  (* int *)
  destruct ty; try discriminate. 
  destruct i; inv EQ2.
  destruct s; simpl in H2; inv H2. rewrite <- Mem.store_signed_unsigned_8; auto. auto.
  destruct s; simpl in H2; inv H2. rewrite <- Mem.store_signed_unsigned_16; auto. auto.
  simpl in H2; inv H2. assumption.
  inv EQ2. simpl in H2; inv H2. assumption.
  (* float *)
  destruct ty; try discriminate. 
  destruct f1; inv EQ2; simpl in H2; inv H2; assumption.
  (* pointer *)
  assert (data = Init_addrof id ofs0 /\ chunk = Mint32).
    destruct ty; inv EQ2; inv H2. destruct i; inv H5. intuition congruence. auto.
  destruct H4; subst. rewrite H. assumption.
  (* undef *)
  discriminate.
Qed.

(** Size properties for initializers. *)

Lemma transl_init_single_size:
  forall ty a data,
  transl_init_single ty a = OK data ->
  Genv.init_data_size data = sizeof ty.
Proof.
  intros. monadInv H. destruct x0. 
  monadInv EQ2.
  destruct ty; try discriminate. 
  destruct i0; inv EQ2; reflexivity.
  inv EQ2; reflexivity.
  destruct ty; try discriminate.
  destruct f0; inv EQ2; reflexivity.
  destruct b; try discriminate.
  destruct ty; try discriminate.
  destruct i0; inv EQ2; reflexivity.
  inv EQ2; reflexivity.
Qed.

Notation idlsize := Genv.init_data_list_size.

Remark padding_size:
  forall frm to,
  frm <= to -> idlsize (padding frm to) = to - frm.
Proof.
  intros. unfold padding. 
  destruct (zle (to - frm) 0). 
  simpl. omega.
  simpl. rewrite Zmax_spec. rewrite zlt_true. omega. omega.
Qed. 

Remark idlsize_app:
  forall d1 d2, idlsize (d1 ++ d2) = idlsize d1 + idlsize d2.
Proof.
  induction d1; simpl; intros. 
  auto.
  rewrite IHd1. omega.
Qed.

Remark sizeof_struct_incr:
  forall fl pos, pos <= sizeof_struct fl pos.
Proof.
  induction fl; intros; simpl. 
  omega.
  eapply Zle_trans. apply align_le with (y := alignof t). apply alignof_pos.
  eapply Zle_trans. 2: apply IHfl.
  generalize (sizeof_pos t); omega.
Qed.

Remark sizeof_struct_eq:
  forall id fl,
  fl <> Fnil ->
  sizeof (Tstruct id fl) = align (sizeof_struct fl 0) (alignof (Tstruct id fl)).
Proof.
  intros. simpl. f_equal. rewrite Zmax_spec. apply zlt_false. 
  destruct fl. congruence. simpl. 
  apply Zle_ge. eapply Zle_trans. 2: apply sizeof_struct_incr. 
  assert (0 <= align 0 (alignof t)). apply align_le. apply alignof_pos. 
  generalize (sizeof_pos t). omega.
Qed.

Remark sizeof_union_eq:
  forall id fl,
  fl <> Fnil ->
  sizeof (Tunion id fl) = align (sizeof_union fl) (alignof (Tunion id fl)).
Proof.
  intros. simpl. f_equal. rewrite Zmax_spec. apply zlt_false. 
  destruct fl. congruence. simpl. 
  apply Zle_ge. apply Zmax_bound_l. generalize (sizeof_pos t). omega.
Qed.

Lemma transl_init_size:
  forall i ty data,
  transl_init ty i = OK data ->
  idlsize data = sizeof ty

with transl_init_list_size:
  forall il,
  (forall ty sz data,
   transl_init_array ty il sz = OK data ->
   idlsize data = sizeof ty * sz)
  /\
  (forall id ty fl pos data,
   transl_init_struct id ty fl il pos = OK data ->
   sizeof_struct fl pos <= sizeof ty ->
   idlsize data + pos = sizeof ty)
  /\
  (forall id ty ty1 data,
   transl_init_union id ty ty1 il = OK data ->
   sizeof ty1 <= sizeof ty ->
   idlsize data = sizeof ty).

Proof.
  induction i; intros. 
  (* single *)
  monadInv H. simpl. rewrite (transl_init_single_size _ _ _ EQ). omega.
  (* compound *)
  simpl in H. destruct ty; try discriminate.
  (* compound array *)
  destruct (zle z 0). 
  monadInv H. simpl. repeat rewrite Zmax_spec. rewrite zlt_true. rewrite zlt_true. ring.
  omega. generalize (sizeof_pos ty); omega.
  simpl. rewrite Zmax_spec. rewrite zlt_false.
  eapply (proj1 (transl_init_list_size il)). auto. omega.
  (* compound struct *)
  destruct f. 
  inv H. reflexivity.
  replace (idlsize data) with (idlsize data + 0) by omega.
  eapply (proj1 (proj2 (transl_init_list_size il))). eauto.
  rewrite sizeof_struct_eq. 2: congruence. 
  apply align_le. apply alignof_pos.
  (* compound union *)
  destruct f.
  inv H. reflexivity.
  eapply (proj2 (proj2 (transl_init_list_size il))). eauto. 
  rewrite sizeof_union_eq. 2: congruence. 
  eapply Zle_trans. 2: apply align_le. simpl. apply Zmax_bound_l. omega. 
  apply alignof_pos.

  induction il.
  (* base cases *)
  simpl. intuition. 
  (* arrays *)
  destruct (zeq sz 0); inv H. simpl. ring. 
  (* structs *)
  destruct fl; inv H.
  simpl in H0. generalize (padding_size pos (sizeof ty) H0). omega.
  (* unions *)
  inv H.
  (* inductive cases *)
  destruct IHil as [A [B C]]. split.
  (* arrays *)
  intros. monadInv H.
  rewrite idlsize_app. 
  rewrite (transl_init_size _ _ _ EQ). 
  rewrite (A _ _ _ EQ1).
  ring.
  (* structs *)
  split. intros. simpl in H. destruct fl; monadInv H.
  repeat rewrite idlsize_app. 
  simpl in H0. 
  rewrite padding_size.
  rewrite (transl_init_size _ _ _ EQ). rewrite sizeof_unroll_composite.
  rewrite <- (B _ _ _ _ _ EQ1). omega.
  auto. apply align_le. apply alignof_pos. 
  (* unions *)
  intros. simpl in H. monadInv H. 
  rewrite idlsize_app.
  rewrite (transl_init_size _ _ _ EQ). rewrite sizeof_unroll_composite. 
  rewrite padding_size. omega. auto.
Qed.

(** A semantics for general initializers *)

Definition dummy_function := mkfunction Tvoid nil nil Sskip.

Fixpoint fields_of_struct (id: ident) (ty: type) (fl: fieldlist) (pos: Z) : list (Z * type) :=
  match fl with
  | Fnil => nil
  | Fcons id1 ty1 fl' =>
      (align pos (alignof ty1), unroll_composite id ty ty1) 
      :: fields_of_struct id ty fl' (align pos (alignof ty1) + sizeof ty1)
  end.

Inductive exec_init: mem -> block -> Z -> type -> initializer -> mem -> Prop :=
  | exec_init_single: forall m b ofs ty a v1 ty1 chunk m' v m'',
      star step ge (ExprState dummy_function a Kstop empty_env m) 
                E0 (ExprState dummy_function (Eval v1 ty1) Kstop empty_env m') ->
      sem_cast v1 ty1 ty = Some v ->
      access_mode ty = By_value chunk ->
      Mem.store chunk m' b ofs v = Some m'' ->
      exec_init m b ofs ty (Init_single a) m''
  | exec_init_compound_array: forall m b ofs ty sz il m',
      exec_init_array m b ofs ty sz il m' ->
      exec_init m b ofs (Tarray ty sz) (Init_compound il) m'
  | exec_init_compound_struct: forall m b ofs id fl il m',
      exec_init_list m b ofs (fields_of_struct id (Tstruct id fl) fl 0) il m' ->
      exec_init m b ofs (Tstruct id fl) (Init_compound il) m'
  | exec_init_compound_union: forall m b ofs id id1 ty1 fl i m',
      exec_init m b ofs (unroll_composite id (Tunion id (Fcons id1 ty1 fl)) ty1) i m' ->
      exec_init m b ofs (Tunion id (Fcons id1 ty1 fl)) (Init_compound (Init_cons i Init_nil)) m'

with exec_init_array: mem -> block -> Z -> type -> Z -> initializer_list -> mem -> Prop :=
  | exec_init_array_nil: forall m b ofs ty,
      exec_init_array m b ofs ty 0 Init_nil m
  | exec_init_array_cons: forall m b ofs ty sz i1 il m' m'',
      exec_init m b ofs ty i1 m' ->
      exec_init_array m' b (ofs + sizeof ty) ty (sz - 1) il m'' ->
      exec_init_array m b ofs ty sz (Init_cons i1 il) m''

with exec_init_list: mem -> block -> Z -> list (Z * type) -> initializer_list -> mem -> Prop :=
  | exec_init_list_nil: forall m b ofs,
      exec_init_list m b ofs nil Init_nil m
  | exec_init_list_cons: forall m b ofs pos ty l i1 il m' m'',
      exec_init m b (ofs + pos) ty i1 m' ->
      exec_init_list m' b ofs l il m'' ->
      exec_init_list m b ofs ((pos, ty) :: l) (Init_cons i1 il) m''.

Scheme exec_init_ind3 := Minimality for exec_init Sort Prop
  with exec_init_array_ind3 := Minimality for exec_init_array Sort Prop
  with exec_init_list_ind3 := Minimality for exec_init_list Sort Prop.
Combined Scheme exec_init_scheme from exec_init_ind3, exec_init_array_ind3, exec_init_list_ind3.

Remark exec_init_array_length:
  forall m b ofs ty sz il m', 
  exec_init_array m b ofs ty sz il m' ->
  match il with Init_nil => sz = 0 | Init_cons _ _ => sz > 0 end.
Proof.
  induction 1. auto. destruct il; omega. 
Qed.

Lemma store_init_data_list_app:
  forall data1 m b ofs m' data2 m'',
  Genv.store_init_data_list ge m b ofs data1 = Some m' ->
  Genv.store_init_data_list ge m' b (ofs + idlsize data1) data2 = Some m'' ->
  Genv.store_init_data_list ge m b ofs (data1 ++ data2) = Some m''.
Proof.
  induction data1; simpl; intros. 
  inv H. rewrite Zplus_0_r in H0. auto.
  destruct (Genv.store_init_data ge m b ofs a); try discriminate.
  rewrite Zplus_assoc in H0. eauto.
Qed.

Remark store_init_data_list_padding:
  forall frm to b ofs m,
  Genv.store_init_data_list ge m b ofs (padding frm to) = Some m.
Proof.
  intros. unfold padding. destruct (zle (to - frm) 0); auto.
Qed.

Lemma transl_init_sound_gen:
  (forall m b ofs ty i m', exec_init m b ofs ty i m' ->
   forall data, transl_init ty i = OK data ->
   Genv.store_init_data_list ge m b ofs data = Some m')
/\(forall m b ofs ty sz il m', exec_init_array m b ofs ty sz il m' ->
   forall data, transl_init_array ty il sz = OK data ->
   Genv.store_init_data_list ge m b ofs data = Some m')
/\(forall m b ofs l il m', exec_init_list m b ofs l il m' ->
   forall id ty fl data pos,
   l = fields_of_struct id ty fl pos ->
   transl_init_struct id ty fl il pos = OK data ->
   Genv.store_init_data_list ge m b (ofs + pos) data = Some m').
Proof.
  apply exec_init_scheme; simpl; intros.
  (* single *)
  monadInv H3.
  exploit transl_init_single_steps; eauto. intros. 
  simpl. rewrite H3. auto.
  (* array *)
  destruct (zle sz 0).
  exploit exec_init_array_length; eauto. destruct il; intros.
  subst. inv H. inv H1. auto. omegaContradiction.
  eauto.
  (* struct *)
  destruct fl.
  inv H. inv H1. auto.
  replace ofs with (ofs + 0) by omega. eauto.
  (* union *)
  monadInv H1. eapply store_init_data_list_app. eauto. apply store_init_data_list_padding. 

  (* array, empty *)
  inv H. auto.
  (* array, nonempty *)
  monadInv H3. 
  eapply store_init_data_list_app.
  eauto.
  rewrite (transl_init_size _ _ _ EQ). eauto.

  (* struct, empty *)
  destruct fl; simpl in H; inv H. 
  inv H0. apply store_init_data_list_padding.
  (* struct, nonempty *)
  destruct fl; simpl in H3; inv H3.
  monadInv H4. 
  eapply store_init_data_list_app. apply store_init_data_list_padding.
  rewrite padding_size. 
  replace (ofs + pos0 + (align pos0 (alignof t) - pos0))
     with (ofs + align pos0 (alignof t)) by omega.
  eapply store_init_data_list_app.
  eauto.
  rewrite (transl_init_size _ _ _ EQ).
  rewrite <- Zplus_assoc. eapply H2.
  rewrite sizeof_unroll_composite. eauto. 
  rewrite sizeof_unroll_composite. eauto. 
  apply align_le. apply alignof_pos.
Qed.

Theorem transl_init_sound:
  forall m b ty i m' data,
  exec_init m b 0 ty i m' ->
  transl_init ty i = OK data ->
  Genv.store_init_data_list ge m b 0 data = Some m'.
Proof.
  intros. eapply (proj1 transl_init_sound_gen); eauto.
Qed.

End SOUNDNESS.


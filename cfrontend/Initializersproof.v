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
      cast v1 (typeof r1) ty v ->
      eval_simple_rvalue (Ecast r1 ty) v
  | esr_sizeof: forall ty1 ty,
      eval_simple_rvalue (Esizeof ty1 ty) (Vint (Int.repr (sizeof ty1)))
  | esr_condition_true: forall r1 r2 r3 ty v v1,
      eval_simple_rvalue r1 v1 -> is_true v1 (typeof r1) -> eval_simple_rvalue r2 v ->
      eval_simple_rvalue (Econdition r1 r2 r3 ty) v
  | esr_condition_false: forall r1 r2 r3 ty v v1,
      eval_simple_rvalue r1 v1 -> is_false v1 (typeof r1) -> eval_simple_rvalue r3 v ->
      eval_simple_rvalue (Econdition r1 r2 r3 ty) v
  | esr_comma: forall r1 r2 ty v1 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v ->
      eval_simple_rvalue (Ecomma r1 r2 ty) v
  | esr_paren: forall r ty v,
      eval_simple_rvalue r v ->
      eval_simple_rvalue (Eparen r ty) v.

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
  induction 1; simpl; tauto.
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
  inv EV. eapply esr_condition_true; eauto. constructor. 
  inv EV. eapply esr_condition_false; eauto. constructor.
  inv EV. constructor.
  econstructor; eauto. constructor.
  constructor; auto.
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
  inv H0.
    eapply esr_condition_true; eauto. congruence.
    eapply esr_condition_false; eauto. congruence.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  red; split; intros. auto. inv H0.
  inv H0. econstructor; eauto.
  inv H0. constructor. auto. 
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
    inv H9; simpl in S; contradiction.
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
  intros. unfold sem_cmp in *.
  destruct (classify_cmp ty1 ty2); inv H1; inv H2; inv H; inv H0; auto with mval.
  destruct (Int.eq n Int.zero); try discriminate. 
  unfold sem_cmp_mismatch in *. destruct c; inv H3; inv H2; constructor.
  destruct (Int.eq n Int.zero); try discriminate. 
  unfold sem_cmp_mismatch in *. destruct c; inv H2; inv H1; constructor.
  rewrite (mem_empty_not_valid_pointer (Zpos id) (Int.signed ofs)) in H4. discriminate.
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

Lemma is_neutral_for_cast_correct:
  forall t, neutral_for_cast t -> is_neutral_for_cast t = true.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma cast_match:
  forall v1 ty1 ty2 v2, cast v1 ty1 ty2 v2 ->
  forall v1' v2',  match_val v1' v1 -> do_cast v1' ty1 ty2 = OK v2' ->
  match_val v2' v2.
Proof.
  induction 1; intros v1' v2' MV DC; inv MV; simpl in DC.
  inv DC; constructor.
  rewrite H in DC. inv DC. constructor.
  inv DC; constructor.
  inv DC; constructor.
  rewrite (is_neutral_for_cast_correct _ H) in DC. 
  rewrite (is_neutral_for_cast_correct _ H0) in DC.
  simpl in DC. inv DC. constructor; auto.
  rewrite (is_neutral_for_cast_correct _ H) in DC. 
  rewrite (is_neutral_for_cast_correct _ H0) in DC.
  simpl in DC. 
  assert (OK v2' = OK (Vint n)). 
    inv H; auto. inv H0; auto.
  inv H1. constructor.
Qed.

Lemma bool_val_true:
  forall v v' ty, is_true v' ty -> match_val v v' -> bool_val v ty = OK true.
Proof.
  induction 1; intros MV; inv MV; simpl; auto.
  predSpec Int.eq Int.eq_spec n Int.zero. congruence. auto.
  predSpec Int.eq Int.eq_spec n Int.zero. congruence. auto.
  rewrite H; auto.
Qed.

Lemma bool_val_false:
  forall v v' ty, is_false v' ty -> match_val v v' -> bool_val v ty = OK false.
Proof.
  induction 1; intros MV; inv MV; simpl; auto.
  rewrite H; auto.
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
  induction 1; intros v' CV; simpl in CV; try (monadInv CV).
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
  eapply cast_match; eauto. 
  (* sizeof *)
  constructor.
  (* conditional true *)
  assert (x0 = true). exploit bool_val_true; eauto. congruence. subst x0. auto.
  (* conditional false *)
  assert (x0 = false). exploit bool_val_false; eauto. congruence. subst x0. auto.
  (* comma *)
  auto.
  (* paren *)
  auto.

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

Theorem transl_init_single_steps:
  forall ty a data f m w v1 ty1 m' v b ofs m'',
  transl_init_single ty a = OK data ->
  star step ge (ExprState f a Kstop empty_env m) w (ExprState f (Eval v1 ty1) Kstop empty_env m') ->
  cast v1 ty1 ty v ->
  store_value_of_type ty m' b ofs v = Some m'' ->
  Genv.store_init_data ge m b (Int.signed ofs) data = Some m''.
Proof.
  intros. monadInv H. 
  exploit constval_steps; eauto. intros [A [B C]]. subst m' ty1.
  exploit cast_match; eauto. intros D.
  unfold Genv.store_init_data. unfold store_value_of_type in H2. simpl in H2. 
  inv D. 
  (* int *)
  destruct ty; try discriminate. 
  destruct i; inv EQ2.
  destruct s; simpl in H2. rewrite <- Mem.store_signed_unsigned_8; auto. auto. 
  destruct s; simpl in H2. rewrite <- Mem.store_signed_unsigned_16; auto. auto.
  assumption.
  inv EQ2. assumption.
  (* float *)
  destruct ty; try discriminate. 
  destruct f1; inv EQ2; assumption.
  (* pointer *)
  assert (data = Init_addrof id ofs0 /\ access_mode ty = By_value Mint32).
    destruct ty; inv EQ2; auto. destruct i; inv H4; auto.
  destruct H3; subst. rewrite H4 in H2. rewrite H. assumption.
  (* undef *)
  discriminate.
Qed.

End SOUNDNESS.


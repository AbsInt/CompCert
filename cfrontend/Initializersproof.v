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
Require Import Ctypes.
Require Import Cop.
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
  | Eseqand r1 r2 _ => simple r1 /\ simple r2
  | Eseqor r1 r2 _ => simple r1 /\ simple r2
  | Econdition r1 r2 r3 _ => simple r1 /\ simple r2 /\ simple r3
  | Esizeof _ _ => True
  | Ealignof _ _ => True
  | Eassign _ _ _ => False
  | Eassignop _ _ _ _ _ => False
  | Epostincr _ _ _ => False
  | Ecomma r1 r2 _ => simple r1 /\ simple r2
  | Ecall _ _ _ => False
  | Ebuiltin _ _ _ _ => False
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
  | esl_field_struct: forall r f ty b ofs id fList a delta,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tstruct id fList a -> field_offset f fList = OK delta ->
      eval_simple_lvalue (Efield r f ty) b (Int.add ofs (Int.repr delta))
  | esl_field_union: forall r f ty b ofs id fList a,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tunion id fList a ->
      eval_simple_lvalue (Efield r f ty) b ofs

with eval_simple_rvalue: expr -> val -> Prop :=
  | esr_val: forall v ty,
      eval_simple_rvalue (Eval v ty) v
  | esr_rvalof: forall b ofs l ty v,
      eval_simple_lvalue l b ofs ->
      ty = typeof l ->
      deref_loc ge ty m b ofs E0 v ->
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
  | esr_alignof: forall ty1 ty,
      eval_simple_rvalue (Ealignof ty1 ty) (Vint (Int.repr (alignof ty1)))
  | esr_seqand_true: forall r1 r2 ty v1 v2 v3 v4,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) = Some true ->
      eval_simple_rvalue r2 v2 ->
      sem_cast v2 (typeof r2) type_bool = Some v3 ->
      sem_cast v3 type_bool ty = Some v4 ->
      eval_simple_rvalue (Eseqand r1 r2 ty) v4
  | esr_seqand_false: forall r1 r2 ty v1,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) = Some false ->
      eval_simple_rvalue (Eseqand r1 r2 ty) (Vint Int.zero)
  | esr_seqor_false: forall r1 r2 ty v1 v2 v3 v4,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) = Some false ->
      eval_simple_rvalue r2 v2 ->
      sem_cast v2 (typeof r2) type_bool = Some v3 ->
      sem_cast v3 type_bool ty = Some v4 ->
      eval_simple_rvalue (Eseqor r1 r2 ty) v4
  | esr_seqor_true: forall r1 r2 ty v1,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) = Some true ->
      eval_simple_rvalue (Eseqor r1 r2 ty) (Vint Int.one)
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
  forall r m t r' m', rred ge r m t r' m' -> simple r -> simple r'.
Proof.
  induction 1; simpl; intuition. destruct b; auto. 
Qed.

Lemma rred_compat:
  forall e r m r' m', rred ge r m E0 r' m' ->
  simple r ->
  m = m' /\ compat_eval RV e r r' m.
Proof.
  intros until m'; intros RED SIMP. inv RED; simpl in SIMP; try contradiction; split; auto; split; auto; intros vx EV.
  inv EV. econstructor. constructor. auto. auto. 
  inv EV. econstructor. constructor.
  inv EV. econstructor; eauto. constructor. 
  inv EV. econstructor; eauto. constructor. constructor.
  inv EV. econstructor; eauto. constructor.
  inv EV. inv H2. eapply esr_seqand_true; eauto. constructor.
  inv EV. eapply esr_seqand_false; eauto. constructor.
  inv EV. eapply esr_seqor_true; eauto. constructor.
  inv EV. inv H2. eapply esr_seqor_false; eauto. constructor.
  inv EV. eapply esr_condition; eauto. constructor. 
  inv EV. constructor.
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
  inv H0. 
    eapply esr_seqand_true; eauto. rewrite TY; auto. 
    eapply esr_seqand_false; eauto. rewrite TY; auto.
  inv H0. 
    eapply esr_seqor_false; eauto. rewrite TY; auto. 
    eapply esr_seqor_true; eauto. rewrite TY; auto.
  inv H0. eapply esr_condition; eauto. congruence.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  red; split; intros. auto. inv H0.
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
  induction 2; simpl; try tauto. 
Qed.

Lemma compat_eval_steps_aux f r e m r' m' s2 :
  simple r ->
  star step ge s2 nil (ExprState f r' Kstop e m') ->
  estep ge (ExprState f r Kstop e m) nil s2 ->
  exists r1,
    s2 = ExprState f r1 Kstop e m /\
    compat_eval RV e r r1 m /\ simple r1.
Proof.
  intros.
  inv H1.
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
  inv H8; simpl in S; contradiction.
  (* stuckred *)
  inv H0. destruct H1; inv H0.
Qed.

Lemma compat_eval_steps:
  forall f r e m  r' m',
  star step ge (ExprState f r Kstop e m) E0 (ExprState f r' Kstop e m') ->
  simple r -> 
  m' = m /\ compat_eval RV e r r' m.
Proof.
  intros. 
  remember (ExprState f r Kstop e m) as S1.
  remember E0 as t.
  remember (ExprState f r' Kstop e m') as S2.
  revert S1 t S2 H r m r' m' HeqS1 Heqt HeqS2 H0.
  induction 1; intros; subst.
  (* base case *) 
  inv HeqS2. split. auto. red; auto.
  (* inductive case *)
  destruct (app_eq_nil t1 t2); auto. subst. inv H.
  (* expression step *)
  exploit compat_eval_steps_aux; eauto.
  intros [r1 [A [B C]]]. subst s2.
  exploit IHstar; eauto. intros [D E].
  split. auto. destruct B; destruct E. split. congruence. auto. 
  (* statement steps *)
  inv H1.
Qed.

Theorem eval_simple_steps:
  forall f r e m v ty m',
  star step ge (ExprState f r Kstop e m) E0 (ExprState f (Eval v ty) Kstop e m') ->
  simple r ->
  m' = m /\ ty = typeof r /\ eval_simple_rvalue e m r v.
Proof.
  intros. exploit compat_eval_steps; eauto. intros [A [B C]]. 
  intuition. apply C. constructor.
Qed.

(** * Soundness of the compile-time evaluator *)

(** A global environment [ge] induces a memory injection mapping
  our symbolic pointers [Vptr id ofs] to run-time pointers
  [Vptr b ofs] where [Genv.find_symbol ge id = Some b]. *)

Definition inj (b: block) :=
  match Genv.find_symbol ge b with
  | Some b' => Some (b', 0)
  | None => None
  end.

Lemma mem_empty_not_valid_pointer:
  forall b ofs, Mem.valid_pointer Mem.empty b ofs = false.
Proof.
  intros. unfold Mem.valid_pointer. destruct (Mem.perm_dec Mem.empty b ofs Cur Nonempty); auto.
  eelim Mem.perm_empty; eauto. 
Qed.

Lemma mem_empty_not_weak_valid_pointer:
  forall b ofs, Mem.weak_valid_pointer Mem.empty b ofs = false.
Proof.
  intros. unfold Mem.weak_valid_pointer.
  now rewrite !mem_empty_not_valid_pointer.
Qed.

Lemma sem_cast_match:
  forall v1 ty1 ty2 v2 v1' v2',
  sem_cast v1 ty1 ty2 = Some v2 ->
  do_cast v1' ty1 ty2 = OK v2' ->
  val_inject inj v1' v1 ->
  val_inject inj v2' v2.
Proof.
  intros. unfold do_cast in H0. destruct (sem_cast v1' ty1 ty2) as [v2''|] eqn:E; inv H0.
  exploit sem_cast_inject. eexact E. eauto. 
  intros [v' [A B]]. congruence.
Qed.

(** Soundness of [constval] with respect to the big-step semantics *)

Lemma constval_rvalue:
  forall m a v,
  eval_simple_rvalue empty_env m a v ->
  forall v',
  constval a = OK v' ->
  val_inject inj v' v
with constval_lvalue:
  forall m a b ofs,
  eval_simple_lvalue empty_env m a b ofs ->
  forall v',
  constval a = OK v' ->
  val_inject inj v' (Vptr b ofs).
Proof.
  (* rvalue *)
  induction 1; intros vres CV; simpl in CV; try (monadInv CV).
  (* val *)
  destruct v; monadInv CV; constructor.
  (* rval *)
  inv H1; rewrite H2 in CV; try congruence. eauto. eauto. 
  (* addrof *)
  eauto.
  (* unop *)
  destruct (sem_unary_operation op x (typeof r1)) as [v1'|] eqn:E; inv EQ0.
  exploit sem_unary_operation_inject. eexact E. eauto. 
  intros [v' [A B]]. congruence.
  (* binop *)
  destruct (sem_binary_operation op x (typeof r1) x0 (typeof r2) Mem.empty) as [v1'|] eqn:E; inv EQ2.
  exploit (sem_binary_operation_inj inj Mem.empty m).
  intros. rewrite mem_empty_not_valid_pointer in H3; discriminate.
  intros. rewrite mem_empty_not_weak_valid_pointer in H3; discriminate.
  intros. rewrite mem_empty_not_weak_valid_pointer in H3; discriminate.
  intros. rewrite mem_empty_not_valid_pointer in H3; discriminate.
  eauto. eauto. eauto. 
  intros [v' [A B]]. congruence.
  (* cast *)
  eapply sem_cast_match; eauto. 
  (* sizeof *)
  constructor.
  (* alignof *)
  constructor.
  (* seqand *)
  destruct (bool_val x (typeof r1)) as [b|] eqn:E; inv EQ2. 
  exploit bool_val_inject. eexact E. eauto. intros E'.
  assert (b = true) by congruence. subst b. monadInv H5. 
  eapply sem_cast_match; eauto. eapply sem_cast_match; eauto.
  destruct (bool_val x (typeof r1)) as [b|] eqn:E; inv EQ2. 
  exploit bool_val_inject. eexact E. eauto. intros E'.
  assert (b = false) by congruence. subst b. inv H2. auto.
  (* seqor *)
  destruct (bool_val x (typeof r1)) as [b|] eqn:E; inv EQ2. 
  exploit bool_val_inject. eexact E. eauto. intros E'.
  assert (b = false) by congruence. subst b. monadInv H5. 
  eapply sem_cast_match; eauto. eapply sem_cast_match; eauto.
  destruct (bool_val x (typeof r1)) as [b|] eqn:E; inv EQ2. 
  exploit bool_val_inject. eexact E. eauto. intros E'.
  assert (b = true) by congruence. subst b. inv H2. auto.
  (* conditional *)
  destruct (bool_val x (typeof r1)) as [b'|] eqn:E; inv EQ3.
  exploit bool_val_inject. eexact E. eauto. intros E'.
  assert (b' = b) by congruence. subst b'. 
  destruct b; eapply sem_cast_match; eauto.
  (* comma *)
  auto.
  (* paren *)
  eapply sem_cast_match; eauto.

  (* lvalue *)
  induction 1; intros v' CV; simpl in CV; try (monadInv CV).
  (* var local *)
  unfold empty_env in H. rewrite PTree.gempty in H. congruence.
  (* var_global *)
  econstructor. unfold inj. rewrite H0. eauto. auto. 
  (* deref *)
  eauto.
  (* field struct *)
  rewrite H0 in CV. monadInv CV. exploit constval_rvalue; eauto. intro MV. inv MV.
  simpl. replace x with delta by congruence. econstructor; eauto. 
  rewrite ! Int.add_assoc. f_equal. apply Int.add_commut. 
  simpl. auto.
  (* field union *)
  rewrite H0 in CV. eauto.
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
  forall f r m v v' ty m',
  star step ge (ExprState f r Kstop empty_env m) E0 (ExprState f (Eval v' ty) Kstop empty_env m') ->
  constval r = OK v ->
  m' = m /\ ty = typeof r /\ val_inject inj v v'.
Proof.
  intros. exploit eval_simple_steps; eauto. eapply constval_simple; eauto. 
  intros [A [B C]]. intuition. eapply constval_rvalue; eauto.
Qed.

(** * Soundness of the translation of initializers *)

(** Soundness for single initializers. *)

Theorem transl_init_single_steps:
  forall ty a data f m v1 ty1 m' v chunk b ofs m'',
  transl_init_single ty a = OK data ->
  star step ge (ExprState f a Kstop empty_env m) E0 (ExprState f (Eval v1 ty1) Kstop empty_env m') ->
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
  destruct i0; inv EQ2.
  destruct s; simpl in H2; inv H2. rewrite <- Mem.store_signed_unsigned_8; auto. auto.
  destruct s; simpl in H2; inv H2. rewrite <- Mem.store_signed_unsigned_16; auto. auto.
  simpl in H2; inv H2. assumption.
  simpl in H2; inv H2. assumption. 
  inv EQ2. simpl in H2; inv H2. assumption.
  (* long *)
  destruct ty; inv EQ2. simpl in H2; inv H2. assumption.
  (* float *)
  destruct ty; try discriminate. 
  destruct f1; inv EQ2; simpl in H2; inv H2; assumption.
  (* pointer *)
  unfold inj in H.
  assert (data = Init_addrof b1 ofs1 /\ chunk = Mint32).
    destruct ty; inv EQ2; inv H2.
    destruct i; inv H5. intuition congruence. auto.
  destruct H4; subst. destruct (Genv.find_symbol ge b1); inv H. 
  rewrite Int.add_zero in H3. auto.
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
  inv EQ2; reflexivity.
  destruct ty; inv EQ2; reflexivity. 
  destruct ty; try discriminate.
  destruct f0; inv EQ2; reflexivity.
  destruct ty; try discriminate.
  destruct i0; inv EQ2; reflexivity.
  inv EQ2; reflexivity.
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
  forall id fl a,
  fl <> Fnil ->
  sizeof (Tstruct id fl a) = align (sizeof_struct fl 0) (alignof (Tstruct id fl a)).
Proof.
  intros. simpl. f_equal. rewrite Zmax_spec. apply zlt_false. 
  destruct fl. congruence. simpl. 
  apply Zle_ge. eapply Zle_trans. 2: apply sizeof_struct_incr. 
  assert (0 <= align 0 (alignof t)). apply align_le. apply alignof_pos. 
  generalize (sizeof_pos t). omega.
Qed.

Remark sizeof_union_eq:
  forall id fl a,
  fl <> Fnil ->
  sizeof (Tunion id fl a) = align (sizeof_union fl) (alignof (Tunion id fl a)).
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
  rewrite (transl_init_size _ _ _ EQ). 
  rewrite <- (B _ _ _ _ _ EQ1). omega.
  auto. apply align_le. apply alignof_pos. 
  (* unions *)
  intros. simpl in H. monadInv H. 
  rewrite idlsize_app.
  rewrite (transl_init_size _ _ _ EQ). 
  rewrite padding_size. omega. auto.
Qed.

(** A semantics for general initializers *)

Definition dummy_function := mkfunction Tvoid nil nil Sskip.

Fixpoint fields_of_struct (id: ident) (ty: type) (fl: fieldlist) (pos: Z) : list (Z * type) :=
  match fl with
  | Fnil => nil
  | Fcons id1 ty1 fl' =>
      (align pos (alignof ty1), ty1) :: fields_of_struct id ty fl' (align pos (alignof ty1) + sizeof ty1)
  end.

Inductive exec_init: mem -> block -> Z -> type -> initializer -> mem -> Prop :=
  | exec_init_single: forall m b ofs ty a v1 ty1 chunk m' v m'',
      star step ge (ExprState dummy_function a Kstop empty_env m) 
                E0 (ExprState dummy_function (Eval v1 ty1) Kstop empty_env m') ->
      sem_cast v1 ty1 ty = Some v ->
      access_mode ty = By_value chunk ->
      Mem.store chunk m' b ofs v = Some m'' ->
      exec_init m b ofs ty (Init_single a) m''
  | exec_init_compound_array: forall m b ofs ty sz a il m',
      exec_init_array m b ofs ty sz il m' ->
      exec_init m b ofs (Tarray ty sz a) (Init_compound il) m'
  | exec_init_compound_struct: forall m b ofs id fl a il m',
      exec_init_list m b ofs (fields_of_struct id (Tstruct id fl a) fl 0) il m' ->
      exec_init m b ofs (Tstruct id fl a) (Init_compound il) m'
  | exec_init_compound_union: forall m b ofs id id1 ty1 fl a i m',
      exec_init m b ofs ty1 i m' ->
      exec_init m b ofs (Tunion id (Fcons id1 ty1 fl) a) (Init_compound (Init_cons i Init_nil)) m'

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
  rewrite <- Zplus_assoc. eapply H2. eauto. eauto.
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



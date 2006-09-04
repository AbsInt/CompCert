(** * Correctness of the C front end, part 2: Csharpminor construction functions *)

Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Csharpminor.
Require Import Cshmgen.
Require Import Cshmgenproof1.

Section CONSTRUCTORS.

Variable tprog: Csharpminor.program.

(** Properties of the translation of [switch] constructs. *)

Lemma transl_lblstmts_exit:
  forall e m1 t m2 sl body n tsl nbrk ncnt,
  exec_stmt tprog e m1 body t m2 (Out_exit (lblstmts_length sl + n)) ->
  transl_lblstmts nbrk ncnt sl body = Some tsl ->
  exec_stmt tprog e m1 tsl t m2 (outcome_block (Out_exit n)).
Proof.
  induction sl; intros.
  simpl in H; simpl in H0; monadInv H0. 
  rewrite <- H2. constructor. apply exec_Sseq_stop. auto. congruence.
  simpl in H; simpl in H0; monadInv H0.
  eapply IHsl with (body := Sblock (Sseq body s0)); eauto.
  change (Out_exit (lblstmts_length sl + n))
    with (outcome_block (Out_exit (S (lblstmts_length sl + n)))).
  constructor. apply exec_Sseq_stop. auto. congruence.
Qed.

Lemma transl_lblstmts_return:
  forall e m1 t m2 sl body optv tsl nbrk ncnt,
  exec_stmt tprog e m1 body t m2 (Out_return optv) ->
  transl_lblstmts nbrk ncnt sl body = Some tsl ->
  exec_stmt tprog e m1 tsl t m2 (Out_return optv).
Proof.
  induction sl; intros.
  simpl in H; simpl in H0; monadInv H0. 
  rewrite <- H2. change (Out_return optv) with (outcome_block (Out_return optv)).
  constructor. apply exec_Sseq_stop. auto. congruence.
  simpl in H; simpl in H0; monadInv H0.
  eapply IHsl with (body := Sblock (Sseq body s0)); eauto.
  change (Out_return optv) with (outcome_block (Out_return optv)).
  constructor. apply exec_Sseq_stop. auto. congruence.
Qed.


(** Correctness of Csharpminor construction functions *)

Lemma make_intconst_correct:
  forall n le e m1,
  Csharpminor.eval_expr tprog le e m1 (make_intconst n) E0 m1 (Vint n).
Proof.
  intros. unfold make_intconst. econstructor. constructor. reflexivity. 
Qed.

Lemma make_floatconst_correct:
  forall n le e m1,
  Csharpminor.eval_expr tprog le e m1 (make_floatconst n) E0 m1 (Vfloat n).
Proof.
  intros. unfold make_floatconst. econstructor. constructor. reflexivity. 
Qed.

Lemma make_unop_correct:
  forall op le e m1 a ta m2 va v,
  Csharpminor.eval_expr tprog le e m1 a ta m2 va ->
  eval_operation op (va :: nil) m2 = Some v ->
  Csharpminor.eval_expr tprog le e m1 (make_unop op a) ta m2 v.
Proof.
  intros. unfold make_unop. econstructor. econstructor. eauto. constructor.
  traceEq. auto.
Qed.

Lemma make_binop_correct:
  forall op le e m1 a ta m2 va b tb m3 vb t v,
  Csharpminor.eval_expr tprog le e m1 a ta m2 va ->
  Csharpminor.eval_expr tprog le e m2 b tb m3 vb ->
  eval_operation op (va :: vb :: nil) m3 = Some v ->
  t = ta ** tb ->
  Csharpminor.eval_expr tprog le e m1 (make_binop op a b) t m3 v.
Proof.
  intros. unfold make_binop. 
  econstructor. econstructor. eauto. econstructor. eauto. constructor.
  reflexivity. traceEq. auto.
Qed.

Hint Resolve make_intconst_correct make_floatconst_correct
             make_unop_correct make_binop_correct: cshm.
Hint Extern 2 (@eq trace _ _) => traceEq: cshm.

Remark Vtrue_is_true: Val.is_true Vtrue.
Proof.
  simpl. apply Int.one_not_zero.
Qed.

Remark Vfalse_is_false: Val.is_false Vfalse.
Proof.
  simpl. auto.
Qed.

Lemma make_boolean_correct_true:
 forall le e m1 a t m2 v ty,
  Csharpminor.eval_expr tprog le e m1 a t m2 v ->
  is_true v ty ->
  exists vb,
    Csharpminor.eval_expr tprog le e m1 (make_boolean a ty) t m2 vb
    /\ Val.is_true vb.
Proof.
  intros until ty; intros EXEC VTRUE.
  destruct ty; simpl;
  try (exists v; intuition; inversion VTRUE; simpl; auto; fail).
  exists Vtrue; split.
  eapply make_binop_correct; eauto with cshm. 
  inversion VTRUE; simpl. 
  replace (Float.cmp Cne f0 Float.zero) with (negb (Float.cmp Ceq f0 Float.zero)).
  rewrite Float.eq_zero_false. reflexivity. auto.
  rewrite Float.cmp_ne_eq. auto.
  apply Vtrue_is_true.
Qed.

Lemma make_boolean_correct_false:
 forall le e m1 a t m2 v ty,
  Csharpminor.eval_expr tprog le e m1 a t m2 v ->
  is_false v ty ->
  exists vb,
    Csharpminor.eval_expr tprog le e m1 (make_boolean a ty) t m2 vb
    /\ Val.is_false vb.
Proof.
  intros until ty; intros EXEC VFALSE.
  destruct ty; simpl;
  try (exists v; intuition; inversion VFALSE; simpl; auto; fail).
  exists Vfalse; split.
  eapply make_binop_correct; eauto with cshm. 
  inversion VFALSE; simpl. 
  replace (Float.cmp Cne Float.zero Float.zero) with (negb (Float.cmp Ceq Float.zero Float.zero)).
  rewrite Float.eq_zero_true. reflexivity. 
  rewrite Float.cmp_ne_eq. auto.
  apply Vfalse_is_false.
Qed.

Lemma make_neg_correct:
  forall a tya c ta va v le e m1 m2,
  sem_neg va tya = Some v ->
  make_neg a tya = Some c ->  
  eval_expr tprog le e m1 a ta m2 va ->
  eval_expr tprog le e m1 c ta m2 v.
Proof.
  intros until m2; intro SEM. unfold make_neg. 
  functional inversion SEM; intros.
  inversion H4. eapply make_binop_correct; eauto with cshm.
  inversion H4. eauto with cshm.
Qed.

Lemma make_notbool_correct:
  forall a tya c ta va v le e m1 m2,
  sem_notbool va tya = Some v ->
  make_notbool a tya = c ->  
  eval_expr tprog le e m1 a ta m2 va ->
  eval_expr tprog le e m1 c ta m2 v.
Proof.
  intros until m2; intro SEM. unfold make_notbool. 
  functional inversion SEM; intros; inversion H4; simpl;
  eauto with cshm.
  eapply make_binop_correct. 
  eapply make_binop_correct. eauto. eauto with cshm. 
  simpl; reflexivity. reflexivity. eauto with cshm. 
  simpl. rewrite Float.cmp_ne_eq. 
  destruct (Float.cmp Ceq f Float.zero); reflexivity.
  traceEq.
Qed.

Lemma make_notint_correct:
  forall a tya c ta va v le e m1 m2,
  sem_notint va = Some v ->
  make_notint a tya = c ->  
  eval_expr tprog le e m1 a ta m2 va ->
  eval_expr tprog le e m1 c ta m2 v.
Proof.
  intros until m2; intro SEM. unfold make_notint. 
  functional inversion SEM; intros. 
  inversion H2; eauto with cshm.
Qed.

Definition binary_constructor_correct
    (make: expr -> type -> expr -> type -> option expr)
    (sem: val -> type -> val -> type -> option val): Prop :=
  forall a tya b tyb c ta va tb vb v le e m1 m2 m3,
  sem va tya vb tyb = Some v ->
  make a tya b tyb = Some c ->  
  eval_expr tprog le e m1 a ta m2 va ->
  eval_expr tprog le e m2 b tb m3 vb ->
  eval_expr tprog le e m1 c (ta ** tb) m3 v.

Definition binary_constructor_correct'
    (make: expr -> type -> expr -> type -> option expr)
    (sem: val -> val -> option val): Prop :=
  forall a tya b tyb c ta va tb vb v le e m1 m2 m3,
  sem va vb = Some v ->
  make a tya b tyb = Some c ->  
  eval_expr tprog le e m1 a ta m2 va ->
  eval_expr tprog le e m2 b tb m3 vb ->
  eval_expr tprog le e m1 c (ta ** tb) m3 v.

Lemma make_add_correct: binary_constructor_correct make_add sem_add.
Proof.
  red; intros until m3. intro SEM. unfold make_add. 
  functional inversion SEM; rewrite H0; intros.
  inversion H7. eauto with cshm. 
  inversion H7. eauto with cshm.
  inversion H7. 
  eapply make_binop_correct. eauto. 
  eapply make_binop_correct. eauto with cshm. eauto.
  simpl. reflexivity. reflexivity. 
  simpl. reflexivity. traceEq.
Qed.

Lemma make_sub_correct: binary_constructor_correct make_sub sem_sub.
Proof.
  red; intros until m3. intro SEM. unfold make_sub. 
  functional inversion SEM; rewrite H0; intros;
  inversion H7; eauto with cshm. 
  eapply make_binop_correct. eauto. 
  eapply make_binop_correct. eauto with cshm. eauto.
  simpl. reflexivity. reflexivity. 
  simpl. reflexivity. traceEq.
  inversion H9. eapply make_binop_correct. 
  eapply make_binop_correct; eauto. 
  simpl. unfold eq_block; rewrite H3. reflexivity.
  eauto with cshm. simpl. rewrite H8. reflexivity. traceEq.
Qed.

Lemma make_mul_correct: binary_constructor_correct make_mul sem_mul.
Proof.
  red; intros until m3. intro SEM. unfold make_mul. 
  functional inversion SEM; rewrite H0; intros;
  inversion H7; eauto with cshm. 
Qed.

Lemma make_div_correct: binary_constructor_correct make_div sem_div.
Proof.
  red; intros until m3. intro SEM. unfold make_div. 
  functional inversion SEM; rewrite H0; intros.
  inversion H8. eapply make_binop_correct; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H8. eapply make_binop_correct; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H7; eauto with cshm. 
Qed.

Lemma make_mod_correct: binary_constructor_correct make_mod sem_mod.
  red; intros until m3. intro SEM. unfold make_mod. 
  functional inversion SEM; rewrite H0; intros.
  inversion H8. eapply make_binop_correct; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H8. eapply make_binop_correct; eauto with cshm. 
  simpl. rewrite H7; auto.
Qed.

Lemma make_and_correct: binary_constructor_correct' make_and sem_and.
Proof.
  red; intros until m3. intro SEM. unfold make_and. 
  functional inversion SEM. intros. inversion H4. 
  eauto with cshm. 
Qed.

Lemma make_or_correct: binary_constructor_correct' make_or sem_or.
Proof.
  red; intros until m3. intro SEM. unfold make_or. 
  functional inversion SEM. intros. inversion H4. 
  eauto with cshm. 
Qed.

Lemma make_xor_correct: binary_constructor_correct' make_xor sem_xor.
Proof.
  red; intros until m3. intro SEM. unfold make_xor. 
  functional inversion SEM. intros. inversion H4. 
  eauto with cshm. 
Qed.

Lemma make_shl_correct: binary_constructor_correct' make_shl sem_shl.
Proof.
  red; intros until m3. intro SEM. unfold make_shl. 
  functional inversion SEM. intros. inversion H5. 
  eapply make_binop_correct; eauto with cshm. 
  simpl. rewrite H4. auto.
Qed.

Lemma make_shr_correct: binary_constructor_correct make_shr sem_shr.
Proof.
  red; intros until m3. intro SEM. unfold make_shr. 
  functional inversion SEM; intros; rewrite H0 in H8; inversion H8.
  eapply make_binop_correct; eauto with cshm.
  simpl; rewrite H7; auto.
  eapply make_binop_correct; eauto with cshm.
  simpl; rewrite H7; auto.
Qed.

Lemma make_cmp_correct:
  forall cmp a tya b tyb c ta va tb vb v le e m1 m2 m3,
  sem_cmp cmp va tya vb tyb m3 = Some v ->
  make_cmp cmp a tya b tyb = Some c ->  
  eval_expr tprog le e m1 a ta m2 va ->
  eval_expr tprog le e m2 b tb m3 vb ->
  eval_expr tprog le e m1 c (ta ** tb) m3 v.
Proof.
  intros until m3. intro SEM. unfold make_cmp.
  functional inversion SEM; rewrite H0; intros. 
  inversion H8. eauto with cshm.
  inversion H8. eauto with cshm.
  inversion H8. eauto with cshm.
  inversion H9. eapply make_binop_correct; eauto with cshm.
  simpl. functional inversion H; subst; unfold eval_compare_null;
  rewrite H8; auto.
  inversion H10. eapply make_binop_correct; eauto with cshm.
  simpl. rewrite H3. unfold eq_block; rewrite H9. auto.
Qed.

Lemma transl_unop_correct:
  forall op a tya c ta va v le e m1 m2, 
  transl_unop op a tya = Some c ->
  sem_unary_operation op va tya = Some v ->
  eval_expr tprog le e m1 a ta m2 va ->
  eval_expr tprog le e m1 c ta m2 v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_notbool_correct; eauto. congruence.
  eapply make_notint_correct with (tya := tya); eauto. congruence.
  eapply make_neg_correct; eauto.
Qed.

Lemma transl_binop_correct:
forall op a tya b tyb c ta va tb vb v le e m1 m2 m3,
  transl_binop op a tya b tyb = Some c ->  
  sem_binary_operation op va tya vb tyb m3 = Some v ->
  eval_expr tprog le e m1 a ta m2 va ->
  eval_expr tprog le e m2 b tb m3 vb ->
  eval_expr tprog le e m1 c (ta ** tb) m3 v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_add_correct; eauto.
  eapply make_sub_correct; eauto.
  eapply make_mul_correct; eauto.
  eapply make_div_correct; eauto.
  eapply make_mod_correct; eauto.
  eapply make_and_correct; eauto.
  eapply make_or_correct; eauto.
  eapply make_xor_correct; eauto.
  eapply make_shl_correct; eauto.
  eapply make_shr_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
Qed. 

Lemma make_cast_correct:
  forall le e m1 a t m2 v ty1 ty2 v',
   eval_expr tprog le e m1 a t m2 v ->
   cast v ty1 ty2 v' ->
   eval_expr tprog le e m1 (make_cast ty1 ty2 a) t m2 v'.
Proof.
  unfold make_cast, make_cast1, make_cast2, make_unop.
  intros until v'; intros EVAL CAST.
  inversion CAST; clear CAST; subst; auto.
  (* cast_int_int *)
    destruct sz2; destruct si2; repeat econstructor; eauto with cshm.
  (* cast_float_int *)
    destruct sz2; destruct si2; repeat econstructor; eauto with cshm; simpl; auto.
  (* cast_int_float *)
    destruct sz2; destruct si1; unfold make_floatofint, make_unop; repeat econstructor; eauto with cshm; simpl; auto.
  (* cast_float_float *)
    destruct sz2; repeat econstructor; eauto with cshm.
Qed.

Lemma make_load_correct:
  forall addr ty code b ofs v le e m1 t m2,
  make_load addr ty = Some code ->
  eval_expr tprog le e m1 addr t m2 (Vptr b ofs) ->
  load_value_of_type ty m2 b ofs = Some v ->
  eval_expr tprog le e m1 code t m2 v.
Proof.
  unfold make_load, load_value_of_type.
  intros until m2; intros MKLOAD EVEXP LDVAL.
  destruct (access_mode ty); inversion MKLOAD.
  (* access_mode ty = By_value m *)
  apply eval_Eload with (Vptr b ofs); auto.
  (* access_mode ty = By_reference *)
  subst code. inversion LDVAL. auto.
Qed.

Lemma make_store_correct:
  forall addr ty rhs code e m1 t1 m2 b ofs t2 m3 v m4,
  make_store addr ty rhs = Some code ->
  eval_expr tprog nil e m1 addr t1 m2 (Vptr b ofs) ->
  eval_expr tprog nil e m2 rhs t2 m3 v ->
  store_value_of_type ty m3 b ofs v = Some m4 ->
  exec_stmt tprog e m1 code (t1 ** t2) m4 Out_normal.
Proof.
  unfold make_store, store_value_of_type.
  intros until m4; intros MKSTORE EV1 EV2 STVAL.
  destruct (access_mode ty); inversion MKSTORE.
  (* access_mode ty = By_value m *)
  eapply eval_Sstore; eauto. 
Qed.

End CONSTRUCTORS.


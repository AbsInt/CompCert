(** * Correctness of the C front end, part 2: Csharpminor construction functions *)

Require Import Coqlib.
Require Import Errors.
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
Require Import Cminor.
Require Import Csharpminor.
Require Import Cshmgen.
Require Import Cshmgenproof1.

Section CONSTRUCTORS.

Variable tprog: Csharpminor.program.

(** * Properties of the translation of [switch] constructs. *)

Lemma transl_lblstmts_exit:
  forall e m1 t m2 sl body n tsl nbrk ncnt,
  exec_stmt tprog e m1 body t m2 (Out_exit (lblstmts_length sl + n)) ->
  transl_lblstmts nbrk ncnt sl body = OK tsl ->
  exec_stmt tprog e m1 tsl t m2 (outcome_block (Out_exit n)).
Proof.
  induction sl; intros.
  simpl in H; simpl in H0; monadInv H0. 
  constructor. apply exec_Sseq_stop. auto. congruence.
  simpl in H; simpl in H0; monadInv H0.
  eapply IHsl with (body := Sblock (Sseq body x)); eauto.
  change (Out_exit (lblstmts_length sl + n))
    with (outcome_block (Out_exit (S (lblstmts_length sl + n)))).
  constructor. apply exec_Sseq_stop. auto. congruence.
Qed.

Lemma transl_lblstmts_return:
  forall e m1 t m2 sl body optv tsl nbrk ncnt,
  exec_stmt tprog e m1 body t m2 (Out_return optv) ->
  transl_lblstmts nbrk ncnt sl body = OK tsl ->
  exec_stmt tprog e m1 tsl t m2 (Out_return optv).
Proof.
  induction sl; intros.
  simpl in H; simpl in H0; monadInv H0. 
  change (Out_return optv) with (outcome_block (Out_return optv)).
  constructor. apply exec_Sseq_stop. auto. congruence.
  simpl in H; simpl in H0; monadInv H0.
  eapply IHsl with (body := Sblock (Sseq body x)); eauto.
  change (Out_return optv) with (outcome_block (Out_return optv)).
  constructor. apply exec_Sseq_stop. auto. congruence.
Qed.


(** * Correctness of Csharpminor construction functions *)

Lemma make_intconst_correct:
  forall n e m,
  eval_expr tprog e m (make_intconst n) (Vint n).
Proof.
  intros. unfold make_intconst. econstructor. reflexivity. 
Qed.

Lemma make_floatconst_correct:
  forall n e m,
  eval_expr tprog e m (make_floatconst n) (Vfloat n).
Proof.
  intros. unfold make_floatconst. econstructor. reflexivity. 
Qed.

Hint Resolve make_intconst_correct make_floatconst_correct
             eval_Eunop eval_Ebinop: cshm.
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
 forall e m a v ty,
  eval_expr tprog e m a v ->
  is_true v ty ->
  exists vb,
    eval_expr tprog e m (make_boolean a ty) vb
    /\ Val.is_true vb.
Proof.
  intros until ty; intros EXEC VTRUE.
  destruct ty; simpl;
  try (exists v; intuition; inversion VTRUE; simpl; auto; fail).
  exists Vtrue; split.
  eapply eval_Ebinop; eauto with cshm. 
  inversion VTRUE; simpl. 
  replace (Float.cmp Cne f0 Float.zero) with (negb (Float.cmp Ceq f0 Float.zero)).
  rewrite Float.eq_zero_false. reflexivity. auto.
  rewrite Float.cmp_ne_eq. auto.
  apply Vtrue_is_true.
Qed.

Lemma make_boolean_correct_false:
 forall e m a v ty,
  eval_expr tprog e m a v ->
  is_false v ty ->
  exists vb,
    eval_expr tprog e m (make_boolean a ty) vb
    /\ Val.is_false vb.
Proof.
  intros until ty; intros EXEC VFALSE.
  destruct ty; simpl;
  try (exists v; intuition; inversion VFALSE; simpl; auto; fail).
  exists Vfalse; split.
  eapply eval_Ebinop; eauto with cshm. 
  inversion VFALSE; simpl. 
  replace (Float.cmp Cne Float.zero Float.zero) with (negb (Float.cmp Ceq Float.zero Float.zero)).
  rewrite Float.eq_zero_true. reflexivity. 
  rewrite Float.cmp_ne_eq. auto.
  apply Vfalse_is_false.
Qed.

Lemma make_neg_correct:
  forall a tya c va v e m,
  sem_neg va tya = Some v ->
  make_neg a tya = OK c ->  
  eval_expr tprog e m a va ->
  eval_expr tprog e m c v.
Proof.
  intros until m; intro SEM. unfold make_neg. 
  functional inversion SEM; intros.
  inversion H4. eapply eval_Eunop; eauto with cshm.
  inversion H4. eauto with cshm.
Qed.

Lemma make_notbool_correct:
  forall a tya c va v e m,
  sem_notbool va tya = Some v ->
  make_notbool a tya = c ->  
  eval_expr tprog e m a va ->
  eval_expr tprog e m c v.
Proof.
  intros until m; intro SEM. unfold make_notbool. 
  functional inversion SEM; intros; inversion H4; simpl;
  eauto with cshm.
Qed.

Lemma make_notint_correct:
  forall a tya c va v e m,
  sem_notint va = Some v ->
  make_notint a tya = c ->  
  eval_expr tprog e m a va ->
  eval_expr tprog e m c v.
Proof.
  intros until m; intro SEM. unfold make_notint. 
  functional inversion SEM; intros. 
  inversion H2; eauto with cshm.
Qed.

Definition binary_constructor_correct
    (make: expr -> type -> expr -> type -> res expr)
    (sem: val -> type -> val -> type -> option val): Prop :=
  forall a tya b tyb c va vb v e m,
  sem va tya vb tyb = Some v ->
  make a tya b tyb = OK c ->  
  eval_expr tprog e m a va ->
  eval_expr tprog e m b vb ->
  eval_expr tprog e m c v.

Definition binary_constructor_correct'
    (make: expr -> type -> expr -> type -> res expr)
    (sem: val -> val -> option val): Prop :=
  forall a tya b tyb c va vb v e m,
  sem va vb = Some v ->
  make a tya b tyb = OK c ->  
  eval_expr tprog e m a va ->
  eval_expr tprog e m b vb ->
  eval_expr tprog e m c v.

Lemma make_add_correct: binary_constructor_correct make_add sem_add.
Proof.
  red; intros until m. intro SEM. unfold make_add. 
  functional inversion SEM; rewrite H0; intros.
  inversion H7. eauto with cshm. 
  inversion H7. eauto with cshm.
  inversion H7. 
  eapply eval_Ebinop. eauto. 
  eapply eval_Ebinop. eauto with cshm. eauto.
  simpl. reflexivity. reflexivity. 
Qed.

Lemma make_sub_correct: binary_constructor_correct make_sub sem_sub.
Proof.
  red; intros until m. intro SEM. unfold make_sub. 
  functional inversion SEM; rewrite H0; intros;
  inversion H7; eauto with cshm. 
  eapply eval_Ebinop. eauto. 
  eapply eval_Ebinop. eauto with cshm. eauto.
  simpl. reflexivity. reflexivity. 
  inversion H9. eapply eval_Ebinop. 
  eapply eval_Ebinop; eauto. 
  simpl. unfold eq_block; rewrite H3. reflexivity.
  eauto with cshm. simpl. rewrite H8. reflexivity.
Qed.

Lemma make_mul_correct: binary_constructor_correct make_mul sem_mul.
Proof.
  red; intros until m. intro SEM. unfold make_mul. 
  functional inversion SEM; rewrite H0; intros;
  inversion H7; eauto with cshm. 
Qed.

Lemma make_div_correct: binary_constructor_correct make_div sem_div.
Proof.
  red; intros until m. intro SEM. unfold make_div. 
  functional inversion SEM; rewrite H0; intros.
  inversion H8. eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H8. eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H7; eauto with cshm. 
Qed.

Lemma make_mod_correct: binary_constructor_correct make_mod sem_mod.
  red; intros until m. intro SEM. unfold make_mod. 
  functional inversion SEM; rewrite H0; intros.
  inversion H8. eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7; auto.
  inversion H8. eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H7; auto.
Qed.

Lemma make_and_correct: binary_constructor_correct' make_and sem_and.
Proof.
  red; intros until m. intro SEM. unfold make_and. 
  functional inversion SEM. intros. inversion H4. 
  eauto with cshm. 
Qed.

Lemma make_or_correct: binary_constructor_correct' make_or sem_or.
Proof.
  red; intros until m. intro SEM. unfold make_or. 
  functional inversion SEM. intros. inversion H4. 
  eauto with cshm. 
Qed.

Lemma make_xor_correct: binary_constructor_correct' make_xor sem_xor.
Proof.
  red; intros until m. intro SEM. unfold make_xor. 
  functional inversion SEM. intros. inversion H4. 
  eauto with cshm. 
Qed.

Lemma make_shl_correct: binary_constructor_correct' make_shl sem_shl.
Proof.
  red; intros until m. intro SEM. unfold make_shl. 
  functional inversion SEM. intros. inversion H5. 
  eapply eval_Ebinop; eauto with cshm. 
  simpl. rewrite H4. auto.
Qed.

Lemma make_shr_correct: binary_constructor_correct make_shr sem_shr.
Proof.
  red; intros until m. intro SEM. unfold make_shr. 
  functional inversion SEM; intros; rewrite H0 in H8; inversion H8.
  eapply eval_Ebinop; eauto with cshm.
  simpl; rewrite H7; auto.
  eapply eval_Ebinop; eauto with cshm.
  simpl; rewrite H7; auto.
Qed.

Lemma make_cmp_correct:
  forall cmp a tya b tyb c va vb v e m,
  sem_cmp cmp va tya vb tyb m = Some v ->
  make_cmp cmp a tya b tyb = OK c ->  
  eval_expr tprog e m a va ->
  eval_expr tprog e m b vb ->
  eval_expr tprog e m c v.
Proof.
  intros until m. intro SEM. unfold make_cmp.
  functional inversion SEM; rewrite H0; intros.
  (* I32unsi *) 
  inversion H8. eauto with cshm.
  (* ipip int int *)
  inversion H8. eauto with cshm.
  (* ipip ptr ptr *)
  inversion H10. eapply eval_Ebinop; eauto with cshm.
  simpl. rewrite H3. unfold eq_block. rewrite H9. auto.
  (* ipip ptr int *)
  inversion H9. eapply eval_Ebinop; eauto with cshm.
  simpl. unfold eval_compare_null. rewrite H8. 
  functional inversion H; subst; auto.
  (* ipip int ptr *)
  inversion H9. eapply eval_Ebinop; eauto with cshm.
  simpl. unfold eval_compare_null. rewrite H8. 
  functional inversion H; subst; auto.
  (* ff *)
  inversion H8. eauto with cshm.
Qed.

Lemma transl_unop_correct:
  forall op a tya c va v e m, 
  transl_unop op a tya = OK c ->
  sem_unary_operation op va tya = Some v ->
  eval_expr tprog e m a va ->
  eval_expr tprog e m c v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_notbool_correct; eauto. congruence.
  eapply make_notint_correct with (tya := tya); eauto. congruence.
  eapply make_neg_correct; eauto.
Qed.

Lemma transl_binop_correct:
  forall op a tya b tyb c va vb v e m,
  transl_binop op a tya b tyb = OK c ->  
  sem_binary_operation op va tya vb tyb m = Some v ->
  eval_expr tprog e m a va ->
  eval_expr tprog e m b vb ->
  eval_expr tprog e m c v.
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
  forall e m a v ty1 ty2 v',
   eval_expr tprog e m a v ->
   cast v ty1 ty2 v' ->
   eval_expr tprog e m (make_cast ty1 ty2 a) v'.
Proof.
  unfold make_cast, make_cast1, make_cast2.
  intros until v'; intros EVAL CAST.
  inversion CAST; clear CAST; subst.
  (* cast_int_int *)
    destruct sz2; destruct si2; repeat econstructor; eauto with cshm.
  (* cast_float_int *)
    destruct sz2; destruct si2; repeat econstructor; eauto with cshm; simpl; auto.
  (* cast_int_float *)
    destruct sz2; destruct si1; unfold make_floatofint; repeat econstructor; eauto with cshm; simpl; auto.
  (* cast_float_float *)
    destruct sz2; repeat econstructor; eauto with cshm.
  (* neutral, ptr *)
   inversion H0; auto; inversion H; auto.
  (* neutral, int *)
   inversion H0; auto; inversion H; auto.
Qed.

Lemma make_load_correct:
  forall addr ty code b ofs v e m,
  make_load addr ty = OK code ->
  eval_expr tprog e m addr (Vptr b ofs) ->
  load_value_of_type ty m b ofs = Some v ->
  eval_expr tprog e m code v.
Proof.
  unfold make_load, load_value_of_type.
  intros until m; intros MKLOAD EVEXP LDVAL.
  destruct (access_mode ty); inversion MKLOAD.
  (* access_mode ty = By_value m *)
  apply eval_Eload with (Vptr b ofs); auto.
  (* access_mode ty = By_reference *)
  subst code. inversion LDVAL. auto.
Qed.

Lemma make_store_correct:
  forall addr ty rhs code e m b ofs v m',
  make_store addr ty rhs = OK code ->
  eval_expr tprog e m addr (Vptr b ofs) ->
  eval_expr tprog e m rhs v ->
  store_value_of_type ty m b ofs v = Some m' ->
  exec_stmt tprog e m code E0 m' Out_normal.
Proof.
  unfold make_store, store_value_of_type.
  intros until m'; intros MKSTORE EV1 EV2 STVAL.
  destruct (access_mode ty); inversion MKSTORE.
  (* access_mode ty = By_value m *)
  eapply exec_Sstore; eauto. 
Qed.

End CONSTRUCTORS.


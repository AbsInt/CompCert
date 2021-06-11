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

Require Import Zwf Coqlib Maps.
Require Import Errors Integers Floats Values AST Memory Globalenvs Events Smallstep.
Require Import Ctypes Cop Csyntax Csem.
Require Import Initializers.

Open Scope error_monad_scope.

Section SOUNDNESS.

Variable ge: genv.

(** * Simple expressions and their big-step semantics *)

(** An expression is simple if it contains no assignments and no
  function calls. *)

Fixpoint simple (a: expr) : Prop :=
  match a with
  | Eloc _ _ _ _ => True
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
  | Eparen r1 _ _ => simple r1
  end.

(** A big-step semantics for simple expressions.  Similar to the
  big-step semantics from [Cstrategy], with the addition of
  conditionals, comma and paren operators.  It is a pity we do not
  share definitions with [Cstrategy], but such sharing raises
  technical difficulties. *)

Section SIMPLE_EXPRS.

Variable e: env.
Variable m: mem.

Inductive eval_simple_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=
  | esl_loc: forall b ofs bf ty,
      eval_simple_lvalue (Eloc b ofs bf ty) b ofs bf
  | esl_var_local: forall x ty b,
      e!x = Some(b, ty) ->
      eval_simple_lvalue (Evar x ty) b Ptrofs.zero Full
  | esl_var_global: forall x ty b,
      e!x = None ->
      Genv.find_symbol ge x = Some b ->
      eval_simple_lvalue (Evar x ty) b Ptrofs.zero Full
  | esl_deref: forall r ty b ofs,
      eval_simple_rvalue r (Vptr b ofs) ->
      eval_simple_lvalue (Ederef r ty) b ofs Full
  | esl_field_struct: forall r f ty b ofs id co a delta bf,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tstruct id a -> ge.(genv_cenv)!id = Some co -> field_offset ge f (co_members co) = OK (delta, bf) ->
      eval_simple_lvalue (Efield r f ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) bf
  | esl_field_union: forall r f ty b ofs id co a delta bf,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tunion id a -> ge.(genv_cenv)!id = Some co -> union_field_offset ge f (co_members co) = OK (delta, bf) ->
      eval_simple_lvalue (Efield r f ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) bf

with eval_simple_rvalue: expr -> val -> Prop :=
  | esr_val: forall v ty,
      eval_simple_rvalue (Eval v ty) v
  | esr_rvalof: forall b ofs bf l ty v,
      eval_simple_lvalue l b ofs bf ->
      ty = typeof l ->
      deref_loc ge ty m b ofs bf E0 v ->
      eval_simple_rvalue (Evalof l ty) v
  | esr_addrof: forall b ofs l ty,
      eval_simple_lvalue l b ofs Full ->
      eval_simple_rvalue (Eaddrof l ty) (Vptr b ofs)
  | esr_unop: forall op r1 ty v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_unary_operation op v1 (typeof r1) m = Some v ->
      eval_simple_rvalue (Eunop op r1 ty) v
  | esr_binop: forall op r1 r2 ty v1 v2 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v2 ->
      sem_binary_operation ge op v1 (typeof r1) v2 (typeof r2) m = Some v ->
      eval_simple_rvalue (Ebinop op r1 r2 ty) v
  | esr_cast: forall ty r1 v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_cast v1 (typeof r1) ty m = Some v ->
      eval_simple_rvalue (Ecast r1 ty) v
  | esr_sizeof: forall ty1 ty,
      eval_simple_rvalue (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | esr_alignof: forall ty1 ty,
      eval_simple_rvalue (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | esr_seqand_true: forall r1 r2 ty v1 v2 v3,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some true ->
      eval_simple_rvalue r2 v2 ->
      sem_cast v2 (typeof r2) type_bool m = Some v3 ->
      eval_simple_rvalue (Eseqand r1 r2 ty) v3
  | esr_seqand_false: forall r1 r2 ty v1,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some false ->
      eval_simple_rvalue (Eseqand r1 r2 ty) (Vint Int.zero)
  | esr_seqor_false: forall r1 r2 ty v1 v2 v3,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some false ->
      eval_simple_rvalue r2 v2 ->
      sem_cast v2 (typeof r2) type_bool m = Some v3 ->
      eval_simple_rvalue (Eseqor r1 r2 ty) v3
  | esr_seqor_true: forall r1 r2 ty v1,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some true ->
      eval_simple_rvalue (Eseqor r1 r2 ty) (Vint Int.one)
  | esr_condition: forall r1 r2 r3 ty v v1 b v',
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some b ->
      eval_simple_rvalue (if b then r2 else r3) v' ->
      sem_cast v' (typeof (if b then r2 else r3)) ty m = Some v ->
      eval_simple_rvalue (Econdition r1 r2 r3 ty) v
  | esr_comma: forall r1 r2 ty v1 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v ->
      eval_simple_rvalue (Ecomma r1 r2 ty) v
  | esr_paren: forall r tycast ty v v',
      eval_simple_rvalue r v -> sem_cast v (typeof r) tycast m = Some v' ->
      eval_simple_rvalue (Eparen r tycast ty) v'.

End SIMPLE_EXPRS.

(** * Correctness of the big-step semantics with respect to reduction sequences *)

(** In this section, we show that if a simple expression [a] reduces to
  some value (with the transition semantics from module [Csem]),
  then it evaluates to this value (with the big-step semantics above). *)

Definition compat_eval (k: kind) (e: env) (a a': expr) (m: mem) : Prop :=
  typeof a = typeof a' /\
  match k with
  | LV => forall b ofs bf, eval_simple_lvalue e m a' b ofs bf -> eval_simple_lvalue e m a b ofs bf
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
  induction 1; simpl; split; auto; split; auto; intros bx ofsx bf' EV; inv EV.
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
  inv EV. eapply esr_seqand_true; eauto. constructor.
  inv EV. eapply esr_seqand_false; eauto. constructor.
  inv EV. eapply esr_seqor_true; eauto. constructor.
  inv EV. eapply esr_seqor_false; eauto. constructor.
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
  forall v1 ty1 ty2 m v2 v1' v2',
  sem_cast v1 ty1 ty2 m = Some v2 ->
  do_cast v1' ty1 ty2 = OK v2' ->
  Val.inject inj v1' v1 ->
  Val.inject inj v2' v2.
Proof.
  intros. unfold do_cast in H0. destruct (sem_cast v1' ty1 ty2 Mem.empty) as [v2''|] eqn:E; inv H0.
  exploit (sem_cast_inj inj Mem.empty m).
  intros. rewrite mem_empty_not_weak_valid_pointer in H2. discriminate.
  eexact E. eauto.
  intros [v' [A B]]. congruence.
Qed.

Lemma bool_val_match:
  forall v ty b v' m,
  bool_val v ty Mem.empty = Some b ->
  Val.inject inj v v' ->
  bool_val v' ty m = Some b.
Proof.
  intros. eapply bool_val_inj; eauto. intros. rewrite mem_empty_not_weak_valid_pointer in H2; discriminate.
Qed.

(** Soundness of [constval] with respect to the big-step semantics *)

Lemma constval_rvalue:
  forall m a v,
  eval_simple_rvalue empty_env m a v ->
  forall v',
  constval ge a = OK v' ->
  Val.inject inj v' v
with constval_lvalue:
  forall m a b ofs bf,
  eval_simple_lvalue empty_env m a b ofs bf ->
  forall v',
  constval ge a = OK v' ->
  bf = Full /\ Val.inject inj v' (Vptr b ofs).
Proof.
  (* rvalue *)
  induction 1; intros vres CV; simpl in CV; try (monadInv CV).
  (* val *)
  destruct v; monadInv CV; constructor.
  (* rval *)
  assert (constval ge l = OK vres) by (destruct (access_mode ty); congruence).
  exploit constval_lvalue; eauto. intros [A B]. subst bf.
  inv H1; rewrite H3 in CV; congruence.
  (* addrof *)
  eapply constval_lvalue; eauto.
  (* unop *)
  destruct (sem_unary_operation op x (typeof r1) Mem.empty) as [v1'|] eqn:E; inv EQ0.
  exploit (sem_unary_operation_inj inj Mem.empty m).
  intros. rewrite mem_empty_not_weak_valid_pointer in H2; discriminate.
  eexact E. eauto.
  intros [v' [A B]]. congruence.
  (* binop *)
  destruct (sem_binary_operation ge op x (typeof r1) x0 (typeof r2) Mem.empty) as [v1'|] eqn:E; inv EQ2.
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
  auto.
  (* alignof *)
  auto.
  (* seqand *)
  destruct (bool_val x (typeof r1) Mem.empty) as [b|] eqn:E; inv EQ2.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b = true) by congruence. subst b.
  eapply sem_cast_match; eauto.
  destruct (bool_val x (typeof r1) Mem.empty) as [b|] eqn:E; inv EQ2.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b = false) by congruence. subst b. inv H2. auto.
  (* seqor *)
  destruct (bool_val x (typeof r1) Mem.empty) as [b|] eqn:E; inv EQ2.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b = false) by congruence. subst b.
  eapply sem_cast_match; eauto.
  destruct (bool_val x (typeof r1) Mem.empty) as [b|] eqn:E; inv EQ2.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b = true) by congruence. subst b. inv H2. auto.
  (* conditional *)
  destruct (bool_val x (typeof r1) Mem.empty) as [b'|] eqn:E; inv EQ3.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b' = b) by congruence. subst b'.
  destruct b; eapply sem_cast_match; eauto.
  (* comma *)
  auto.
  (* paren *)
  eapply sem_cast_match; eauto.

  (* lvalue *)
  induction 1; intros v' CV; simpl in CV; try (monadInv CV).
  (* var local *)
  split; auto. unfold empty_env in H. rewrite PTree.gempty in H. congruence.
  (* var_global *)
  split; auto. econstructor. unfold inj. rewrite H0. eauto. auto.
  (* deref *)
  split; eauto.
  (* field struct *)
  rewrite H0 in EQ. monadInv EQ. destruct x0; monadInv EQ2.
  unfold lookup_composite in EQ0; rewrite H1 in EQ0; monadInv EQ0.
  exploit constval_rvalue; eauto. intro MV.
  split. congruence.
  replace x with delta by congruence. 
  apply (Val.offset_ptr_inject inj _ _ _ MV).
  (* field union *)
  rewrite H0 in EQ. monadInv EQ. destruct x0; monadInv EQ2.
  unfold lookup_composite in EQ0; rewrite H1 in EQ0; monadInv EQ0.
  exploit constval_rvalue; eauto. intro MV.
  split. congruence.
  replace x with delta by congruence. 
  apply (Val.offset_ptr_inject inj _ _ _ MV).
Qed.

Lemma constval_simple:
  forall a v, constval ge a = OK v -> simple a.
Proof.
  induction a; simpl; intros vx CV; try (monadInv CV); eauto.
  destruct (access_mode ty); discriminate || eauto.
  intuition eauto.
Qed.

(** Soundness of [constval] with respect to the reduction semantics. *)

Theorem constval_steps:
  forall f r m v v' ty m',
  star step ge (ExprState f r Kstop empty_env m) E0 (ExprState f (Eval v' ty) Kstop empty_env m') ->
  constval ge r = OK v ->
  m' = m /\ ty = typeof r /\ Val.inject inj v v'.
Proof.
  intros. exploit eval_simple_steps; eauto. eapply constval_simple; eauto.
  intros [A [B C]]. intuition. eapply constval_rvalue; eauto.
Qed.

(** * Correctness of operations over the initialization state *)

(** ** Properties of the in-memory bytes denoted by initialization data *)

Local Notation boid := (Genv.bytes_of_init_data (genv_genv ge)).
Local Notation boidl := (Genv.bytes_of_init_data_list (genv_genv ge)).

Lemma boidl_app: forall il2 il1,
  boidl (il1 ++ il2) = boidl il1 ++ boidl il2.
Proof.
  induction il1 as [ | il il1]; simpl. auto. rewrite app_ass. f_equal; auto.
Qed.

Corollary boidl_rev_cons: forall i il,
  boidl (rev il ++ i :: nil) = boidl (rev il) ++ boid i.
Proof.
  intros. rewrite boidl_app. simpl. rewrite <- app_nil_end. auto.
Qed. 

Definition byte_of_int (n: int) := Byte.repr (Int.unsigned n).

Lemma byte_of_int_of_byte: forall b, byte_of_int (int_of_byte b) = b.
Proof.
  intros. unfold int_of_byte, byte_of_int.
  rewrite Int.unsigned_repr, Byte.repr_unsigned. auto.
  assert(Byte.max_unsigned < Int.max_unsigned) by reflexivity.
  generalize (Byte.unsigned_range_2 b). lia.
Qed.

Lemma inj_bytes_1: forall n,
  inj_bytes (encode_int 1 n) = Byte (Byte.repr n) :: nil.
Proof.
  intros. unfold encode_int, bytes_of_int, rev_if_be. destruct Archi.big_endian; auto.
Qed.

Lemma inj_bytes_byte: forall b,
  inj_bytes (encode_int 1 (Int.unsigned (int_of_byte b))) = Byte b :: nil.
Proof.
  intros. rewrite inj_bytes_1. do 2 f_equal. apply byte_of_int_of_byte.
Qed.

Lemma boidl_init_ints8: forall l,
  boidl (map Init_int8 l) = inj_bytes (map byte_of_int l).
Proof.
  induction l as [ | i l]; simpl. auto. rewrite inj_bytes_1; simpl. f_equal; auto.
Qed.

Lemma boidl_init_bytes: forall l,
  boidl (map Init_byte l) = inj_bytes l.
Proof.
  induction l as [ | b l]; simpl. auto. rewrite inj_bytes_byte, IHl. auto.
Qed.

Lemma boidl_ints8: forall i n,
  boidl (repeat (Init_int8 i) n) = repeat (Byte (byte_of_int i)) n.
Proof.
  induction n; simpl. auto. rewrite inj_bytes_1. simpl; f_equal; auto.
Qed.

(** ** Properties of operations over list of initialization data *)

Lemma add_rev_bytes_spec: forall l il,
  add_rev_bytes l il = List.map Init_byte (List.rev l) ++ il.
Proof.
  induction l as [ | b l]; intros; simpl.
- auto.
- rewrite IHl. rewrite map_app. simpl. rewrite app_ass. auto.
Qed.

Lemma add_rev_bytes_spec': forall l il,
  List.rev (add_rev_bytes l il) = List.rev il ++ List.map Init_byte l.
Proof.
  intros. rewrite add_rev_bytes_spec. rewrite rev_app_distr, map_rev, rev_involutive. auto.
Qed.

Lemma add_zeros_spec: forall n il,
  0 <= n ->
  add_zeros n il = List.repeat (Init_int8 Int.zero) (Z.to_nat n) ++ il.
Proof.
  intros.
  unfold add_zeros; rewrite iter_nat_of_Z by auto; rewrite Zabs2Nat.abs_nat_nonneg by auto.
  induction (Z.to_nat n); simpl. auto. f_equal; auto.
Qed.

Lemma decompose_spec: forall il depth bl il',
  decompose il depth = OK (bl, il') ->
  exists nl, il = List.map Init_int8 nl ++ il'
          /\ bl = List.map byte_of_int (rev nl)
          /\ List.length nl = Z.to_nat depth.
Proof.
  assert (REC: forall il accu depth bl il',
               decompose_rec accu il depth = OK (bl, il') ->
               exists nl, il = List.map Init_int8 nl ++ il'
                       /\ bl = List.map byte_of_int (rev nl) ++ accu
                       /\ List.length nl = Z.to_nat depth).
  { induction il as [ | i il ]; intros until il'; intros D; simpl in D.
  - destruct (zle depth 0); inv D.
    exists (@nil int); simpl. rewrite Z_to_nat_neg by auto. auto.
  - destruct (zle depth 0). 
    + inv D. exists (@nil int); simpl. rewrite Z_to_nat_neg by auto. auto.
    + destruct i; try discriminate.
      apply IHil in D; destruct D as (nl & P & Q & R).
      exists (i :: nl); simpl; split. congruence. split.
      rewrite map_app. simpl. rewrite app_ass. exact Q.
      rewrite R, <- Z2Nat.inj_succ by lia. f_equal; lia.
  }
  intros. apply REC in H. destruct H as (nl & P & Q & R). rewrite app_nil_r in Q.
  exists nl; auto.
Qed.

Lemma list_repeat_app: forall (A: Type) (a: A) n2 n1,
  List.repeat a n1 ++ List.repeat a n2 = List.repeat a (n1 + n2)%nat.
Proof.
  induction n1; simpl; congruence.
Qed.

Lemma list_rev_repeat: forall (A: Type) (a: A) n,
  rev (List.repeat a n) = List.repeat a n.
Proof.
  induction n; simpl. auto. rewrite IHn. change (a :: nil) with (repeat a 1%nat).
  rewrite list_repeat_app. rewrite Nat.add_comm. auto. 
Qed.

Lemma normalize_boidl: forall il depth il',
  normalize il depth = OK il' ->
  boidl (rev il') = boidl (rev il).
Proof.
  induction il as [ | i il]; simpl; intros depth il' AT.
- destruct (zle depth 0); inv AT. auto.
- destruct (zle depth 0). inv AT. auto.
  destruct i;
  try (monadInv AT; simpl;
       rewrite ? add_rev_bytes_spec', ? boidl_rev_cons, ? boidl_app, ? boidl_init_bytes;
       erewrite IHil by eauto; reflexivity).
  set (n := Z.max 0 z) in *. destruct (zle n depth); monadInv AT.
  + rewrite add_zeros_spec, rev_app_distr, ! boidl_app by lia.
    erewrite IHil by eauto. f_equal.
    rewrite list_rev_repeat. simpl. rewrite app_nil_r, boidl_ints8.
    f_equal. unfold n. apply Z.max_case_strong; intros; auto. rewrite ! Z_to_nat_neg by lia. auto.
  + rewrite add_zeros_spec, rev_app_distr, !boidl_app by lia.
    simpl. rewrite boidl_rev_cons, list_rev_repeat. simpl.
    rewrite app_ass, app_nil_r, !boidl_ints8. f_equal.
    rewrite list_repeat_app. f_equal. rewrite <- Z2Nat.inj_add by lia.
    unfold n. apply Z.max_case_strong; intros; f_equal; lia.
Qed.

Lemma trisection_boidl: forall il depth sz bytes1 bytes2 il',
  trisection il depth sz = OK (bytes1, bytes2, il') ->
  boidl (rev il) = boidl (rev il') ++ inj_bytes bytes2 ++ inj_bytes bytes1
  /\ length bytes1 = Z.to_nat depth
  /\ length bytes2 = Z.to_nat sz.
Proof.
  unfold trisection; intros. monadInv H.
  apply normalize_boidl in EQ. rewrite <- EQ.
  apply decompose_spec in EQ1. destruct EQ1 as (nl1 & A1 & B1 & C1).
  apply decompose_spec in EQ0. destruct EQ0 as (nl2 & A2 & B2 & C2).
  split.
- rewrite A1, A2, !rev_app_distr, !boidl_app, app_ass.
  rewrite <- !map_rev, !boidl_init_ints8. rewrite <- B1, <- B2. auto.
- rewrite B1, B2, !map_length, !rev_length. auto.
Qed. 

Lemma store_init_data_loadbytes:
  forall m b p i m',
  Genv.store_init_data ge m b p i = Some m' ->
  match i with Init_space _ => False | _ => True end ->
  Mem.loadbytes m' b p (init_data_size i) = Some (boid i).
Proof.
  intros; destruct i; simpl in H; try apply (Mem.loadbytes_store_same _ _ _ _ _ _ H).
- contradiction.
- rewrite Genv.init_data_size_addrof. simpl.
  destruct (Genv.find_symbol ge i) as [b'|]; try discriminate.
  rewrite (Mem.loadbytes_store_same _ _ _ _ _ _ H).
  unfold encode_val, Mptr; destruct Archi.ptr64; reflexivity.
Qed.

(** ** Memory areas that are initialized to zeros *)

Definition reads_as_zeros (m: mem) (b: block) (from to: Z) : Prop :=
  forall i, from <= i < to -> Mem.loadbytes m b i 1 = Some (Byte Byte.zero :: nil).

Lemma reads_as_zeros_mono: forall m b from1 from2 to1 to2,
  reads_as_zeros m b from1 to1 -> from1 <= from2 -> to2 <= to1 ->
  reads_as_zeros m b from2 to2.
Proof.
  intros; red; intros. apply H; lia.
Qed.

Remark reads_as_zeros_unchanged:
  forall (P: block -> Z -> Prop) m b from to m',
  reads_as_zeros m b from to ->
  Mem.unchanged_on P m m' ->
  (forall i, from <= i < to -> P b i) ->
  reads_as_zeros m' b from to.
Proof.
  intros; red; intros. eapply Mem.loadbytes_unchanged_on; eauto.
  intros; apply H1. lia.
Qed.

Lemma reads_as_zeros_loadbytes: forall m b from to,
  reads_as_zeros m b from to ->
  forall len pos, from <= pos -> pos + len <= to -> 0 <= len ->
  Mem.loadbytes m b pos len = Some (repeat (Byte Byte.zero) (Z.to_nat len)).
Proof.
  intros until to; intros RZ.
  induction len using (well_founded_induction (Zwf_well_founded 0)).
  intros. destruct (zeq len 0).
- subst len. rewrite Mem.loadbytes_empty by lia. auto.
- replace (Z.to_nat len) with (S (Z.to_nat (len - 1))).
  change (repeat (Byte Byte.zero) (S (Z.to_nat (len - 1))))
    with ((Byte Byte.zero :: nil) ++ repeat (Byte Byte.zero) (Z.to_nat (len - 1))).
  replace len with (1 + (len - 1)) at 1 by lia. 
  apply Mem.loadbytes_concat; try lia.
  + apply RZ. lia.
  + apply H; unfold Zwf; lia.
  + rewrite <- Z2Nat.inj_succ by lia. f_equal; lia. 
Qed.

Lemma reads_as_zeros_equiv: forall m b from to,
  reads_as_zeros m b from to <-> Genv.readbytes_as_zero m b from (to - from).
Proof.
  intros; split; intros.
- red; intros. set (len := Z.of_nat n).
  replace n with (Z.to_nat len) by apply Nat2Z.id.
  eapply reads_as_zeros_loadbytes; eauto. lia. lia.
- red; intros. red in H. apply (H i 1%nat). lia. lia.
Qed.

(** ** Semantic correctness of state operations *)

(** Semantic interpretation of states. *)

Record match_state (s: state) (m: mem) (b: block) : Prop := {
  match_range:
    0 <= s.(curr) <= s.(total_size);
  match_contents:
    Mem.loadbytes m b 0 s.(curr) = Some (boidl (rev s.(init)));
  match_uninitialized:
    reads_as_zeros m b s.(curr) s.(total_size)
}.

Lemma curr_pad_to: forall s pos,
  curr s <= curr (pad_to s pos) /\ pos <= curr (pad_to s pos).
Proof.
  unfold pad_to; intros. destruct (zle pos (curr s)); simpl; lia.
Qed.

Lemma total_size_pad_to: forall s pos,
  total_size (pad_to s pos) = total_size s.
Proof.
  unfold pad_to; intros. destruct (zle pos (curr s)); auto.
Qed.

Lemma pad_to_correct: forall pos s m b,
  match_state s m b -> pos <= s.(total_size) ->
  match_state (pad_to s pos) m b.
Proof.
  intros. unfold pad_to. destruct (zle pos (curr s)); auto.
  destruct H. constructor; simpl; intros.
- lia.
- rewrite boidl_rev_cons. simpl.
  replace pos with (s.(curr) + (pos - s.(curr))) at 1 by lia.
  apply Mem.loadbytes_concat; try lia.
    * auto.
    * eapply reads_as_zeros_loadbytes; eauto. lia. lia. lia.
- eapply reads_as_zeros_mono; eauto; lia.
Qed.

Lemma trisection_correct: forall s m b pos sz bytes1 bytes2 il,
  match_state s m b ->
  trisection s.(init) (s.(curr) - (pos + sz)) sz = OK (bytes1, bytes2, il) ->
  0 <= pos -> pos + sz <= s.(curr) -> 0 <= sz ->
  Mem.loadbytes m b 0 pos = Some (boidl (rev il))
  /\ Mem.loadbytes m b pos sz = Some (inj_bytes bytes2)
  /\ Mem.loadbytes m b (pos + sz) (s.(curr) - (pos + sz)) = Some (inj_bytes bytes1).
Proof.
  intros. apply trisection_boidl in H0. destruct H0 as (A & B & C).
  set (depth := curr s - (pos + sz)) in *.
  pose proof (match_contents _ _ _ H) as D.
  replace (curr s) with ((pos + sz) + depth) in D by lia.
  exploit Mem.loadbytes_split. eexact D. lia. lia.
  rewrite Z.add_0_l. intros (bytes0 & bytes1' & LB0 & LB1 & E1).
  exploit Mem.loadbytes_split. eexact LB0. lia. lia.
  rewrite Z.add_0_l. intros (bytes3 & bytes2' & LB3 & LB2 & E2).
  rewrite A in E1. rewrite <- app_ass in E1.
  exploit list_append_injective_r. eexact E1.
  { unfold inj_bytes; rewrite map_length. erewrite Mem.loadbytes_length; eauto. }
  intros (E3 & E4).
  rewrite E2 in E3.
  exploit list_append_injective_r. eexact E3.
  { unfold inj_bytes; rewrite map_length. erewrite Mem.loadbytes_length; eauto. }
  intros (E5 & E6).
  intuition congruence.
Qed.

Remark decode_int_zero_ext: forall n bytes,
  0 <= n <= 4 -> n = Z.of_nat (length bytes) ->
  Int.zero_ext (n * 8) (Int.repr (decode_int bytes)) = Int.repr (decode_int bytes).
Proof.
  intros.
  assert (0 <= decode_int bytes < two_p (n * 8)).
  { rewrite H0. replace (length bytes) with (length (rev_if_be bytes)). 
    apply int_of_bytes_range.
    apply rev_if_be_length. }
  assert (two_p (n * 8) <= Int.modulus).
  { apply (two_p_monotone (n * 8) 32); lia. } 
  unfold Int.zero_ext.
  rewrite Int.unsigned_repr by (unfold Int.max_unsigned; lia).
  rewrite Zbits.Zzero_ext_mod by lia.
  rewrite Zmod_small by auto. auto.
Qed.

Theorem load_int_correct: forall s m b pos isz i v,
  match_state s m b ->
  load_int s pos isz = OK i ->
  Mem.load (chunk_for_carrier isz) m b pos = Some v ->
  v = Vint i.
Proof.
  intros until v; intros MS RI LD.
  exploit Mem.load_valid_access. eauto. intros [PERM ALIGN].
  unfold load_int in RI. 
  set (chunk := chunk_for_carrier isz) in *.
  set (sz := size_chunk chunk) in *.
  assert (sz > 0) by (apply size_chunk_pos).
  set (s1 := pad_to s (pos + sz)) in *.
  assert (pos + sz <= curr s1) by (apply curr_pad_to).
  monadInv RI. InvBooleans. destruct x as [[bytes1 bytes2] il].
  assert (MS': match_state s1 m b) by (apply pad_to_correct; auto).
  exploit trisection_correct; eauto. lia.
  intros (L1 & L2 & L3).
  assert (LEN: Z.of_nat (length bytes2) = sz).
  { apply Mem.loadbytes_length in L2. unfold inj_bytes in L2.
    rewrite map_length in L2. rewrite L2. apply Z2Nat.id; lia. }
  exploit Mem.loadbytes_load. eexact L2. exact ALIGN. rewrite LD. 
  unfold decode_val. rewrite proj_inj_bytes. intros E; inv E; inv EQ0.
  unfold chunk, chunk_for_carrier; destruct isz; f_equal.
  - apply (decode_int_zero_ext 1). lia. auto.
  - apply (decode_int_zero_ext 2). lia. auto.
  - apply (decode_int_zero_ext 1). lia. auto.
Qed.

Remark loadbytes_concat_3: forall m b ofs1 len1 l1 ofs2 len2 l2 ofs3 len3 l3 len,
  Mem.loadbytes m b ofs1 len1 = Some l1 ->
  Mem.loadbytes m b ofs2 len2 = Some l2 ->
  Mem.loadbytes m b ofs3 len3 = Some l3 ->
  ofs2 = ofs1 + len1 -> ofs3 = ofs2 + len2 -> 0 <= len1 -> 0 <= len2 -> 0 <= len3 ->
  len = len1 + len2 + len3 ->
  Mem.loadbytes m b ofs1 len = Some (l1 ++ l2 ++ l3).
Proof.
  intros. rewrite H7, <- Z.add_assoc. apply Mem.loadbytes_concat. auto.
  apply Mem.loadbytes_concat. rewrite <- H2; auto. rewrite <- H2, <- H3; auto.
  lia. lia. lia. lia.
Qed. 

Theorem store_data_correct: forall s m b pos i s' m',
  match_state s m b ->
  store_data s pos i = OK s' ->
  Genv.store_init_data ge m b pos i = Some m' ->
  match i with Init_space _ => False | _ => True end ->
  match_state s' m' b.
Proof.
  intros until m'; intros MS ST SI NOSPACE.
  unfold store_data in ST.
  set (sz := init_data_size i) in *.
  assert (sz >= 0) by (apply init_data_size_pos).
  set (s1 := pad_to s (pos + sz)) in *.
  monadInv ST. InvBooleans.
  assert (U: Mem.unchanged_on (fun b i => ~(pos <= i < pos + sz)) m m').
  { eapply Genv.store_init_data_unchanged. eauto. tauto. }
  exploit store_init_data_loadbytes; eauto. fold sz. intros D.
  destruct (zle (curr s) pos).
- inv ST.
  set (il := if zlt (curr s) pos then Init_space (pos - curr s) :: init s else init s).
  assert (IL: boidl (rev il) = boidl (rev (init s)) ++ repeat (Byte Byte.zero) (Z.to_nat (pos - curr s))).
  { unfold il; destruct (zlt (curr s) pos).
  - simpl rev. rewrite boidl_rev_cons. simpl. auto.
  - rewrite Z_to_nat_neg by lia. simpl. rewrite app_nil_r; auto.
  }
  constructor; simpl; intros.
  + lia.
  + rewrite boidl_rev_cons, IL, app_ass.
    apply loadbytes_concat_3 with (len1 := curr s) (ofs2 := curr s) (len2 := pos - curr s) (ofs3 := pos) (len3 := sz); try lia.
    * eapply Mem.loadbytes_unchanged_on; eauto.
      intros. simpl. lia.
      eapply match_contents; eauto.
    * eapply Mem.loadbytes_unchanged_on; eauto.
      intros. simpl. lia.
      eapply reads_as_zeros_loadbytes. eapply match_uninitialized; eauto. lia. lia. lia.
    * exact D.
    * eapply match_range; eauto.
  + eapply reads_as_zeros_unchanged; eauto.
    eapply reads_as_zeros_mono. eapply match_uninitialized; eauto. lia. lia.
    intros. simpl. lia.
- monadInv ST. destruct x as [[bytes1 bytes2] il]. inv EQ0.
  assert (pos + sz <= curr s1) by (apply curr_pad_to).
  assert (MS': match_state s1 m b) by (apply pad_to_correct; auto).
  exploit trisection_correct; eauto. lia.
  intros (L1 & L2 & L3).
  constructor; simpl; intros.
  + eapply match_range; eauto.
  + rewrite add_rev_bytes_spec, rev_app_distr; simpl; rewrite app_ass; simpl.
    rewrite <- map_rev, rev_involutive.
    rewrite boidl_app. simpl. rewrite boidl_init_bytes.
    apply loadbytes_concat_3 with (len1 := pos) (ofs2 := pos) (len2 := sz) (ofs3 := pos + sz)
                                  (len3 := curr s1 - (pos + sz)); try lia.
    * eapply Mem.loadbytes_unchanged_on; eauto.
      intros. simpl. lia.
    * exact D.
    * eapply Mem.loadbytes_unchanged_on; eauto.
      intros. simpl. lia.
  + eapply reads_as_zeros_unchanged; eauto. eapply match_uninitialized; eauto.
    intros. simpl. lia.
Qed.

Corollary store_int_correct: forall s m b pos isz n s' m',
  match_state s m b ->
  store_int s pos isz n = OK s' ->
  Mem.store (chunk_for_carrier isz) m b pos (Vint n) = Some m' ->
  match_state s' m' b.
Proof.
  intros. eapply store_data_correct; eauto.
- destruct isz; exact H1.
- destruct isz; exact I.
Qed.

Theorem init_data_list_of_state_correct: forall s m b il m0 b' m1 m2,
  match_state s m b ->
  init_data_list_of_state s = OK il ->
  store_zeros m0 b' 0 (init_data_list_size il) = Some m1 ->
  Genv.store_init_data_list ge m1 b' 0 il = Some m2 ->
  Mem.loadbytes m2 b' 0 (init_data_list_size il) = Mem.loadbytes m b 0 s.(total_size).
Proof.
  intros. unfold init_data_list_of_state in H0; monadInv H0.
  set (s1 := pad_to s s.(total_size)) in *.
  transitivity (Some (boidl (rev' (init s1)))).
  eapply Genv.store_init_data_list_loadbytes; eauto.
  eapply Genv.store_zeros_loadbytes; eauto.
  symmetry. unfold rev'. rewrite <- rev_alt.
  replace (total_size s) with (curr s1). eapply match_contents; eauto. apply pad_to_correct; auto. lia.
  unfold s1, pad_to. destruct (zle (total_size s) (curr s)); simpl; lia.
Qed.

(** REVISE

(** * Soundness of the translation of initializers *)

(** Soundness for single initializers. *)

Theorem transl_init_single_steps:
  forall ty a data f m v1 ty1 m' v chunk b ofs m'',
  transl_init_single ge ty a = OK data ->
  star step ge (ExprState f a Kstop empty_env m) E0 (ExprState f (Eval v1 ty1) Kstop empty_env m') ->
  sem_cast v1 ty1 ty m' = Some v ->
  access_mode ty = By_value chunk ->
  Mem.store chunk m' b ofs v = Some m'' ->
  Genv.store_init_data ge m b ofs data = Some m''.
Proof.
  intros. monadInv H. monadInv EQ. 
  exploit constval_steps; eauto. intros [A [B C]]. subst m' ty1.
  exploit sem_cast_match; eauto. intros D.
  unfold Genv.store_init_data.
  inv D.
- (* int *)
  remember Archi.ptr64 as ptr64.  destruct ty; try discriminate EQ0.
+ destruct i0; inv EQ0.
  destruct s; simpl in H2; inv H2. rewrite <- Mem.store_signed_unsigned_8; auto. auto.
  destruct s; simpl in H2; inv H2. rewrite <- Mem.store_signed_unsigned_16; auto. auto.
  simpl in H2; inv H2. assumption.
  simpl in H2; inv H2. assumption.
+ destruct ptr64; inv EQ0. simpl in H2; unfold Mptr in H2; rewrite <- Heqptr64 in H2; inv H2. assumption.
- (* Long *)
  remember Archi.ptr64 as ptr64. destruct ty; inv EQ0.
+ simpl in H2; inv H2. assumption.
+ simpl in H2; unfold Mptr in H2; destruct Archi.ptr64; inv H4. 
  inv H2; assumption.
- (* float *)
  destruct ty; try discriminate.
  destruct f1; inv EQ0; simpl in H2; inv H2; assumption.
- (* single *)
  destruct ty; try discriminate.
  destruct f1; inv EQ0; simpl in H2; inv H2; assumption.
- (* pointer *)
  unfold inj in H.
  assert (data = Init_addrof b1 ofs1 /\ chunk = Mptr).
  { remember Archi.ptr64 as ptr64.
    destruct ty; inversion EQ0.
    destruct i; inv H5. unfold Mptr. destruct Archi.ptr64; inv H6; inv H2; auto.
    subst ptr64. unfold Mptr. destruct Archi.ptr64; inv H5; inv H2; auto.
    inv H2. auto. }
  destruct H4; subst. destruct (Genv.find_symbol ge b1); inv H.
  rewrite Ptrofs.add_zero in H3. auto.
- (* undef *)
  discriminate.
Qed.

(** Size properties for initializers. *)

Lemma transl_init_single_size:
  forall ty a data,
  transl_init_single ge ty a = OK data ->
  init_data_size data = sizeof ge ty.
Proof.
  intros. monadInv H. monadInv EQ. remember Archi.ptr64 as ptr64. destruct x.
- monadInv EQ0.
- destruct ty; try discriminate.
  destruct i0; inv EQ0; auto.
  destruct ptr64; inv EQ0. 
Local Transparent sizeof.
  unfold sizeof. rewrite <- Heqptr64; auto.
- destruct ty; inv EQ0; auto. 
  unfold sizeof. destruct Archi.ptr64; inv H0; auto.
- destruct ty; try discriminate.
  destruct f0; inv EQ0; auto.
- destruct ty; try discriminate.
  destruct f0; inv EQ0; auto.
- destruct ty; try discriminate.
  destruct i0; inv EQ0; auto.
  destruct Archi.ptr64 eqn:SF; inv H0. simpl. rewrite SF; auto.
  destruct ptr64; inv EQ0. simpl. rewrite <- Heqptr64; auto.
  inv EQ0. unfold init_data_size, sizeof. auto.
Qed.

Notation idlsize := init_data_list_size.

Remark padding_size:
  forall frm to, frm <= to -> idlsize (tr_padding frm to) = to - frm.
Proof.
  unfold tr_padding; intros. destruct (zlt frm to).
  simpl. extlia.
  simpl. lia.
Qed.

Remark idlsize_app:
  forall d1 d2, idlsize (d1 ++ d2) = idlsize d1 + idlsize d2.
Proof.
  induction d1; simpl; intros.
  auto.
  rewrite IHd1. lia.
Qed.

Remark union_field_size:
  forall f ty fl, field_type f fl = OK ty -> sizeof ge ty <= sizeof_union ge fl.
Proof.
  induction fl as [|m fl]; simpl; intros.
- inv H.
- destruct (ident_eq f (name_member m)).
  + inv H. extlia.
  + specialize (IHfl H). extlia.
Qed.

Hypothesis ce_consistent: composite_env_consistent ge.

Lemma tr_init_size:
  forall i ty data,
  tr_init ty i data ->
  idlsize data = sizeof ge ty
with tr_init_array_size:
  forall ty il sz data,
  tr_init_array ty il sz data ->
  idlsize data = sizeof ge ty * sz
with tr_init_struct_size:
  forall ty fl il pos data,
  tr_init_struct ty fl il pos data ->
  sizeof_struct ge pos fl <= sizeof ge ty ->
  idlsize data + pos = sizeof ge ty.
Proof.
Local Opaque sizeof.
- destruct 1; simpl.
+ erewrite transl_init_single_size by eauto. lia.
+ Local Transparent sizeof. simpl. eapply tr_init_array_size; eauto. 
+ replace (idlsize d) with (idlsize d + 0) by lia.
  eapply tr_init_struct_size; eauto. simpl.
  unfold lookup_composite in H. destruct (ge.(genv_cenv)!id) as [co'|] eqn:?; inv H.
  erewrite co_consistent_sizeof by (eapply ce_consistent; eauto).
  unfold sizeof_composite. rewrite H0. apply align_le.
  destruct (co_alignof_two_p co) as [n EQ]. rewrite EQ. apply two_power_nat_pos.
+ rewrite idlsize_app, padding_size. 
  exploit tr_init_size; eauto. intros EQ; rewrite EQ. lia.
  simpl. unfold lookup_composite in H. destruct (ge.(genv_cenv)!id) as [co'|] eqn:?; inv H.
  apply Z.le_trans with (sizeof_union ge (co_members co)).
  eapply union_field_size; eauto.
  erewrite co_consistent_sizeof by (eapply ce_consistent; eauto).
  unfold sizeof_composite. rewrite H0. apply align_le.
  destruct (co_alignof_two_p co) as [n EQ]. rewrite EQ. apply two_power_nat_pos.

- destruct 1; simpl.
+ lia.
+ rewrite Z.mul_comm.
  assert (0 <= sizeof ge ty * sz).
  { apply Zmult_gt_0_le_0_compat. lia. generalize (sizeof_pos ge ty); lia. }
  extlia.
+ rewrite idlsize_app. 
  erewrite tr_init_size by eauto. 
  erewrite tr_init_array_size by eauto.
  ring.

- destruct 1; simpl; intros.
+ rewrite padding_size by auto. lia.
+ rewrite ! idlsize_app, padding_size. 
  erewrite tr_init_size by eauto. 
  rewrite <- (tr_init_struct_size _ _ _ _ _ H0 H1). lia.
  unfold pos1. apply align_le. apply alignof_pos. 
Qed.

(** A semantics for general initializers *)

Definition dummy_function := mkfunction Tvoid cc_default nil nil Sskip.

Fixpoint fields_of_struct (fl: members) (pos: Z) : list (Z * type) :=
  match fl with
  | nil => nil
  | (id1, ty1) :: fl' =>
      (align pos (alignof ge ty1), ty1) :: fields_of_struct fl' (align pos (alignof ge ty1) + sizeof ge ty1)
  end.

Inductive exec_init: mem -> block -> Z -> type -> initializer -> mem -> Prop :=
  | exec_init_single: forall m b ofs ty a v1 ty1 chunk m' v m'',
      star step ge (ExprState dummy_function a Kstop empty_env m)
                E0 (ExprState dummy_function (Eval v1 ty1) Kstop empty_env m') ->
      sem_cast v1 ty1 ty m' = Some v ->
      access_mode ty = By_value chunk ->
      Mem.store chunk m' b ofs v = Some m'' ->
      exec_init m b ofs ty (Init_single a) m''
  | exec_init_array_: forall m b ofs ty sz a il m',
      exec_init_array m b ofs ty sz il m' ->
      exec_init m b ofs (Tarray ty sz a) (Init_array il) m'
  | exec_init_struct: forall m b ofs id a il co m',
      ge.(genv_cenv)!id = Some co -> co_su co = Struct ->
      exec_init_list m b ofs (fields_of_struct (co_members co) 0) il m' ->
      exec_init m b ofs (Tstruct id a) (Init_struct il) m'
  | exec_init_union: forall m b ofs id a f i ty co m',
      ge.(genv_cenv)!id = Some co -> co_su co = Union ->
      field_type f (co_members co) = OK ty ->
      exec_init m b ofs ty i m' ->
      exec_init m b ofs (Tunion id a) (Init_union f i) m'

with exec_init_array: mem -> block -> Z -> type -> Z -> initializer_list -> mem -> Prop :=
  | exec_init_array_nil: forall m b ofs ty sz,
      sz >= 0 ->
      exec_init_array m b ofs ty sz Init_nil m
  | exec_init_array_cons: forall m b ofs ty sz i1 il m' m'',
      exec_init m b ofs ty i1 m' ->
      exec_init_array m' b (ofs + sizeof ge ty) ty (sz - 1) il m'' ->
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
  exec_init_array m b ofs ty sz il m' -> sz >= 0.
Proof.
  induction 1; lia.
Qed.

Lemma store_init_data_list_app:
  forall data1 m b ofs m' data2 m'',
  Genv.store_init_data_list ge m b ofs data1 = Some m' ->
  Genv.store_init_data_list ge m' b (ofs + idlsize data1) data2 = Some m'' ->
  Genv.store_init_data_list ge m b ofs (data1 ++ data2) = Some m''.
Proof.
  induction data1; simpl; intros.
  inv H. rewrite Z.add_0_r in H0. auto.
  destruct (Genv.store_init_data ge m b ofs a); try discriminate.
  rewrite Z.add_assoc in H0. eauto.
Qed.

Remark store_init_data_list_padding:
  forall frm to b ofs m,
  Genv.store_init_data_list ge m b ofs (tr_padding frm to) = Some m.
Proof.
  intros. unfold tr_padding. destruct (zlt frm to); auto.
Qed.

Lemma tr_init_sound:
  (forall m b ofs ty i m', exec_init m b ofs ty i m' ->
   forall data, tr_init ty i data ->
   Genv.store_init_data_list ge m b ofs data = Some m')
/\(forall m b ofs ty sz il m', exec_init_array m b ofs ty sz il m' ->
   forall data, tr_init_array ty il sz data ->
   Genv.store_init_data_list ge m b ofs data = Some m')
/\(forall m b ofs l il m', exec_init_list m b ofs l il m' ->
   forall ty fl data pos,
   l = fields_of_struct fl pos ->
   tr_init_struct ty fl il pos data ->
   Genv.store_init_data_list ge m b (ofs + pos) data = Some m').
Proof.
Local Opaque sizeof.
  apply exec_init_scheme; simpl; intros.
- (* single *)
  inv H3. simpl. erewrite transl_init_single_steps by eauto. auto.
- (* array *)
  inv H1. replace (Z.max 0 sz) with sz in H7. eauto.
  assert (sz >= 0) by (eapply exec_init_array_length; eauto). extlia.
- (* struct *)
  inv H3. unfold lookup_composite in H7. rewrite H in H7. inv H7. 
  replace ofs with (ofs + 0) by lia. eauto.
- (* union *)
  inv H4. unfold lookup_composite in H9. rewrite H in H9. inv H9. rewrite H1 in H12; inv H12. 
  eapply store_init_data_list_app. eauto.
  apply store_init_data_list_padding.

- (* array, empty *)
  inv H0; auto.
- (* array, nonempty *)
  inv H3.
  eapply store_init_data_list_app.
  eauto.
  rewrite (tr_init_size _ _ _ H7). eauto.

- (* struct, empty *)
  inv H0. apply store_init_data_list_padding.
- (* struct, nonempty *)
  inv H4. simpl in H3; inv H3. 
  eapply store_init_data_list_app. apply store_init_data_list_padding.
  rewrite padding_size.
  replace (ofs + pos0 + (pos2 - pos0)) with (ofs + pos2) by lia.
  eapply store_init_data_list_app.
  eauto.
  rewrite (tr_init_size _ _ _ H9).
  rewrite <- Z.add_assoc. eapply H2. eauto. eauto.
  apply align_le. apply alignof_pos.
Qed.

*)

End SOUNDNESS.

(*
Theorem transl_init_sound:
  forall p m b ty i m' data,
  exec_init (globalenv p) m b 0 ty i m' ->
  transl_init (prog_comp_env p) ty i = OK data ->
  Genv.store_init_data_list (globalenv p) m b 0 data = Some m'.
Proof.
  intros.
  set (ge := globalenv p) in *.
  change (prog_comp_env p) with (genv_cenv ge) in H0.
  destruct (tr_init_sound ge) as (A & B & C).
  eapply build_composite_env_consistent. apply prog_comp_env_eq.
  eapply A; eauto. apply transl_init_spec; auto.
Qed.
*)

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

(** Correctness proof for constant propagation (processor-dependent part). *)

Require Import Coqlib.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import ValueDomain.
Require Import ConstpropOp.

Local Transparent Archi.ptr64.

(** * Correctness of strength reduction *)

(** We now show that strength reduction over operators and addressing
  modes preserve semantics: the strength-reduced operations and
  addressings evaluate to the same values as the original ones if the
  actual arguments match the static approximations used for strength
  reduction. *)

Section STRENGTH_REDUCTION.

Variable bc: block_classification.
Variable ge: genv.
Hypothesis GENV: genv_match bc ge.
Variable sp: block.
Hypothesis STACK: bc sp = BCstack.
Variable ae: AE.t.
Variable rs: regset.
Variable m: mem.
Hypothesis MATCH: ematch bc rs ae.

Lemma match_G:
  forall r id ofs,
  AE.get r ae = Ptr(Gl id ofs) -> Val.lessdef rs#r (Genv.symbol_address ge id ofs).
Proof.
  intros. apply vmatch_ptr_gl with bc; auto. rewrite <- H. apply MATCH.
Qed.

Lemma match_S:
  forall r ofs,
  AE.get r ae = Ptr(Stk ofs) -> Val.lessdef rs#r (Vptr sp ofs).
Proof.
  intros. apply vmatch_ptr_stk with bc; auto. rewrite <- H. apply MATCH.
Qed.

Ltac InvApproxRegs :=
  match goal with
  | [ H: _ :: _ = _ :: _ |- _ ] =>
        injection H; clear H; intros; InvApproxRegs
  | [ H: ?v = AE.get ?r ae |- _ ] =>
        generalize (MATCH r); rewrite <- H; clear H; intro; InvApproxRegs
  | _ => idtac
  end.

Ltac SimplVM :=
  match goal with
  | [ H: vmatch _ ?v (I ?n) |- _ ] =>
      let E := fresh in
      assert (E: v = Vint n) by (inversion H; auto);
      rewrite E in *; clear H; SimplVM
  | [ H: vmatch _ ?v (F ?n) |- _ ] =>
      let E := fresh in
      assert (E: v = Vfloat n) by (inversion H; auto);
      rewrite E in *; clear H; SimplVM
  | [ H: vmatch _ ?v (FS ?n) |- _ ] =>
      let E := fresh in
      assert (E: v = Vsingle n) by (inversion H; auto);
      rewrite E in *; clear H; SimplVM
  | [ H: vmatch _ ?v (Ptr(Gl ?id ?ofs)) |- _ ] =>
      let E := fresh in
      assert (E: Val.lessdef v (Genv.symbol_address ge id ofs)) by (eapply vmatch_ptr_gl; eauto);
      clear H; SimplVM
  | [ H: vmatch _ ?v (Ptr(Stk ?ofs)) |- _ ] =>
      let E := fresh in
      assert (E: Val.lessdef v (Vptr sp ofs)) by (eapply vmatch_ptr_stk; eauto);
      clear H; SimplVM
  | _ => idtac
  end.

Lemma const_for_result_correct:
  forall a op v,
  const_for_result a = Some op ->
  vmatch bc v a ->
  exists v', eval_operation ge (Vptr sp Ptrofs.zero) op nil m = Some v' /\ Val.lessdef v v'.
Proof.
  unfold const_for_result; intros.
  destruct a; inv H; SimplVM.
- (* integer *)
  exists (Vint n); auto.
- (* float *)
  destruct (generate_float_constants tt); inv H2. exists (Vfloat f); auto.
- (* single *)
  destruct (generate_float_constants tt); inv H2. exists (Vsingle f); auto.
- (* pointer *)
  destruct p; try discriminate; SimplVM.
  + (* global *)
    inv H2. exists (Genv.symbol_address ge id ofs); auto.
  + (* stack *)
    inv H2. exists (Vptr sp ofs); split; auto. simpl. rewrite Ptrofs.add_zero_l; auto.
Qed.

Lemma eval_static_shift_correct:
  forall s n, eval_shift s (Vint n) = Vint (eval_static_shift s n).
Proof.
  intros. destruct s; simpl; rewrite ? s_range; auto.
Qed.

Lemma cond_strength_reduction_correct:
  forall cond args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (cond', args') := cond_strength_reduction cond args vl in
  eval_condition cond' rs##args' m = eval_condition cond rs##args m.
Proof.
  intros until vl. unfold cond_strength_reduction.
  case (cond_strength_reduction_match cond args vl); simpl; intros; InvApproxRegs; SimplVM.
- apply Val.swap_cmp_bool.
- auto.
- apply Val.swap_cmpu_bool.
- auto.
- rewrite eval_static_shift_correct. auto.
- rewrite eval_static_shift_correct. auto.
- destruct (Float.eq_dec n1 Float.zero).
  subst n1. simpl. destruct (rs#r2); simpl; auto. rewrite Float.cmp_swap. auto.
  simpl. rewrite H1; auto.
- destruct (Float.eq_dec n2 Float.zero).
  subst n2. simpl. auto.
  simpl. rewrite H1; auto.
- destruct (Float.eq_dec n1 Float.zero).
  subst n1. simpl. destruct (rs#r2); simpl; auto. rewrite Float.cmp_swap. auto.
  simpl. rewrite H1; auto.
- destruct (Float.eq_dec n2 Float.zero); simpl; auto.
  subst n2; auto.
  rewrite H1; auto.
- destruct (Float32.eq_dec n1 Float32.zero).
  subst n1. simpl. destruct (rs#r2); simpl; auto. rewrite Float32.cmp_swap. auto.
  simpl. rewrite H1; auto.
- destruct (Float32.eq_dec n2 Float32.zero).
  subst n2. simpl. auto.
  simpl. rewrite H1; auto.
- destruct (Float32.eq_dec n1 Float32.zero).
  subst n1. simpl. destruct (rs#r2); simpl; auto. rewrite Float32.cmp_swap. auto.
  simpl. rewrite H1; auto.
- destruct (Float32.eq_dec n2 Float32.zero); simpl; auto.
  subst n2; auto.
  rewrite H1; auto.
- auto.
Qed.

Lemma make_cmp_base_correct:
  forall c args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (op', args') := make_cmp_base c args vl in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op' rs##args' m = Some v
         /\ Val.lessdef (Val.of_optbool (eval_condition c rs##args m)) v.
Proof.
  intros. unfold make_cmp_base.
  generalize (cond_strength_reduction_correct c args vl H).
  destruct (cond_strength_reduction c args vl) as [c' args']. intros EQ.
  econstructor; split. simpl; eauto. rewrite EQ. auto.
Qed.

Lemma make_cmp_correct:
  forall c args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (op', args') := make_cmp c args vl in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op' rs##args' m = Some v
         /\ Val.lessdef (Val.of_optbool (eval_condition c rs##args m)) v.
Proof.
  intros c args vl.
  assert (Y: forall r, vincl (AE.get r ae) (Uns Ptop 1) = true ->
             rs#r = Vundef \/ rs#r = Vint Int.zero \/ rs#r = Vint Int.one).
  { intros. apply vmatch_Uns_1 with bc Ptop. eapply vmatch_ge. eapply vincl_ge; eauto. apply MATCH. }
  unfold make_cmp. case (make_cmp_match c args vl); intros.
- unfold make_cmp_imm_eq.
  destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (rs#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor rs#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- unfold make_cmp_imm_ne.
  destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (rs#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor rs#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- unfold make_cmp_imm_eq.
  destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (rs#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor rs#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- unfold make_cmp_imm_ne.
  destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (rs#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor rs#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- apply make_cmp_base_correct; auto.
Qed.

Lemma make_addimm_correct:
  forall n r,
  let (op, args) := make_addimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.add rs#r (Vint n)) v.
Proof.
  intros. unfold make_addimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst. exists (rs#r); split; auto.
  destruct (rs#r); simpl; auto. rewrite Int.add_zero; auto. rewrite Ptrofs.add_zero; auto.
  exists (Val.add rs#r (Vint n)); auto.
Qed.

Lemma make_shlimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shlimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shl rs#r1 (Vint n)) v.
Proof.
  Opaque mk_shift_amount.
  intros; unfold make_shlimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shl_zero. auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; intros.
  econstructor; split. simpl; eauto.  rewrite mk_shift_amount_eq; auto.
  econstructor; split; eauto. simpl. congruence.
Qed.

Lemma make_shrimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shrimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shr rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shr_zero. auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; intros.
  econstructor; split. simpl; eauto.  rewrite mk_shift_amount_eq; auto.
  econstructor; split; eauto. simpl. congruence.
Qed.

Lemma make_shruimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shruimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shru rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shruimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shru_zero. auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; intros.
  econstructor; split. simpl; eauto.  rewrite mk_shift_amount_eq; auto.
  econstructor; split; eauto. simpl. congruence.
Qed.

Lemma make_mulimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_mulimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.mul rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_mulimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (Vint Int.zero); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.mul_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.one; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.mul_one; auto.
  destruct (Int.is_power2 n) eqn:?; intros.
  exploit Int.is_power2_range; eauto. intros R.
  econstructor; split. simpl; eauto. rewrite mk_shift_amount_eq; auto.
  rewrite (Val.mul_pow2 rs#r1 _ _ Heqo). auto.
  econstructor; split; eauto. simpl. congruence.
Qed.

Lemma make_mla_mulimm_correct:
  forall n1 r1 r2 r3,
  rs#r1 = Vint n1 ->
  let (op, args) := make_mla_mulimm n1 r1 r2 r3 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.add (Val.mul (Vint n1) rs#r2) rs#r3) v.
Proof.
  intros; unfold make_mla_mulimm.
  predSpec Int.eq Int.eq_spec n1 Int.zero; intros. subst.
    exists (rs#r3); split; auto. destruct (rs#r2); simpl; auto.
    destruct (rs#r3); simpl; auto.
    rewrite Int.mul_commut, Int.mul_zero, Int.add_zero_l; auto.
    rewrite Int.mul_commut, Int.mul_zero, Ptrofs.add_zero; auto.
  predSpec Int.eq Int.eq_spec n1 Int.one; intros. subst.
    exists (Val.add rs#r2 rs#r3); split; auto. destruct (rs#r2); simpl; auto.
    destruct (rs#r3); simpl; auto.
    rewrite Int.mul_commut, Int.mul_one; auto.
    rewrite Int.mul_commut, Int.mul_one; auto.
    eexists. simpl; split; eauto.
    fold (Val.mul (Vint n1) (rs#r2)). rewrite H; auto.
Qed.

Lemma make_mla_addimm_correct:
  forall n3 r1 r2 r3,
  rs#r3 = Vint n3 ->
  let (op, args) := make_mla_addimm n3 r1 r2 r3 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.add (Val.mul rs#r1 rs#r2) (Vint n3)) v.
Proof.
  intros; unfold make_mla_addimm.
  predSpec Int.eq Int.eq_spec n3 Int.zero; intros. subst.
    exists (Val.mul rs#r1 rs#r2); split; auto.
    destruct (rs#r1), (rs#r2); simpl; auto.
    rewrite Int.add_zero; auto.
    eexists. simpl; split; eauto. rewrite H; auto.
Qed.

Lemma make_mla_bothimm_correct:
  forall n1 n3 r1 r2 r3,
  rs#r1 = Vint n1 ->
  rs#r3 = Vint n3 ->
  let (op, args) := make_mla_bothimm n1 n3 r1 r2 r3 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.add (Val.mul (Vint n1) rs#r2) (Vint n3)) v.
Proof.
  intros; unfold make_mla_bothimm.
  predSpec Int.eq Int.eq_spec n1 Int.zero; intros. subst.
    exists (Vint n3); split; auto.
    destruct (rs#r2); simpl; auto.
    rewrite Int.mul_commut, Int.mul_zero, Int.add_zero_l; auto.
  predSpec Int.eq Int.eq_spec n1 Int.one; intros. subst.
    generalize (make_addimm_correct n3 r2); intro ADDIMM.
    destruct (make_addimm n3 r2) as [op args]. destruct ADDIMM as [v [OP LESSDEF]].
    exists v; split; auto.
    destruct (rs#r2); simpl; auto.
    simpl in LESSDEF. rewrite Int.mul_commut, Int.mul_one; auto.
  predSpec Int.eq Int.eq_spec n3 Int.zero; intros. subst.
    generalize (make_mulimm_correct n1 r2 r1 H); eauto; intro MULIMM.
    destruct (make_mulimm n1 r2 r1) as [op args]. destruct MULIMM as [v [OP LESSDEF]].
    exists v; split; auto.
    destruct (rs#r2); simpl; auto.
    simpl in LESSDEF. rewrite Int.add_zero, Int.mul_commut; auto.
    eexists. simpl; split; eauto.
    fold (Val.mul (Vint n1) (rs#r2)). rewrite H, H0; auto.
Qed.

Lemma make_divimm_correct:
  forall n r1 r2 v,
  Val.divs rs#r1 rs#r2 = Some v ->
  rs#r2 = Vint n ->
  let (op, args) := make_divimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divimm.
  predSpec Int.eq Int.eq_spec n Int.one; intros. subst. rewrite H0 in H.
  destruct (rs#r1) eqn:?;
    try (rewrite Val.divs_one in H; exists (Vint i); split; simpl; try rewrite Heqv0; auto);
    inv H; auto.
  destruct (Int.is_power2 n) eqn:?.
  destruct (Int.ltu i (Int.repr 31)) eqn:?.
  exists v; split; auto. simpl. eapply Val.divs_pow2; eauto. congruence.
  exists v; auto.
  exists v; auto.
Qed.

Lemma make_divuimm_correct:
  forall n r1 r2 v,
  Val.divu rs#r1 rs#r2 = Some v ->
  rs#r2 = Vint n ->
  let (op, args) := make_divuimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divuimm.
  predSpec Int.eq Int.eq_spec n Int.one; intros. subst. rewrite H0 in H.
  destruct (rs#r1) eqn:?;
    try (rewrite Val.divu_one in H; exists (Vint i); split; simpl; try rewrite Heqv0; auto);
    inv H; auto.
  destruct (Int.is_power2 n) eqn:?.
  replace v with (Val.shru rs#r1 (Vint i)).
  econstructor; split. simpl. rewrite mk_shift_amount_eq. eauto.
  eapply Int.is_power2_range; eauto. auto.
  eapply Val.divu_pow2; eauto. congruence.
  exists v; auto.
Qed.

Lemma make_andimm_correct:
  forall n r x,
  vmatch bc rs#r x ->
  let (op, args) := make_andimm n r x in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.and rs#r (Vint n)) v.
Proof.
  intros; unfold make_andimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (Vint Int.zero); split; auto. destruct (rs#r); simpl; auto. rewrite Int.and_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.and_mone; auto.
  destruct (match x with Uns _ k => Int.eq (Int.zero_ext k (Int.not n)) Int.zero
                       | _ => false end) eqn:UNS.
  destruct x; try congruence.
  exists (rs#r); split; auto.
  inv H; auto. simpl. replace (Int.and i n) with i; auto.
  generalize (Int.eq_spec (Int.zero_ext n0 (Int.not n)) Int.zero); rewrite UNS; intro EQ.
  Int.bit_solve. destruct (zlt i0 n0).
  replace (Int.testbit n i0) with (negb (Int.testbit Int.zero i0)).
  rewrite Int.bits_zero. simpl. rewrite andb_true_r. auto.
  rewrite <- EQ. rewrite Int.bits_zero_ext by omega. rewrite zlt_true by auto.
  rewrite Int.bits_not by auto. apply negb_involutive.
  rewrite H6 by auto. auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_orimm_correct:
  forall n r,
  let (op, args) := make_orimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.or rs#r (Vint n)) v.
Proof.
  intros; unfold make_orimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.or_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (Vint Int.mone); split; auto. destruct (rs#r); simpl; auto. rewrite Int.or_mone; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_xorimm_correct:
  forall n r,
  let (op, args) := make_xorimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.xor rs#r (Vint n)) v.
Proof.
  intros; unfold make_xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.xor_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (Val.notint (rs#r)); split. auto.
  destruct (rs#r); simpl; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_mulfimm_correct:
  forall n r1 r2,
  rs#r2 = Vfloat n ->
  let (op, args) := make_mulfimm n r1 r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.mulf rs#r1 rs#r2) v.
Proof.
  intros; unfold make_mulfimm.
  destruct (Float.eq_dec n (Float.of_int (Int.repr 2))); intros.
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (rs#r1); simpl; auto. rewrite Float.mul2_add; auto.
  simpl. econstructor; split; eauto.
Qed.

Lemma make_mulfimm_correct_2:
  forall n r1 r2,
  rs#r1 = Vfloat n ->
  let (op, args) := make_mulfimm n r2 r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.mulf rs#r1 rs#r2) v.
Proof.
  intros; unfold make_mulfimm.
  destruct (Float.eq_dec n (Float.of_int (Int.repr 2))); intros.
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (rs#r2); simpl; auto. rewrite Float.mul2_add; auto.
  rewrite Float.mul_commut; auto.
  simpl. econstructor; split; eauto.
Qed.

Lemma make_mulfsimm_correct:
  forall n r1 r2,
  rs#r2 = Vsingle n ->
  let (op, args) := make_mulfsimm n r1 r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.mulfs rs#r1 rs#r2) v.
Proof.
  intros; unfold make_mulfsimm.
  destruct (Float32.eq_dec n (Float32.of_int (Int.repr 2))); intros.
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (rs#r1); simpl; auto. rewrite Float32.mul2_add; auto.
  simpl. econstructor; split; eauto.
Qed.

Lemma make_mulfsimm_correct_2:
  forall n r1 r2,
  rs#r1 = Vsingle n ->
  let (op, args) := make_mulfsimm n r2 r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.mulfs rs#r1 rs#r2) v.
Proof.
  intros; unfold make_mulfsimm.
  destruct (Float32.eq_dec n (Float32.of_int (Int.repr 2))); intros.
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (rs#r2); simpl; auto. rewrite Float32.mul2_add; auto.
  rewrite Float32.mul_commut; auto.
  simpl. econstructor; split; eauto.
Qed.

Lemma make_cast8signed_correct:
  forall r x,
  vmatch bc rs#r x ->
  let (op, args) := make_cast8signed r x in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.sign_ext 8 rs#r) v.
Proof.
  intros; unfold make_cast8signed. destruct (vincl x (Sgn Ptop 8)) eqn:INCL.
  exists rs#r; split; auto.
  assert (V: vmatch bc rs#r (Sgn Ptop 8)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_sgn_sign_ext in H4 by auto. rewrite H4; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_cast16signed_correct:
  forall r x,
  vmatch bc rs#r x ->
  let (op, args) := make_cast16signed r x in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.sign_ext 16 rs#r) v.
Proof.
  intros; unfold make_cast16signed. destruct (vincl x (Sgn Ptop 16)) eqn:INCL.
  exists rs#r; split; auto.
  assert (V: vmatch bc rs#r (Sgn Ptop 16)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_sgn_sign_ext in H4 by auto. rewrite H4; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma op_strength_reduction_correct:
  forall op args vl v,
  vl = map (fun r => AE.get r ae) args ->
  eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v ->
  let (op', args') := op_strength_reduction op args vl in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op' rs##args' m = Some w /\ Val.lessdef v w.
Proof.
  intros until v; unfold op_strength_reduction;
  case (op_strength_reduction_match op args vl); simpl; intros.
(* cast8signed *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast8signed_correct; auto.
(* cast8signed *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast16signed_correct; auto.
(* add *)
  InvApproxRegs; SimplVM. rewrite Val.add_commut in H0. inv H0. apply make_addimm_correct.
  InvApproxRegs; SimplVM. inv H0. apply make_addimm_correct.
(* addshift *)
  InvApproxRegs; SimplVM. inv H0. rewrite eval_static_shift_correct. apply make_addimm_correct.
(* sub *)
  InvApproxRegs; SimplVM. inv H0. econstructor; split; eauto.
  InvApproxRegs; SimplVM. inv H0. rewrite Val.sub_add_opp. apply make_addimm_correct.
(* subshift *)
  InvApproxRegs; SimplVM. inv H0. rewrite eval_static_shift_correct. rewrite Val.sub_add_opp. apply make_addimm_correct.
(* rsubshift *)
  InvApproxRegs; SimplVM. inv H0. rewrite eval_static_shift_correct. econstructor; split; eauto.
(* mul *)
  InvApproxRegs; SimplVM. inv H0. fold (Val.mul (Vint n1) rs#r2).
  rewrite Val.mul_commut. apply make_mulimm_correct; auto.
  InvApproxRegs; SimplVM. inv H0. apply make_mulimm_correct; auto.
(* mla *)
  InvApproxRegs; SimplVM. inv H0. fold (Val.mul (Vint n1) rs#r2).
  apply make_mla_bothimm_correct; auto.
  InvApproxRegs; SimplVM. inv H0.
  rewrite Val.mul_commut. apply make_mla_bothimm_correct; auto.
  InvApproxRegs; SimplVM. inv H0. fold (Val.mul (Vint n1) rs#r2).
  apply make_mla_mulimm_correct; auto.
  InvApproxRegs; SimplVM. inv H0.
  rewrite Val.mul_commut. apply make_mla_mulimm_correct; auto.
  InvApproxRegs; SimplVM. inv H0. apply make_mla_addimm_correct; auto.
(* divs *)
  assert (rs#r2 = Vint n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divimm_correct; auto.
(* divu *)
  assert (rs#r2 = Vint n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divuimm_correct; auto.
(* and *)
  InvApproxRegs; SimplVM. inv H0. fold (Val.and (Vint n1) rs#r2). rewrite Val.and_commut. apply make_andimm_correct; auto.
  InvApproxRegs; SimplVM. inv H0. apply make_andimm_correct; auto.
(* andshift *)
  InvApproxRegs; SimplVM. inv H0. rewrite eval_static_shift_correct. apply make_andimm_correct; auto.
(* or *)
  InvApproxRegs; SimplVM. inv H0. fold (Val.or (Vint n1) rs#r2). rewrite Val.or_commut. apply make_orimm_correct.
  InvApproxRegs; SimplVM. inv H0. apply make_orimm_correct.
(* orshift *)
  InvApproxRegs; SimplVM. inv H0. rewrite eval_static_shift_correct. apply make_orimm_correct.
(* xor *)
  InvApproxRegs; SimplVM. inv H0. fold (Val.xor (Vint n1) rs#r2). rewrite Val.xor_commut. apply make_xorimm_correct.
  InvApproxRegs; SimplVM. inv H0. apply make_xorimm_correct.
(* xorshift *)
  InvApproxRegs; SimplVM. inv H0. rewrite eval_static_shift_correct. apply make_xorimm_correct.
(* bic *)
  InvApproxRegs; SimplVM. inv H0. apply make_andimm_correct; auto.
(* bicshift *)
  InvApproxRegs; SimplVM. inv H0. rewrite eval_static_shift_correct. apply make_andimm_correct; auto.
(* shl *)
  InvApproxRegs; SimplVM. inv H0. apply make_shlimm_correct; auto.
(* shr *)
  InvApproxRegs; SimplVM. inv H0. apply make_shrimm_correct; auto.
(* shru *)
  InvApproxRegs; SimplVM. inv H0. apply make_shruimm_correct; auto.
(* cmp *)
  inv H0. apply make_cmp_correct; auto.
(* mulf *)
  InvApproxRegs; SimplVM; inv H0. rewrite <- H2. apply make_mulfimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. fold (Val.mulf (Vfloat n1) rs#r2).
  rewrite <- H2. apply make_mulfimm_correct_2; auto.
(* mulfs *)
  InvApproxRegs; SimplVM; inv H0. rewrite <- H2. apply make_mulfsimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. fold (Val.mulfs (Vsingle n1) rs#r2).
  rewrite <- H2. apply make_mulfsimm_correct_2; auto.
(* default *)
  exists v; auto.
Qed.

Lemma addr_strength_reduction_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing ge (Vptr sp Ptrofs.zero) addr rs##args = Some res ->
  let (addr', args') := addr_strength_reduction addr args vl in
  exists res', eval_addressing ge (Vptr sp Ptrofs.zero) addr' rs##args' = Some res' /\ Val.lessdef res res'.
Proof.
  intros until res. unfold addr_strength_reduction.
  destruct (addr_strength_reduction_match addr args vl); simpl;
  intros VL EA; InvApproxRegs; SimplVM; try (inv EA).
- rewrite Ptrofs.add_zero_l.
  change (Vptr sp (Ptrofs.add n1 (Ptrofs.of_int n2))) with (Val.add (Vptr sp n1) (Vint n2)).
  econstructor; split; eauto. apply Val.add_lessdef; auto.
- rewrite Ptrofs.add_zero_l. econstructor; split; eauto. rewrite Ptrofs.add_commut.
  change (Val.lessdef (Val.add (Vint n1) rs#r2) (Val.add (Vptr sp n2) (Vint n1))).
  rewrite Val.add_commut; apply Val.add_lessdef; auto.
- econstructor; split; eauto.
  change (Val.lessdef (Val.add (Vint n1) rs#r2) (Val.add rs#r2 (Vint n1))).
  rewrite Val.add_commut; apply Val.add_lessdef; auto.
- econstructor; split; eauto.
- rewrite eval_static_shift_correct. rewrite Ptrofs.add_zero_l. econstructor; split; eauto.
  change (Vptr sp (Ptrofs.add n1 (Ptrofs.of_int (eval_static_shift s n2))))
    with (Val.add (Vptr sp n1) (Vint (eval_static_shift s n2))).
  apply Val.add_lessdef; auto.
- rewrite eval_static_shift_correct. econstructor; split; eauto.
- rewrite Ptrofs.add_zero_l.
  change (Vptr sp (Ptrofs.add n1 (Ptrofs.of_int n))) with (Val.add (Vptr sp n1) (Vint n)).
  econstructor; split; eauto. apply Val.add_lessdef; auto.
- exists res; auto.
Qed.

End STRENGTH_REDUCTION.

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

(** Correctness proof for operator strength reduction. *)

Require Import Coqlib Compopts.
Require Import Integers Floats Values Memory Globalenvs Events.
Require Import Op Registers RTL ValueDomain.
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
  | [ H: vmatch _ ?v (L ?n) |- _ ] =>
      let E := fresh in
      assert (E: v = Vlong n) by (inversion H; auto);
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
- apply Val.swap_cmpl_bool.
- auto.
- apply Val.swap_cmplu_bool.
- auto.
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
  assert (Z: forall r, is_an_integer (AE.get r ae) = true -> 
             match rs#r with Vptr _ _ => False | _ => True end).
  { intros. generalize (MATCH r); intro V. revert H. inv V; auto; discriminate. }
  unfold make_cmp. case (make_cmp_match c args vl); intros.
- destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (rs#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor rs#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (rs#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor rs#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (rs#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor rs#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* destruct (is_an_integer v1) eqn:E.
** simpl in H; inv H.
  replace (eval_condition (Ccompuimm Ceq n) rs##(r1::nil) m)
     with (eval_condition (Ccompimm Ceq n) rs##(r1::nil) m).
  apply make_cmp_base_correct; auto.
  simpl. apply Z in E. destruct (rs#r1); auto; contradiction.
** apply make_cmp_base_correct; auto.
- destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (rs#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor rs#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* destruct (is_an_integer v1) eqn:E.
** simpl in H; inv H.
  replace (eval_condition (Ccompuimm Cne n) rs##(r1::nil) m)
     with (eval_condition (Ccompimm Cne n) rs##(r1::nil) m).
  apply make_cmp_base_correct; auto.
  simpl. apply Z in E. destruct (rs#r1); auto; contradiction.
** apply make_cmp_base_correct; auto.
- apply make_cmp_base_correct; auto.
Qed.

Lemma make_addimm_correct:
  forall n r,
  let (op, args) := make_addimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.add rs#r (Vint n)) v.
Proof.
  intros. unfold make_addimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.add_zero; auto. rewrite Ptrofs.add_zero; auto.
  exists (Val.add rs#r (Vint n)); auto.
Qed.

Lemma make_shlimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shlimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shl rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shlimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shl_zero. auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; intros.
  rewrite Val.shl_rolm; auto. econstructor; split; eauto. auto.
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
  destruct (Int.ltu n Int.iwordsize) eqn:?.
  econstructor; split; eauto. simpl. auto.
  econstructor; split; eauto. simpl. congruence.
Qed.

Lemma make_shruimm_aux_correct:
  forall n r1,
  Int.ltu n Int.iwordsize = true ->
  let (op, args) := make_shruimm_aux n r1 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shru rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shruimm_aux.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shru_zero. auto.
  rewrite Val.shru_rolm; auto. econstructor; split; eauto. auto.
Qed.

Lemma make_shruimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shruimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shru rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shruimm.
  destruct (Int.ltu n Int.iwordsize) eqn:?; intros.
  apply make_shruimm_aux_correct; auto.
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
  rewrite (Val.mul_pow2 rs#r1 _ _ Heqo). rewrite Val.shl_rolm.
  econstructor; split; eauto. auto.
  eapply Int.is_power2_range; eauto.
  econstructor; split; eauto. auto.
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
  destruct (Int.is_power2 n) eqn:?.
  exploit Int.is_power2_range; eauto. intros RANGE.
  replace v with (Val.shru rs#r1 (Vint i)). 
  apply make_shruimm_aux_correct; auto.
  rewrite H0 in H.
  destruct (rs#r1); simpl in *; inv H. rewrite RANGE.
  destruct (Int.eq n Int.zero); inv H2.
  f_equal; symmetry; apply Int.divu_pow2; auto.
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
  subst n. exists (Val.notint rs#r); split; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_addlimm_correct:
  forall n r,
  let (op, args) := make_addlimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.addl rs#r (Vlong n)) v.
Proof.
  intros. unfold make_addlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros.
  subst. exists (rs#r); split; auto.
  destruct (rs#r); simpl; auto. rewrite Int64.add_zero.  auto.
  exists (Val.addl rs#r (Vlong n)); split; auto.
Qed.

Lemma make_mullimm_correct:
  forall n r1 r2,
  rs#r2 = Vlong n ->
  let (op, args) := make_mullimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.mull rs#r1 (Vlong n)) v.
Proof.
  intros; unfold make_mullimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros. subst.
  exists (Vlong Int64.zero); split; auto. destruct (rs#r1); simpl; auto. rewrite Int64.mul_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.one; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int64.mul_one; auto.
  destruct (Int64.is_power2' n) eqn:?; intros.
  assert (Int.ltu i Int64.iwordsize' = true) by (erewrite  Int64.is_power2'_range; eauto).
  exists (Val.shll rs#r1 (Vint i)); split; auto.
  rewrite Val.shll_rolml by apply H2. auto.
  destruct (rs#r1); auto. simpl. rewrite H2.
  erewrite Int64.mul_pow2'; auto.
  econstructor ; split; auto. simpl. congruence.
Qed.

Lemma make_shllimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shllimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shll rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shllimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto.
  unfold Int64.shl'. rewrite Z.shiftl_0_r, Int64.repr_unsigned. auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; simpl.
  rewrite Val.shll_rolml by apply LT. eauto.
  econstructor; split. simpl. eauto. rewrite H; auto.
Qed.

Lemma make_shrlimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shrlimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shrl rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrlimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto.
  unfold Int64.shr'. rewrite Z.shiftr_0_r, Int64.repr_signed. auto.
  econstructor; split. simpl. eauto. rewrite H; auto.
Qed.

Lemma make_shrluimm_aux_correct:
  forall n r1,
  Int.ltu n Int64.iwordsize' = true ->
  let (op, args) := make_shrluimm_aux n r1 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shrlu rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrluimm_aux.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  - exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto.
  unfold Int64.shru'. rewrite Z.shiftr_0_r, Int64.repr_unsigned. auto.
 - rewrite Val.shrlu_rolml by apply H; auto. econstructor; split; eauto. auto.
Qed.

Lemma make_shrluimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shrluimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.shrlu rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrluimm.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; simpl.
  apply make_shrluimm_aux_correct; auto.
  rewrite H.  eauto.
Qed.

Lemma make_andlimm_correct:
  forall n r x,
  let (op, args) := make_andlimm n r x in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.andl rs#r (Vlong n)) v.
Proof.
  intros; unfold make_andlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros.
  subst n. exists (Vlong Int64.zero); split; auto. destruct (rs#r); simpl; auto. rewrite Int64.and_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int64.and_mone; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_orlimm_correct:
  forall n r,
  let (op, args) := make_orlimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.orl rs#r (Vlong n)) v.
Proof.
  intros; unfold make_orlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int64.or_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone; intros.
  subst n. exists (Vlong Int64.mone); split; auto. destruct (rs#r); simpl; auto. rewrite Int64.or_mone; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_xorlimm_correct:
  forall n r,
  let (op, args) := make_xorlimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some v /\ Val.lessdef (Val.xorl rs#r (Vlong n)) v.
Proof.
  intros; unfold make_xorlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int64.xor_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone; intros.
  subst n. exists (Val.notl rs#r); split; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_divluimm_correct:
  forall n r1 r2 v,
  Val.divlu rs#r1 rs#r2 = Some v ->
  rs#r2 = Vlong n ->
  let (op, args) := make_divluimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divluimm.
  destruct (Int64.is_power2' n) eqn:?.
  exploit Int64.is_power2'_range; eauto. intros RANGE.
  replace v with (Val.shrlu rs#r1 (Vint i)).
  apply make_shrluimm_aux_correct; auto.
  rewrite H0 in H.
  destruct (rs#r1); simpl in *; inv H. rewrite RANGE.
  destruct (Int64.eq n Int64.zero); inv H2.
  rewrite (Int64.divu_pow2' i0 n i) by auto. auto.
  exists v; auto.
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

Lemma make_divlimm_correct:
  forall n r1 r2 v,
  Val.divls rs#r1 rs#r2 = Some v ->
  rs#r2 = Vlong n ->
  let (op, args) := make_divlimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divlimm.
  destruct (Int64.is_power2' n) eqn:?. destruct (Int.ltu i (Int.repr 63)) eqn:?.
  rewrite H0 in H. econstructor; split. simpl; eauto. eapply Val.divls_pow2; eauto. auto.
  exists v; auto.
  exists v; auto.
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
  InvApproxRegs; SimplVM; inv H0.
  change (let (op', args') := make_addimm n1 r2 in
          exists w : val,
          eval_operation ge (Vptr sp Ptrofs.zero) op' rs ## args' m = Some w /\
          Val.lessdef (Val.add (Vint n1) rs#r2) w).
  rewrite Val.add_commut. apply make_addimm_correct.
  InvApproxRegs; SimplVM; inv H0. apply make_addimm_correct.
  InvApproxRegs; SimplVM; inv H0. econstructor; split; eauto. apply Val.add_lessdef; auto.
  InvApproxRegs; SimplVM; inv H0. econstructor; split; eauto. rewrite Val.add_commut. apply Val.add_lessdef; auto.
(* sub *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.sub (Vint n1) rs#r2). econstructor; split; eauto.
  InvApproxRegs; SimplVM; inv H0. rewrite Val.sub_add_opp. apply make_addimm_correct.
(* mul *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.mul (Vint n1) rs#r2). rewrite Val.mul_commut. apply make_mulimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_mulimm_correct; auto.
(* divs *)
  assert (rs#r2 = Vint n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divimm_correct; auto.
(* divu *)
  assert (rs#r2 = Vint n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divuimm_correct; auto.
(* and *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.and (Vint n1) rs#r2). rewrite Val.and_commut. apply make_andimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_andimm_correct. auto.
  inv H; inv H0. apply make_andimm_correct. auto.
(* or *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.or (Vint n1) rs#r2). rewrite Val.or_commut. apply make_orimm_correct.
  InvApproxRegs; SimplVM; inv H0. apply make_orimm_correct.
(* xor *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.xor (Vint n1) rs#r2). rewrite Val.xor_commut. apply make_xorimm_correct.
  InvApproxRegs; SimplVM; inv H0. apply make_xorimm_correct.
(* shl *)
  InvApproxRegs; SimplVM; inv H0. apply make_shlimm_correct; auto.
(* shr *)
  InvApproxRegs; SimplVM; inv H0. apply make_shrimm_correct; auto.
(* shru *)
  InvApproxRegs; SimplVM; inv H0. apply make_shruimm_correct; auto.
(* addl *)
  InvApproxRegs; SimplVM; inv H0.
  change (let (op', args') := make_addlimm n1 r2 in
          exists w : val,
          eval_operation ge (Vptr sp Ptrofs.zero) op' rs ## args' m = Some w /\
          Val.lessdef (Val.addl (Vlong n1) rs#r2) w).
  rewrite Val.addl_commut. apply make_addlimm_correct.
  InvApproxRegs; SimplVM; inv H0. apply make_addlimm_correct.
(* subl *)
  InvApproxRegs; SimplVM; inv H0.
  replace (Val.subl rs#r1 (Vlong n2)) with (Val.addl rs#r1 (Vlong (Int64.neg n2))).
  apply make_addlimm_correct; auto.
  unfold Val.addl, Val.subl. destruct Archi.ptr64 eqn:SF, rs#r1; auto.
  rewrite Int64.sub_add_opp; auto.
  rewrite Ptrofs.sub_add_opp. do 2 f_equal. auto with ptrofs.
  rewrite Int64.sub_add_opp; auto.
(* mull *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.mull (Vlong n1) rs#r2). rewrite Val.mull_commut. apply make_mullimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_mullimm_correct; auto.
(* divl *)
  assert (rs#r2 = Vlong n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divlimm_correct; auto.
(* divlu *)
  assert (rs#r2 = Vlong n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divluimm_correct; auto.
(* andl *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.andl (Vlong n1) rs#r2). rewrite Val.andl_commut. apply make_andlimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_andlimm_correct; auto.
  inv H; inv H0. apply make_andlimm_correct; auto.
(* orlimm *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.orl (Vlong n1) rs#r2). rewrite Val.orl_commut. apply make_orlimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_orlimm_correct; auto.
(* xorlimm *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.xorl (Vlong n1) rs#r2). rewrite Val.xorl_commut. apply make_xorlimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_xorlimm_correct; auto.
(* shll *)
  InvApproxRegs; SimplVM; inv H0. apply make_shllimm_correct; auto.
(* shrl *)
  InvApproxRegs; SimplVM; inv H0. apply make_shrlimm_correct; auto.
(* shrlu *)
  InvApproxRegs; SimplVM; inv H0. apply make_shrluimm_correct; auto.
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

Remark shift_symbol_address:
  forall id ofs delta,
  Genv.symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int delta)) = Val.add (Genv.symbol_address ge id ofs) (Vint delta).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id); auto.
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
- rewrite shift_symbol_address. econstructor; split; eauto. apply Val.add_lessdef; auto.
- econstructor; split; eauto.
  change (Val.lessdef (Val.add (Vint n1) rs#r2) (Genv.symbol_address ge symb (Ptrofs.add (Ptrofs.of_int n1) n2))).
  rewrite Ptrofs.add_commut. rewrite shift_symbol_address. rewrite Val.add_commut.
  apply Val.add_lessdef; auto.
- rewrite Ptrofs.add_zero_l.
  change (Vptr sp (Ptrofs.add n1 (Ptrofs.of_int n2))) with (Val.add (Vptr sp n1) (Vint n2)).
  econstructor; split; eauto. apply Val.add_lessdef; auto.
- econstructor; split; eauto.
  change (Val.lessdef (Val.add (Vint n1) rs#r2) (Vptr sp (Ptrofs.add Ptrofs.zero (Ptrofs.add (Ptrofs.of_int n1) n2)))).
  rewrite Ptrofs.add_zero_l. rewrite Ptrofs.add_commut.
  change (Val.lessdef (Val.add (Vint n1) rs#r2) (Val.add (Vptr sp n2) (Vint n1))).
  rewrite Val.add_commut. apply Val.add_lessdef; auto.
- econstructor; split; eauto. apply Val.add_lessdef; auto.
- rewrite Val.add_commut. econstructor; split; eauto. apply Val.add_lessdef; auto.
- econstructor; split; eauto.
  change (Val.lessdef (Val.add (Vint n1) rs#r2) (Val.add rs#r2 (Vint n1))).
  rewrite Val.add_commut. auto.
- econstructor; split; eauto.
- rewrite shift_symbol_address. econstructor; split; eauto.
- rewrite shift_symbol_address. econstructor; split; eauto. apply Val.add_lessdef; auto.
- rewrite Ptrofs.add_zero_l.
  change (Vptr sp (Ptrofs.add n1 (Ptrofs.of_int n))) with (Val.add (Vptr sp n1) (Vint n)).
  econstructor; split; eauto. apply Val.add_lessdef; auto.
- exists res; auto.
Qed.

End STRENGTH_REDUCTION.

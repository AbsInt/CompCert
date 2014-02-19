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
  AE.get r ae = Ptr(Gl id ofs) -> Val.lessdef rs#r (symbol_address ge id ofs).
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
  | [ H: vmatch _ ?v (Ptr(Gl ?id ?ofs)) |- _ ] =>
      let E := fresh in
      assert (E: Val.lessdef v (Op.symbol_address ge id ofs)) by (eapply vmatch_ptr_gl; eauto); 
      clear H; SimplVM
  | [ H: vmatch _ ?v (Ptr(Stk ?ofs)) |- _ ] =>
      let E := fresh in
      assert (E: Val.lessdef v (Vptr sp ofs)) by (eapply vmatch_ptr_stk; eauto); 
      clear H; SimplVM
  | _ => idtac
  end.

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
- auto.
Qed.

Lemma make_addimm_correct:
  forall n r,
  let (op, args) := make_addimm n r in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.add rs#r (Vint n)) v.
Proof.
  intros. unfold make_addimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. 
  subst. exists (rs#r); split; auto. destruct (rs#r); simpl; auto; rewrite Int.add_zero; auto.
  exists (Val.add rs#r (Vint n)); auto.
Qed.

Lemma make_shlimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shlimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.shl rs#r1 (Vint n)) v.
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
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.shr rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shr_zero. auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?.
  econstructor; split; eauto. simpl. auto.
  econstructor; split; eauto. simpl. congruence.
Qed.

Lemma make_shruimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_shruimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.shru rs#r1 (Vint n)) v.
Proof.
  intros; unfold make_shruimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (rs#r1); split; auto. destruct (rs#r1); simpl; auto. rewrite Int.shru_zero. auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; intros.
  rewrite Val.shru_rolm; auto. econstructor; split; eauto. auto. 
  econstructor; split; eauto. simpl. congruence.
Qed.

Lemma make_mulimm_correct:
  forall n r1 r2,
  rs#r2 = Vint n ->
  let (op, args) := make_mulimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.mul rs#r1 (Vint n)) v.
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
  exists w, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divimm.
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
  exists w, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divuimm.
  destruct (Int.is_power2 n) eqn:?. 
  econstructor; split. simpl; eauto.
  exploit Int.is_power2_range; eauto. intros RANGE.
  rewrite <- Val.shru_rolm; auto. rewrite H0 in H. 
  destruct (rs#r1); simpl in *; inv H. 
  destruct (Int.eq n Int.zero); inv H2.
  rewrite RANGE. rewrite (Int.divu_pow2 i0 _ _ Heqo). auto.
  exists v; auto.
Qed.

Lemma make_andimm_correct:
  forall n r x,
  vmatch bc rs#r x ->
  let (op, args) := make_andimm n r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.and rs#r (Vint n)) v.
Proof.
  intros; unfold make_andimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (Vint Int.zero); split; auto. destruct (rs#r); simpl; auto. rewrite Int.and_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.and_mone; auto.
  destruct (match x with Uns k => Int.eq (Int.zero_ext k (Int.not n)) Int.zero
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
  rewrite H5 by auto. auto. 
  econstructor; split; eauto. auto. 
Qed.

Lemma make_orimm_correct:
  forall n r,
  let (op, args) := make_orimm n r in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.or rs#r (Vint n)) v.
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
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.xor rs#r (Vint n)) v.
Proof.
  intros; unfold make_xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (rs#r); split; auto. destruct (rs#r); simpl; auto. rewrite Int.xor_zero; auto.
  econstructor; split; eauto. auto. 
Qed.

Lemma make_mulfimm_correct:
  forall n r1 r2,
  rs#r2 = Vfloat n ->
  let (op, args) := make_mulfimm n r1 r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.mulf rs#r1 rs#r2) v.
Proof.
  intros; unfold make_mulfimm. 
  destruct (Float.eq_dec n (Float.floatofint (Int.repr 2))); intros. 
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (rs#r1); simpl; auto. rewrite Float.mul2_add; auto. 
  simpl. econstructor; split; eauto. 
Qed.

Lemma make_mulfimm_correct_2:
  forall n r1 r2,
  rs#r1 = Vfloat n ->
  let (op, args) := make_mulfimm n r2 r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.mulf rs#r1 rs#r2) v.
Proof.
  intros; unfold make_mulfimm. 
  destruct (Float.eq_dec n (Float.floatofint (Int.repr 2))); intros. 
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (rs#r2); simpl; auto. rewrite Float.mul2_add; auto. 
  rewrite Float.mul_commut; auto. 
  simpl. econstructor; split; eauto. 
Qed.

Lemma make_cast8signed_correct:
  forall r x,
  vmatch bc rs#r x ->
  let (op, args) := make_cast8signed r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.sign_ext 8 rs#r) v.
Proof.
  intros; unfold make_cast8signed. destruct (vincl x (Sgn 8)) eqn:INCL. 
  exists rs#r; split; auto. 
  assert (V: vmatch bc rs#r (Sgn 8)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_sgn_sign_ext in H3 by auto. rewrite H3; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_cast16signed_correct:
  forall r x,
  vmatch bc rs#r x ->
  let (op, args) := make_cast16signed r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.sign_ext 16 rs#r) v.
Proof.
  intros; unfold make_cast16signed. destruct (vincl x (Sgn 16)) eqn:INCL. 
  exists rs#r; split; auto. 
  assert (V: vmatch bc rs#r (Sgn 16)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_sgn_sign_ext in H3 by auto. rewrite H3; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_singleoffloat_correct:
  forall r x,
  vmatch bc rs#r x ->
  let (op, args) := make_singleoffloat r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v /\ Val.lessdef (Val.singleoffloat rs#r) v.
Proof.
  intros; unfold make_singleoffloat. 
  destruct (vincl x Fsingle && generate_float_constants tt) eqn:INCL. 
  InvBooleans. exists rs#r; split; auto. 
  assert (V: vmatch bc rs#r Fsingle).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite Float.singleoffloat_of_single by auto. auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma op_strength_reduction_correct:
  forall op args vl v,
  vl = map (fun r => AE.get r ae) args ->
  eval_operation ge (Vptr sp Int.zero) op rs##args m = Some v ->
  let (op', args') := op_strength_reduction op args vl in
  exists w, eval_operation ge (Vptr sp Int.zero) op' rs##args' m = Some w /\ Val.lessdef v w.
Proof.
  intros until v; unfold op_strength_reduction;
  case (op_strength_reduction_match op args vl); simpl; intros.
(* cast8signed *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast8signed_correct; auto.
(* cast8signed *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast16signed_correct; auto.
(* add *)
  InvApproxRegs; SimplVM; inv H0. fold (Val.add (Vint n1) rs#r2). rewrite Val.add_commut. apply make_addimm_correct.
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
(* singleoffloat *)
  InvApproxRegs; SimplVM; inv H0. apply make_singleoffloat_correct; auto.
(* cmp *)
  generalize (cond_strength_reduction_correct c args0 vl0). 
  destruct (cond_strength_reduction c args0 vl0) as [c' args']; intros.
  rewrite <- H1 in H0; auto. econstructor; split; eauto.
(* mulf *)
  InvApproxRegs; SimplVM; inv H0. rewrite <- H2. apply make_mulfimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. fold (Val.mulf (Vfloat n1) rs#r2).
  rewrite <- H2. apply make_mulfimm_correct_2; auto.
(* default *)
  exists v; auto.
Qed.

Remark shift_symbol_address:
  forall symb ofs n,
  Op.symbol_address ge symb (Int.add ofs n) = Val.add (Op.symbol_address ge symb ofs) (Vint n).
Proof.
  unfold Op.symbol_address; intros. destruct (Genv.find_symbol ge symb); auto. 
Qed.

Lemma addr_strength_reduction_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing ge (Vptr sp Int.zero) addr rs##args = Some res ->
  let (addr', args') := addr_strength_reduction addr args vl in
  exists res', eval_addressing ge (Vptr sp Int.zero) addr' rs##args' = Some res' /\ Val.lessdef res res'.
Proof.
  intros until res. unfold addr_strength_reduction.
  destruct (addr_strength_reduction_match addr args vl); simpl;
  intros VL EA; InvApproxRegs; SimplVM; try (inv EA).
- rewrite shift_symbol_address. econstructor; split; eauto. apply Val.add_lessdef; auto. 
- fold (Val.add (Vint n1) rs#r2). rewrite Int.add_commut. rewrite shift_symbol_address. rewrite Val.add_commut.
  econstructor; split; eauto. apply Val.add_lessdef; auto.
- rewrite Int.add_zero_l. 
  change (Vptr sp (Int.add n1 n2)) with (Val.add (Vptr sp n1) (Vint n2)).
  econstructor; split; eauto. apply Val.add_lessdef; auto.
- fold (Val.add (Vint n1) rs#r2).  rewrite Int.add_zero_l. rewrite Int.add_commut.
  change (Vptr sp (Int.add n2 n1)) with (Val.add (Vptr sp n2) (Vint n1)).
  rewrite Val.add_commut. econstructor; split; eauto. apply Val.add_lessdef; auto.
- econstructor; split; eauto. apply Val.add_lessdef; auto. 
- rewrite Val.add_commut. econstructor; split; eauto. apply Val.add_lessdef; auto. 
- fold (Val.add (Vint n1) rs#r2).
  rewrite Val.add_commut. econstructor; split; eauto.
- econstructor; split; eauto.
- rewrite shift_symbol_address. econstructor; split; eauto. 
- rewrite shift_symbol_address. econstructor; split; eauto. apply Val.add_lessdef; auto. 
- rewrite Int.add_zero_l.  
  change (Vptr sp (Int.add n1 n)) with (Val.add (Vptr sp n1) (Vint n)).
  econstructor; split; eauto. apply Val.add_lessdef; auto.
- exists res; auto.
Qed.

End STRENGTH_REDUCTION.

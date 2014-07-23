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
Variable e: regset.
Variable m: mem.
Hypothesis MATCH: ematch bc e ae.

Lemma match_G:
  forall r id ofs,
  AE.get r ae = Ptr(Gl id ofs) -> Val.lessdef e#r (Genv.symbol_address ge id ofs).
Proof.
  intros. apply vmatch_ptr_gl with bc; auto. rewrite <- H. apply MATCH. 
Qed.

Lemma match_S:
  forall r ofs,
  AE.get r ae = Ptr(Stk ofs) -> Val.lessdef e#r (Vptr sp ofs).
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

Lemma cond_strength_reduction_correct:
  forall cond args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (cond', args') := cond_strength_reduction cond args vl in
  eval_condition cond' e##args' m = eval_condition cond e##args m.
Proof.
  intros until vl. unfold cond_strength_reduction.
  case (cond_strength_reduction_match cond args vl); simpl; intros; InvApproxRegs; SimplVM.
- apply Val.swap_cmp_bool.
- auto.
- apply Val.swap_cmpu_bool.
- auto.
- auto.
Qed.

Lemma addr_strength_reduction_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing ge (Vptr sp Int.zero) addr e##args = Some res ->
  let (addr', args') := addr_strength_reduction addr args vl in
  exists res', eval_addressing ge (Vptr sp Int.zero) addr' e##args' = Some res' /\ Val.lessdef res res'.
Proof.
  intros until res. unfold addr_strength_reduction.
  destruct (addr_strength_reduction_match addr args vl); simpl;
  intros VL EA; InvApproxRegs; SimplVM; try (inv EA).
- rewrite Genv.shift_symbol_address. econstructor; split. eauto. apply Val.add_lessdef; auto.
- econstructor; split; eauto. rewrite Int.add_zero_l.
  change (Vptr sp (Int.add n ofs)) with (Val.add (Vptr sp n) (Vint ofs)). apply Val.add_lessdef; auto.
- econstructor; split; eauto. rewrite Int.add_assoc. rewrite Genv.shift_symbol_address. 
  rewrite Val.add_assoc. apply Val.add_lessdef; auto.
- econstructor; split; eauto.
  fold (Val.add (Vint n1) e#r2). rewrite (Val.add_commut (Vint n1)).
  rewrite Genv.shift_symbol_address. apply Val.add_lessdef; auto.
  rewrite Int.add_commut. rewrite Genv.shift_symbol_address. apply Val.add_lessdef; auto. 
- econstructor; split; eauto. rewrite Int.add_zero_l. rewrite Int.add_assoc. 
  change (Vptr sp (Int.add n1 (Int.add n2 ofs)))
    with (Val.add (Vptr sp n1) (Vint (Int.add n2 ofs))).
  rewrite Val.add_assoc. apply Val.add_lessdef; auto. 
- econstructor; split; eauto. rewrite Int.add_zero_l. 
  fold (Val.add (Vint n1) e#r2). rewrite (Int.add_commut n1). 
  change (Vptr sp (Int.add (Int.add n2 n1) ofs))
    with (Val.add (Val.add (Vint n1) (Vptr sp n2)) (Vint ofs)).
  apply Val.add_lessdef; auto. apply Val.add_lessdef; auto. 
- econstructor; split; eauto. rewrite Genv.shift_symbol_address. 
  rewrite ! Val.add_assoc. apply Val.add_lessdef; auto. 
  rewrite Val.add_commut. apply Val.add_lessdef; auto. 
- econstructor; split; eauto. rewrite Genv.shift_symbol_address.
  rewrite (Val.add_commut e#r1). rewrite ! Val.add_assoc.
  apply Val.add_lessdef; auto. rewrite Val.add_commut. apply Val.add_lessdef; auto.
- fold (Val.add (Vint n1) e#r2). econstructor; split; eauto. 
  rewrite (Val.add_commut (Vint n1)). rewrite Val.add_assoc. 
  apply Val.add_lessdef; eauto. 
- econstructor; split; eauto.  rewrite ! Val.add_assoc.
  apply Val.add_lessdef; eauto. 
- econstructor; split; eauto. rewrite Int.add_assoc. 
  rewrite Genv.shift_symbol_address. apply Val.add_lessdef; auto. 
- econstructor; split; eauto. 
  rewrite Genv.shift_symbol_address. rewrite ! Val.add_assoc. apply Val.add_lessdef; auto.
  rewrite Val.add_commut; auto.
- econstructor; split; eauto.
- econstructor; split; eauto. rewrite Genv.shift_symbol_address. auto.
- econstructor; split; eauto. rewrite Genv.shift_symbol_address. rewrite Int.mul_commut; auto.
- econstructor; eauto.
Qed.

Lemma make_cmp_base_correct:
  forall c args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (op', args') := make_cmp_base c args vl in
  exists v, eval_operation ge (Vptr sp Int.zero) op' e##args' m = Some v 
         /\ Val.lessdef (Val.of_optbool (eval_condition c e##args m)) v.
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
  exists v, eval_operation ge (Vptr sp Int.zero) op' e##args' m = Some v 
         /\ Val.lessdef (Val.of_optbool (eval_condition c e##args m)) v.
Proof.
  intros c args vl.
  assert (Y: forall r, vincl (AE.get r ae) (Uns 1) = true ->
             e#r = Vundef \/ e#r = Vint Int.zero \/ e#r = Vint Int.one).
  { intros. apply vmatch_Uns_1 with bc. eapply vmatch_ge. eapply vincl_ge; eauto. apply MATCH. }
  unfold make_cmp. case (make_cmp_match c args vl); intros.
- destruct (Int.eq_dec n Int.one && vincl v1 (Uns 1)) eqn:E1.
  simpl in H; inv H. InvBooleans. subst n. 
  exists (e#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
  destruct (Int.eq_dec n Int.zero && vincl v1 (Uns 1)) eqn:E0.
  simpl in H; inv H. InvBooleans. subst n. 
  exists (Val.xor e#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
  apply make_cmp_base_correct; auto.
- destruct (Int.eq_dec n Int.zero && vincl v1 (Uns 1)) eqn:E0.
  simpl in H; inv H. InvBooleans. subst n. 
  exists (e#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
  destruct (Int.eq_dec n Int.one && vincl v1 (Uns 1)) eqn:E1.
  simpl in H; inv H. InvBooleans. subst n. 
  exists (Val.xor e#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
  apply make_cmp_base_correct; auto.
- apply make_cmp_base_correct; auto.
Qed.

Lemma make_addimm_correct:
  forall n r,
  let (op, args) := make_addimm n r in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.add e#r (Vint n)) v.
Proof.
  intros. unfold make_addimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. 
  subst. exists (e#r); split; auto. destruct (e#r); simpl; auto; rewrite Int.add_zero; auto.
  exists (Val.add e#r (Vint n)); auto.
Qed.
  
Lemma make_shlimm_correct:
  forall n r1 r2,
  e#r2 = Vint n ->
  let (op, args) := make_shlimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.shl e#r1 (Vint n)) v.
Proof.
  intros; unfold make_shlimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (e#r1); split; auto. destruct (e#r1); simpl; auto. rewrite Int.shl_zero. auto.
  destruct (Int.ltu n Int.iwordsize). 
  econstructor; split. simpl. eauto. auto.
  econstructor; split. simpl. eauto. rewrite H; auto.
Qed.

Lemma make_shrimm_correct:
  forall n r1 r2,
  e#r2 = Vint n ->
  let (op, args) := make_shrimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.shr e#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (e#r1); split; auto. destruct (e#r1); simpl; auto. rewrite Int.shr_zero. auto.
  destruct (Int.ltu n Int.iwordsize). 
  econstructor; split. simpl. eauto. auto.
  econstructor; split. simpl. eauto. rewrite H; auto.
Qed.

Lemma make_shruimm_correct:
  forall n r1 r2,
  e#r2 = Vint n ->
  let (op, args) := make_shruimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.shru e#r1 (Vint n)) v.
Proof.
  intros; unfold make_shruimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (e#r1); split; auto. destruct (e#r1); simpl; auto. rewrite Int.shru_zero. auto.
  destruct (Int.ltu n Int.iwordsize). 
  econstructor; split. simpl. eauto. auto.
  econstructor; split. simpl. eauto. rewrite H; auto.
Qed.

Lemma make_mulimm_correct:
  forall n r1,
  let (op, args) := make_mulimm n r1 in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.mul e#r1 (Vint n)) v.
Proof.
  intros; unfold make_mulimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (Vint Int.zero); split; auto. destruct (e#r1); simpl; auto. rewrite Int.mul_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.one; intros. subst.
  exists (e#r1); split; auto. destruct (e#r1); simpl; auto. rewrite Int.mul_one; auto.
  destruct (Int.is_power2 n) eqn:?; intros.
  rewrite (Val.mul_pow2 e#r1 _ _ Heqo). econstructor; split. simpl; eauto. auto.
  econstructor; split; eauto. auto. 
Qed.

Lemma make_divimm_correct:
  forall n r1 r2 v,
  Val.divs e#r1 e#r2 = Some v ->
  e#r2 = Vint n ->
  let (op, args) := make_divimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Int.zero) op e##args m = Some w /\ Val.lessdef v w.
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
  Val.divu e#r1 e#r2 = Some v ->
  e#r2 = Vint n ->
  let (op, args) := make_divuimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Int.zero) op e##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divuimm.
  destruct (Int.is_power2 n) eqn:?.
  econstructor; split. simpl; eauto. 
  rewrite H0 in H. erewrite Val.divu_pow2 by eauto. auto.
  exists v; auto.
Qed.

Lemma make_moduimm_correct:
  forall n r1 r2 v,
  Val.modu e#r1 e#r2 = Some v ->
  e#r2 = Vint n ->
  let (op, args) := make_moduimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Int.zero) op e##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_moduimm.
  destruct (Int.is_power2 n) eqn:?.
  exists v; split; auto. simpl. decEq. eapply Val.modu_pow2; eauto. congruence.
  exists v; auto.
Qed.

Lemma make_andimm_correct:
  forall n r x,
  vmatch bc e#r x ->
  let (op, args) := make_andimm n r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.and e#r (Vint n)) v.
Proof.
  intros; unfold make_andimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (Vint Int.zero); split; auto. destruct (e#r); simpl; auto. rewrite Int.and_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (e#r); split; auto. destruct (e#r); simpl; auto. rewrite Int.and_mone; auto.
  destruct (match x with Uns k => Int.eq (Int.zero_ext k (Int.not n)) Int.zero
                       | _ => false end) eqn:UNS.
  destruct x; try congruence. 
  exists (e#r); split; auto.
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
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.or e#r (Vint n)) v.
Proof.
  intros; unfold make_orimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (e#r); split; auto. destruct (e#r); simpl; auto. rewrite Int.or_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (Vint Int.mone); split; auto. destruct (e#r); simpl; auto. rewrite Int.or_mone; auto.
  econstructor; split; eauto. auto. 
Qed.

Lemma make_xorimm_correct:
  forall n r,
  let (op, args) := make_xorimm n r in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.xor e#r (Vint n)) v.
Proof.
  intros; unfold make_xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (e#r); split; auto. destruct (e#r); simpl; auto. rewrite Int.xor_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (Val.notint e#r); split; auto. 
  econstructor; split; eauto. auto. 
Qed.

Lemma make_mulfimm_correct:
  forall n r1 r2,
  e#r2 = Vfloat n ->
  let (op, args) := make_mulfimm n r1 r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.mulf e#r1 e#r2) v.
Proof.
  intros; unfold make_mulfimm. 
  destruct (Float.eq_dec n (Float.of_int (Int.repr 2))); intros. 
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (e#r1); simpl; auto. rewrite Float.mul2_add; auto. 
  simpl. econstructor; split; eauto. 
Qed.

Lemma make_mulfimm_correct_2:
  forall n r1 r2,
  e#r1 = Vfloat n ->
  let (op, args) := make_mulfimm n r2 r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.mulf e#r1 e#r2) v.
Proof.
  intros; unfold make_mulfimm. 
  destruct (Float.eq_dec n (Float.of_int (Int.repr 2))); intros. 
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (e#r2); simpl; auto. rewrite Float.mul2_add; auto. 
  rewrite Float.mul_commut; auto. 
  simpl. econstructor; split; eauto. 
Qed.

Lemma make_mulfsimm_correct:
  forall n r1 r2,
  e#r2 = Vsingle n ->
  let (op, args) := make_mulfsimm n r1 r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.mulfs e#r1 e#r2) v.
Proof.
  intros; unfold make_mulfsimm. 
  destruct (Float32.eq_dec n (Float32.of_int (Int.repr 2))); intros. 
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (e#r1); simpl; auto. rewrite Float32.mul2_add; auto. 
  simpl. econstructor; split; eauto. 
Qed.

Lemma make_mulfsimm_correct_2:
  forall n r1 r2,
  e#r1 = Vsingle n ->
  let (op, args) := make_mulfsimm n r2 r1 r2 in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.mulfs e#r1 e#r2) v.
Proof.
  intros; unfold make_mulfsimm. 
  destruct (Float32.eq_dec n (Float32.of_int (Int.repr 2))); intros. 
  simpl. econstructor; split. eauto. rewrite H; subst n.
  destruct (e#r2); simpl; auto. rewrite Float32.mul2_add; auto. 
  rewrite Float32.mul_commut; auto. 
  simpl. econstructor; split; eauto. 
Qed.

Lemma make_cast8signed_correct:
  forall r x,
  vmatch bc e#r x ->
  let (op, args) := make_cast8signed r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.sign_ext 8 e#r) v.
Proof.
  intros; unfold make_cast8signed. destruct (vincl x (Sgn 8)) eqn:INCL. 
  exists e#r; split; auto. 
  assert (V: vmatch bc e#r (Sgn 8)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_sgn_sign_ext in H3 by auto. rewrite H3; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_cast8unsigned_correct:
  forall r x,
  vmatch bc e#r x ->
  let (op, args) := make_cast8unsigned r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.zero_ext 8 e#r) v.
Proof.
  intros; unfold make_cast8unsigned. destruct (vincl x (Uns 8)) eqn:INCL. 
  exists e#r; split; auto. 
  assert (V: vmatch bc e#r (Uns 8)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_uns_zero_ext in H3 by auto. rewrite H3; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_cast16signed_correct:
  forall r x,
  vmatch bc e#r x ->
  let (op, args) := make_cast16signed r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.sign_ext 16 e#r) v.
Proof.
  intros; unfold make_cast16signed. destruct (vincl x (Sgn 16)) eqn:INCL. 
  exists e#r; split; auto. 
  assert (V: vmatch bc e#r (Sgn 16)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_sgn_sign_ext in H3 by auto. rewrite H3; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_cast16unsigned_correct:
  forall r x,
  vmatch bc e#r x ->
  let (op, args) := make_cast16unsigned r x in
  exists v, eval_operation ge (Vptr sp Int.zero) op e##args m = Some v /\ Val.lessdef (Val.zero_ext 16 e#r) v.
Proof.
  intros; unfold make_cast16unsigned. destruct (vincl x (Uns 16)) eqn:INCL. 
  exists e#r; split; auto. 
  assert (V: vmatch bc e#r (Uns 16)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_uns_zero_ext in H3 by auto. rewrite H3; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma op_strength_reduction_correct:
  forall op args vl v,
  vl = map (fun r => AE.get r ae) args ->
  eval_operation ge (Vptr sp Int.zero) op e##args m = Some v ->
  let (op', args') := op_strength_reduction op args vl in
  exists w, eval_operation ge (Vptr sp Int.zero) op' e##args' m = Some w /\ Val.lessdef v w.
Proof.
  intros until v; unfold op_strength_reduction;
  case (op_strength_reduction_match op args vl); simpl; intros.
(* cast8signed *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast8signed_correct; auto.
(* cast8unsigned *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast8unsigned_correct; auto.
(* cast16signed *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast16signed_correct; auto.
(* cast16unsigned *)
  InvApproxRegs; SimplVM; inv H0. apply make_cast16unsigned_correct; auto.
(* sub *)
  InvApproxRegs; SimplVM; inv H0. rewrite Val.sub_add_opp. apply make_addimm_correct; auto. 
(* mul *)
  rewrite Val.mul_commut in H0. InvApproxRegs; SimplVM; inv H0. apply make_mulimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_mulimm_correct; auto.
(* divs *) 
  assert (e#r2 = Vint n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divimm_correct; auto.
(* divu *) 
  assert (e#r2 = Vint n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divuimm_correct; auto.
(* modu *) 
  assert (e#r2 = Vint n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_moduimm_correct; auto.
(* and *)
  rewrite Val.and_commut in H0. InvApproxRegs; SimplVM; inv H0. apply make_andimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_andimm_correct; auto.
  inv H; inv H0. apply make_andimm_correct; auto.
(* or *)
  rewrite Val.or_commut in H0. InvApproxRegs; SimplVM; inv H0. apply make_orimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_orimm_correct; auto.
(* xor *)
  rewrite Val.xor_commut in H0. InvApproxRegs; SimplVM; inv H0. apply make_xorimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_xorimm_correct; auto.
(* shl *)
  InvApproxRegs; SimplVM; inv H0. apply make_shlimm_correct; auto.
(* shr *)
  InvApproxRegs; SimplVM; inv H0. apply make_shrimm_correct; auto.
(* shru *)
  InvApproxRegs; SimplVM; inv H0. apply make_shruimm_correct; auto.
(* lea *)
  exploit addr_strength_reduction_correct; eauto. 
  destruct (addr_strength_reduction addr args0 vl0) as [addr' args'].
  auto.
(* cond *)
  inv H0. apply make_cmp_correct; auto.
(* mulf *)
  InvApproxRegs; SimplVM; inv H0. rewrite <- H2. apply make_mulfimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. fold (Val.mulf (Vfloat n1) e#r2).
  rewrite <- H2. apply make_mulfimm_correct_2; auto.
(* mulfs *)
  InvApproxRegs; SimplVM; inv H0. rewrite <- H2. apply make_mulfsimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. fold (Val.mulfs (Vsingle n1) e#r2).
  rewrite <- H2. apply make_mulfsimm_correct_2; auto.
(* default *)
  exists v; auto.
Qed.

End STRENGTH_REDUCTION.

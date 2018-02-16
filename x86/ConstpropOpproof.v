(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
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

Lemma eval_Olea_ptr:
  forall a el,
  eval_operation ge (Vptr sp Ptrofs.zero) (Olea_ptr a) el m = eval_addressing ge (Vptr sp Ptrofs.zero) a el.
Proof.
  unfold Olea_ptr, eval_addressing; intros. destruct Archi.ptr64; auto.
Qed.

Lemma const_for_result_correct:
  forall a op v,
  const_for_result a = Some op ->
  vmatch bc v a ->
  exists v', eval_operation ge (Vptr sp Ptrofs.zero) op nil m = Some v' /\ Val.lessdef v v'.
Proof.
  unfold const_for_result. generalize Archi.ptr64; intros ptr64; intros.
  destruct a; inv H; SimplVM.
- (* integer *)
  exists (Vint n); auto.
- (* long *)
  destruct ptr64; inv H2. exists (Vlong n); auto.
- (* float *)
  destruct (Compopts.generate_float_constants tt); inv H2. exists (Vfloat f); auto.
- (* single *)
  destruct (Compopts.generate_float_constants tt); inv H2. exists (Vsingle f); auto.
- (* pointer *)
  destruct p; try discriminate; SimplVM.
  + (* global *)
    destruct (symbol_is_external id).
  * revert H2; predSpec Ptrofs.eq Ptrofs.eq_spec ofs Ptrofs.zero; intros EQ; inv EQ.
    exists (Genv.symbol_address ge id Ptrofs.zero); auto.
  * inv H2. exists (Genv.symbol_address ge id ofs); split.
    rewrite eval_Olea_ptr. apply eval_addressing_Aglobal.
    auto.
  + (* stack *)
    inv H2. exists (Vptr sp ofs); split.
    rewrite eval_Olea_ptr. rewrite eval_addressing_Ainstack.
    simpl. rewrite Ptrofs.add_zero_l; auto.
    auto.
Qed.

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
- apply Val.swap_cmpl_bool.
- auto.
- apply Val.swap_cmplu_bool.
- auto.
- auto.
Qed.

Lemma addr_strength_reduction_32_generic_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing32 ge (Vptr sp Ptrofs.zero) addr e##args = Some res ->
  let (addr', args') := addr_strength_reduction_32_generic addr args vl in
  exists res', eval_addressing32 ge (Vptr sp Ptrofs.zero) addr' e##args' = Some res' /\ Val.lessdef res res'.
Proof.
Local Opaque Val.add.
  assert (A: forall x y, Int.repr (Int.signed x + y) = Int.add x (Int.repr y)).
  { intros; apply Int.eqm_samerepr; auto using Int.eqm_signed_unsigned with ints. }
  assert (B: forall x y z, Int.repr (Int.signed x * y + z) = Int.add (Int.mul x (Int.repr y)) (Int.repr z)).
  { intros; apply Int.eqm_samerepr; apply Int.eqm_add; auto with ints.
    unfold Int.mul; auto using Int.eqm_signed_unsigned with ints. }
  intros until res; intros VL EA.
  unfold addr_strength_reduction_32_generic; destruct (addr_strength_reduction_32_generic_match addr args vl);
  simpl in *; InvApproxRegs; SimplVM; try (inv EA).
- econstructor; split; eauto. rewrite A, Val.add_assoc, Val.add_permut. auto.
- econstructor; split; eauto. rewrite A, Val.add_assoc. auto.
- Local Transparent Val.add.
  econstructor; split; eauto. simpl. rewrite B. auto.
- econstructor; split; eauto. rewrite A, Val.add_permut. auto.
- exists res; auto.
Qed.

Lemma addr_strength_reduction_32_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing32 ge (Vptr sp Ptrofs.zero) addr e##args = Some res ->
  let (addr', args') := addr_strength_reduction_32 addr args vl in
  exists res', eval_addressing32 ge (Vptr sp Ptrofs.zero) addr' e##args' = Some res' /\ Val.lessdef res res'.
Proof.
  intros until res; intros VL EA. unfold addr_strength_reduction_32.
  destruct Archi.ptr64 eqn:SF. apply addr_strength_reduction_32_generic_correct; auto.
  assert (A: forall n, Ptrofs.of_int (Int.repr n) = Ptrofs.repr n) by auto with ptrofs.
  assert (B: forall symb ofs n,
             Genv.symbol_address ge symb (Ptrofs.add ofs (Ptrofs.repr n)) =
             Val.add (Genv.symbol_address ge symb ofs) (Vint (Int.repr n))).
  { intros. rewrite <- A. apply Genv.shift_symbol_address_32; auto. }
Local Opaque Val.add.
  destruct (addr_strength_reduction_32_match addr args vl);
  simpl in *; InvApproxRegs; SimplVM; FuncInv; subst; rewrite ?SF.
- econstructor; split; eauto. rewrite B. apply Val.add_lessdef; auto.
- econstructor; split; eauto. rewrite Ptrofs.add_zero_l.
Local Transparent Val.add.
  inv H0; auto. rewrite H2. simpl; rewrite SF, A. auto.
- econstructor; split; eauto.
  unfold Ptrofs.add at 2. rewrite B.
  fold (Ptrofs.add n1 (Ptrofs.of_int n2)).
  rewrite Genv.shift_symbol_address_32 by auto.
  rewrite ! Val.add_assoc. apply Val.add_lessdef; auto.
- econstructor; split; eauto.
  unfold Ptrofs.add at 2. rewrite B.
  fold (Ptrofs.add n2 (Ptrofs.of_int n1)).
  rewrite Genv.shift_symbol_address_32 by auto.
  rewrite ! Val.add_assoc. rewrite Val.add_permut. apply Val.add_lessdef; auto.
- econstructor; split; eauto. rewrite Ptrofs.add_zero_l. rewrite Val.add_assoc.
  eapply Val.lessdef_trans. apply Val.add_lessdef; eauto.
  simpl. rewrite SF. rewrite Ptrofs.add_assoc. apply Val.lessdef_same; do 3 f_equal. auto with ptrofs.
- econstructor; split; eauto. rewrite Ptrofs.add_zero_l. rewrite Val.add_assoc, Val.add_permut.
  eapply Val.lessdef_trans. apply Val.add_lessdef; eauto.
  simpl. rewrite SF. rewrite <- (Ptrofs.add_commut n2). rewrite Ptrofs.add_assoc.
  apply Val.lessdef_same; do 3 f_equal. auto with ptrofs.
- econstructor; split; eauto. rewrite B. rewrite ! Val.add_assoc. rewrite (Val.add_commut (Vint (Int.repr ofs))).
  apply Val.add_lessdef; auto.
- econstructor; split; eauto. rewrite B. rewrite (Val.add_commut e#r1). rewrite ! Val.add_assoc.
  rewrite (Val.add_commut (Vint (Int.repr ofs))). apply Val.add_lessdef; auto.
- econstructor; split; eauto. rewrite B. rewrite Genv.shift_symbol_address_32 by auto.
  rewrite ! Val.add_assoc. apply Val.add_lessdef; auto.
- econstructor; split; eauto. rewrite B. rewrite ! Val.add_assoc.
  rewrite (Val.add_commut (Vint (Int.repr ofs))). apply Val.add_lessdef; auto.
- econstructor; split; eauto.
  rewrite Genv.shift_symbol_address_32 by auto. auto.
- econstructor; split; eauto.
  rewrite Genv.shift_symbol_address_32 by auto. auto.
- apply addr_strength_reduction_32_generic_correct; auto.
Qed.

Lemma addr_strength_reduction_64_generic_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing64 ge (Vptr sp Ptrofs.zero) addr e##args = Some res ->
  let (addr', args') := addr_strength_reduction_64_generic addr args vl in
  exists res', eval_addressing64 ge (Vptr sp Ptrofs.zero) addr' e##args' = Some res' /\ Val.lessdef res res'.
Proof.
Local Opaque Val.addl.
  assert (A: forall x y, Int64.repr (Int64.signed x + y) = Int64.add x (Int64.repr y)).
  { intros; apply Int64.eqm_samerepr; auto using Int64.eqm_signed_unsigned with ints. }
  assert (B: forall x y z, Int64.repr (Int64.signed x * y + z) = Int64.add (Int64.mul x (Int64.repr y)) (Int64.repr z)).
  { intros; apply Int64.eqm_samerepr; apply Int64.eqm_add; auto with ints.
    unfold Int64.mul; auto using Int64.eqm_signed_unsigned with ints. }
  intros until res; intros VL EA.
  unfold addr_strength_reduction_64_generic; destruct (addr_strength_reduction_64_generic_match addr args vl);
  simpl in *; InvApproxRegs; SimplVM; try (inv EA).
- econstructor; split; eauto. rewrite A, Val.addl_assoc, Val.addl_permut. auto.
- econstructor; split; eauto. rewrite A, Val.addl_assoc. auto.
- Local Transparent Val.addl.
  econstructor; split; eauto. simpl. rewrite B. auto.
- econstructor; split; eauto. rewrite A, Val.addl_permut. auto.
- exists res; auto.
Qed.

Lemma addr_strength_reduction_64_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing64 ge (Vptr sp Ptrofs.zero) addr e##args = Some res ->
  let (addr', args') := addr_strength_reduction_64 addr args vl in
  exists res', eval_addressing64 ge (Vptr sp Ptrofs.zero) addr' e##args' = Some res' /\ Val.lessdef res res'.
Proof.
  intros until res; intros VL EA. unfold addr_strength_reduction_64.
  destruct (negb Archi.ptr64) eqn:SF. apply addr_strength_reduction_64_generic_correct; auto.
  rewrite negb_false_iff in SF.
  assert (A: forall n, Ptrofs.of_int64 (Int64.repr n) = Ptrofs.repr n) by auto with ptrofs.
  assert (B: forall symb ofs n,
             Genv.symbol_address ge symb (Ptrofs.add ofs (Ptrofs.repr n)) =
             Val.addl (Genv.symbol_address ge symb ofs) (Vlong (Int64.repr n))).
  { intros. rewrite <- A. apply Genv.shift_symbol_address_64; auto. }
Local Opaque Val.addl.
  destruct (addr_strength_reduction_64_match addr args vl);
  simpl in *; InvApproxRegs; SimplVM; FuncInv; subst; rewrite ?SF.
- econstructor; split; eauto. rewrite B. apply Val.addl_lessdef; auto.
- econstructor; split; eauto. rewrite Ptrofs.add_zero_l.
Local Transparent Val.addl.
  inv H0; auto. rewrite H2. simpl; rewrite SF, A. auto.
- econstructor; split; eauto.
  unfold Ptrofs.add at 2. rewrite B.
  fold (Ptrofs.add n1 (Ptrofs.of_int64 n2)).
  rewrite Genv.shift_symbol_address_64 by auto.
  rewrite ! Val.addl_assoc. apply Val.addl_lessdef; auto.
- econstructor; split; eauto.
  unfold Ptrofs.add at 2. rewrite B.
  fold (Ptrofs.add n2 (Ptrofs.of_int64 n1)).
  rewrite Genv.shift_symbol_address_64 by auto.
  rewrite ! Val.addl_assoc. rewrite Val.addl_permut. apply Val.addl_lessdef; auto.
- econstructor; split; eauto. rewrite Ptrofs.add_zero_l. rewrite Val.addl_assoc.
  eapply Val.lessdef_trans. apply Val.addl_lessdef; eauto.
  simpl. rewrite SF. rewrite Ptrofs.add_assoc. apply Val.lessdef_same; do 3 f_equal. auto with ptrofs.
- econstructor; split; eauto. rewrite Ptrofs.add_zero_l. rewrite Val.addl_assoc, Val.addl_permut.
  eapply Val.lessdef_trans. apply Val.addl_lessdef; eauto.
  simpl. rewrite SF. rewrite <- (Ptrofs.add_commut n2). rewrite Ptrofs.add_assoc.
  apply Val.lessdef_same; do 3 f_equal. auto with ptrofs.
- econstructor; split; eauto. rewrite B. rewrite Genv.shift_symbol_address_64 by auto.
  rewrite ! Val.addl_assoc. apply Val.addl_lessdef; auto.
- apply addr_strength_reduction_64_generic_correct; auto.
Qed.

Lemma addr_strength_reduction_correct:
  forall addr args vl res,
  vl = map (fun r => AE.get r ae) args ->
  eval_addressing ge (Vptr sp Ptrofs.zero) addr e##args = Some res ->
  let (addr', args') := addr_strength_reduction addr args vl in
  exists res', eval_addressing ge (Vptr sp Ptrofs.zero) addr' e##args' = Some res' /\ Val.lessdef res res'.
Proof.
  intros until res. unfold addr_strength_reduction.
  set (aa := if Archi.ptr64
         then addr_strength_reduction_64 addr args vl
         else addr_strength_reduction_32 addr args vl).
  intros.
  destruct (addressing_valid (fst aa)).
- unfold aa, eval_addressing in *. destruct Archi.ptr64.
+ apply addr_strength_reduction_64_correct; auto.
+ apply addr_strength_reduction_32_correct; auto.
- exists res; auto.
Qed.

Lemma make_cmp_base_correct:
  forall c args vl,
  vl = map (fun r => AE.get r ae) args ->
  let (op', args') := make_cmp_base c args vl in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op' e##args' m = Some v
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op' e##args' m = Some v
         /\ Val.lessdef (Val.of_optbool (eval_condition c e##args m)) v.
Proof.
  intros c args vl.
  assert (Y: forall r, vincl (AE.get r ae) (Uns Ptop 1) = true ->
             e#r = Vundef \/ e#r = Vint Int.zero \/ e#r = Vint Int.one).
  { intros. apply vmatch_Uns_1 with bc Ptop. eapply vmatch_ge. eapply vincl_ge; eauto. apply MATCH. }
  unfold make_cmp. case (make_cmp_match c args vl); intros.
- unfold make_cmp_imm_eq.
  destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (e#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor e#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- unfold make_cmp_imm_ne.
  destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (e#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor e#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- unfold make_cmp_imm_eq.
  destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (e#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor e#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- unfold make_cmp_imm_ne.
  destruct (Int.eq_dec n Int.zero && vincl v1 (Uns Ptop 1)) eqn:E0.
+ simpl in H; inv H. InvBooleans. subst n.
  exists (e#r1); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
+ destruct (Int.eq_dec n Int.one && vincl v1 (Uns Ptop 1)) eqn:E1.
* simpl in H; inv H. InvBooleans. subst n.
  exists (Val.xor e#r1 (Vint Int.one)); split; auto. simpl.
  exploit Y; eauto. intros [A | [A | A]]; rewrite A; simpl; auto.
* apply make_cmp_base_correct; auto.
- apply make_cmp_base_correct; auto.
Qed.

Lemma make_addimm_correct:
  forall n r,
  let (op, args) := make_addimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.add e#r (Vint n)) v.
Proof.
  intros. unfold make_addimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst. exists (e#r); split; auto.
  destruct (e#r); simpl; auto; rewrite ?Int.add_zero, ?Ptrofs.add_zero; auto.
  exists (Val.add e#r (Vint n)); split; auto. simpl. rewrite Int.repr_signed; auto.
Qed.

Lemma make_shlimm_correct:
  forall n r1 r2,
  e#r2 = Vint n ->
  let (op, args) := make_shlimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.shl e#r1 (Vint n)) v.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.shr e#r1 (Vint n)) v.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.shru e#r1 (Vint n)) v.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.mul e#r1 (Vint n)) v.
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
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divimm.
  predSpec Int.eq Int.eq_spec n Int.one; intros. subst. rewrite H0 in H.
  destruct (e#r1) eqn:?;
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
  Val.divu e#r1 e#r2 = Some v ->
  e#r2 = Vint n ->
  let (op, args) := make_divuimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divuimm.
  predSpec Int.eq Int.eq_spec n Int.one; intros. subst. rewrite H0 in H.
  destruct (e#r1) eqn:?;
    try (rewrite Val.divu_one in H; exists (Vint i); split; simpl; try rewrite Heqv0; auto);
    inv H; auto.
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
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some w /\ Val.lessdef v w.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.and e#r (Vint n)) v.
Proof.
  intros; unfold make_andimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (Vint Int.zero); split; auto. destruct (e#r); simpl; auto. rewrite Int.and_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (e#r); split; auto. destruct (e#r); simpl; auto. rewrite Int.and_mone; auto.
  destruct (match x with Uns _ k => Int.eq (Int.zero_ext k (Int.not n)) Int.zero
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
  rewrite H6 by auto. auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_orimm_correct:
  forall n r,
  let (op, args) := make_orimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.or e#r (Vint n)) v.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.xor e#r (Vint n)) v.
Proof.
  intros; unfold make_xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros.
  subst n. exists (e#r); split; auto. destruct (e#r); simpl; auto. rewrite Int.xor_zero; auto.
  predSpec Int.eq Int.eq_spec n Int.mone; intros.
  subst n. exists (Val.notint e#r); split; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_addlimm_correct:
  forall n r,
  let (op, args) := make_addlimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.addl e#r (Vlong n)) v.
Proof.
  intros. unfold make_addlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros.
  subst. exists (e#r); split; auto.
  destruct (e#r); simpl; auto; rewrite ? Int64.add_zero, ? Ptrofs.add_zero; auto.
  exists (Val.addl e#r (Vlong n)); split; auto. simpl. rewrite Int64.repr_signed; auto.
Qed.

Lemma make_shllimm_correct:
  forall n r1 r2,
  e#r2 = Vint n ->
  let (op, args) := make_shllimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.shll e#r1 (Vint n)) v.
Proof.
  intros; unfold make_shllimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (e#r1); split; auto. destruct (e#r1); simpl; auto.
  unfold Int64.shl'. rewrite Z.shiftl_0_r, Int64.repr_unsigned. auto.
  destruct (Int.ltu n Int64.iwordsize').
  econstructor; split. simpl. eauto. auto.
  econstructor; split. simpl. eauto. rewrite H; auto.
Qed.

Lemma make_shrlimm_correct:
  forall n r1 r2,
  e#r2 = Vint n ->
  let (op, args) := make_shrlimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.shrl e#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrlimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (e#r1); split; auto. destruct (e#r1); simpl; auto.
  unfold Int64.shr'. rewrite Z.shiftr_0_r, Int64.repr_signed. auto.
  destruct (Int.ltu n Int64.iwordsize').
  econstructor; split. simpl. eauto. auto.
  econstructor; split. simpl. eauto. rewrite H; auto.
Qed.

Lemma make_shrluimm_correct:
  forall n r1 r2,
  e#r2 = Vint n ->
  let (op, args) := make_shrluimm n r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.shrlu e#r1 (Vint n)) v.
Proof.
  intros; unfold make_shrluimm.
  predSpec Int.eq Int.eq_spec n Int.zero; intros. subst.
  exists (e#r1); split; auto. destruct (e#r1); simpl; auto.
  unfold Int64.shru'. rewrite Z.shiftr_0_r, Int64.repr_unsigned. auto.
  destruct (Int.ltu n Int64.iwordsize').
  econstructor; split. simpl. eauto. auto.
  econstructor; split. simpl. eauto. rewrite H; auto.
Qed.

Lemma make_mullimm_correct:
  forall n r1,
  let (op, args) := make_mullimm n r1 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.mull e#r1 (Vlong n)) v.
Proof.
  intros; unfold make_mullimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros. subst.
  exists (Vlong Int64.zero); split; auto. destruct (e#r1); simpl; auto. rewrite Int64.mul_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.one; intros. subst.
  exists (e#r1); split; auto. destruct (e#r1); simpl; auto. rewrite Int64.mul_one; auto.
  destruct (Int64.is_power2' n) eqn:?; intros.
  exists (Val.shll e#r1 (Vint i)); split; auto.
  destruct (e#r1); simpl; auto.
  erewrite Int64.is_power2'_range by eauto.
  erewrite Int64.mul_pow2' by eauto. auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_divlimm_correct:
  forall n r1 r2 v,
  Val.divls e#r1 e#r2 = Some v ->
  e#r2 = Vlong n ->
  let (op, args) := make_divlimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divlimm.
  destruct (Int64.is_power2' n) eqn:?. destruct (Int.ltu i (Int.repr 63)) eqn:?.
  rewrite H0 in H. econstructor; split. simpl; eauto. eapply Val.divls_pow2; eauto. auto.
  exists v; auto.
  exists v; auto.
Qed.

Lemma make_divluimm_correct:
  forall n r1 r2 v,
  Val.divlu e#r1 e#r2 = Some v ->
  e#r2 = Vlong n ->
  let (op, args) := make_divluimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_divluimm.
  destruct (Int64.is_power2' n) eqn:?.
  econstructor; split. simpl; eauto.
  rewrite H0 in H. destruct (e#r1); inv H. destruct (Int64.eq n Int64.zero); inv H2.
  simpl.
  erewrite Int64.is_power2'_range by eauto.
  erewrite Int64.divu_pow2' by eauto.  auto.
  exists v; auto.
Qed.

Lemma make_modluimm_correct:
  forall n r1 r2 v,
  Val.modlu e#r1 e#r2 = Some v ->
  e#r2 = Vlong n ->
  let (op, args) := make_modluimm n r1 r2 in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some w /\ Val.lessdef v w.
Proof.
  intros; unfold make_modluimm.
  destruct (Int64.is_power2 n) eqn:?.
  exists v; split; auto. simpl. decEq.
  rewrite H0 in H. destruct (e#r1); inv H. destruct (Int64.eq n Int64.zero); inv H2.
  simpl. erewrite Int64.modu_and by eauto. auto.
  exists v; auto.
Qed.

Lemma make_andlimm_correct:
  forall n r x,
  let (op, args) := make_andlimm n r x in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.andl e#r (Vlong n)) v.
Proof.
  intros; unfold make_andlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros.
  subst n. exists (Vlong Int64.zero); split; auto. destruct (e#r); simpl; auto. rewrite Int64.and_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone; intros.
  subst n. exists (e#r); split; auto. destruct (e#r); simpl; auto. rewrite Int64.and_mone; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_orlimm_correct:
  forall n r,
  let (op, args) := make_orlimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.orl e#r (Vlong n)) v.
Proof.
  intros; unfold make_orlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros.
  subst n. exists (e#r); split; auto. destruct (e#r); simpl; auto. rewrite Int64.or_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone; intros.
  subst n. exists (Vlong Int64.mone); split; auto. destruct (e#r); simpl; auto. rewrite Int64.or_mone; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_xorlimm_correct:
  forall n r,
  let (op, args) := make_xorlimm n r in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.xorl e#r (Vlong n)) v.
Proof.
  intros; unfold make_xorlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero; intros.
  subst n. exists (e#r); split; auto. destruct (e#r); simpl; auto. rewrite Int64.xor_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone; intros.
  subst n. exists (Val.notl e#r); split; auto.
  econstructor; split; eauto. auto.
Qed.

Lemma make_mulfimm_correct:
  forall n r1 r2,
  e#r2 = Vfloat n ->
  let (op, args) := make_mulfimm n r1 r1 r2 in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.mulf e#r1 e#r2) v.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.mulf e#r1 e#r2) v.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.mulfs e#r1 e#r2) v.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.mulfs e#r1 e#r2) v.
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
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.sign_ext 8 e#r) v.
Proof.
  intros; unfold make_cast8signed. destruct (vincl x (Sgn Ptop 8)) eqn:INCL.
  exists e#r; split; auto.
  assert (V: vmatch bc e#r (Sgn Ptop 8)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_sgn_sign_ext in H4 by auto. rewrite H4; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_cast8unsigned_correct:
  forall r x,
  vmatch bc e#r x ->
  let (op, args) := make_cast8unsigned r x in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.zero_ext 8 e#r) v.
Proof.
  intros; unfold make_cast8unsigned. destruct (vincl x (Uns Ptop 8)) eqn:INCL.
  exists e#r; split; auto.
  assert (V: vmatch bc e#r (Uns Ptop 8)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_uns_zero_ext in H4 by auto. rewrite H4; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_cast16signed_correct:
  forall r x,
  vmatch bc e#r x ->
  let (op, args) := make_cast16signed r x in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.sign_ext 16 e#r) v.
Proof.
  intros; unfold make_cast16signed. destruct (vincl x (Sgn Ptop 16)) eqn:INCL.
  exists e#r; split; auto.
  assert (V: vmatch bc e#r (Sgn Ptop 16)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_sgn_sign_ext in H4 by auto. rewrite H4; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma make_cast16unsigned_correct:
  forall r x,
  vmatch bc e#r x ->
  let (op, args) := make_cast16unsigned r x in
  exists v, eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v /\ Val.lessdef (Val.zero_ext 16 e#r) v.
Proof.
  intros; unfold make_cast16unsigned. destruct (vincl x (Uns Ptop 16)) eqn:INCL.
  exists e#r; split; auto.
  assert (V: vmatch bc e#r (Uns Ptop 16)).
  { eapply vmatch_ge; eauto. apply vincl_ge; auto. }
  inv V; simpl; auto. rewrite is_uns_zero_ext in H4 by auto. rewrite H4; auto.
  econstructor; split; simpl; eauto.
Qed.

Lemma op_strength_reduction_correct:
  forall op args vl v,
  vl = map (fun r => AE.get r ae) args ->
  eval_operation ge (Vptr sp Ptrofs.zero) op e##args m = Some v ->
  let (op', args') := op_strength_reduction op args vl in
  exists w, eval_operation ge (Vptr sp Ptrofs.zero) op' e##args' m = Some w /\ Val.lessdef v w.
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
  exploit addr_strength_reduction_32_correct; eauto.
  destruct (addr_strength_reduction_32 addr args0 vl0) as [addr' args'].
  auto.
(* subl *)
  InvApproxRegs; SimplVM; inv H0.
  replace (Val.subl e#r1 (Vlong n2)) with (Val.addl e#r1 (Vlong (Int64.neg n2))).
  apply make_addlimm_correct; auto.
  unfold Val.addl, Val.subl. destruct Archi.ptr64 eqn:SF, e#r1; auto.
  rewrite Int64.sub_add_opp; auto.
  rewrite Ptrofs.sub_add_opp. do 2 f_equal. auto with ptrofs.
  rewrite Int64.sub_add_opp; auto.
(* mull *)
  rewrite Val.mull_commut in H0. InvApproxRegs; SimplVM; inv H0. apply make_mullimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_mullimm_correct; auto.
(* divl *)
  assert (e#r2 = Vlong n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divlimm_correct; auto.
(* divlu *)
  assert (e#r2 = Vlong n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_divluimm_correct; auto.
(* modlu *)
  assert (e#r2 = Vlong n2). clear H0. InvApproxRegs; SimplVM; auto.
  apply make_modluimm_correct; auto.
(* andl *)
  rewrite Val.andl_commut in H0. InvApproxRegs; SimplVM; inv H0. apply make_andlimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_andlimm_correct; auto.
  inv H; inv H0. apply make_andlimm_correct; auto.
(* orl *)
  rewrite Val.orl_commut in H0. InvApproxRegs; SimplVM; inv H0. apply make_orlimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_orlimm_correct; auto.
(* xorl *)
  rewrite Val.xorl_commut in H0. InvApproxRegs; SimplVM; inv H0. apply make_xorlimm_correct; auto.
  InvApproxRegs; SimplVM; inv H0. apply make_xorlimm_correct; auto.
(* shll *)
  InvApproxRegs; SimplVM; inv H0. apply make_shllimm_correct; auto.
(* shrl *)
  InvApproxRegs; SimplVM; inv H0. apply make_shrlimm_correct; auto.
(* shrlu *)
  InvApproxRegs; SimplVM; inv H0. apply make_shrluimm_correct; auto.
(* leal *)
  exploit addr_strength_reduction_64_correct; eauto.
  destruct (addr_strength_reduction_64 addr args0 vl0) as [addr' args'].
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

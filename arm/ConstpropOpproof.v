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
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import ConstpropOp.
Require Import Constprop.

(** * Correctness of the static analysis *)

Section ANALYSIS.

Variable ge: genv.

(** We first show that the dataflow analysis is correct with respect
  to the dynamic semantics: the approximations (sets of values) 
  of a register at a program point predicted by the static analysis
  are a superset of the values actually encountered during concrete
  executions.  We formalize this correspondence between run-time values and
  compile-time approximations by the following predicate. *)

Definition val_match_approx (a: approx) (v: val) : Prop :=
  match a with
  | Unknown => True
  | I p => v = Vint p
  | F p => v = Vfloat p
  | S symb ofs => exists b, Genv.find_symbol ge symb = Some b /\ v = Vptr b ofs
  | _ => False
  end.

Inductive val_list_match_approx: list approx -> list val -> Prop :=
  | vlma_nil:
      val_list_match_approx nil nil
  | vlma_cons:
      forall a al v vl,
      val_match_approx a v ->
      val_list_match_approx al vl ->
      val_list_match_approx (a :: al) (v :: vl).

Ltac SimplVMA :=
  match goal with
  | H: (val_match_approx (I _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (F _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (S _ _) ?v) |- _ =>
      simpl in H; 
      (try (elim H;
            let b := fresh "b" in let A := fresh in let B := fresh in
            (intros b [A B]; subst v; clear H)));
      SimplVMA
  | _ =>
      idtac
  end.

Ltac InvVLMA :=
  match goal with
  | H: (val_list_match_approx nil ?vl) |- _ =>
      inversion H
  | H: (val_list_match_approx (?a :: ?al) ?vl) |- _ =>
      inversion H; SimplVMA; InvVLMA
  | _ =>
      idtac
  end.

(** We then show that [eval_static_operation] is a correct abstract
  interpretations of [eval_operation]: if the concrete arguments match
  the given approximations, the concrete results match the
  approximations returned by [eval_static_operation]. *)

Lemma eval_static_condition_correct:
  forall cond al vl m b,
  val_list_match_approx al vl ->
  eval_static_condition cond al = Some b ->
  eval_condition cond vl m = Some b.
Proof.
  intros until b.
  unfold eval_static_condition. 
  case (eval_static_condition_match cond al); intros;
  InvVLMA; simpl; congruence.
Qed.

Lemma eval_static_operation_correct:
  forall op sp al vl m v,
  val_list_match_approx al vl ->
  eval_operation ge sp op vl m = Some v ->
  val_match_approx (eval_static_operation op al) v.
Proof.
  intros until v.
  unfold eval_static_operation. 
  case (eval_static_operation_match op al); intros;
  InvVLMA; simpl in *; FuncInv; try congruence.

  destruct (Genv.find_symbol ge s). exists b. intuition congruence.
  congruence.

  rewrite <- H3. replace v0 with (Vint n1). reflexivity. congruence.
  rewrite <- H3. replace v0 with (Vint n1). reflexivity. congruence.
  rewrite <- H3. replace v0 with (Vint n1). reflexivity. congruence.
  rewrite <- H3. replace v0 with (Vint n1). reflexivity. congruence.

  exists b. split. auto. congruence. 
  exists b. split. auto. congruence.
  exists b. split. auto. congruence.
  exists b. split. auto. congruence.
  exists b. split. auto. congruence.

  replace n2 with i0. destruct (Int.eq i0 Int.zero). 
  discriminate. injection H0; intro; subst v. simpl. congruence. congruence.

  replace n2 with i0. destruct (Int.eq i0 Int.zero). 
  discriminate. injection H0; intro; subst v. simpl. congruence. congruence.

  replace n2 with i0. destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v. simpl. congruence. discriminate. congruence. 

  replace n2 with i0. destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v. simpl. congruence. discriminate. congruence. 

  replace n2 with i0. destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v. simpl. congruence. discriminate. congruence. 

  rewrite <- H3. replace v0 with (Vfloat n1). reflexivity. congruence.

  inv H4. destruct (Float.intoffloat f); simpl in H0; inv H0. red; auto.

  inv H4. destruct (Float.intuoffloat f); simpl in H0; inv H0. red; auto.

  caseEq (eval_static_condition c vl0).
  intros. generalize (eval_static_condition_correct _ _ _ m _ H H1).
  intro. rewrite H2 in H0. 
  destruct b; injection H0; intro; subst v; simpl; auto.
  intros; simpl; auto.

  replace n1 with i. destruct (Int.ltu n (Int.repr 31)).
  injection H0; intro; subst v. simpl. auto. congruence. congruence.

  auto.
Qed.

(** * Correctness of strength reduction *)

(** We now show that strength reduction over operators and addressing
  modes preserve semantics: the strength-reduced operations and
  addressings evaluate to the same values as the original ones if the
  actual arguments match the static approximations used for strength
  reduction. *)

Section STRENGTH_REDUCTION.

Variable app: reg -> approx.
Variable sp: val.
Variable rs: regset.
Variable m: mem.
Hypothesis MATCH: forall r, val_match_approx (app r) rs#r.

Lemma intval_correct:
  forall r n,
  intval app r = Some n -> rs#r = Vint n.
Proof.
  intros until n.
  unfold intval. caseEq (app r); intros; try discriminate.
  generalize (MATCH r). unfold val_match_approx. rewrite H.
  congruence. 
Qed.

Lemma cond_strength_reduction_correct:
  forall cond args,
  let (cond', args') := cond_strength_reduction app cond args in
  eval_condition cond' rs##args' m = eval_condition cond rs##args m.
Proof.
  intros. unfold cond_strength_reduction.
  case (cond_strength_reduction_match cond args); intros.

  caseEq (intval app r1); intros.
  simpl. rewrite (intval_correct _ _ H). 
  destruct (rs#r2); auto. rewrite Int.swap_cmp. auto.
  caseEq (intval app r2); intros.
  simpl. rewrite (intval_correct _ _ H0). auto.
  auto.

  caseEq (intval app r1); intros.
  simpl. rewrite (intval_correct _ _ H). 
  destruct (rs#r2); auto. rewrite Int.swap_cmpu. auto.
  destruct c; reflexivity.
  caseEq (intval app r2); intros.
  simpl. rewrite (intval_correct _ _ H0). auto.
  auto.

  caseEq (intval app r2); intros.
  simpl. rewrite (intval_correct _ _ H). auto.
  auto.

  caseEq (intval app r2); intros.
  simpl. rewrite (intval_correct _ _ H). auto.
  auto.

  auto.
Qed.

Lemma make_addimm_correct:
  forall n r v,
  let (op, args) := make_addimm n r in
  eval_operation ge sp Oadd (rs#r :: Vint n :: nil) m = Some v ->
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros; unfold make_addimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.add_zero in H. congruence.
  rewrite Int.add_zero in H. congruence.
  exact H0.
Qed.
  
Lemma make_shlimm_correct:
  forall n r v,
  let (op, args) := make_shlimm n r in
  eval_operation ge sp Oshl (rs#r :: Vint n :: nil) m = Some v ->
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros; unfold make_shlimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shl_zero in H. congruence.
  unfold is_shift_amount. destruct (is_shift_amount_aux n); intros.
  simpl in *. FuncInv. rewrite e in H0. auto.
  simpl in *. FuncInv. rewrite e in H0. discriminate.
Qed.

Lemma make_shrimm_correct:
  forall n r v,
  let (op, args) := make_shrimm n r in
  eval_operation ge sp Oshr (rs#r :: Vint n :: nil) m = Some v ->
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros; unfold make_shrimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shr_zero in H. congruence.
  unfold is_shift_amount. destruct (is_shift_amount_aux n); intros.
  simpl in *. FuncInv. rewrite e in H0. auto.
  simpl in *. FuncInv. rewrite e in H0. discriminate.
Qed.

Lemma make_shruimm_correct:
  forall n r v,
  let (op, args) := make_shruimm n r in
  eval_operation ge sp Oshru (rs#r :: Vint n :: nil) m = Some v ->
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros; unfold make_shruimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shru_zero in H. congruence.
  unfold is_shift_amount. destruct (is_shift_amount_aux n); intros.
  simpl in *. FuncInv. rewrite e in H0. auto.
  simpl in *. FuncInv. rewrite e in H0. discriminate.
Qed.

Lemma make_mulimm_correct:
  forall n r r' v,
  rs#r' = Vint n ->
  let (op, args) := make_mulimm n r r' in
  eval_operation ge sp Omul (rs#r :: Vint n :: nil) m = Some v ->
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros; unfold make_mulimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in H1. FuncInv. rewrite Int.mul_zero in H0. simpl. congruence.
  generalize (Int.eq_spec n Int.one); case (Int.eq n Int.one); intros.
  subst n. simpl in H2. simpl. FuncInv. rewrite Int.mul_one in H1. congruence.
  caseEq (Int.is_power2 n); intros.
  replace (eval_operation ge sp Omul (rs # r :: Vint n :: nil) m)
     with (eval_operation ge sp Oshl (rs # r :: Vint i :: nil) m).
  apply make_shlimm_correct. 
  simpl. generalize (Int.is_power2_range _ _ H2). 
  change (Z_of_nat Int.wordsize) with 32. intro. rewrite H3.
  destruct rs#r; auto. rewrite (Int.mul_pow2 i0 _ _ H2). auto.
  simpl List.map. rewrite H. auto.
Qed.

Lemma make_andimm_correct:
  forall n r v,
  let (op, args) := make_andimm n r in
  eval_operation ge sp Oand (rs#r :: Vint n :: nil) m = Some v ->
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros; unfold make_andimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.and_zero in H. congruence.
  generalize (Int.eq_spec n Int.mone); case (Int.eq n Int.mone); intros.
  subst n. simpl in *. FuncInv. rewrite Int.and_mone in H0. congruence.
  exact H1.
Qed.

Lemma make_orimm_correct:
  forall n r v,
  let (op, args) := make_orimm n r in
  eval_operation ge sp Oor (rs#r :: Vint n :: nil) m = Some v ->
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros; unfold make_orimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.or_zero in H. congruence.
  generalize (Int.eq_spec n Int.mone); case (Int.eq n Int.mone); intros.
  subst n. simpl in *. FuncInv. rewrite Int.or_mone in H0. congruence.
  exact H1.
Qed.

Lemma make_xorimm_correct:
  forall n r v,
  let (op, args) := make_xorimm n r in
  eval_operation ge sp Oxor (rs#r :: Vint n :: nil) m = Some v ->
  eval_operation ge sp op rs##args m = Some v.
Proof.
  intros; unfold make_xorimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.xor_zero in H. congruence.
  generalize (Int.eq_spec n Int.mone); case (Int.eq n Int.mone); intros.
  subst n. simpl in *. FuncInv. decEq. auto.
  exact H1.
Qed.

Lemma op_strength_reduction_correct:
  forall op args v,
  let (op', args') := op_strength_reduction app op args in
  eval_operation ge sp op rs##args m = Some v ->
  eval_operation ge sp op' rs##args' m = Some v.
Proof.
  intros; unfold op_strength_reduction;
  case (op_strength_reduction_match op args); intros; simpl List.map.
  (* Oadd *)
  caseEq (intval app r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Oadd (Vint i :: rs # r2 :: nil) m)
     with (eval_operation ge sp Oadd (rs # r2 :: Vint i :: nil) m).
  apply make_addimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.add_commut; auto.
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H0). apply make_addimm_correct.
  assumption.
  (* Oaddshift *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp (Oaddshift s) (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oadd (rs # r1 :: Vint (eval_shift s i) :: nil) m).
  apply make_addimm_correct. 
  simpl. destruct rs#r1; auto.
  assumption.
  (* Osub *)
  caseEq (intval app r1); intros.
  rewrite (intval_correct _ _ H) in H0.
  simpl in *. destruct rs#r2; auto. 
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H0).
  replace (eval_operation ge sp Osub (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oadd (rs # r1 :: Vint (Int.neg i) :: nil) m).
  apply make_addimm_correct.
  simpl. destruct rs#r1; auto; rewrite Int.sub_add_opp; auto.
  assumption.
  (* Osubshift *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp (Osubshift s) (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oadd (rs # r1 :: Vint (Int.neg (eval_shift s i)) :: nil) m).
  apply make_addimm_correct. 
  simpl. destruct rs#r1; auto; rewrite Int.sub_add_opp; auto.
  assumption.
  (* Orsubshift *)
  caseEq (intval app r2). intros n H.
  rewrite (intval_correct _ _ H).
  simpl. destruct rs#r1; auto. 
  auto.
  (* Omul *)
  caseEq (intval app r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Omul (Vint i :: rs # r2 :: nil) m)
     with (eval_operation ge sp Omul (rs # r2 :: Vint i :: nil) m).
  apply make_mulimm_correct. apply intval_correct; auto. 
  simpl. destruct rs#r2; auto. rewrite Int.mul_commut; auto.
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H0). apply make_mulimm_correct.
  apply intval_correct; auto.
  assumption.
  (* Odivu *)
  caseEq (intval app r2); intros.
  caseEq (Int.is_power2 i); intros.
  rewrite (intval_correct _ _ H).
  replace (eval_operation ge sp Odivu (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oshru (rs # r1 :: Vint i0 :: nil) m).
  apply make_shruimm_correct. 
  simpl. destruct rs#r1; auto. 
  change 32 with (Z_of_nat Int.wordsize). 
  rewrite (Int.is_power2_range _ _ H0). 
  generalize (Int.eq_spec i Int.zero); case (Int.eq i Int.zero); intros.
  subst i. discriminate. 
  rewrite (Int.divu_pow2 i1 _ _ H0). auto.
  assumption.
  assumption.
  (* Oand *)
  caseEq (intval app r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Oand (Vint i :: rs # r2 :: nil) m)
     with (eval_operation ge sp Oand (rs # r2 :: Vint i :: nil) m).
  apply make_andimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.and_commut; auto.
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H0). apply make_andimm_correct.
  assumption.
  (* Oandshift *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp (Oandshift s) (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oand (rs # r1 :: Vint (eval_shift s i) :: nil) m).
  apply make_andimm_correct. reflexivity.
  assumption.
  (* Oor *)
  caseEq (intval app r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Oor (Vint i :: rs # r2 :: nil) m)
     with (eval_operation ge sp Oor (rs # r2 :: Vint i :: nil) m).
  apply make_orimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.or_commut; auto.
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H0). apply make_orimm_correct.
  assumption.
  (* Oorshift *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp (Oorshift s) (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oor (rs # r1 :: Vint (eval_shift s i) :: nil) m).
  apply make_orimm_correct. reflexivity.
  assumption.
  (* Oxor *)
  caseEq (intval app r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Oxor (Vint i :: rs # r2 :: nil) m)
     with (eval_operation ge sp Oxor (rs # r2 :: Vint i :: nil) m).
  apply make_xorimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.xor_commut; auto.
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H0). apply make_xorimm_correct.
  assumption.
  (* Oxorshift *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp (Oxorshift s) (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oxor (rs # r1 :: Vint (eval_shift s i) :: nil) m).
  apply make_xorimm_correct. reflexivity.
  assumption.
  (* Obic *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Obic (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oand (rs # r1 :: Vint (Int.not i) :: nil) m).
  apply make_andimm_correct. reflexivity.
  assumption.
  (* Obicshift *)
  caseEq (intval app r2); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp (Obicshift s) (rs # r1 :: Vint i :: nil) m)
     with (eval_operation ge sp Oand (rs # r1 :: Vint (Int.not (eval_shift s i)) :: nil) m).
  apply make_andimm_correct. reflexivity.
  assumption.
  (* Oshl *)
  caseEq (intval app r2); intros.
  caseEq (Int.ltu i Int.iwordsize); intros.
  rewrite (intval_correct _ _ H). apply make_shlimm_correct.
  assumption.
  assumption.
  (* Oshr *)
  caseEq (intval app r2); intros.
  caseEq (Int.ltu i Int.iwordsize); intros.
  rewrite (intval_correct _ _ H). apply make_shrimm_correct.
  assumption.
  assumption.
  (* Oshru *)
  caseEq (intval app r2); intros.
  caseEq (Int.ltu i Int.iwordsize); intros.
  rewrite (intval_correct _ _ H). apply make_shruimm_correct.
  assumption.
  assumption.
  (* Ocmp *)
  generalize (cond_strength_reduction_correct c rl).
  destruct (cond_strength_reduction app c rl).
  simpl. intro. rewrite H. auto.
  (* default *)
  assumption.
Qed.
 
Lemma addr_strength_reduction_correct:
  forall addr args,
  let (addr', args') := addr_strength_reduction app addr args in
  eval_addressing ge sp addr' rs##args' = eval_addressing ge sp addr rs##args.
Proof.
  intros. 

  unfold addr_strength_reduction;
  case (addr_strength_reduction_match addr args); intros.

  (* Aindexed2 *)
  caseEq (intval app r1); intros.
  simpl; rewrite (intval_correct _ _ H).
  destruct rs#r2; auto. rewrite Int.add_commut; auto.
  caseEq (intval app r2); intros.
  simpl; rewrite (intval_correct _ _ H0). auto.
  auto.

  (* Aindexed2shift *)
  caseEq (intval app r2); intros.
  simpl; rewrite (intval_correct _ _ H). auto.
  auto.

  (* default *)
  reflexivity.
Qed.

End STRENGTH_REDUCTION.

End ANALYSIS.

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

(** Correctness proof for constant propagation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
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

Definition regs_match_approx (a: D.t) (rs: regset) : Prop :=
  forall r, val_match_approx (D.get r a) rs#r.

Lemma regs_match_approx_top:
  forall rs, regs_match_approx D.top rs.
Proof.
  intros. red; intros. simpl. rewrite PTree.gempty. 
  unfold Approx.top, val_match_approx. auto.
Qed.

Lemma val_match_approx_increasing:
  forall a1 a2 v,
  Approx.ge a1 a2 -> val_match_approx a2 v -> val_match_approx a1 v.
Proof.
  intros until v.
  intros [A|[B|C]].
  subst a1. simpl. auto.
  subst a2. simpl. tauto.
  subst a2. auto.
Qed.

Lemma regs_match_approx_increasing:
  forall a1 a2 rs,
  D.ge a1 a2 -> regs_match_approx a2 rs -> regs_match_approx a1 rs.
Proof.
  unfold D.ge, regs_match_approx. intros.
  apply val_match_approx_increasing with (D.get r a2); auto.
Qed.

Lemma regs_match_approx_update:
  forall ra rs a v r,
  val_match_approx a v ->
  regs_match_approx ra rs ->
  regs_match_approx (D.set r a ra) (rs#r <- v).
Proof.
  intros; red; intros. rewrite Regmap.gsspec. 
  case (peq r0 r); intro.
  subst r0. rewrite D.gss. auto.
  rewrite D.gso; auto. 
Qed.

Inductive val_list_match_approx: list approx -> list val -> Prop :=
  | vlma_nil:
      val_list_match_approx nil nil
  | vlma_cons:
      forall a al v vl,
      val_match_approx a v ->
      val_list_match_approx al vl ->
      val_list_match_approx (a :: al) (v :: vl).

Lemma approx_regs_val_list:
  forall ra rs rl,
  regs_match_approx ra rs ->
  val_list_match_approx (approx_regs rl ra) rs##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. apply H. auto.
Qed.

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
  forall cond al vl b,
  val_list_match_approx al vl ->
  eval_static_condition cond al = Some b ->
  eval_condition cond vl = Some b.
Proof.
  intros until b.
  unfold eval_static_condition. 
  case (eval_static_condition_match cond al); intros;
  InvVLMA; simpl; congruence.
Qed.

Lemma eval_static_operation_correct:
  forall op sp al vl v,
  val_list_match_approx al vl ->
  eval_operation ge sp op vl = Some v ->
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

  exists b. split. auto. congruence. 
  exists b. split. auto. congruence.
  exists b. split. auto. congruence.

  replace n2 with i0. destruct (Int.eq i0 Int.zero). 
  discriminate. injection H0; intro; subst v. simpl. congruence. congruence.

  replace n2 with i0. destruct (Int.eq i0 Int.zero). 
  discriminate. injection H0; intro; subst v. simpl. congruence. congruence.

  subst v. unfold Int.not. congruence.
  subst v. unfold Int.not. congruence.
  subst v. unfold Int.not. congruence.

  replace n2 with i0. destruct (Int.ltu i0 (Int.repr 32)).
  injection H0; intro; subst v. simpl. congruence. discriminate. congruence. 

  replace n2 with i0. destruct (Int.ltu i0 (Int.repr 32)).
  injection H0; intro; subst v. simpl. congruence. discriminate. congruence. 

  destruct (Int.ltu n (Int.repr 32)).
  injection H0; intro; subst v. simpl. congruence. discriminate. 

  destruct (Int.ltu n (Int.repr 32)).
  injection H0; intro; subst v. simpl. congruence. discriminate. 

  replace n2 with i0. destruct (Int.ltu i0 (Int.repr 32)).
  injection H0; intro; subst v. simpl. congruence. discriminate. congruence. 

  rewrite <- H3. replace v0 with (Vfloat n1). reflexivity. congruence.

  caseEq (eval_static_condition c vl0).
  intros. generalize (eval_static_condition_correct _ _ _ _ H H1).
  intro. rewrite H2 in H0. 
  destruct b; injection H0; intro; subst v; simpl; auto.
  intros; simpl; auto.

  rewrite <- H3. replace v0 with (Vint n1). reflexivity. congruence.
  rewrite <- H3. replace v0 with (Vint n1). reflexivity. congruence.

  auto.
Qed.

(** The correctness of the static analysis follows from the results
  above and the fact that the result of the static analysis is
  a solution of the forward dataflow inequations. *)

Lemma analyze_correct_1:
  forall f pc rs pc' i,
  f.(fn_code)!pc = Some i ->
  In pc' (successors_instr i) ->
  regs_match_approx (transfer f pc (analyze f)!!pc) rs ->
  regs_match_approx (analyze f)!!pc' rs.
Proof.
  intros until i. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with (transfer f pc approxs!!pc).
  eapply DS.fixpoint_solution; eauto.
  unfold successors_list, successors. rewrite PTree.gmap. rewrite H0. auto.
  auto.
  intros. rewrite PMap.gi. apply regs_match_approx_top. 
Qed.

Lemma analyze_correct_3:
  forall f rs,
  regs_match_approx (analyze f)!!(f.(fn_entrypoint)) rs.
Proof.
  intros. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with D.top.
  eapply DS.fixpoint_entry; eauto. auto with coqlib.
  apply regs_match_approx_top. 
  intros. rewrite PMap.gi. apply regs_match_approx_top.
Qed.

(** * Correctness of strength reduction *)

(** We now show that strength reduction over operators and addressing
  modes preserve semantics: the strength-reduced operations and
  addressings evaluate to the same values as the original ones if the
  actual arguments match the static approximations used for strength
  reduction. *)

Section STRENGTH_REDUCTION.

Variable approx: D.t.
Variable sp: val.
Variable rs: regset.
Hypothesis MATCH: regs_match_approx approx rs.

Lemma intval_correct:
  forall r n,
  intval approx r = Some n -> rs#r = Vint n.
Proof.
  intros until n.
  unfold intval. caseEq (D.get r approx); intros; try discriminate.
  generalize (MATCH r). unfold val_match_approx. rewrite H.
  congruence. 
Qed.

Lemma cond_strength_reduction_correct:
  forall cond args,
  let (cond', args') := cond_strength_reduction approx cond args in
  eval_condition cond' rs##args' = eval_condition cond rs##args.
Proof.
  intros. unfold cond_strength_reduction.
  case (cond_strength_reduction_match cond args); intros.
  caseEq (intval approx r1); intros.
  simpl. rewrite (intval_correct _ _ H). 
  destruct (rs#r2); auto. rewrite Int.swap_cmp. auto.
  destruct c; reflexivity.
  caseEq (intval approx r2); intros.
  simpl. rewrite (intval_correct _ _ H0). auto.
  auto.
  caseEq (intval approx r1); intros.
  simpl. rewrite (intval_correct _ _ H). 
  destruct (rs#r2); auto. rewrite Int.swap_cmpu. auto.
  caseEq (intval approx r2); intros.
  simpl. rewrite (intval_correct _ _ H0). auto.
  auto.
  auto.
Qed.

Lemma make_addimm_correct:
  forall n r v,
  let (op, args) := make_addimm n r in
  eval_operation ge sp Oadd (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
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
  eval_operation ge sp Oshl (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_shlimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shl_zero in H. congruence.
  simpl in *. FuncInv. caseEq (Int.ltu n (Int.repr 32)); intros.
  rewrite H1 in H0. rewrite Int.shl_rolm in H0. auto. exact H1.
  rewrite H1 in H0. discriminate.
Qed.

Lemma make_shrimm_correct:
  forall n r v,
  let (op, args) := make_shrimm n r in
  eval_operation ge sp Oshr (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_shrimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shr_zero in H. congruence.
  assumption.
Qed.

Lemma make_shruimm_correct:
  forall n r v,
  let (op, args) := make_shruimm n r in
  eval_operation ge sp Oshru (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_shruimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.shru_zero in H. congruence.
  simpl in *. FuncInv. caseEq (Int.ltu n (Int.repr 32)); intros.
  rewrite H1 in H0. rewrite Int.shru_rolm in H0. auto. exact H1.
  rewrite H1 in H0. discriminate.
Qed.

Lemma make_mulimm_correct:
  forall n r v,
  let (op, args) := make_mulimm n r in
  eval_operation ge sp Omul (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_mulimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in H0. FuncInv. rewrite Int.mul_zero in H. simpl. congruence.
  generalize (Int.eq_spec n Int.one); case (Int.eq n Int.one); intros.
  subst n. simpl in H1. simpl. FuncInv. rewrite Int.mul_one in H0. congruence.
  caseEq (Int.is_power2 n); intros.
  replace (eval_operation ge sp Omul (rs # r :: Vint n :: nil))
     with (eval_operation ge sp Oshl (rs # r :: Vint i :: nil)).
  apply make_shlimm_correct. 
  simpl. generalize (Int.is_power2_range _ _ H1). 
  change (Z_of_nat wordsize) with 32. intro. rewrite H2.
  destruct rs#r; auto. rewrite (Int.mul_pow2 i0 _ _ H1). auto.
  exact H2.
Qed.

Lemma make_andimm_correct:
  forall n r v,
  let (op, args) := make_andimm n r in
  eval_operation ge sp Oand (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
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
  eval_operation ge sp Oor (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
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
  eval_operation ge sp Oxor (rs#r :: Vint n :: nil) = Some v ->
  eval_operation ge sp op rs##args = Some v.
Proof.
  intros; unfold make_xorimm.
  generalize (Int.eq_spec n Int.zero); case (Int.eq n Int.zero); intros.
  subst n. simpl in *. FuncInv. rewrite Int.xor_zero in H. congruence.
  exact H0.
Qed.

Lemma op_strength_reduction_correct:
  forall op args v,
  let (op', args') := op_strength_reduction approx op args in
  eval_operation ge sp op rs##args = Some v ->
  eval_operation ge sp op' rs##args' = Some v.
Proof.
  intros; unfold op_strength_reduction;
  case (op_strength_reduction_match op args); intros; simpl List.map.
  (* Oadd *)
  caseEq (intval approx r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Oadd (Vint i :: rs # r2 :: nil))
     with (eval_operation ge sp Oadd (rs # r2 :: Vint i :: nil)).
  apply make_addimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.add_commut; auto.
  caseEq (intval approx r2); intros.
  rewrite (intval_correct _ _ H0). apply make_addimm_correct.
  assumption.
  (* Osub *)
  caseEq (intval approx r1); intros.
  rewrite (intval_correct _ _ H) in H0. assumption. 
  caseEq (intval approx r2); intros.
  rewrite (intval_correct _ _ H0). 
  replace (eval_operation ge sp Osub (rs # r1 :: Vint i :: nil))
     with (eval_operation ge sp Oadd (rs # r1 :: Vint (Int.neg i) :: nil)).
  apply make_addimm_correct.
  simpl. destruct rs#r1; auto; rewrite Int.sub_add_opp; auto. 
  assumption.
  (* Omul *)
  caseEq (intval approx r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Omul (Vint i :: rs # r2 :: nil))
     with (eval_operation ge sp Omul (rs # r2 :: Vint i :: nil)).
  apply make_mulimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.mul_commut; auto.
  caseEq (intval approx r2); intros.
  rewrite (intval_correct _ _ H0). apply make_mulimm_correct.
  assumption.
  (* Odiv *)
  caseEq (intval approx r2); intros.
  caseEq (Int.is_power2 i); intros.
  rewrite (intval_correct _ _ H) in H1.   
  simpl in *; FuncInv. destruct (Int.eq i Int.zero). congruence.
  change 32 with (Z_of_nat wordsize). 
  rewrite (Int.is_power2_range _ _ H0). 
  rewrite (Int.divs_pow2 i1 _ _ H0) in H1. auto.
  assumption.
  assumption.
  (* Odivu *)
  caseEq (intval approx r2); intros.
  caseEq (Int.is_power2 i); intros.
  rewrite (intval_correct _ _ H).
  replace (eval_operation ge sp Odivu (rs # r1 :: Vint i :: nil))
     with (eval_operation ge sp Oshru (rs # r1 :: Vint i0 :: nil)).
  apply make_shruimm_correct. 
  simpl. destruct rs#r1; auto. 
  change 32 with (Z_of_nat wordsize). 
  rewrite (Int.is_power2_range _ _ H0). 
  generalize (Int.eq_spec i Int.zero); case (Int.eq i Int.zero); intros.
  subst i. discriminate. 
  rewrite (Int.divu_pow2 i1 _ _ H0). auto.
  assumption.
  assumption.
  (* Oand *)
  caseEq (intval approx r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Oand (Vint i :: rs # r2 :: nil))
     with (eval_operation ge sp Oand (rs # r2 :: Vint i :: nil)).
  apply make_andimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.and_commut; auto.
  caseEq (intval approx r2); intros.
  rewrite (intval_correct _ _ H0). apply make_andimm_correct.
  assumption.
  (* Oor *)
  caseEq (intval approx r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Oor (Vint i :: rs # r2 :: nil))
     with (eval_operation ge sp Oor (rs # r2 :: Vint i :: nil)).
  apply make_orimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.or_commut; auto.
  caseEq (intval approx r2); intros.
  rewrite (intval_correct _ _ H0). apply make_orimm_correct.
  assumption.
  (* Oxor *)
  caseEq (intval approx r1); intros.
  rewrite (intval_correct _ _ H). 
  replace (eval_operation ge sp Oxor (Vint i :: rs # r2 :: nil))
     with (eval_operation ge sp Oxor (rs # r2 :: Vint i :: nil)).
  apply make_xorimm_correct. 
  simpl. destruct rs#r2; auto. rewrite Int.xor_commut; auto.
  caseEq (intval approx r2); intros.
  rewrite (intval_correct _ _ H0). apply make_xorimm_correct.
  assumption.
  (* Oshl *)
  caseEq (intval approx r2); intros.
  caseEq (Int.ltu i (Int.repr 32)); intros.
  rewrite (intval_correct _ _ H). apply make_shlimm_correct.
  assumption.
  assumption.
  (* Oshr *)
  caseEq (intval approx r2); intros.
  caseEq (Int.ltu i (Int.repr 32)); intros.
  rewrite (intval_correct _ _ H). apply make_shrimm_correct.
  assumption.
  assumption.
  (* Oshru *)
  caseEq (intval approx r2); intros.
  caseEq (Int.ltu i (Int.repr 32)); intros.
  rewrite (intval_correct _ _ H). apply make_shruimm_correct.
  assumption.
  assumption.
  (* Ocmp *)
  generalize (cond_strength_reduction_correct c rl).
  destruct (cond_strength_reduction approx c rl).
  simpl. intro. rewrite H. auto.
  (* default *)
  assumption.
Qed.

Ltac KnownApprox :=
  match goal with
  | MATCH: (regs_match_approx ?approx ?rs),
    H: (D.get ?r ?approx = ?a) |- _ =>
      generalize (MATCH r); rewrite H; intro; clear H; KnownApprox
  | _ => idtac
  end.
 
Lemma addr_strength_reduction_correct:
  forall addr args,
  let (addr', args') := addr_strength_reduction approx addr args in
  eval_addressing ge sp addr' rs##args' = eval_addressing ge sp addr rs##args.
Proof.
  intros. 

  (* Useful lemmas *)
  assert (A0: forall r1 r2,
    eval_addressing ge sp Aindexed2 (rs ## (r1 :: r2 :: nil)) =
    eval_addressing ge sp Aindexed2 (rs ## (r2 :: r1 :: nil))).
  intros. simpl. destruct (rs#r1); destruct (rs#r2); auto;
  rewrite Int.add_commut; auto.

  assert (A1: forall r1 r2 n,
    val_match_approx (I n) rs#r2 -> 
    eval_addressing ge sp (Aindexed n) (rs ## (r1 :: nil)) =
    eval_addressing ge sp Aindexed2 (rs ## (r1 :: r2 :: nil))).
  intros; simpl in *. rewrite H. auto.

  assert (A2: forall r1 r2 n,
    val_match_approx (I n) rs#r1 -> 
    eval_addressing ge sp (Aindexed n) (rs ## (r2 :: nil)) =
    eval_addressing ge sp Aindexed2 (rs ## (r1 :: r2 :: nil))).
  intros. rewrite A0. apply A1. auto.

  assert (A3: forall r1 r2 id ofs,
    val_match_approx (S id ofs) rs#r1 ->
    eval_addressing ge sp (Abased id ofs) (rs ## (r2 :: nil)) =
    eval_addressing ge sp Aindexed2 (rs ## (r1 :: r2 :: nil))).
  intros. elim H. intros b [A B]. simpl. rewrite A; rewrite B. auto.

  assert (A4: forall r1 r2 id ofs,
    val_match_approx (S id ofs) rs#r2 ->
    eval_addressing ge sp (Abased id ofs) (rs ## (r1 :: nil)) =
    eval_addressing ge sp Aindexed2 (rs ## (r1 :: r2 :: nil))).
  intros. rewrite A0. apply A3. auto.

  assert (A5: forall r1 r2 id ofs n,
    val_match_approx (S id ofs) rs#r1 ->
    val_match_approx (I n) rs#r2 ->
    eval_addressing ge sp (Aglobal id (Int.add ofs n)) nil =
    eval_addressing ge sp Aindexed2 (rs ## (r1 :: r2 :: nil))).
  intros. elim H. intros b [A B]. simpl. rewrite A; rewrite B. 
  simpl in H0. rewrite H0. auto.

  unfold addr_strength_reduction;
  case (addr_strength_reduction_match addr args); intros.

  (* Aindexed2 *)
  caseEq (D.get r1 approx); intros;
  caseEq (D.get r2 approx); intros;
  try reflexivity; KnownApprox; auto.
  rewrite A0. rewrite Int.add_commut. apply A5; auto.

  (* Abased *)
  caseEq (intval approx r1); intros.
  simpl; rewrite (intval_correct _ _ H). auto.
  auto.

  (* Aindexed *)
  caseEq (D.get r1 approx); intros; auto.
  simpl; KnownApprox. 
  elim H0. intros b [A B]. rewrite A; rewrite B. auto.

  (* default *)
  reflexivity.
Qed.

End STRENGTH_REDUCTION.

End ANALYSIS.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Section PRESERVATION.

Variable prog: program.
Let tprog := transf_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_symbol_transf.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.  
  intros.
  exact (Genv.find_funct_transf transf_fundef H).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf transf_fundef H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (transf_fundef f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma transf_ros_correct:
  forall ros rs f approx,
  regs_match_approx ge approx rs ->
  find_function ge ros rs = Some f ->
  find_function tge (transf_ros approx ros) rs = Some (transf_fundef f).
Proof.
  intros until approx; intro MATCH.
  destruct ros; simpl.
  intro.
  exploit functions_translated; eauto. intro FIND.  
  caseEq (D.get r approx); intros; auto.
  generalize (Int.eq_spec i0 Int.zero); case (Int.eq i0 Int.zero); intros; auto.
  generalize (MATCH r). rewrite H0. intros [b [A B]].
  rewrite <- symbols_preserved in A.
  rewrite B in FIND. rewrite H1 in FIND. 
  rewrite Genv.find_funct_find_funct_ptr in FIND.
  simpl. rewrite A. auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  intro. apply function_ptr_translated. auto.
  congruence.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the values of registers in [st1]
  must match their compile-time approximations at the current program
  point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res c sp pc rs f,
      c = f.(RTL.fn_code) ->
      (forall v, regs_match_approx ge (analyze f)!!pc (rs#res <- v)) ->
    match_stackframes
        (Stackframe res c sp pc rs)
        (Stackframe res (transf_code (analyze f) c) sp pc rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s c sp pc rs m f s'
           (CF: c = f.(RTL.fn_code))
           (MATCH: regs_match_approx ge (analyze f)!!pc rs)
           (STACKS: list_forall2 match_stackframes s s'),
      match_states (State s c sp pc rs m)
                   (State s' (transf_code (analyze f) c) sp pc rs m)
  | match_states_call:
      forall s f args m s',
      list_forall2 match_stackframes s s' ->
      match_states (Callstate s f args m)
                   (Callstate s' (transf_fundef f) args m)
  | match_states_return:
      forall s s' v m,
      list_forall2 match_stackframes s s' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v m).

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function |- _ =>
      cut ((transf_code (analyze f) c)!pc = Some(transf_instr (analyze f)!!pc instr));
      [ simpl
      | unfold transf_code; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS.

  (* Inop *)
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' rs m); split.
  TransfInstr; intro. eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analyze_correct_1 with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. auto.

  (* Iop *)
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' (rs#res <- v) m); split.
  TransfInstr. caseEq (op_strength_reduction (analyze f)!!pc op args);
  intros op' args' OSR.
  assert (eval_operation tge sp op' rs##args' = Some v).
    rewrite (eval_operation_preserved symbols_preserved). 
    generalize (op_strength_reduction_correct ge (analyze f)!!pc sp rs
                  MATCH op args v).
    rewrite OSR; simpl. auto.
  generalize (eval_static_operation_correct ge op sp
               (approx_regs args (analyze f)!!pc) rs##args v
               (approx_regs_val_list _ _ _ args MATCH) H0).
  case (eval_static_operation op (approx_regs args (analyze f)!!pc)); intros;
  simpl in H2;
  eapply exec_Iop; eauto; simpl.
  congruence.
  congruence.
  elim H2; intros b [A B]. rewrite symbols_preserved. 
  rewrite A; rewrite B; auto.
  econstructor; eauto. 
  eapply analyze_correct_1 with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. 
  eapply eval_static_operation_correct; eauto.
  apply approx_regs_val_list; auto.

  (* Iload *)
  caseEq (addr_strength_reduction (analyze f)!!pc addr args);
  intros addr' args' ASR.
  assert (eval_addressing tge sp addr' rs##args' = Some a).
    rewrite (eval_addressing_preserved symbols_preserved). 
    generalize (addr_strength_reduction_correct ge (analyze f)!!pc sp rs
                  MATCH addr args).
    rewrite ASR; simpl. congruence. 
  TransfInstr. rewrite ASR. intro.
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' (rs#dst <- v) m); split.
  eapply exec_Iload; eauto.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. simpl; auto.

  (* Istore *)
  caseEq (addr_strength_reduction (analyze f)!!pc addr args);
  intros addr' args' ASR.
  assert (eval_addressing tge sp addr' rs##args' = Some a).
    rewrite (eval_addressing_preserved symbols_preserved). 
    generalize (addr_strength_reduction_correct ge (analyze f)!!pc sp rs
                  MATCH addr args).
    rewrite ASR; simpl. congruence. 
  TransfInstr. rewrite ASR. intro.
  exists (State s' (transf_code (analyze f) (fn_code f)) sp pc' rs m'); split.
  eapply exec_Istore; eauto.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. auto. 

  (* Icall *)
  exploit transf_ros_correct; eauto. intro FIND'.
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Icall; eauto. apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto. 
  intros. eapply analyze_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  apply regs_match_approx_update; auto. simpl. auto.

  (* Itailcall *)
  exploit transf_ros_correct; eauto. intros FIND'.
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  constructor; auto. 

  (* Icond, true *)
  exists (State s' (transf_code (analyze f) (fn_code f)) sp ifso rs m); split. 
  caseEq (cond_strength_reduction (analyze f)!!pc cond args);
  intros cond' args' CSR.
  assert (eval_condition cond' rs##args' = Some true).
    generalize (cond_strength_reduction_correct
                  ge (analyze f)!!pc rs MATCH cond args).
    rewrite CSR.  intro. congruence.
  TransfInstr. rewrite CSR. 
  caseEq (eval_static_condition cond (approx_regs args (analyze f)!!pc)).
  intros b ESC. 
  generalize (eval_static_condition_correct ge cond _ _ _
               (approx_regs_val_list _ _ _ args MATCH) ESC); intro.
  replace b with true. intro; eapply exec_Inop; eauto. congruence.
  intros. eapply exec_Icond_true; eauto.
  econstructor; eauto.
  eapply analyze_correct_1; eauto.
  simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Icond, false *)
  exists (State s' (transf_code (analyze f) (fn_code f)) sp ifnot rs m); split. 
  caseEq (cond_strength_reduction (analyze f)!!pc cond args);
  intros cond' args' CSR.
  assert (eval_condition cond' rs##args' = Some false).
    generalize (cond_strength_reduction_correct
                  ge (analyze f)!!pc rs MATCH cond args).
    rewrite CSR.  intro. congruence.
  TransfInstr. rewrite CSR. 
  caseEq (eval_static_condition cond (approx_regs args (analyze f)!!pc)).
  intros b ESC. 
  generalize (eval_static_condition_correct ge cond _ _ _
               (approx_regs_val_list _ _ _ args MATCH) ESC); intro.
  replace b with false. intro; eapply exec_Inop; eauto. congruence.
  intros. eapply exec_Icond_false; eauto.
  econstructor; eauto.
  eapply analyze_correct_1; eauto.
  simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Ireturn *)
  exists (Returnstate s' (regmap_optget or Vundef rs) (free m stk)); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.

  (* internal function *)
  simpl. unfold transf_function.
  econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  apply analyze_correct_3; auto.

  (* external function *)
  simpl. econstructor; split.
  eapply exec_function_external; eauto.
  constructor; auto.

  (* return *)
  inv H3. inv H1. 
  econstructor; split.
  eapply exec_return; eauto. 
  econstructor; eauto. 
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil (Genv.init_mem tprog)); split.
  econstructor; eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  reflexivity.
  rewrite <- H2. apply sig_function_translated.
  replace (Genv.init_mem tprog) with (Genv.init_mem prog).
  constructor. constructor. auto.
  symmetry. unfold tprog, transf_program. apply Genv.init_mem_transf. 
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. constructor. 
Qed.

(** The preservation of the observable behavior of the program then
  follows, using the generic preservation theorem
  [Smallstep.simulation_step_preservation]. *)

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  exec_program prog beh -> exec_program tprog beh.
Proof.
  unfold exec_program; intros.
  eapply simulation_step_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct. 
Qed.

End PRESERVATION.

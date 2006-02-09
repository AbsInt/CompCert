(** Correctness proof for constant propagation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
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

  replace v with v0. auto. congruence.

  destruct (Genv.find_symbol ge s). exists b. intuition congruence.
  congruence.

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

  caseEq (eval_static_condition c vl0).
  intros. generalize (eval_static_condition_correct _ _ _ _ H H1).
  intro. rewrite H2 in H0. 
  destruct b; injection H0; intro; subst v; simpl; auto.
  intros; simpl; auto.

  auto.
Qed.

(** The correctness of the transfer function follows: if the register
  state before a transition matches the static approximations at that
  program point, the register state after that transition matches
  the static approximation returned by the transfer function. *)

Lemma transfer_correct:
  forall f c sp pc rs m pc' rs' m' ra,
  exec_instr ge c sp pc rs m pc' rs' m' ->
  c = f.(fn_code) ->
  regs_match_approx ra rs ->
  regs_match_approx (transfer f pc ra) rs'.
Proof.
  induction 1; intros; subst c; unfold transfer; rewrite H; auto.
  (* Iop *)
  apply regs_match_approx_update. 
  apply eval_static_operation_correct with sp rs##args. 
  eapply approx_regs_val_list. auto. auto. auto.
  (* Iload *)
  apply regs_match_approx_update; auto. simpl; auto.
  (* Icall *)
  apply regs_match_approx_update; auto. simpl; auto.
Qed.

(** The correctness of the static analysis follows from the results
  above and the fact that the result of the static analysis is
  a solution of the forward dataflow inequations. *)

Lemma analyze_correct_1:
  forall f approxs,
  analyze f = Some approxs ->
  forall c sp pc rs m pc' rs' m',
  exec_instr ge c sp pc rs m pc' rs' m' ->
  c = f.(fn_code) ->
  regs_match_approx approxs!!pc rs ->
  regs_match_approx approxs!!pc' rs'.
Proof.
  intros. 
  apply regs_match_approx_increasing with (transfer f pc approxs!!pc).
  eapply DS.fixpoint_solution. 
  unfold analyze in H. eexact H. 
  elim (fn_code_wf f pc); intro. auto. 
  generalize (exec_instr_present _ _ _ _ _ _ _ _ _ H0).
  rewrite H1. intro. contradiction.
  eapply successors_correct. rewrite <- H1. eauto.
  eapply transfer_correct; eauto.
Qed.

Lemma analyze_correct_2:
  forall f approxs,
  analyze f = Some approxs ->
  forall c sp pc rs m pc' rs' m',
  exec_instrs ge c sp pc rs m pc' rs' m' ->
  c = f.(fn_code) ->
  regs_match_approx approxs!!pc rs ->
  regs_match_approx approxs!!pc' rs'.
Proof.
  intros f approxs ANL. induction 1.
  auto.
  intros. eapply analyze_correct_1; eauto.
  eauto.
Qed.

Lemma analyze_correct_3:
  forall f approxs rs,
  analyze f = Some approxs ->
  regs_match_approx approxs!!(f.(fn_entrypoint)) rs.
Proof.
  intros. 
  apply regs_match_approx_increasing with D.top.
  eapply DS.fixpoint_entry. unfold analyze in H; eexact H.
  auto with coqlib.
  red; intros. rewrite D.get_top. simpl; auto.
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
  destruct c; reflexivity.
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
Proof (Genv.find_symbol_transf transf_function prog).

Lemma functions_translated:
  forall (v: val) (f: RTL.function),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_function f).
Proof (@Genv.find_funct_transf _ _ transf_function prog).

Lemma function_ptr_translated:
  forall (v: block) (f: RTL.function),
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_function f).
Proof (@Genv.find_funct_ptr_transf _ _ transf_function prog).

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
        pc, rs, m ------------------- pc, rs, m
            |                             |
            |                             |
            v                             v
        pc', rs', m' ---------------- pc', rs', m'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar expresses that the values
  of registers [rs] match their compile-time approximations at point [pc].
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that [rs'] matches the compile-time
  approximations at [pc'].

  To help express those diagrams, we define the following propositions
  parameterized by the transition in the original RTL code (left arrow)
  and summarizing the three other arrows of the diagram.  *)

Definition exec_instr_prop
        (c: code) (sp: val)
        (pc: node) (rs: regset) (m: mem)
        (pc': node) (rs': regset) (m': mem) : Prop :=
  exec_instr tge c sp pc rs m pc' rs' m' /\
  forall f approxs
         (CF: c = f.(RTL.fn_code))
         (ANL: analyze f = Some approxs)
         (MATCH: regs_match_approx ge approxs!!pc rs),
  exec_instr tge (transf_code approxs c) sp pc rs m pc' rs' m'.

Definition exec_instrs_prop
        (c: code) (sp: val)
        (pc: node) (rs: regset) (m: mem)
        (pc': node) (rs': regset) (m': mem) : Prop :=
  exec_instrs tge c sp pc rs m pc' rs' m' /\
  forall f approxs
         (CF: c = f.(RTL.fn_code))
         (ANL: analyze f = Some approxs)
         (MATCH: regs_match_approx ge approxs!!pc rs),
  exec_instrs tge (transf_code approxs c) sp pc rs m pc' rs' m'.

Definition exec_function_prop
        (f: RTL.function) (args: list val) (m: mem)
        (res: val) (m': mem) : Prop :=
  exec_function tge (transf_function f) args m res m'.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr),
    H2: (analyze ?f = Some ?approxs) |- _ =>
      cut ((transf_code approxs c)!pc = Some(transf_instr approxs!!pc instr));
      [ simpl
      | unfold transf_code; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The predicates above serve as induction hypotheses in the proof of
  simulation, which proceeds by induction over the
  evaluation derivation of the original code. *)

Lemma transf_funct_correct:
  forall f args m res m',
  exec_function ge f args m res m' ->
  exec_function_prop f args m res m'.
Proof.
  apply (exec_function_ind_3 ge
          exec_instr_prop exec_instrs_prop exec_function_prop);
  intros; red.
  (* Inop *)
  split; [idtac| intros; TransfInstr].
  apply exec_Inop; auto.
  intros; apply exec_Inop; auto.
  (* Iop *)
  split; [idtac| intros; TransfInstr].
  apply exec_Iop with op args. auto. 
  rewrite (eval_operation_preserved symbols_preserved). auto.
  caseEq (op_strength_reduction approxs!!pc op args);
  intros op' args' OSR.
  assert (eval_operation tge sp op' rs##args' = Some v).
    rewrite (eval_operation_preserved symbols_preserved). 
    generalize (op_strength_reduction_correct ge approxs!!pc sp rs
                  MATCH op args v).
    rewrite OSR; simpl. auto.
  generalize (eval_static_operation_correct ge op sp
               (approx_regs args approxs!!pc) rs##args v
               (approx_regs_val_list _ _ _ args MATCH) H0).
  case (eval_static_operation op (approx_regs args approxs!!pc)); intros;
  simpl in H1;
  eapply exec_Iop; eauto; simpl.
  simpl in H2; congruence.
  simpl in H2; congruence.
  elim H2; intros b [A B]. rewrite symbols_preserved. 
  rewrite A; rewrite B; auto.
  (* Iload *)
  split; [idtac| intros; TransfInstr].
  eapply exec_Iload; eauto. 
  rewrite (eval_addressing_preserved symbols_preserved). auto.
  caseEq (addr_strength_reduction approxs!!pc addr args);
  intros addr' args' ASR.
  assert (eval_addressing tge sp addr' rs##args' = Some a).
    rewrite (eval_addressing_preserved symbols_preserved). 
    generalize (addr_strength_reduction_correct ge approxs!!pc sp rs
                  MATCH addr args).
    rewrite ASR; simpl. congruence. 
  intro. eapply exec_Iload; eauto. 
  (* Istore *)
  split; [idtac| intros; TransfInstr].
  eapply exec_Istore; eauto.
  rewrite (eval_addressing_preserved symbols_preserved). auto.
  caseEq (addr_strength_reduction approxs!!pc addr args);
  intros addr' args' ASR.
  assert (eval_addressing tge sp addr' rs##args' = Some a).
    rewrite (eval_addressing_preserved symbols_preserved). 
    generalize (addr_strength_reduction_correct ge approxs!!pc sp rs
                  MATCH addr args).
    rewrite ASR; simpl. congruence.
  intro. eapply exec_Istore; eauto. 
  (* Icall *)
  assert (find_function tge ros rs = Some (transf_function f)).
  generalize H0; unfold find_function; destruct ros.
  apply functions_translated. 
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated. congruence.
  assert (sig = fn_sig (transf_function f)).
  rewrite H1. unfold transf_function. destruct (analyze f); reflexivity.
  split; [idtac| intros; TransfInstr].
  eapply exec_Icall; eauto.
  set (ros' :=
     match ros with
     | inl r =>
         match D.get r approxs !! pc with
         | Novalue => ros
         | Unknown => ros
         | I _ => ros
         | F _ => ros
         | S symb ofs => if Int.eq ofs Int.zero then inr reg symb else ros
         end
     | inr _ => ros
     end).
  intros; eapply exec_Icall; eauto. 
  unfold ros'; destruct ros; auto.
  caseEq (D.get r approxs!!pc); intros; auto.
  generalize (Int.eq_spec i0 Int.zero); case (Int.eq i0 Int.zero); intros; auto.
  generalize (MATCH r). rewrite H7. intros [b [A B]].
  rewrite <- symbols_preserved in A. 
  generalize H4. simpl. rewrite A. rewrite B. subst i0. 
  rewrite Genv.find_funct_find_funct_ptr. auto.

  (* Icond, true *)
  split; [idtac| intros; TransfInstr].
  eapply exec_Icond_true; eauto.
  caseEq (cond_strength_reduction approxs!!pc cond args);
  intros cond' args' CSR.
  assert (eval_condition cond' rs##args' = Some true).
    generalize (cond_strength_reduction_correct
                  ge approxs!!pc rs MATCH cond args).
    rewrite CSR.  intro. congruence.
  caseEq (eval_static_condition cond (approx_regs args approxs!!pc)).
  intros b ESC. 
  generalize (eval_static_condition_correct ge cond _ _ _
               (approx_regs_val_list _ _ _ args MATCH) ESC); intro.
  replace b with true. intro; eapply exec_Inop; eauto. congruence.
  intros. eapply exec_Icond_true; eauto. 

  (* Icond, false *)
  split; [idtac| intros; TransfInstr].
  eapply exec_Icond_false; eauto.
  caseEq (cond_strength_reduction approxs!!pc cond args);
  intros cond' args' CSR.
  assert (eval_condition cond' rs##args' = Some false).
    generalize (cond_strength_reduction_correct
                  ge approxs!!pc rs MATCH cond args).
    rewrite CSR.  intro. congruence.
  caseEq (eval_static_condition cond (approx_regs args approxs!!pc)).
  intros b ESC. 
  generalize (eval_static_condition_correct ge cond _ _ _
               (approx_regs_val_list _ _ _ args MATCH) ESC); intro.
  replace b with false. intro; eapply exec_Inop; eauto. congruence.
  intros. eapply exec_Icond_false; eauto. 

  (* refl *)
  split. apply exec_refl. intros. apply exec_refl.
  (* one *)
  elim H0; intros.
  split. apply exec_one; auto.
  intros. apply exec_one. eapply H2; eauto.
  (* trans *)
  elim H0; intros. elim H2; intros.
  split.
  apply exec_trans with pc2 rs2 m2; auto.
  intros; apply exec_trans with pc2 rs2 m2.
  eapply H4; eauto. eapply H6; eauto.
  eapply analyze_correct_2; eauto.

  (* function *)
  elim H1; intros.
  unfold transf_function.
  caseEq (analyze f). 
  intros approxs ANL.
  eapply exec_funct; simpl; eauto. 
  eapply H5. reflexivity. auto. 
  apply analyze_correct_3; auto.
  TransfInstr; auto.
  intros. eapply exec_funct; eauto.
Qed.

(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forall (r: val),
  exec_program prog r -> exec_program tprog r.
Proof.
  intros r [b [f [m [SYMB [FIND [SIG EXEC]]]]]].
  red. exists b. exists (transf_function f). exists m. 
  split. change (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. auto.
  split. apply function_ptr_translated; auto.
  split. unfold transf_function. 
  rewrite <- SIG. destruct (analyze f); reflexivity.
  apply transf_funct_correct. 
  unfold tprog, transf_program. rewrite Genv.init_mem_transf. 
  exact EXEC.
Qed.

End PRESERVATION.

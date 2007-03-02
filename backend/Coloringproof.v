(** Correctness of graph coloring. *)

Require Import SetoidList.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Locations.
Require Import Conventions.
Require Import InterfGraph.
Require Import Coloring.

(** * Correctness of the interference graph *)

(** We show that the interference graph built by [interf_graph]
  is correct in the sense that it contains all conflict edges
  that we need.

  Many boring lemmas on the auxiliary functions used to construct
  the interference graph follow.  The lemmas are of two kinds:
  the ``increasing'' lemmas show that the auxiliary functions only add 
  edges to the interference graph, but do not remove existing edges;
  and the ``correct'' lemmas show that the auxiliary functions
  correctly add the edges that we'd like them to add. *)

Lemma graph_incl_refl:
  forall g, graph_incl g g.
Proof.
  intros; split; auto.
Qed.

Lemma add_interf_live_incl_aux:
  forall (filter: reg -> bool) res live g,
  graph_incl g
    (List.fold_left
      (fun g r => if filter r then add_interf r res g else g)
      live g).
Proof.
  induction live; simpl; intros.
  apply graph_incl_refl.
  apply graph_incl_trans with (if filter a then add_interf a res g else g).
  case (filter a).
  apply add_interf_incl.
  apply graph_incl_refl.
  apply IHlive. 
Qed.

Lemma add_interf_live_incl:
  forall (filter: reg -> bool) res live g,
  graph_incl g (add_interf_live filter res live g).
Proof.
  intros. unfold add_interf_live. rewrite Regset.fold_1.
  apply add_interf_live_incl_aux.
Qed.

Lemma add_interf_live_correct_aux:
  forall filter res r live,
  InA Regset.E.eq r live -> filter r = true ->
  forall g,
  interfere r res
    (List.fold_left
      (fun g r => if filter r then add_interf r res g else g)
      live g).
Proof.
  induction 1; simpl; intros.
  hnf in H. subst y. rewrite H0.
  generalize (add_interf_live_incl_aux filter res l (add_interf r res g)).
  intros [A B].
  apply A. apply add_interf_correct.
  apply IHInA; auto.
Qed.

Lemma add_interf_live_correct:
  forall filter res live g r,
  Regset.In r live ->
  filter r = true ->
  interfere r res (add_interf_live filter res live g).
Proof.
  intros.  unfold add_interf_live. rewrite Regset.fold_1.
  apply add_interf_live_correct_aux; auto.
  apply Regset.elements_1. auto.
Qed.

Lemma add_interf_op_incl: 
  forall res live g,
  graph_incl g (add_interf_op res live g).
Proof.
  intros; unfold add_interf_op. apply add_interf_live_incl.
Qed.

Lemma add_interf_op_correct:
  forall res live g r,
  Regset.In r live ->
  r <> res ->
  interfere r res (add_interf_op res live g).
Proof.
  intros.  unfold add_interf_op.
  apply add_interf_live_correct.
  auto. destruct (Reg.eq r res); congruence. 
Qed.

Lemma add_interf_move_incl: 
  forall arg res live g,
  graph_incl g (add_interf_move arg res live g).
Proof.
  intros; unfold add_interf_move. apply add_interf_live_incl.
Qed.

Lemma add_interf_move_correct:
  forall arg res live g r,
  Regset.In r live ->
  r <> arg -> r <> res ->
  interfere r res (add_interf_move arg res live g).
Proof.
  intros.  unfold add_interf_move.
  apply add_interf_live_correct.
  auto.
  rewrite dec_eq_false; auto. rewrite dec_eq_false; auto.
Qed.

Lemma add_interf_call_incl_aux_1:
  forall mr live g,
  graph_incl g
    (List.fold_left (fun g r => add_interf_mreg r mr g) live g).
Proof.
  induction live; simpl; intros.
  apply graph_incl_refl.
  apply graph_incl_trans with (add_interf_mreg a mr g).
  apply add_interf_mreg_incl.
  auto.
Qed.

Lemma add_interf_call_incl_aux_2:
  forall mr live g,
  graph_incl g
    (Regset.fold graph (fun r g => add_interf_mreg r mr g) live g).
Proof.
  intros. rewrite Regset.fold_1. apply add_interf_call_incl_aux_1.
Qed.

Lemma add_interf_call_incl:
  forall live destroyed g,
  graph_incl g (add_interf_call live destroyed g).
Proof.
  induction destroyed; simpl; intros.
  apply graph_incl_refl.
  eapply graph_incl_trans; [idtac|apply IHdestroyed].
  apply add_interf_call_incl_aux_2.
Qed.

Lemma interfere_incl:
  forall r1 r2 g1 g2,
  graph_incl g1 g2 ->
  interfere r1 r2 g1 ->
  interfere r1 r2 g2.
Proof.
  unfold graph_incl; intros. elim H; auto.
Qed.

Lemma interfere_mreg_incl:
  forall r1 r2 g1 g2,
  graph_incl g1 g2 ->
  interfere_mreg r1 r2 g1 ->
  interfere_mreg r1 r2 g2.
Proof.
  unfold graph_incl; intros. elim H; auto.
Qed.

Lemma add_interf_call_correct_aux_1:
  forall mr r live,
  InA Regset.E.eq r live ->
  forall g,
  interfere_mreg r mr
    (List.fold_left (fun g r => add_interf_mreg r mr g) live g).
Proof.
  induction 1; simpl; intros.
  hnf in H; subst y. eapply interfere_mreg_incl. 
  apply add_interf_call_incl_aux_1.
  apply add_interf_mreg_correct.
  auto.
Qed.

Lemma add_interf_call_correct_aux_2:
  forall mr live g r,
  Regset.In r live ->
  interfere_mreg r mr
    (Regset.fold graph (fun r g => add_interf_mreg r mr g) live g).
Proof.
  intros. rewrite Regset.fold_1. apply add_interf_call_correct_aux_1.
  apply Regset.elements_1. auto.
Qed.

Lemma add_interf_call_correct:
  forall live destroyed g r mr,
  Regset.In r live ->
  In mr destroyed ->
  interfere_mreg r mr (add_interf_call live destroyed g).
Proof.
  induction destroyed; simpl; intros.
  elim H0.
  elim H0; intros. 
  subst a. eapply interfere_mreg_incl.
  apply add_interf_call_incl.
  apply add_interf_call_correct_aux_2; auto.
  apply IHdestroyed; auto.
Qed.

Lemma add_prefs_call_incl:
  forall args locs g,
  graph_incl g (add_prefs_call args locs g).
Proof.
  induction args; destruct locs; simpl; intros;
  try apply graph_incl_refl.
  destruct l. 
  eapply graph_incl_trans; [idtac|eauto]. 
  apply add_pref_mreg_incl.
  auto.
Qed.

Lemma add_interf_entry_incl:
  forall params live g,
  graph_incl g (add_interf_entry params live g).
Proof.
  unfold add_interf_entry; induction params; simpl; intros.
  apply graph_incl_refl.
  eapply graph_incl_trans; [idtac|eauto].
  apply add_interf_op_incl.
Qed.

Lemma add_interf_entry_correct:
  forall params live g r1 r2,
  In r1 params ->
  Regset.In r2 live ->
  r1 <> r2 ->
  interfere r1 r2 (add_interf_entry params live g).
Proof.
  unfold add_interf_entry; induction params; simpl; intros.
  elim H.
  elim H; intro.
  subst a. apply interfere_incl with (add_interf_op r1 live g).
  exact (add_interf_entry_incl _ _ _).
  apply interfere_sym. apply add_interf_op_correct; auto.
  auto.
Qed.

Lemma add_interf_params_incl_aux:
  forall p1 pl g,
  graph_incl g
   (List.fold_left
      (fun g r => if Reg.eq r p1 then g else add_interf r p1 g)
      pl g).
Proof.
  induction pl; simpl; intros.
  apply graph_incl_refl.
  eapply graph_incl_trans; [idtac|eauto].
  case (Reg.eq a p1); intro.
  apply graph_incl_refl. apply add_interf_incl.
Qed.

Lemma add_interf_params_incl:
  forall pl g,
  graph_incl g (add_interf_params pl g).
Proof.
  induction pl; simpl; intros.
  apply graph_incl_refl.
  eapply graph_incl_trans; [idtac|eauto].
  apply add_interf_params_incl_aux.
Qed.

Lemma add_interf_params_correct_aux:
  forall p1 pl g p2,
  In p2 pl ->
  p1 <> p2 ->
  interfere p1 p2
   (List.fold_left
      (fun g r => if Reg.eq r p1 then g else add_interf r p1 g)
      pl g).
Proof.
  induction pl; simpl; intros.
  elim H.
  elim H; intro; clear H.
  subst a. apply interfere_sym. eapply interfere_incl.
  apply add_interf_params_incl_aux. 
  case (Reg.eq p2 p1); intro.
  congruence. apply add_interf_correct.
  auto.
Qed.

Lemma add_interf_params_correct:
  forall pl g r1 r2,
  In r1 pl -> In r2 pl -> r1 <> r2 ->
  interfere r1 r2 (add_interf_params pl g).
Proof.
  induction pl; simpl; intros.
  elim H.
  elim H; intro; clear H; elim H0; intro; clear H0.
  congruence.
  subst a. eapply interfere_incl. apply add_interf_params_incl.
  apply add_interf_params_correct_aux; auto.
  subst a. apply interfere_sym.
  eapply interfere_incl. apply add_interf_params_incl.
  apply add_interf_params_correct_aux; auto.
  auto.
Qed.

Lemma add_edges_instr_incl:
  forall sig instr live g,
  graph_incl g (add_edges_instr sig instr live g).
Proof.
  intros. destruct instr; unfold add_edges_instr;
  try apply graph_incl_refl.
  case (Regset.mem r live).
  destruct (is_move_operation o l).
  eapply graph_incl_trans; [idtac|apply add_pref_incl].
  apply add_interf_move_incl.
  apply add_interf_op_incl.
  apply graph_incl_refl.
  case (Regset.mem r live).
  apply add_interf_op_incl.
  apply graph_incl_refl.
  eapply graph_incl_trans; [idtac|apply add_prefs_call_incl].
  eapply graph_incl_trans; [idtac|apply add_pref_mreg_incl].
  eapply graph_incl_trans; [idtac|apply add_interf_op_incl].
  apply add_interf_call_incl.
  eapply graph_incl_trans; [idtac|apply add_pref_mreg_incl].
  eapply graph_incl_trans; [idtac|apply add_pref_mreg_incl].
  eapply graph_incl_trans; [idtac|apply add_interf_op_incl].
  apply add_interf_call_incl.
  destruct o.
  apply add_pref_mreg_incl.
  apply graph_incl_refl.
Qed.

(** The proposition below states that graph [g] contains
  all the conflict edges expected for instruction [instr]. *)

Definition correct_interf_instr
    (live: Regset.t) (instr: instruction) (g: graph) : Prop :=
  match instr with
  | Iop op args res s =>
      match is_move_operation op args with
      | Some arg =>
          forall r,
          Regset.In res live ->
          Regset.In r live ->
          r <> res -> r <> arg -> interfere r res g
      | None =>
          forall r,
          Regset.In res live ->
          Regset.In r live ->
          r <> res -> interfere r res g
      end
  | Iload chunk addr args res s =>
      forall r,
      Regset.In res live ->
      Regset.In r live ->
      r <> res -> interfere r res g
  | Icall sig ros args res s =>
      (forall r mr,
        Regset.In r live ->
        In mr destroyed_at_call_regs ->
        r <> res ->
        interfere_mreg r mr g)
   /\ (forall r,
        Regset.In r live ->
        r <> res -> interfere r res g)
  | Ialloc arg res s =>
      (forall r mr,
        Regset.In r live ->
        In mr destroyed_at_call_regs ->
        r <> res ->
        interfere_mreg r mr g)
   /\ (forall r,
        Regset.In r live ->
        r <> res -> interfere r res g)
  | _ =>
      True
  end.

Lemma correct_interf_instr_incl:
  forall live instr g1 g2,
  graph_incl g1 g2 ->
  correct_interf_instr live instr g1 ->
  correct_interf_instr live instr g2.
Proof.
  intros until g2. intro. 
  unfold correct_interf_instr; destruct instr; auto.
  destruct (is_move_operation o l).
  intros. eapply interfere_incl; eauto.
  intros. eapply interfere_incl; eauto.
  intros. eapply interfere_incl; eauto.
  intros [A B]. split.
  intros. eapply interfere_mreg_incl; eauto.
  intros. eapply interfere_incl; eauto.
  intros [A B]. split.
  intros. eapply interfere_mreg_incl; eauto.
  intros. eapply interfere_incl; eauto.
Qed.

Lemma add_edges_instr_correct:
  forall sig instr live g,
  correct_interf_instr live instr (add_edges_instr sig instr live g).
Proof.
  intros.
  destruct instr; unfold add_edges_instr; unfold correct_interf_instr; auto.
  destruct (is_move_operation o l); intros.
  rewrite Regset.mem_1; auto. eapply interfere_incl. 
  apply add_pref_incl. apply add_interf_move_correct; auto.
  rewrite Regset.mem_1; auto. apply add_interf_op_correct; auto. 

  intros. rewrite Regset.mem_1; auto. apply add_interf_op_correct; auto.

  split; intros.
  apply interfere_mreg_incl with
    (add_interf_call (Regset.remove r live) destroyed_at_call_regs g).
  eapply graph_incl_trans; [idtac|apply add_prefs_call_incl].
  eapply graph_incl_trans; [idtac|apply add_pref_mreg_incl].
  apply add_interf_op_incl.
  apply add_interf_call_correct; auto.
  apply Regset.remove_2; auto. 

  eapply interfere_incl.
  eapply graph_incl_trans; [idtac|apply add_prefs_call_incl].
  apply add_pref_mreg_incl.
  apply add_interf_op_correct; auto.

  split; intros.
  apply interfere_mreg_incl with
    (add_interf_call (Regset.remove r0 live) destroyed_at_call_regs g).
  eapply graph_incl_trans; [idtac|apply add_pref_mreg_incl].
  eapply graph_incl_trans; [idtac|apply add_pref_mreg_incl].
  apply add_interf_op_incl.
  apply add_interf_call_correct; auto.
  apply Regset.remove_2; auto.

  eapply interfere_incl.
  eapply graph_incl_trans; apply add_pref_mreg_incl.
  apply add_interf_op_correct; auto.
Qed.

Lemma add_edges_instrs_incl_aux:
  forall sig live instrs g,
  graph_incl g
    (fold_left
       (fun (a : graph) (p : positive * instruction) =>
          add_edges_instr sig (snd p) live !! (fst p) a)
       instrs g).
Proof.
  induction instrs; simpl; intros.
  apply graph_incl_refl.
  eapply graph_incl_trans; [idtac|eauto].
  apply add_edges_instr_incl.
Qed.

Lemma add_edges_instrs_correct_aux:
  forall sig live instrs g pc i,
  In (pc, i) instrs ->
  correct_interf_instr live!!pc i
    (fold_left
       (fun (a : graph) (p : positive * instruction) =>
          add_edges_instr sig (snd p) live !! (fst p) a)
       instrs g).
Proof.
  induction instrs; simpl; intros.
  elim H.
  elim H; intro.
  subst a; simpl. eapply correct_interf_instr_incl.
  apply add_edges_instrs_incl_aux.
  apply add_edges_instr_correct.
  auto.
Qed.

Lemma add_edges_instrs_correct:
  forall f live pc i,
  f.(fn_code)!pc = Some i ->
  correct_interf_instr live!!pc i (add_edges_instrs f live).
Proof.
  intros.
  unfold add_edges_instrs.
  rewrite PTree.fold_spec.
  apply add_edges_instrs_correct_aux.
  apply PTree.elements_correct. auto.
Qed.

(** Here are the three correctness properties of the generated
  inference graph.  First, it contains the conflict edges
  needed by every instruction of the function. *)

Lemma interf_graph_correct_1:
  forall f live live0 pc i,
  f.(fn_code)!pc = Some i ->
  correct_interf_instr live!!pc i (interf_graph f live live0).
Proof.
  intros. unfold interf_graph.
  apply correct_interf_instr_incl with (add_edges_instrs f live).
  eapply graph_incl_trans; [idtac|apply add_prefs_call_incl].
  eapply graph_incl_trans; [idtac|apply add_interf_params_incl].
  apply add_interf_entry_incl.
  apply add_edges_instrs_correct; auto.
Qed.

(** Second, function parameters conflict pairwise. *)

Lemma interf_graph_correct_2:
  forall f live live0 r1 r2,
  In r1 f.(fn_params) ->
  In r2 f.(fn_params) ->
  r1 <> r2 ->
  interfere r1 r2 (interf_graph f live live0).
Proof.
  intros. unfold interf_graph. 
  eapply interfere_incl.
  apply add_prefs_call_incl.
  apply add_interf_params_correct; auto.
Qed.

(** Third, function parameters conflict pairwise with pseudo-registers
  live at function entry.  If the function never uses a pseudo-register
  before it is defined, pseudo-registers live at function entry
  are a subset of the function parameters and therefore this condition
  is implied by [interf_graph_correct_3].  However, we prefer not
  to make this assumption. *)

Lemma interf_graph_correct_3:
  forall f live live0 r1 r2,
  In r1 f.(fn_params) ->
  Regset.In r2 live0 ->
  r1 <> r2 ->
  interfere r1 r2 (interf_graph f live live0).
Proof.
  intros. unfold interf_graph.
  eapply interfere_incl.
  eapply graph_incl_trans; [idtac|apply add_prefs_call_incl].
  apply add_interf_params_incl.
  apply add_interf_entry_correct; auto.
Qed.

(** * Correctness of the a priori checks over the result of graph coloring *)

(** We now show that the checks performed over the candidate coloring
  returned by [graph_coloring] are correct: candidate colorings that
  pass these checks are indeed correct colorings. *)

Section CORRECT_COLORING.

Variable g: graph.
Variable env: regenv.
Variable allregs: Regset.t.
Variable coloring: reg -> loc.

Lemma check_coloring_1_correct:
  forall r1 r2,
  check_coloring_1 g coloring = true ->
  SetRegReg.In (r1, r2) g.(interf_reg_reg) ->
  coloring r1 <> coloring r2.
Proof.
  unfold check_coloring_1. intros. 
  assert (FSetInterface.compat_bool OrderedRegReg.eq
     (fun r1r2 => if Loc.eq (coloring (fst r1r2)) (coloring (snd r1r2))
                  then false else true)).
  red. unfold OrderedRegReg.eq. unfold OrderedReg.eq.
  intros x y [EQ1 EQ2]. rewrite EQ1; rewrite EQ2; auto.
  generalize (SetRegReg.for_all_2 _ _ H1 H _ H0). 
  simpl. case (Loc.eq (coloring r1) (coloring r2)); intro.
  intro; discriminate. auto.
Qed.

Lemma check_coloring_2_correct:
  forall r1 mr2,
  check_coloring_2 g coloring = true ->
  SetRegMreg.In (r1, mr2) g.(interf_reg_mreg) ->
  coloring r1 <> R mr2.
Proof.
  unfold check_coloring_2. intros. 
  assert (FSetInterface.compat_bool OrderedRegMreg.eq
     (fun r1r2 => if Loc.eq (coloring (fst r1r2)) (R (snd r1r2))
                  then false else true)).
  red. unfold OrderedRegMreg.eq. unfold OrderedReg.eq.
  intros x y [EQ1 EQ2]. rewrite EQ1; rewrite EQ2; auto.
  generalize (SetRegMreg.for_all_2 _ _ H1 H _ H0). 
  simpl. case (Loc.eq (coloring r1) (R mr2)); intro.
  intro; discriminate. auto.
Qed.

Lemma same_typ_correct:
  forall t1 t2, same_typ t1 t2 = true -> t1 = t2.
Proof.
  destruct t1; destruct t2; simpl; congruence.
Qed.

Lemma loc_is_acceptable_correct:
  forall l, loc_is_acceptable l = true -> loc_acceptable l.
Proof.
  destruct l; unfold loc_is_acceptable, loc_acceptable.
  case (In_dec Loc.eq (R m) temporaries); intro.
  intro; discriminate. auto.
  destruct s.
  case (zlt z 0); intro. intro; discriminate. auto.
  intro; discriminate.
  intro; discriminate.
Qed.

Lemma check_coloring_3_correct:
  forall r,
  check_coloring_3 allregs env coloring = true ->
  Regset.mem r allregs = true ->
  loc_acceptable (coloring r) /\ env r = Loc.type (coloring r).
Proof.
  unfold check_coloring_3; intros.
  exploit Regset.for_all_2; eauto.
  red; intros. hnf in H1. congruence.
  apply Regset.mem_2. eauto.
  simpl. intro. elim (andb_prop _ _ H1); intros.
  split. apply loc_is_acceptable_correct; auto.
  apply same_typ_correct; auto.
Qed.

End CORRECT_COLORING.

(** * Correctness of clipping *)

(** We then show the correctness of the ``clipped'' coloring
  returned by [alloc_of_coloring] applied to a candidate coloring
  that passes the a posteriori checks. *)

Section ALLOC_OF_COLORING.

Variable g: graph.
Variable env: regenv.
Let allregs := all_interf_regs g.
Variable coloring: reg -> loc.
Let alloc := alloc_of_coloring coloring env allregs.

Lemma alloc_of_coloring_correct_1:
  forall r1 r2,
  check_coloring g env allregs coloring = true ->
  SetRegReg.In (r1, r2) g.(interf_reg_reg) ->
  alloc r1 <> alloc r2.
Proof.
  unfold check_coloring, alloc, alloc_of_coloring; intros.
  elim (andb_prop _ _ H); intros.
  generalize (all_interf_regs_correct_1 _ _ _ H0).
  intros [A B].
  unfold allregs. rewrite Regset.mem_1; auto. rewrite Regset.mem_1; auto.
  eapply check_coloring_1_correct; eauto.
Qed.

Lemma alloc_of_coloring_correct_2:
  forall r1 mr2,
  check_coloring g env allregs coloring = true ->
  SetRegMreg.In (r1, mr2) g.(interf_reg_mreg) ->
  alloc r1 <> R mr2.
Proof.
  unfold check_coloring, alloc, alloc_of_coloring; intros.
  elim (andb_prop _ _ H); intros.
  elim (andb_prop _ _ H2); intros.
  generalize (all_interf_regs_correct_2 _ _ _ H0). intros.
  unfold allregs. rewrite Regset.mem_1; auto. 
  eapply check_coloring_2_correct; eauto.
Qed.

Lemma alloc_of_coloring_correct_3:
  forall r,
  check_coloring g env allregs coloring = true ->
  loc_acceptable (alloc r).
Proof.
  unfold check_coloring, alloc, alloc_of_coloring; intros.
  elim (andb_prop _ _ H); intros.
  elim (andb_prop _ _ H1); intros.
  caseEq (Regset.mem r allregs); intro.
  generalize (check_coloring_3_correct _ _ _ r H3 H4). tauto.
  case (env r); simpl; intuition congruence. 
Qed.

Lemma alloc_of_coloring_correct_4:
  forall r,
  check_coloring g env allregs coloring = true ->
  env r = Loc.type (alloc r).
Proof.
  unfold check_coloring, alloc, alloc_of_coloring; intros.
  elim (andb_prop _ _ H); intros.
  elim (andb_prop _ _ H1); intros.
  caseEq (Regset.mem r allregs); intro.
  generalize (check_coloring_3_correct _ _ _ r H3 H4). tauto.
  case (env r); reflexivity.
Qed.

End ALLOC_OF_COLORING.

(** * Correctness of the whole graph coloring algorithm *)

(** Combining results from the previous sections, we now summarize
  the correctness properties of the assignment (of locations to
  registers) returned by [regalloc]. *)

Definition correct_alloc_instr
    (live: PMap.t Regset.t) (alloc: reg -> loc) 
    (pc: node) (instr: instruction) : Prop :=
  match instr with
  | Iop op args res s =>
      match is_move_operation op args with
      | Some arg =>
          forall r,
          Regset.In res live!!pc ->
          Regset.In r live!!pc ->
          r <> res -> r <> arg -> alloc r <> alloc res
      | None =>
          forall r,
          Regset.In res live!!pc ->
          Regset.In r live!!pc ->
          r <> res -> alloc r <> alloc res
      end
  | Iload chunk addr args res s =>
      forall r,
      Regset.In res live!!pc ->
      Regset.In r live!!pc ->
      r <> res -> alloc r <> alloc res
  | Icall sig ros args res s =>
      (forall r,
        Regset.In r live!!pc ->
        r <> res ->
        ~(In (alloc r) Conventions.destroyed_at_call))
   /\ (forall r,
        Regset.In r live!!pc ->
        r <> res -> alloc r <> alloc res)
  | Ialloc arg res s =>
      (forall r,
        Regset.In r live!!pc ->
        r <> res ->
        ~(In (alloc r) Conventions.destroyed_at_call))
   /\ (forall r,
        Regset.In r live!!pc ->
        r <> res -> alloc r <> alloc res)
  | _ =>
      True
  end.

Section REGALLOC_PROPERTIES.

Variable f: function.
Variable env: regenv.
Variable live: PMap.t Regset.t.
Variable live0: Regset.t.
Variable alloc: reg -> loc.

Let g := interf_graph f live live0.
Let allregs := all_interf_regs g.
Let coloring := graph_coloring f g env allregs.

Lemma regalloc_ok:
  regalloc f live live0 env = Some alloc ->
  check_coloring g env allregs coloring = true /\
  alloc = alloc_of_coloring coloring env allregs.
Proof.
  unfold regalloc, coloring, allregs, g.
  case (check_coloring (interf_graph f live live0) env).
  intro EQ; injection EQ; intro; clear EQ.
  split. auto. auto.
  intro; discriminate.
Qed.

Lemma regalloc_acceptable:
  forall r,
  regalloc f live live0 env = Some alloc ->
  loc_acceptable (alloc r).
Proof.
  intros. elim (regalloc_ok H); intros.
  rewrite H1. unfold allregs. apply alloc_of_coloring_correct_3.
  exact H0.
Qed.

Lemma regsalloc_acceptable:
  forall rl,
  regalloc f live live0 env = Some alloc ->
  locs_acceptable (List.map alloc rl).
Proof.
  intros; red; intros.
  elim (list_in_map_inv _ _ _ H0). intros r [EQ IN].
  subst l. apply regalloc_acceptable. auto. 
Qed.

Lemma regalloc_preserves_types:
  forall r,
  regalloc f live live0 env = Some alloc ->
  Loc.type (alloc r) = env r.
Proof.
  intros. elim (regalloc_ok H); intros.
  rewrite H1. unfold allregs. symmetry.
  apply alloc_of_coloring_correct_4.
  exact H0.
Qed.

Lemma correct_interf_alloc_instr:
  forall pc instr,
  (forall r1 r2, interfere r1 r2 g -> alloc r1 <> alloc r2) ->
  (forall r1 mr2, interfere_mreg r1 mr2 g -> alloc r1 <> R mr2) ->
  correct_interf_instr live!!pc instr g ->
  correct_alloc_instr live alloc pc instr.
Proof.
  intros pc instr ALL1 ALL2.
  unfold correct_interf_instr, correct_alloc_instr;
  destruct instr; auto.
  destruct (is_move_operation o l); auto.
  intros [A B]. split. 
  intros; red; intros. 
  unfold destroyed_at_call in H1.
  generalize (list_in_map_inv R _ _ H1). 
  intros [mr [EQ IN]]. 
  generalize (A r0 mr H IN H0). intro.
  generalize (ALL2 _ _ H2). contradiction.
  auto.
  intros [A B]. split. 
  intros; red; intros. 
  unfold destroyed_at_call in H1.
  generalize (list_in_map_inv R _ _ H1). 
  intros [mr [EQ IN]]. 
  generalize (A r1 mr H IN H0). intro.
  generalize (ALL2 _ _ H2). contradiction.
  auto.
Qed.
  
Lemma regalloc_correct_1:
  forall pc instr,
  regalloc f live live0 env = Some alloc ->
  f.(fn_code)!pc = Some instr ->
  correct_alloc_instr live alloc pc instr.
Proof.
  intros. elim (regalloc_ok H); intros.
  apply correct_interf_alloc_instr.
  intros. rewrite H2. unfold allregs. red in H3. 
  elim (ordered_pair_charact r1 r2); intro.
  apply alloc_of_coloring_correct_1. auto. rewrite H4 in H3; auto.
  apply sym_not_equal.
  apply alloc_of_coloring_correct_1. auto. rewrite H4 in H3; auto.
  intros. rewrite H2. unfold allregs.
  apply alloc_of_coloring_correct_2. auto. exact H3.
  unfold g. apply interf_graph_correct_1. auto. 
Qed.

Lemma regalloc_correct_2:
  regalloc f live live0 env = Some alloc ->
  list_norepet f.(fn_params) ->
  list_norepet (List.map alloc f.(fn_params)).
Proof.
  intros. elim (regalloc_ok H); intros.
  apply list_map_norepet; auto.
  intros. rewrite H2. unfold allregs. 
  elim (ordered_pair_charact x y); intro.
  apply alloc_of_coloring_correct_1. auto. 
  change OrderedReg.t with reg. rewrite <- H6.
  change (interfere x y g). unfold g. 
  apply interf_graph_correct_2; auto.
  apply sym_not_equal.
  apply alloc_of_coloring_correct_1. auto. 
  change OrderedReg.t with reg. rewrite <- H6.
  change (interfere x y g). unfold g. 
  apply interf_graph_correct_2; auto.
Qed.

Lemma regalloc_correct_3:
  forall r1 r2,
  regalloc f live live0 env = Some alloc ->
  In r1 f.(fn_params) ->
  Regset.In r2 live0 ->
  r1 <> r2 ->
  alloc r1 <> alloc r2.
Proof.
  intros. elim (regalloc_ok H); intros.
  rewrite H4; unfold allregs.
  elim (ordered_pair_charact r1 r2); intro.
  apply alloc_of_coloring_correct_1. auto. 
  change OrderedReg.t with reg. rewrite <- H5.
  change (interfere r1 r2 g). unfold g.
  apply interf_graph_correct_3; auto.
  apply sym_not_equal.
  apply alloc_of_coloring_correct_1. auto. 
  change OrderedReg.t with reg. rewrite <- H5.
  change (interfere r1 r2 g). unfold g.
  apply interf_graph_correct_3; auto.
Qed.

End REGALLOC_PROPERTIES.

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

(** Correctness proof for the [Debugvar] pass. *)

Require Import Axioms Coqlib Maps Iteration Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Machregs Locations Conventions Op Linear.
Require Import Debugvar.

(** * Relational characterization of the transformation *)

Definition match_prog (p tp: program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Inductive match_code: code -> code -> Prop :=
  | match_code_nil:
      match_code nil nil
  | match_code_cons: forall i before after c c',
      match_code c c' ->
      match_code (i :: c) (i :: add_delta_ranges before after c').

Remark diff_same:
  forall s, diff s s = nil.
Proof.
  induction s as [ | [v i] s]; simpl.
  auto.
  rewrite Pos.compare_refl. rewrite dec_eq_true. auto.
Qed.

Remark delta_state_same:
  forall s, delta_state s s = (nil, nil).
Proof.
  destruct s; simpl. rewrite ! diff_same; auto. auto.
Qed.

Lemma transf_code_match:
  forall lm c before, match_code c (transf_code lm before c).
Proof.
  intros lm. fix REC 1. destruct c; intros before; simpl.
- constructor.
- assert (DEFAULT: forall before after,
            match_code (i :: c)
                       (i :: add_delta_ranges before after (transf_code lm after c))).
  { intros. constructor. apply REC. }
  destruct i; auto. destruct c; auto. destruct i; auto.
  set (after := get_label l0 lm).
  set (c1 := Llabel l0 :: add_delta_ranges before after (transf_code lm after c)).
  replace c1 with (add_delta_ranges before before c1).
  constructor. constructor. apply REC.
  unfold add_delta_ranges. rewrite delta_state_same. auto.
Qed.

Inductive match_function: function -> function -> Prop :=
  | match_function_intro: forall f c,
      match_code f.(fn_code) c ->
      match_function f (mkfunction f.(fn_sig) f.(fn_stacksize) c).

Lemma transf_function_match:
  forall f tf, transf_function f = OK tf -> match_function f tf.
Proof.
  unfold transf_function; intros.
  destruct (ana_function f) as [lm|]; inv H.
  constructor. apply transf_code_match.
Qed.

Remark find_label_add_delta_ranges:
  forall lbl c before after, find_label lbl (add_delta_ranges before after c) = find_label lbl c.
Proof.
  intros. unfold add_delta_ranges.
  destruct (delta_state before after) as [killed born].
  induction killed as [ | [v i] l]; simpl; auto.
  induction born as [ | [v i] l]; simpl; auto.
Qed.

Lemma find_label_match_rec:
  forall lbl c' c tc,
  match_code c tc ->
  find_label lbl c = Some c' ->
  exists before after tc', find_label lbl tc = Some (add_delta_ranges before after tc') /\ match_code c' tc'.
Proof.
  induction 1; simpl; intros.
- discriminate.
- destruct (is_label lbl i).
  inv H0. econstructor; econstructor; econstructor; eauto.
  rewrite find_label_add_delta_ranges. auto.
Qed.

Lemma find_label_match:
  forall f tf lbl c,
  match_function f tf ->
  find_label lbl f.(fn_code) = Some c ->
  exists before after tc, find_label lbl tf.(fn_code) = Some (add_delta_ranges before after tc) /\ match_code c tc.
Proof.
  intros. inv H. eapply find_label_match_rec; eauto.
Qed.

(** * Properties of availability sets *)

(** These properties are not used in the semantic preservation proof,
    but establish some confidence in the availability analysis. *)

Definition avail_above (v: ident) (s: avail) : Prop :=
  forall v' i', In (v', i') s -> Plt v v'.

Inductive wf_avail: avail -> Prop :=
  | wf_avail_nil:
      wf_avail nil
  | wf_avail_cons: forall v i s,
     avail_above v s ->
     wf_avail s ->
     wf_avail ((v, i) :: s).

Lemma set_state_1:
  forall v i s, In (v, i) (set_state v i s).
Proof.
  induction s as [ | [v' i'] s]; simpl.
- auto.
- destruct (Pos.compare v v'); simpl; auto.
Qed.

Lemma set_state_2:
  forall v i v' i' s,
  v' <> v -> In (v', i') s -> In (v', i') (set_state v i s).
Proof.
  induction s as [ | [v1 i1] s]; simpl; intros.
- contradiction.
- destruct (Pos.compare_spec v v1); simpl.
+ subst v1. destruct H0. congruence. auto.
+ auto.
+ destruct H0; auto.
Qed.

Lemma set_state_3:
  forall v i v' i' s,
  wf_avail s ->
  In (v', i') (set_state v i s) ->
  (v' = v /\ i' = i) \/ (v' <> v /\ In (v', i') s).
Proof.
  induction 1; simpl; intros.
- intuition congruence.
- destruct (Pos.compare_spec v v0); simpl in H1.
+ subst v0. destruct H1. inv H1; auto. right; split.
  apply not_eq_sym. apply Plt_ne. eapply H; eauto.
  auto.
+ destruct H1. inv H1; auto.
  destruct H1. inv H1. right; split; auto. apply not_eq_sym. apply Plt_ne. auto.
  right; split; auto. apply not_eq_sym. apply Plt_ne. apply Plt_trans with v0; eauto.
+ destruct H1. inv H1. right; split; auto. apply Plt_ne. auto.
  destruct IHwf_avail as [A | [A B]]; auto.
Qed.

Lemma wf_set_state:
  forall v i s, wf_avail s -> wf_avail (set_state v i s).
Proof.
  induction 1; simpl.
- constructor. red; simpl; tauto. constructor.
- destruct (Pos.compare_spec v v0).
+ subst v0. constructor; auto.
+ constructor.
  red; simpl; intros. destruct H2.
  inv H2. auto. apply Plt_trans with v0; eauto.
  constructor; auto.
+ constructor.
  red; intros. exploit set_state_3. eexact H0. eauto. intros [[A B] | [A B]]; subst; eauto.
  auto.
Qed.

Lemma remove_state_1:
  forall v i s, wf_avail s -> ~ In (v, i) (remove_state v s).
Proof.
  induction 1; simpl; red; intros.
- auto.
- destruct (Pos.compare_spec v v0); simpl in *.
+ subst v0. elim (Plt_strict v); eauto.
+ destruct H1. inv H1.  elim (Plt_strict v); eauto.
  elim (Plt_strict v). apply Plt_trans with v0; eauto.
+ destruct H1. inv H1. elim (Plt_strict v); eauto.  tauto.
Qed.

Lemma remove_state_2:
  forall v v' i' s, v' <> v -> In (v', i') s -> In (v', i') (remove_state v s).
Proof.
  induction s as [ | [v1 i1] s]; simpl; intros.
- auto.
- destruct (Pos.compare_spec v v1); simpl.
+ subst v1. destruct H0. congruence. auto.
+ auto.
+ destruct H0; auto.
Qed.

Lemma remove_state_3:
  forall v v' i' s, wf_avail s -> In (v', i') (remove_state v s) -> v' <> v /\ In (v', i') s.
Proof.
  induction 1; simpl; intros.
- contradiction.
- destruct (Pos.compare_spec v v0); simpl in H1.
+ subst v0. split; auto. apply not_eq_sym; apply Plt_ne; eauto.
+ destruct H1. inv H1. split; auto. apply not_eq_sym; apply Plt_ne; eauto.
  split; auto. apply not_eq_sym; apply Plt_ne. apply Plt_trans with v0; eauto.
+ destruct H1. inv H1. split; auto. apply Plt_ne; auto.
  destruct IHwf_avail as [A B] ; auto.
Qed.

Lemma wf_remove_state:
  forall v s, wf_avail s -> wf_avail (remove_state v s).
Proof.
  induction 1; simpl.
- constructor.
- destruct (Pos.compare_spec v v0).
+ auto.
+ constructor; auto.
+ constructor; auto. red; intros.
  exploit remove_state_3. eexact H0. eauto. intros [A B]. eauto.
Qed.

Lemma wf_filter:
  forall pred s, wf_avail s -> wf_avail (List.filter pred s).
Proof.
  induction 1; simpl.
- constructor.
- destruct (pred (v, i)) eqn:P; auto.
  constructor; auto.
  red; intros. apply filter_In in H1. destruct H1. eauto.
Qed.

Lemma join_1:
  forall v i s1, wf_avail s1 -> forall s2, wf_avail s2 ->
  In (v, i) s1 -> In (v, i) s2 -> In (v, i) (join s1 s2).
Proof.
  induction 1; simpl; try tauto; induction 1; simpl; intros I1 I2; auto.
  destruct I1, I2.
- inv H3; inv H4. rewrite Pos.compare_refl. rewrite dec_eq_true; auto with coqlib.
- inv H3.
  assert (L: Plt v1 v) by eauto. apply Pos.compare_gt_iff in L. rewrite L. auto.
- inv H4.
  assert (L: Plt v0 v) by eauto. apply Pos.compare_lt_iff in L. rewrite L. apply IHwf_avail. constructor; auto. auto. auto with coqlib.
- destruct (Pos.compare v0 v1).
+ destruct (eq_debuginfo i0 i1); auto with coqlib.
+ apply IHwf_avail; auto with coqlib. constructor; auto.
+ eauto.
Qed.

Lemma join_2:
  forall v i s1, wf_avail s1 -> forall s2, wf_avail s2 ->
  In (v, i) (join s1 s2) -> In (v, i) s1 /\ In (v, i) s2.
Proof.
  induction 1; simpl; try tauto; induction 1; simpl; intros I; try tauto.
  destruct (Pos.compare_spec v0 v1).
- subst v1. destruct (eq_debuginfo i0 i1).
  + subst i1. destruct I. auto. exploit IHwf_avail; eauto. tauto.
  + exploit IHwf_avail; eauto. tauto.
- exploit (IHwf_avail ((v1, i1) :: s0)); eauto. constructor; auto.
  simpl. tauto.
- exploit IHwf_avail0; eauto. tauto.
Qed.

Lemma wf_join:
  forall s1, wf_avail s1 -> forall s2, wf_avail s2 -> wf_avail (join s1 s2).
Proof.
  induction 1; simpl; induction 1; simpl; try constructor.
  destruct (Pos.compare_spec v v0).
- subst v0. destruct (eq_debuginfo i i0); auto. constructor; auto.
  red; intros. apply join_2 in H3; auto. destruct H3. eauto.
- apply IHwf_avail. constructor; auto.
- apply IHwf_avail0.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.

Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  funsig tf = funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H.
  exploit transf_function_match; eauto. intros M; inv M; auto.
  inv H. reflexivity.
Qed.

Lemma find_function_translated:
  forall ros ls f,
  find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros ls = Some tf /\ transf_fundef f = OK tf.
Proof.
  unfold find_function; intros; destruct ros; simpl.
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

(** Evaluation of the debug annotations introduced by the transformation. *)

Lemma can_eval_safe_arg:
  forall (rs: locset) sp m (a: builtin_arg loc),
  safe_builtin_arg a -> exists v, eval_builtin_arg tge rs sp m a v.
Proof.
  induction a; simpl; intros; try contradiction;
  try (econstructor; now eauto with barg).
  destruct H as [S1 S2].
  destruct (IHa1 S1) as [v1 E1]. destruct (IHa2 S2) as [v2 E2].
  exists (Val.longofwords v1 v2); auto with barg.
Qed.

Lemma eval_add_delta_ranges:
  forall s f sp c rs m before after,
  star step tge (State s f sp (add_delta_ranges before after c) rs m)
             E0 (State s f sp c rs m).
Proof.
  intros. unfold add_delta_ranges.
  destruct (delta_state before after) as [killed born].
  induction killed as [ | [v i] l]; simpl.
- induction born as [ | [v i] l]; simpl.
+ apply star_refl.
+ destruct i as [a SAFE]; simpl.
  exploit can_eval_safe_arg; eauto. intros [v1 E1].
  eapply star_step; eauto.
  econstructor.
  constructor. eexact E1. constructor.
  simpl; constructor.
  simpl; auto.
  traceEq.
- eapply star_step; eauto.
  econstructor.
  constructor.
  simpl; constructor.
  simpl; auto.
  traceEq.
Qed.

(** Matching between program states. *)

Inductive match_stackframes: Linear.stackframe -> Linear.stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp rs c tf tc before after,
      match_function f tf ->
      match_code c tc ->
      match_stackframes
        (Stackframe f sp rs c)
        (Stackframe tf sp rs (add_delta_ranges before after tc)).

Inductive match_states: Linear.state ->  Linear.state -> Prop :=
  | match_states_instr:
      forall s f sp c rs m tf ts tc
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: match_function f tf)
        (TRC: match_code c tc),
      match_states (State s f sp c rs m)
                   (State ts tf sp tc rs m)
  | match_states_call:
      forall s f rs m tf ts,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      match_states (Callstate s f rs m)
                   (Callstate ts tf rs m)
  | match_states_return:
      forall s rs m ts,
      list_forall2 match_stackframes s ts ->
      match_states (Returnstate s rs m)
                   (Returnstate ts rs m).

Lemma parent_locset_match:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  parent_locset ts = parent_locset s.
Proof.
  induction 1; simpl. auto. inv H; auto.
Qed.

(** The simulation diagram. *)

Theorem transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall ts1 (MS: match_states s1 ts1),
  exists ts2, plus step tge ts1 t ts2 /\ match_states s2 ts2.
Proof.
  induction 1; intros ts1 MS; inv MS; try (inv TRC).
- (* getstack *)
  econstructor; split.
  eapply plus_left. constructor; auto. apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* setstack *)
  econstructor; split.
  eapply plus_left. constructor; auto. apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* op *)
  econstructor; split.
  eapply plus_left.
  econstructor; eauto.
  instantiate (1 := v). rewrite <- H; apply eval_operation_preserved; exact symbols_preserved.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* load *)
  econstructor; split.
  eapply plus_left.
  eapply exec_Lload with (a := a).
  rewrite <- H; apply eval_addressing_preserved; exact symbols_preserved.
  eauto. eauto.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* store *)
  econstructor; split.
  eapply plus_left.
  eapply exec_Lstore with (a := a).
  rewrite <- H; apply eval_addressing_preserved; exact symbols_preserved.
  eauto. eauto.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* call *)
  exploit find_function_translated; eauto. intros (tf' & A & B).
  econstructor; split.
  apply plus_one.
  econstructor. eexact A. symmetry; apply sig_preserved; auto. traceEq.
  constructor; auto. constructor; auto. constructor; auto.
- (* tailcall *)
  exploit find_function_translated; eauto. intros (tf' & A & B).
  exploit parent_locset_match; eauto. intros PLS.
  econstructor; split.
  apply plus_one.
  econstructor. eauto. rewrite PLS. eexact A.
  symmetry; apply sig_preserved; auto.
  inv TRF; eauto. traceEq.
  rewrite PLS. constructor; auto.
- (* builtin *)
  econstructor; split.
  eapply plus_left.
  econstructor; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* label *)
  econstructor; split.
  eapply plus_left. constructor; auto. apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* goto *)
  exploit find_label_match; eauto. intros (before' & after' & tc' & A & B).
  econstructor; split.
  eapply plus_left. constructor; eauto. apply eval_add_delta_ranges; eauto. traceEq.
  constructor; auto.
- (* cond taken *)
  exploit find_label_match; eauto. intros (before' & after' & tc' & A & B).
  econstructor; split.
  eapply plus_left. eapply exec_Lcond_true; eauto. apply eval_add_delta_ranges; eauto. traceEq.
  constructor; auto.
- (* cond not taken *)
  econstructor; split.
  eapply plus_left. eapply exec_Lcond_false; auto. apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* jumptable *)
  exploit find_label_match; eauto. intros (before' & after' & tc' & A & B).
  econstructor; split.
  eapply plus_left. econstructor; eauto.
  apply eval_add_delta_ranges. reflexivity. traceEq.
  constructor; auto.
- (* return *)
  econstructor; split.
  apply plus_one.  constructor. inv TRF; eauto. traceEq.
  rewrite (parent_locset_match _ _ STACKS). constructor; auto.
- (* internal function *)
  monadInv H7. rename x into tf.
  assert (MF: match_function f tf) by (apply transf_function_match; auto).
  inversion MF; subst.
  econstructor; split.
  apply plus_one. constructor. simpl; eauto. reflexivity.
  constructor; auto.
- (* external function *)
  monadInv H8. econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inv H3. inv H1.
  econstructor; split.
  eapply plus_left. econstructor. apply eval_add_delta_ranges. traceEq.
  constructor; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists (Callstate nil tf (Locmap.init Vundef) m0); split.
  econstructor; eauto. eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  rewrite (match_program_main TRANSF), symbols_preserved. auto.
  rewrite <- H3. apply sig_preserved. auto.
  constructor. constructor. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct.
Qed.

End PRESERVATION.

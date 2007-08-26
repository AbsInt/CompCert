(** Corollaries of the main semantic preservation theorem. *)

Require Import Classical.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import PPC.
Require Import Main.

(** * Determinism of PPC semantics *)

(** In this section, we show that the semantics for the PPC language
  are deterministic, in a sense to be made precise later.
  There are two sources of apparent non-determinism:
- The semantics leaves unspecified the results of calls to external 
  functions.  Different results to e.g. a "read" operation can of
  course lead to different behaviors for the program.
  We address this issue by modeling a notion of deterministic
  external world that uniquely determines the results of external calls.
- For diverging executions, the trace of I/O events is not uniquely
  determined: it can contain events that will never be performed
  because the program diverges earlier.  We address this issue
  by showing the existence of a minimal trace for diverging executions.

*)

(** ** Deterministic worlds *)

(** An external world is a function that, given the name of an
  external call and its arguments, returns either [None], meaning
  that this external call gets stuck, or [Some(r,w)], meaning
  that this external call succeeds, has result [r], and changes
  the world to [w]. *)

Inductive world: Set :=
  World: (ident -> list eventval -> option (eventval * world)) -> world.

Definition nextworld (w: world) (evname: ident) (evargs: list eventval) :
                     option (eventval * world) :=
  match w with World f => f evname evargs end.

(** A trace is possible in a given world if all events correspond
  to non-stuck external calls according to the given world.
  Two predicates are defined, for finite and infinite traces respectively:
- [possible_trace w t w'], where [w] is the initial state of the
  world, [t] the finite trace of interest, and [w'] the state of the
  world after performing trace [t].
- [possible_traceinf w T], where [w] is the initial state of the
  world and [T] the possibly infinite trace of interest.
*)

Inductive possible_trace: world -> trace -> world -> Prop :=
  | possible_trace_nil: forall w,
      possible_trace w E0 w
  | possible_trace_cons: forall w0 evname evargs evres w1 t w2,
      nextworld w0 evname evargs = Some (evres, w1) ->
      possible_trace w1 t w2 ->
      possible_trace w0 (mkevent evname evargs evres :: t) w2.

Lemma possible_trace_app:
  forall t2 w2 w0 t1 w1,
  possible_trace w0 t1 w1 -> possible_trace w1 t2 w2 ->
  possible_trace w0 (t1 ** t2) w2.
Proof.
  induction 1; simpl; intros.
  auto.
  econstructor; eauto.
Qed.

Lemma possible_trace_app_inv:
  forall t2 w2 t1 w0,
  possible_trace w0 (t1 ** t2) w2 ->
  exists w1, possible_trace w0 t1 w1 /\ possible_trace w1 t2 w2.
Proof.
  induction t1; simpl; intros.
  exists w0; split. constructor. auto.
  inv H. exploit IHt1; eauto. intros [w1 [A B]]. 
  exists w1; split. econstructor; eauto. auto.
Qed.

CoInductive possible_traceinf: world -> traceinf -> Prop :=
  | possible_traceinf_nil: forall w0,
      possible_traceinf w0 Enilinf
  | possible_traceinf_cons: forall w0 evname evargs evres w1 T,
      nextworld w0 evname evargs = Some (evres, w1) ->
      possible_traceinf w1 T ->
      possible_traceinf w0 (Econsinf (mkevent evname evargs evres) T).

Lemma possible_traceinf_app:
  forall t2 w0 t1 w1,
  possible_trace w0 t1 w1 -> possible_traceinf w1 t2 ->
  possible_traceinf w0 (t1 *** t2).
Proof.
  induction 1; simpl; intros.
  auto.
  econstructor; eauto.
Qed.

Lemma possible_traceinf_app_inv:
  forall t2 t1 w0,
  possible_traceinf w0 (t1 *** t2) ->
  exists w1, possible_trace w0 t1 w1 /\ possible_traceinf w1 t2.
Proof.
  induction t1; simpl; intros.
  exists w0; split. constructor. auto.
  inv H. exploit IHt1; eauto. intros [w1 [A B]]. 
  exists w1; split. econstructor; eauto. auto.
Qed.

Ltac possibleTraceInv :=
  match goal with
  | [H: possible_trace _ (_ ** _) _ |- _] =>
      let P1 := fresh "P" in
      let w := fresh "w" in
      let P2 := fresh "P" in
      elim (possible_trace_app_inv _ _ _ _ H); clear H;
      intros w [P1 P2];
      possibleTraceInv
  | [H: possible_traceinf _ (_ *** _) |- _] =>
      let P1 := fresh "P" in
      let w := fresh "w" in
      let P2 := fresh "P" in
      elim (possible_traceinf_app_inv _ _ _ H); clear H;
      intros w [P1 P2];
      possibleTraceInv
  | _ => idtac
  end.

(** Determinism properties of [event_match]. *)

Remark eventval_match_deterministic:
  forall ev1 ev2 ty v1 v2,
  eventval_match ev1 ty v1 -> eventval_match ev2 ty v2 ->
  (ev1 = ev2 <-> v1 = v2).
Proof.
  intros. inv H; inv H0; intuition congruence.
Qed.

Remark eventval_list_match_deterministic:
  forall ev1 ty v, eventval_list_match ev1 ty v ->
  forall ev2, eventval_list_match ev2 ty v -> ev1 = ev2.
Proof.
  induction 1; intros.
  inv H. auto.
  inv H1. decEq.
  rewrite (eventval_match_deterministic _ _ _ _ _ H H6). auto.
  eauto.
Qed.

Lemma event_match_deterministic:
  forall w0 t1 w1 t2 w2 ef vargs vres1 vres2,
  possible_trace w0 t1 w1 ->
  possible_trace w0 t2 w2 ->
  event_match ef vargs t1 vres1 ->
  event_match ef vargs t2 vres2 ->
  vres1 = vres2 /\ t1 = t2 /\ w1 = w2.
Proof.
  intros. inv H1. inv H2. 
  assert (eargs = eargs0). eapply eventval_list_match_deterministic; eauto. subst eargs0.
  inv H. inv H12. inv H0. inv H12.
  rewrite H11 in H10. inv H10. intuition. 
  rewrite <- (eventval_match_deterministic _ _ _ _ _ H4 H5). auto.
Qed.

(** ** Determinism of PPC transitions. *)

Remark extcall_arguments_deterministic:
  forall rs m sg args args',
  extcall_arguments rs m sg args ->
  extcall_arguments rs m sg args' -> args = args'.
Proof.
  assert (
    forall rs m tyl iregl fregl ofs args,
    extcall_args rs m tyl iregl fregl ofs args ->
    forall args', extcall_args rs m tyl iregl fregl ofs args' -> args = args').
  induction 1; intros.
  inv H. auto.
  inv H1. decEq; eauto.  
  inv H1. decEq. congruence. eauto.
  inv H1. decEq; eauto.  
  inv H1. decEq. congruence. eauto.

  unfold extcall_arguments; intros; eauto.
Qed.

Lemma step_deterministic:
  forall ge s0 t1 s1 t2 s2 w0 w1 w2,
  step ge s0 t1 s1 -> step ge s0 t2 s2 ->
  possible_trace w0 t1 w1 -> possible_trace w0 t2 w2 ->
  s1 = s2 /\ t1 = t2 /\ w1 = w2.
Proof.
  intros. inv H; inv H0.
  assert (c0 = c) by congruence. subst c0.
  assert (i0 = i) by congruence. subst i0.
  split. congruence. split. auto. inv H1; inv H2; auto.
  congruence.
  congruence.
  assert (ef0 = ef) by congruence. subst ef0.
  assert (args0 = args). eapply extcall_arguments_deterministic; eauto. subst args0.
  exploit event_match_deterministic. eexact H1. eexact H2. eauto. eauto.
  intros [A [B C]]. intuition congruence.
Qed.

Lemma initial_state_deterministic:
  forall p s1 s2,
  initial_state p s1 -> initial_state p s2 -> s1 = s2.
Proof.
  intros. inv H; inv H0. reflexivity. 
Qed.

Lemma final_state_not_step:
  forall ge st r t st', final_state st r -> step ge st t st' -> False.
Proof.
  intros. inv H. inv H0.
  unfold Vzero in H1. congruence.
  unfold Vzero in H1. congruence. 
Qed.

Lemma final_state_deterministic:
  forall st r1 r2, final_state st r1 -> final_state st r2 -> r1 = r2.
Proof.
  intros. inv H; inv H0. congruence.
Qed.

(** ** Determinism for terminating executions. *)

(*
Lemma star_star_inv:
  forall ge s t1 s1, star step ge s t1 s1 ->
  forall t2 s2 w w1 w2, star step ge s t2 s2 ->
  possible_trace w t1 w1 -> possible_trace w t2 w2 ->
  exists t, (star step ge s1 t s2 /\ t2 = t1 ** t)
        \/  (star step ge s2 t s1 /\ t1 = t2 ** t).
Proof.
  induction 1; intros.
  exists t2; left; split; auto.
  inv H2. exists (t1 ** t2); right; split. econstructor; eauto. auto.
  possibleTraceInv. 
  exploit step_deterministic. eexact H. eexact H5. eauto. eauto. 
  intros [U [V W]]. subst s5 t3 w3. 
  exploit IHstar; eauto. intros [t [ [Q R] | [Q R] ]].
  subst t4. exists t; left; split. auto. traceEq.
  subst t2. exists t; right; split. auto. traceEq.
Qed.
*)

Lemma steps_deterministic:
  forall ge s0 t1 s1, star step ge s0 t1 s1 -> 
  forall r1 r2 t2 s2 w0 w1 w2, star step ge s0 t2 s2 -> 
  final_state s1 r1 -> final_state s2 r2 ->
  possible_trace w0 t1 w1 -> possible_trace w0 t2 w2 ->
  t1 = t2 /\ r1 = r2.
Proof.
  induction 1; intros. 
  inv H. split. auto. eapply final_state_deterministic; eauto.
  byContradiction. eapply final_state_not_step with (st := s); eauto.
  inv H2. byContradiction. eapply final_state_not_step with (st := s0); eauto.
  possibleTraceInv.
  exploit step_deterministic. eexact H. eexact H7. eauto. eauto. 
  intros [A [B C]]. subst s5 t3 w3.
  exploit IHstar. eexact H8. eauto. eauto. eauto. eauto. 
  intros [A B]. subst t4 r2. 
  auto.
Qed.

(** ** Determinism for infinite transition sequences. *)

Lemma forever_star_inv:
  forall ge s t s', star step ge s t s' ->
  forall T w w', forever step ge s T ->
  possible_trace w t w' -> possible_traceinf w T ->
  exists T',
  forever step ge s' T' /\ possible_traceinf w' T' /\ T = t *** T'.
Proof.
  induction 1; intros.
  inv H0. exists T; auto.
  subst t. possibleTraceInv. 
  inv H2. possibleTraceInv. 
  exploit step_deterministic.
    eexact H. eexact H1. eauto. eauto. intros [A [B C]]; subst s4 t1 w1.
  exploit IHstar; eauto. intros [T' [A [B C]]]. 
  exists T'; split. auto.
  split. auto.
  rewrite C. rewrite Eappinf_assoc; auto.
Qed.

Lemma star_final_not_forever:
  forall ge s1 t s2 r T w1 w2,
  star step ge s1 t s2 ->
  final_state s2 r -> forever step ge s1 T ->
  possible_trace w1 t w2 -> possible_traceinf w1 T ->
  False.
Proof.
  intros. exploit forever_star_inv; eauto. intros [T' [A [B C]]]. 
  inv A. eapply final_state_not_step; eauto.
Qed.

(** ** Minimal traces for divergence. *)

(** There are two mutually exclusive way in which a program can diverge.
  It can diverge in a reactive fashion: it performs infinitely many
  external calls, and the internal computations between two external
  calls are always finite.  Or it can diverge silently: after a finite
  number of external calls, it enters an infinite sequence of internal
  computations. *)

Definition reactive (ge: genv) (s: state) (w: world) :=
  forall t s1 w1,
  star step ge s t s1 -> possible_trace w t w1 ->
  exists s2, exists t', exists s3, exists w2,
  star step ge s1 E0 s2 
  /\ step ge s2 t' s3
  /\ possible_trace w1 t' w2
  /\ t' <> E0.

Definition diverges_silently (ge: genv) (s: state) :=
  forall s2, star step ge s E0 s2 -> exists s3, step ge s2 E0 s3.

Definition diverges_eventually (ge: genv) (s: state) (w: world) :=
  exists t, exists s1, exists w1,
  star step ge s t s1 /\ possible_trace w t w1 /\ diverges_silently ge s1.

(** Using classical logic, we show that any infinite sequence of transitions
  that is possible in a deterministic world is of one of the two forms 
  described above. *)

Lemma reactive_or_diverges:
  forall ge s T w,
  forever step ge s T -> possible_traceinf w T ->
  reactive ge s w \/ diverges_eventually ge s w.
Proof.
  intros. elim (classic (diverges_eventually ge s w)); intro.
  right; auto.
  left. red; intros.
  generalize (not_ex_all_not trace _ H1 t).
  intro. clear H1.
  generalize (not_ex_all_not state _ H4 s1).
  intro. clear H4.
  generalize (not_ex_all_not world _ H1 w1).
  intro. clear H1.
  elim (not_and_or _ _ H4); clear H4; intro.
  contradiction.
  elim (not_and_or _ _ H1); clear H1; intro.
  contradiction.
  generalize (not_all_ex_not state _ H1). intros [s2 A]. clear H1.
  destruct (imply_to_and _ _ A). clear A.
  exploit forever_star_inv.
    eapply star_trans. eexact H2. eexact H1. reflexivity.
    eauto. rewrite E0_right. eauto. eauto. 
  intros [T' [A [B C]]]. 
  inv A. possibleTraceInv. 
  exists s2; exists t0; exists s3; exists w4. intuition.
  subst t0. apply H4. exists s3; auto.
Qed.

(** Moreover, a program cannot be both reactive and silently diverging. *)

Lemma reactive_not_diverges:
  forall ge s w,
  reactive ge s w -> diverges_eventually ge s w -> False.
Proof.
  intros. destruct H0 as [t [s1 [w1 [A [B C]]]]]. 
  destruct (H _ _ _ A B) as [s2 [t' [s3 [w2 [P [Q [R S]]]]]]].
  destruct (C _ P) as [s4 T].
  assert (s3 = s4 /\ t' = E0 /\ w2 = w1).
    eapply step_deterministic; eauto. constructor.
  intuition congruence.
Qed.

(** A program that silently diverges can be given any finite or
  infinite trace of events.  In particular, taking [T' = Enilinf],
  it can be given the empty trace of events. *)

Lemma diverges_forever:
  forall ge s1 T w T',
  diverges_silently ge s1 ->
  forever step ge s1 T ->
  possible_traceinf w T ->
  forever step ge s1 T'.
Proof.
  cofix COINDHYP; intros. inv H0. possibleTraceInv. 
  assert (exists s3, step ge s1 E0 s3). apply H. constructor.
  destruct H0 as [s3 C]. 
  assert (s2 = s3 /\ t = E0 /\ w0 = w). eapply step_deterministic; eauto. constructor.
  destruct H0 as [Q [R S]]. subst s3 t w0. 
  change T' with (E0 *** T'). econstructor. eassumption. 
  eapply COINDHYP; eauto. 
  red; intros. apply H. eapply star_left; eauto. 
Qed.

(** The trace of I/O events generated by a reactive diverging program
  is uniquely determined up to bisimilarity. *)

Lemma reactive_sim:
  forall ge s w T1 T2,
  reactive ge s w ->
  forever step ge s T1 ->
  forever step ge s T2 ->
  possible_traceinf w T1 ->
  possible_traceinf w T2 ->
  traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros.
  elim (H E0 s w); try constructor. 
  intros s2 [t' [s3 [w2 [A [B [C D]]]]]].
  assert (star step ge s t' s3). eapply star_right; eauto. 
  destruct (forever_star_inv _ _ _ _ H4 _ _ _ H0 C H2)
  as [T1' [P [Q R]]].
  destruct (forever_star_inv _ _ _ _ H4 _ _ _ H1 C H3)
  as [T2' [S [T U]]].
  destruct t'. unfold E0 in D. congruence.
  assert (t' = nil). inversion B. inversion H7. auto. subst t'.
  subst T1 T2. simpl. constructor.
  apply COINDHYP with ge s3 w2; auto.
  red; intros. eapply H. eapply star_trans; eauto.
  eapply possible_trace_app; eauto. 
Qed.

(** A trace is minimal for a program if it is a prefix of all possible
  traces. *)

Definition minimal_trace (ge: genv) (s: state) (w: world) (T: traceinf) :=
  forall T',
  forever step ge s T' -> possible_traceinf w T' ->
  traceinf_prefix T T'.

(** For any program that diverges with some possible trace [T1],
  the set of possible traces admits a minimal element [T].
  If the program is reactive, this trace is [T1]. 
  If the program silently diverges, this trace is the finite trace
  of events performed prior to silent divergence. *)

Lemma forever_minimal_trace:
  forall ge s T1 w,
  forever step ge s T1 -> possible_traceinf w T1 ->
  exists T,
     forever step ge s T
  /\ possible_traceinf w T
  /\ minimal_trace ge s w T.
Proof.
  intros. 
  destruct (reactive_or_diverges _ _ _ _ H H0).
  (* reactive *)
  exists T1; split. auto. split. auto. red; intros.
  elim (reactive_or_diverges _ _ _ _ H2 H3); intro.
  apply traceinf_sim_prefix. eapply reactive_sim; eauto. 
  elimtype False. eapply reactive_not_diverges; eauto.
  (* diverges *) 
  elim H1. intros t [s1 [w1 [A [B C]]]].
  exists (t *** Enilinf); split.
  exploit forever_star_inv; eauto. intros [T' [P [Q R]]]. 
  eapply star_forever. eauto. 
  eapply diverges_forever; eauto.
  split. eapply possible_traceinf_app. eauto. constructor. 
  red; intros. exploit forever_star_inv. eauto. eexact H2. eauto. eauto.
  intros [T2 [P [Q R]]].
  subst T'. apply traceinf_prefix_app. constructor.
Qed.

(** ** Refined semantics for program executions. *)

(** We now define the following variant [exec_program'] of the
  [exec_program] predicate defined in module [Smallstep].
  In the diverging case [Diverges T], the new predicate imposes that the
  finite or infinite trace [T] is minimal. *)

Inductive exec_program' (p: program) (w: world): program_behavior -> Prop :=
  | program_terminates': forall s t s' w' r,
      initial_state p s ->
      star step (Genv.globalenv p) s t s' ->
      possible_trace w t w' ->
      final_state s' r ->
      exec_program' p w (Terminates t r)
  | program_diverges': forall s T,
      initial_state p s ->
      forever step (Genv.globalenv p) s T ->
      possible_traceinf w T ->
      minimal_trace (Genv.globalenv p) s w T ->
      exec_program' p w (Diverges T).

(** We show that any [exec_program] execution corresponds to
  an [exec_program'] execution. *)

Definition possible_behavior (w: world) (b: program_behavior) : Prop :=
  match b with
  | Terminates t r => exists w', possible_trace w t w'
  | Diverges T => possible_traceinf w T
  end.

Inductive matching_behaviors: program_behavior -> program_behavior -> Prop :=
  | matching_behaviors_terminates: forall t r,
      matching_behaviors (Terminates t r) (Terminates t r)
  | matching_behaviors_diverges: forall T1 T2,
      traceinf_prefix T2 T1 ->
      matching_behaviors (Diverges T1) (Diverges T2).

Theorem exec_program_program':
  forall p b w,
  exec_program p b -> possible_behavior w b ->
  exists b', exec_program' p w b' /\ matching_behaviors b b'.
Proof.
  intros. inv H; simpl in H0.
  (* termination *)
  destruct H0 as [w' A].
  exists (Terminates t r).
  split. econstructor; eauto. constructor.
  (* divergence *)
  exploit forever_minimal_trace; eauto. intros [T0 [A [B C]]].
  exists (Diverges T0); split.
  econstructor; eauto.
  constructor. apply C; auto.
Qed.

(** Moreover, [exec_program'] is deterministic, in that the behavior
  associated with a given program and external world is uniquely
  defined up to bisimilarity between infinite traces. *)

Inductive same_behaviors: program_behavior -> program_behavior -> Prop :=
  | same_behaviors_terminates: forall t r,
      same_behaviors (Terminates t r) (Terminates t r)
  | same_behaviors_diverges: forall T1 T2,
      traceinf_sim T2 T1 ->
      same_behaviors (Diverges T1) (Diverges T2).

Theorem exec_program'_deterministic:
  forall p b1 b2 w,
  exec_program' p w b1 -> exec_program' p w b2 ->
  same_behaviors b1 b2.
Proof.
  intros. inv H; inv H0;
  assert (s0 = s) by (eapply initial_state_deterministic; eauto); subst s0.
  (* terminates, terminates *)
  exploit steps_deterministic. eexact H2. eexact H5. eauto. eauto. eauto. eauto.
  intros [A B]. subst. constructor.
  (* terminates, diverges *)
  byContradiction. eapply star_final_not_forever; eauto.
  (* diverges, terminates *)
  byContradiction. eapply star_final_not_forever; eauto.
  (* diverges, diverges *)
  constructor. apply traceinf_prefix_2_sim; auto.
Qed.

Lemma matching_behaviors_same:
  forall b b1' b2',
  matching_behaviors b b1' -> same_behaviors b1' b2' ->
  matching_behaviors b b2'.
Proof.
  intros. inv H; inv H0. 
  constructor.
  constructor. apply traceinf_prefix_compat with T2 T1.
  auto. apply traceinf_sim_sym; auto. apply traceinf_sim_refl.
Qed.

(** * Strong semantic preservation property *)

Require Import Errors.

Theorem transf_rtl_program_correct_strong:
  forall p tp b w,
  transf_rtl_program p = OK tp ->
  RTL.exec_program p b ->
  possible_behavior w b ->
  (exists b', exec_program' tp w b')
/\(forall b', exec_program' tp w b' ->
   exists b0, RTL.exec_program p b0 /\ matching_behaviors b0 b').
Proof.
  intros.
  assert (PPC.exec_program tp b).
    eapply transf_rtl_program_correct; eauto.
  exploit exec_program_program'; eauto. 
  intros [b' [A B]].
  split. exists b'; auto.
  intros. exists b. split. auto.
  apply matching_behaviors_same with b'. auto.
  eapply exec_program'_deterministic; eauto.
Qed.

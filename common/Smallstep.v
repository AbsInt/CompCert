(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Coqlib.
Require Import AST.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Section CLOSURES.

Variable genv: Set.
Variable state: Set.

(** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

Variable step: genv -> state -> trace -> state -> Prop.

(** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)

Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.

Lemma star_one:
  forall ge s1 t s2, step ge s1 t s2 -> star ge s1 t s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl. traceEq. 
Qed.

Lemma star_trans:
  forall ge s1 t1 s2, star ge s1 t1 s2 ->
  forall t2 s3 t, star ge s2 t2 s3 -> t = t1 ** t2 -> star ge s1 t s3.
Proof.
  induction 1; intros.
  rewrite H0. simpl. auto.
  eapply star_step; eauto. traceEq.
Qed.

Lemma star_left:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof star_step.

Lemma star_right:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto. auto.
Qed.

(** One or several transitions.  Also known as the transitive closure. *)

Inductive plus (ge: genv): state -> trace -> state -> Prop :=
  | plus_left: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.

Lemma plus_one:
  forall ge s1 t s2,
  step ge s1 t s2 -> plus ge s1 t s2.
Proof.
  intros. econstructor; eauto. apply star_refl. traceEq.
Qed.

Lemma plus_star:
  forall ge s1 t s2, plus ge s1 t s2 -> star ge s1 t s2.
Proof.
  intros. inversion H; subst.
  eapply star_step; eauto. 
Qed.

Lemma plus_right:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. inversion H; subst. simpl. apply plus_one. auto.
  rewrite Eapp_assoc. eapply plus_left; eauto.
  eapply star_right; eauto. 
Qed.

Lemma plus_left':
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply plus_star; auto.
Qed.

Lemma plus_right':
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_right; eauto. apply plus_star; auto.
Qed.

Lemma plus_star_trans:
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. inversion H; subst. 
  econstructor; eauto. eapply star_trans; eauto.
  traceEq.
Qed.

Lemma star_plus_trans:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. inversion H; subst.
  simpl; auto.
  rewrite Eapp_assoc. 
  econstructor. eauto. eapply star_trans. eauto. 
  apply plus_star. eauto. eauto. auto.
Qed.

Lemma plus_trans:
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. eapply plus_star_trans. eauto. apply plus_star. eauto. auto.
Qed.

Lemma plus_inv:
  forall ge s1 t s2,  plus ge s1 t s2 ->
  step ge s1 t s2 \/ exists s', exists t1, exists t2, step ge s1 t1 s' /\ plus ge s' t2 s2 /\ t = t1 ** t2.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  left. rewrite E0_right. auto.
  right. exists s3; exists t1; exists (t0 ** t3); split. auto.
  split. econstructor; eauto. auto.
Qed.

(** Infinitely many transitions *)

CoInductive forever (ge: genv): state -> traceinf -> Prop :=
  | forever_intro: forall s1 t s2 T,
      step ge s1 t s2 -> forever ge s2 T ->
      forever ge s1 (t *** T).

Lemma star_forever:
  forall ge s1 t s2, star ge s1 t s2 ->
  forall T, forever ge s2 T ->
  forever ge s1 (t *** T).
Proof.
  induction 1; intros. simpl. auto.
  subst t. rewrite Eappinf_assoc. 
  econstructor; eauto.
Qed.  

(** An alternate, equivalent definition of [forever] that is useful
    for coinductive reasoning. *)

CoInductive forever_N (ge: genv): nat -> state -> traceinf -> Prop :=
  | forever_N_star: forall s1 t s2 p q T1 T2,
      star ge s1 t s2 -> 
      (p < q)%nat ->
      forever_N ge p s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge q s1 T1
  | forever_N_plus: forall s1 t s2 p q T1 T2,
      plus ge s1 t s2 ->
      forever_N ge p s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge q s1 T1.

Remark Peano_induction:
  forall (P: nat -> Prop),
  (forall p, (forall q, (q < p)%nat -> P q) -> P p) ->
  forall p, P p.
Proof.
  intros P IH.
  assert (forall p, forall q, (q < p)%nat -> P q).
  induction p; intros. elimtype False; omega.
  apply IH. intros. apply IHp. omega.
  intro. apply H with (S p). omega.
Qed.

Lemma forever_N_inv:
  forall ge p s T,
  forever_N ge p s T ->
  exists t, exists s', exists q, exists T',
  step ge s t s' /\ forever_N ge q s' T' /\ T = t *** T'.
Proof.
  intros ge p. pattern p. apply Peano_induction; intros.
  inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  change (E0 *** T2) with T2. apply H with p1. auto. auto. 
  (* at least one transition *)
  exists t1; exists s0; exists p0; exists (t2 *** T2).
  split. auto. split. eapply forever_N_star; eauto.
  apply Eappinf_assoc.
  (* plus case *)
  inv H1.
  exists t1; exists s0; exists (S p1); exists (t2 *** T2).
  split. auto. split. eapply forever_N_star; eauto. 
  apply Eappinf_assoc.
Qed.

Lemma forever_N_forever:
  forall ge p s T, forever_N ge p s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_N_inv H) as [t [s' [q [T' [A [B C]]]]]].
  rewrite C. apply forever_intro with s'. auto. 
  apply COINDHYP with q; auto.
Qed.

(** * Outcomes for program executions *)

(** The two valid outcomes for the execution of a program:
- Termination, with a finite trace of observable events
  and an integer value that stands for the process exit code
  (the return value of the main function).
- Divergence with an infinite trace of observable events.
  (The actual events generated by the execution can be a
   finite prefix of this trace, or the whole trace.)
*)

Inductive program_behavior: Set :=
  | Terminates: trace -> int -> program_behavior
  | Diverges: traceinf -> program_behavior.

(** Given a characterization of initial states and final states,
  [program_behaves] relates a program behaviour with the 
  sequences of transitions that can be taken from an initial state
  to a final state. *)

Variable initial_state: state -> Prop.
Variable final_state: state -> int -> Prop.

Inductive program_behaves (ge: genv): program_behavior -> Prop :=
  | program_terminates: forall s t s' r,
      initial_state s ->
      star ge s t s' ->
      final_state s' r ->
      program_behaves ge (Terminates t r)
  | program_diverges: forall s T,
      initial_state s ->
      forever ge s T ->
      program_behaves ge (Diverges T).

End CLOSURES.

(** * Simulations between two small-step semantics. *)

(** In this section, we show that if two transition relations 
  satisfy certain simulation diagrams, then every program behaviour
  generated by the first transition relation can also occur
  with the second transition relation. *)

Section SIMULATION.

(** The first small-step semantics is axiomatized as follows. *)

Variable genv1: Set.
Variable state1: Set.
Variable step1: genv1 -> state1 -> trace -> state1 -> Prop.
Variable initial_state1: state1 -> Prop.
Variable final_state1: state1 -> int -> Prop.
Variable ge1: genv1.

(** The second small-step semantics is also axiomatized. *)

Variable genv2: Set.
Variable state2: Set.
Variable step2: genv2 -> state2 -> trace -> state2 -> Prop.
Variable initial_state2: state2 -> Prop.
Variable final_state2: state2 -> int -> Prop.
Variable ge2: genv2.

(** We assume given a matching relation between states of both semantics.
  This matching relation must be compatible with initial states
  and with final states. *)


Variable match_states: state1 -> state2 -> Prop.

Hypothesis match_initial_states:
  forall st1, initial_state1 st1 ->
  exists st2, initial_state2 st2 /\ match_states st1 st2.

Hypothesis match_final_states:
  forall st1 st2 r,
  match_states st1 st2 ->
  final_state1 st1 r ->
  final_state2 st2 r.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR.

(** [measure] is a nonnegative integer associated with states
  of the first semantics.  It must decrease when we take 
  a stuttering step. *)

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall st1 t st1', step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', plus step2 ge2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat.

Lemma simulation_star_star:
  forall st1 t st1', star step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2', star step2 ge2 st2 t st2' /\ match_states st1' st2'.
Proof.
  induction 1; intros.
  exists st2; split. apply star_refl. auto.
  elim (simulation H H2).
  intros [st2' [A B]]. 
  destruct (IHstar _ B) as [st3' [C D]].
  exists st3'; split. apply star_trans with t1 st2' t2.
  apply plus_star; auto. auto. auto. auto.
  intros [A [B C]]. rewrite H1. rewrite B. simpl. apply IHstar; auto.
Qed.

Lemma simulation_star_forever:
  forall st1 st2 T,
  forever step1 ge1 st1 T -> match_states st1 st2 ->
  forever step2 ge2 st2 T.
Proof.
  assert (forall st1 st2 T,
    forever step1 ge1 st1 T -> match_states st1 st2 ->
    forever_N step2 ge2 (measure st1) st2 T).
  cofix COINDHYP; intros.
  inversion H; subst. elim (simulation H1 H0).
  intros [st2' [A B]]. apply forever_N_plus with t st2' (measure s2) T0.
  auto. apply COINDHYP. assumption. assumption. auto.
  intros [A [B C]].
  apply forever_N_star with t st2 (measure s2) T0.
  rewrite B. apply star_refl. auto.
  apply COINDHYP. assumption. auto. auto.
  intros. eapply forever_N_forever; eauto.
Qed.

Lemma simulation_star_preservation:
  forall beh,
  program_behaves step1 initial_state1 final_state1 ge1 beh ->
  program_behaves step2 initial_state2 final_state2 ge2 beh.
Proof.
  intros. inversion H; subst.
  destruct (match_initial_states H0) as [s2 [A B]].
  destruct (simulation_star_star H1 B) as [s2' [C D]].
  econstructor; eauto.
  destruct (match_initial_states H0) as [s2 [A B]].
  econstructor; eauto.
  eapply simulation_star_forever; eauto.
Qed.

End SIMULATION_STAR.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall st1 t st1', step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2', step2 ge2 st2 t st2' /\ match_states st1' st2'.

Lemma simulation_step_preservation:
  forall beh,
  program_behaves step1 initial_state1 final_state1 ge1 beh ->
  program_behaves step2 initial_state2 final_state2 ge2 beh.
Proof.
  intros.
  pose (measure := fun (st: state1) => 0%nat).
  assert (simulation':
  forall st1 t st1', step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', plus step2 ge2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat).
  intros. destruct (simulation H0 H1) as [st2' [A B]].
  left; exists st2'; split. apply plus_one; auto. auto.
  eapply simulation_star_preservation; eauto.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall st1 t st1', step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2', plus step2 ge2 st2 t st2' /\ match_states st1' st2'.

Lemma simulation_plus_preservation:
  forall beh,
  program_behaves step1 initial_state1 final_state1 ge1 beh ->
  program_behaves step2 initial_state2 final_state2 ge2 beh.
Proof.
  intros.
  pose (measure := fun (st: state1) => 0%nat).
  assert (simulation':
  forall st1 t st1', step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', plus step2 ge2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat).
  intros. destruct (simulation H0 H1) as [st2' [A B]].
  left; exists st2'; auto.
  eapply simulation_star_preservation; eauto.
Qed.

End SIMULATION_PLUS.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall st1 t st1', step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', step2 ge2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat.

Lemma simulation_opt_preservation:
  forall beh,
  program_behaves step1 initial_state1 final_state1 ge1 beh ->
  program_behaves step2 initial_state2 final_state2 ge2 beh.
Proof.
  assert (simulation':
    forall st1 t st1', step1 ge1 st1 t st1' ->
    forall st2, match_states st1 st2 ->
    (exists st2', plus step2 ge2 st2 t st2' /\ match_states st1' st2')
    \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat).
  intros. elim (simulation H H0). 
  intros [st2' [A B]]. left. exists st2'; split. apply plus_one; auto. auto.
  intros [A [B C]]. right. intuition.
  intros. eapply simulation_star_preservation; eauto.
Qed.

End SIMULATION_OPT.

End SIMULATION.



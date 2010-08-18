(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Wf.
Require Import Wf_nat.
Require Import Coqlib.
Require Import AST.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Section CLOSURES.

Variable genv: Type.
Variable state: Type.

(** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

Variable step: genv -> state -> trace -> state -> Prop.

(** No transitions: stuck state *)

Definition nostep (ge: genv) (s: state) : Prop :=
  forall t s', ~(step ge s t s').

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

Lemma star_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto.  
Qed.

Lemma star_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  star ge s1 t s4.
Proof.
  intros. eapply star_step; eauto. eapply star_two; eauto. 
Qed.

Lemma star_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  star ge s1 t s5.
Proof.
  intros. eapply star_step; eauto. eapply star_three; eauto. 
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

Lemma plus_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply star_one; auto.  
Qed.

Lemma plus_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  plus ge s1 t s4.
Proof.
  intros. eapply plus_left; eauto. eapply star_two; eauto. 
Qed.

Lemma plus_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  plus ge s1 t s5.
Proof.
  intros. eapply plus_left; eauto. eapply star_three; eauto. 
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
  forall ge s1 t s2, 
  plus ge s1 t s2 ->
  step ge s1 t s2 \/ exists s', exists t1, exists t2, step ge s1 t1 s' /\ plus ge s' t2 s2 /\ t = t1 ** t2.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  left. rewrite E0_right. auto.
  right. exists s3; exists t1; exists (t0 ** t3); split. auto.
  split. econstructor; eauto. auto.
Qed.

Lemma star_inv:
  forall ge s1 t s2,
  star ge s1 t s2 ->
  (s2 = s1 /\ t = E0) \/ plus ge s1 t s2.
Proof.
  intros. inv H. left; auto. right; econstructor; eauto.
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

Variable A: Type.
Variable order: A -> A -> Prop.

CoInductive forever_N (ge: genv) : A -> state -> traceinf -> Prop :=
  | forever_N_star: forall s1 t s2 a1 a2 T1 T2,
      star ge s1 t s2 -> 
      order a2 a1 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1
  | forever_N_plus: forall s1 t s2 a1 a2 T1 T2,
      plus ge s1 t s2 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1.

Hypothesis order_wf: well_founded order.

Lemma forever_N_inv:
  forall ge a s T,
  forever_N ge a s T ->
  exists t, exists s', exists a', exists T',
  step ge s t s' /\ forever_N ge a' s' T' /\ T = t *** T'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  change (E0 *** T2) with T2. apply H with a2. auto. auto. 
  (* at least one transition *)
  exists t1; exists s0; exists x; exists (t2 *** T2).
  split. auto. split. eapply forever_N_star; eauto.
  apply Eappinf_assoc.
  (* plus case *)
  inv H1.
  exists t1; exists s0; exists a2; exists (t2 *** T2).
  split. auto.
  split. inv H3. auto.  
  eapply forever_N_plus. econstructor; eauto. eauto. auto.
  apply Eappinf_assoc.
Qed.

Lemma forever_N_forever:
  forall ge a s T, forever_N ge a s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_N_inv H) as [t [s' [a' [T' [P [Q R]]]]]].
  rewrite R. apply forever_intro with s'. auto. 
  apply COINDHYP with a'; auto.
Qed.

(** Yet another alternative definition of [forever]. *)

CoInductive forever_plus (ge: genv) : state -> traceinf -> Prop :=
  | forever_plus_intro: forall s1 t s2 T1 T2,
      plus ge s1 t s2 -> 
      forever_plus ge s2 T2 ->
      T1 = t *** T2 ->
      forever_plus ge s1 T1.

Lemma forever_plus_inv:
  forall ge s T,
  forever_plus ge s T ->
  exists s', exists t, exists T',
  step ge s t s' /\ forever_plus ge s' T' /\ T = t *** T'.
Proof.
  intros. inv H. inv H0. exists s0; exists t1; exists (t2 *** T2).
  split. auto.
  split. exploit star_inv; eauto. intros [[P Q] | R]. 
    subst. simpl. auto. econstructor; eauto. 
  traceEq.
Qed.

Lemma forever_plus_forever:
  forall ge s T, forever_plus ge s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_plus_inv H) as [s' [t [T' [P [Q R]]]]].
  subst. econstructor; eauto.
Qed.

(** Infinitely many silent transitions *)

CoInductive forever_silent (ge: genv): state -> Prop :=
  | forever_silent_intro: forall s1 s2,
      step ge s1 E0 s2 -> forever_silent ge s2 ->
      forever_silent ge s1.

(** An alternate definition. *)

CoInductive forever_silent_N (ge: genv) : A -> state -> Prop :=
  | forever_silent_N_star: forall s1 s2 a1 a2,
      star ge s1 E0 s2 -> 
      order a2 a1 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1
  | forever_silent_N_plus: forall s1 s2 a1 a2,
      plus ge s1 E0 s2 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1.

Lemma forever_silent_N_inv:
  forall ge a s,
  forever_silent_N ge a s ->
  exists s', exists a',
  step ge s E0 s' /\ forever_silent_N ge a' s'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  apply H with a2. auto. auto. 
  (* at least one transition *)
  exploit Eapp_E0_inv; eauto. intros [P Q]. subst. 
  exists s0; exists x.
  split. auto. eapply forever_silent_N_star; eauto.
  (* plus case *)
  inv H1. exploit Eapp_E0_inv; eauto. intros [P Q]. subst. 
  exists s0; exists a2.
  split. auto. inv H3. auto.  
  eapply forever_silent_N_plus. econstructor; eauto. eauto.
Qed.

Lemma forever_silent_N_forever:
  forall ge a s, forever_silent_N ge a s -> forever_silent ge s.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_silent_N_inv H) as [s' [a' [P Q]]].
  apply forever_silent_intro with s'. auto. 
  apply COINDHYP with a'; auto.
Qed.

(** Infinitely many non-silent transitions *)

CoInductive forever_reactive (ge: genv): state -> traceinf -> Prop :=
  | forever_reactive_intro: forall s1 s2 t T,
      star ge s1 t s2 -> t <> E0 -> forever_reactive ge s2 T ->
      forever_reactive ge s1 (t *** T).

Lemma star_forever_reactive:
  forall ge s1 t s2 T,
  star ge s1 t s2 -> forever_reactive ge s2 T ->
  forever_reactive ge s1 (t *** T).
Proof.
  intros. inv H0. rewrite <- Eappinf_assoc. econstructor. 
  eapply star_trans; eauto. 
  red; intro. exploit Eapp_E0_inv; eauto. intros [P Q]. contradiction.
  auto.
Qed.

(** * Outcomes for program executions *)

(** The four possible outcomes for the execution of a program:
- Termination, with a finite trace of observable events
  and an integer value that stands for the process exit code
  (the return value of the main function).
- Divergence with a finite trace of observable events.
  (At some point, the program runs forever without doing any I/O.)
- Reactive divergence with an infinite trace of observable events.
  (The program performs infinitely many I/O operations separated
   by finite amounts of internal computations.)
- Going wrong, with a finite trace of observable events
  performed before the program gets stuck.
*)

Inductive program_behavior: Type :=
  | Terminates: trace -> int -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.

Definition not_wrong (beh: program_behavior) : Prop :=
  match beh with
  | Terminates _ _ => True
  | Diverges _ => True
  | Reacts _ => True
  | Goes_wrong _ => False
  end.

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
  | program_diverges: forall s t s',
      initial_state s ->
      star ge s t s' -> forever_silent ge s' ->
      program_behaves ge (Diverges t)
  | program_reacts: forall s T,
      initial_state s ->
      forever_reactive ge s T ->
      program_behaves ge (Reacts T)
  | program_goes_wrong: forall s t s',
      initial_state s ->
      star ge s t s' ->
      nostep ge s' ->
      (forall r, ~final_state s' r) ->
      program_behaves ge (Goes_wrong t)
  | program_goes_initially_wrong:
      (forall s, ~initial_state s) ->
      program_behaves ge (Goes_wrong E0).

End CLOSURES.

(** * Simulations between two small-step semantics. *)

(** In this section, we show that if two transition relations 
  satisfy certain simulation diagrams, then every program behaviour
  generated by the first transition relation can also occur
  with the second transition relation. *)

Section SIMULATION.

(** The first small-step semantics is axiomatized as follows. *)

Variable genv1: Type.
Variable state1: Type.
Variable step1: genv1 -> state1 -> trace -> state1 -> Prop.
Variable initial_state1: state1 -> Prop.
Variable final_state1: state1 -> int -> Prop.
Variable ge1: genv1.

(** The second small-step semantics is also axiomatized. *)

Variable genv2: Type.
Variable state2: Type.
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

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state1 -> state1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall st1 t st1', step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2',
  (plus step2 ge2 st2 t st2' \/ (star step2 ge2 st2 t st2' /\ order st1' st1))
  /\ match_states st1' st2'.

Lemma simulation_star_star:
  forall st1 t st1', star step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  exists st2', star step2 ge2 st2 t st2' /\ match_states st1' st2'.
Proof.
  induction 1; intros.
  exists st2; split. apply star_refl. auto.
  destruct (simulation H H2) as [st2' [A B]].
  destruct (IHstar _ B) as [st3' [C D]].
  exists st3'; split; auto.
  apply star_trans with t1 st2' t2; auto. 
  destruct A as [F | [F G]].
  apply plus_star; auto.
  auto.
Qed.

Lemma simulation_star_forever_silent:
  forall st1 st2,
  forever_silent step1 ge1 st1 -> match_states st1 st2 ->
  forever_silent step2 ge2 st2.
Proof.
  assert (forall st1 st2,
    forever_silent step1 ge1 st1 -> match_states st1 st2 ->
    forever_silent_N step2 order ge2 st1 st2).
  cofix COINDHYP; intros.
  inversion H; subst.
  destruct (simulation H1 H0) as [st2' [A B]].
  destruct A as [C | [C D]].
  apply forever_silent_N_plus with st2' s2.
  auto. apply COINDHYP. assumption. assumption.
  apply forever_silent_N_star with st2' s2.
  auto. auto. apply COINDHYP. assumption. auto.
  intros. eapply forever_silent_N_forever; eauto.
Qed.

Lemma simulation_star_forever_reactive:
  forall st1 st2 T,
  forever_reactive step1 ge1 st1 T -> match_states st1 st2 ->
  forever_reactive step2 ge2 st2 T.
Proof.
  cofix COINDHYP; intros.
  inv H. 
  destruct (simulation_star_star H1 H0) as [st2' [A B]].
  econstructor. eexact A. auto. 
  eapply COINDHYP. eauto. auto. 
Qed.

Lemma simulation_star_wf_preservation:
  forall beh,
  not_wrong beh ->
  program_behaves step1 initial_state1 final_state1 ge1 beh ->
  program_behaves step2 initial_state2 final_state2 ge2 beh.
Proof.
  intros. inv H0; simpl in H. 
  destruct (match_initial_states H1) as [s2 [A B]].
  destruct (simulation_star_star H2 B) as [s2' [C D]].
  econstructor; eauto.
  destruct (match_initial_states H1) as [s2 [A B]].
  destruct (simulation_star_star H2 B) as [s2' [C D]].
  econstructor; eauto.
  eapply simulation_star_forever_silent; eauto.
  destruct (match_initial_states H1) as [s2 [A B]].
  econstructor; eauto. eapply simulation_star_forever_reactive; eauto.
  contradiction.
  contradiction.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take 
  a stuttering step. *)

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall st1 t st1', step1 ge1 st1 t st1' ->
  forall st2, match_states st1 st2 ->
  (exists st2', plus step2 ge2 st2 t st2' /\ match_states st1' st2')
  \/ (measure st1' < measure st1 /\ t = E0 /\ match_states st1' st2)%nat.

Lemma simulation_star_preservation:
  forall beh,
  not_wrong beh ->
  program_behaves step1 initial_state1 final_state1 ge1 beh ->
  program_behaves step2 initial_state2 final_state2 ge2 beh.
Proof.
  intros.
  apply simulation_star_wf_preservation with (ltof _ measure).
  apply well_founded_ltof. intros.
  destruct (simulation H1 H2) as [[st2' [A B]] | [A [B C]]].
  exists st2'; auto.
  exists st2; split. right; split. rewrite B. apply star_refl. auto. auto.
  auto. auto.
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
  not_wrong beh ->
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
  intros. destruct (simulation H1 H2) as [st2' [A B]].
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
  not_wrong beh ->
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
  intros. destruct (simulation H1 H2) as [st2' [A B]].
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
  not_wrong beh ->
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

(** * Existence of behaviors *)

Require Import Classical.
Require Import ClassicalEpsilon.

(** We now show that any program admits at least one behavior.
  The proof requires classical logic: the axiom of excluded middle
  and an axiom of description. *)

Section EXISTS_BEHAVIOR.

Variable genv: Type.
Variable state: Type.
Variable initial_state: state -> Prop.
Variable final_state: state -> int -> Prop.
Variable step: genv -> state -> trace -> state -> Prop.

(** The most difficult part of the proof is to show the existence
  of an infinite trace in the case of reactive divergence. *)

Section TRACEINF_REACTS.

Variable ge: genv.
Variable s0: state.

Hypothesis reacts:
  forall s1 t1, star step ge s0 t1 s1 ->
  exists s2, exists t2, star step ge s1 t2 s2 /\ t2 <> E0.

Lemma reacts':
  forall s1 t1, star step ge s0 t1 s1 ->
  { s2 : state & { t2 : trace | star step ge s1 t2 s2 /\ t2 <> E0 } }.
Proof.
  intros. 
  destruct (constructive_indefinite_description _ (reacts H)) as [s2 A].
  destruct (constructive_indefinite_description _ A) as [t2 [B C]].
  exists s2; exists t2; auto.
Qed.

CoFixpoint build_traceinf' (s1: state) (t1: trace) (ST: star step ge s0 t1 s1) : traceinf' :=
  match reacts' ST with
  | existT s2 (exist t2 (conj A B)) =>
      Econsinf' t2 
                (build_traceinf' (star_trans ST A (refl_equal _)))
                B
  end.

Lemma reacts_forever_reactive_rec:
  forall s1 t1 (ST: star step ge s0 t1 s1),
  forever_reactive step ge s1 (traceinf_of_traceinf' (build_traceinf' ST)).
Proof.
  cofix COINDHYP; intros.
  rewrite (unroll_traceinf' (build_traceinf' ST)). simpl. 
  destruct (reacts' ST) as [s2 [t2 [A B]]]. 
  rewrite traceinf_traceinf'_app. 
  econstructor. eexact A. auto. apply COINDHYP. 
Qed.

Lemma reacts_forever_reactive:
  exists T, forever_reactive step ge s0 T.
Proof.
  exists (traceinf_of_traceinf' (build_traceinf' (star_refl step ge s0))).
  apply reacts_forever_reactive_rec.
Qed.

End TRACEINF_REACTS.

Lemma diverges_forever_silent:
  forall ge s0,
  (forall s1 t1, star step ge s0 t1 s1 -> exists s2, step ge s1 E0 s2) ->
  forever_silent step ge s0.
Proof.
  cofix COINDHYP; intros. 
  destruct (H s0 E0) as [s1 ST]. constructor. 
  econstructor. eexact ST. apply COINDHYP. 
  intros. eapply H. eapply star_left; eauto.
Qed.

Theorem program_behaves_exists:
  forall ge, exists beh, program_behaves step initial_state final_state ge beh.
Proof.
  intros.
  destruct (classic (exists s, initial_state s)) as [[s0 INIT] | NOTINIT].
(* 1. Initial state is defined. *)
  destruct (classic (forall s1 t1, star step ge s0 t1 s1 -> exists s2, exists t2, step ge s1 t2 s2)).
(* 1.1 Divergence (silent or reactive) *)
  destruct (classic (exists s1, exists t1, star step ge s0 t1 s1 /\
                       (forall s2 t2, star step ge s1 t2 s2 ->
                        exists s3, step ge s2 E0 s3))).
(* 1.1.1 Silent divergence *)
  destruct H0 as [s1 [t1 [A B]]].
  exists (Diverges t1); econstructor; eauto. 
  apply diverges_forever_silent; auto.
(* 1.1.2 Reactive divergence *)
  destruct (@reacts_forever_reactive ge s0) as [T FR].
  intros.
  generalize (not_ex_all_not _ _ H0 s1). intro A; clear H0.
  generalize (not_ex_all_not _ _ A t1). intro B; clear A.
  destruct (not_and_or _ _ B). contradiction. 
  destruct (not_all_ex_not _ _ H0) as [s2 C]; clear H0. 
  destruct (not_all_ex_not _ _ C) as [t2 D]; clear C.
  destruct (imply_to_and _ _ D) as [E F]; clear D.
  destruct (H s2 (t1 ** t2)) as [s3 [t3 G]]. eapply star_trans; eauto. 
  exists s3; exists (t2 ** t3); split.
  eapply star_right; eauto. 
  red; intros. destruct (app_eq_nil t2 t3 H0). subst. elim F. exists s3; auto.
  exists (Reacts T); econstructor; eauto.
(* 1.2 Termination (normal or by going wrong) *)
  destruct (not_all_ex_not _ _ H) as [s1 A]; clear H.
  destruct (not_all_ex_not _ _ A) as [t1 B]; clear A.
  destruct (imply_to_and _ _ B) as [C D]; clear B.
  destruct (classic (exists r, final_state s1 r)) as [[r FINAL] | NOTFINAL].
(* 1.2.1 Normal termination *)
  exists (Terminates t1 r); econstructor; eauto.
(* 1.2.2 Going wrong *)
  exists (Goes_wrong t1); econstructor; eauto. red. intros. 
  generalize (not_ex_all_not _ _ D s'); intros. 
  generalize (not_ex_all_not _ _ H t); intros. 
  auto.
(* 2. Initial state is undefined *)
  exists (Goes_wrong E0). apply program_goes_initially_wrong. 
  intros. eapply not_ex_all_not; eauto. 
Qed.

End EXISTS_BEHAVIOR.

(** * Additional results about infinite reduction sequences *)

(** We now show that any infinite sequence of reductions is either of
  the "reactive" kind or of the "silent" kind (after a finite number
  of non-silent transitions).  The proof necessitates the axiom of
  excluded middle.  This result is used in [Csem] and [Cminor] to
  relate the coinductive big-step semantics for divergence with the
  small-step notions of divergence. *)

Unset Implicit Arguments.

Section INF_SEQ_DECOMP.

Variable genv: Type.
Variable state: Type.
Variable step: genv -> state -> trace -> state -> Prop.

Variable ge: genv.

Inductive State: Type :=
  ST: forall (s: state) (T: traceinf), forever step ge s T -> State.

Definition state_of_State (S: State): state :=
  match S with ST s T F => s end.
Definition traceinf_of_State (S: State) : traceinf :=
  match S with ST s T F => T end.

Inductive Step: trace -> State -> State -> Prop :=
  | Step_intro: forall s1 t T s2 S F,
      Step t (ST s1 (t *** T) (@forever_intro genv state step ge s1 t s2 T S F))
             (ST s2 T F).

Inductive Steps: State -> State -> Prop :=
  | Steps_refl: forall S, Steps S S
  | Steps_left: forall t S1 S2 S3, Step t S1 S2 -> Steps S2 S3 -> Steps S1 S3.

Remark Steps_trans:
  forall S1 S2, Steps S1 S2 -> forall S3, Steps S2 S3 -> Steps S1 S3.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

Let Reactive (S: State) : Prop :=
  forall S1, 
  Steps S S1 ->
  exists S2, exists S3, exists t, Steps S1 S2 /\ Step t S2 S3 /\ t <> E0.

Let Silent (S: State) : Prop :=
  forall S1 t S2, Steps S S1 -> Step t S1 S2 -> t = E0.

Lemma Reactive_or_Silent:
  forall S, Reactive S \/ (exists S', Steps S S' /\ Silent S').
Proof.
  intros. destruct (classic (exists S', Steps S S' /\ Silent S')).
  auto.
  left. red; intros. 
  generalize (not_ex_all_not _ _ H S1). intros.
  destruct (not_and_or _ _ H1). contradiction. 
  unfold Silent in H2. 
  generalize (not_all_ex_not _ _ H2). intros [S2 A].
  generalize (not_all_ex_not _ _ A). intros [t B].
  generalize (not_all_ex_not _ _ B). intros [S3 C].
  generalize (imply_to_and _ _ C). intros [D F].
  generalize (imply_to_and _ _ F). intros [G J].
  exists S2; exists S3; exists t. auto.  
Qed.

Lemma Steps_star:
  forall S1 S2, Steps S1 S2 ->
  exists t, star step ge (state_of_State S1) t (state_of_State S2)
         /\ traceinf_of_State S1 = t *** traceinf_of_State S2.
Proof.
  induction 1.
  exists E0; split. apply star_refl. auto.
  inv H. destruct IHSteps as [t' [A B]].
  exists (t ** t'); split.
  simpl; eapply star_left; eauto.
  simpl in *. subst T. traceEq.
Qed.

Lemma Silent_forever_silent:
  forall S,
  Silent S -> forever_silent step ge (state_of_State S).
Proof.
  cofix COINDHYP; intro S. case S. intros until f. simpl. case f. intros.
  assert (Step t (ST s1 (t *** T0) (forever_intro s1 t s0 f0))
                 (ST s2 T0 f0)). 
    constructor.
  assert (t = E0). 
    red in H. eapply H; eauto. apply Steps_refl.
  apply forever_silent_intro with (state_of_State (ST s2 T0 f0)).
  rewrite <- H1. assumption. 
  apply COINDHYP. 
  red; intros. eapply H. eapply Steps_left; eauto. eauto. 
Qed.

Lemma Reactive_forever_reactive:
  forall S,
  Reactive S -> forever_reactive step ge (state_of_State S) (traceinf_of_State S).
Proof.
  cofix COINDHYP; intros.
  destruct (H S) as [S1 [S2 [t [A [B C]]]]]. apply Steps_refl. 
  destruct (Steps_star _ _ A) as [t' [P Q]].
  inv B. simpl in *. rewrite Q. rewrite <- Eappinf_assoc. 
  apply forever_reactive_intro with s2. 
  eapply star_right; eauto. 
  red; intros. destruct (Eapp_E0_inv _ _ H0). contradiction.
  change (forever_reactive step ge (state_of_State (ST s2 T F)) (traceinf_of_State (ST s2 T F))).
  apply COINDHYP. 
  red; intros. apply H.
  eapply Steps_trans. eauto.
  eapply Steps_left. constructor. eauto.
Qed.

Theorem forever_silent_or_reactive:
  forall s T,
  forever step ge s T ->
  forever_reactive step ge s T \/
  exists t, exists s', exists T',
  star step ge s t s' /\ forever_silent step ge s' /\ T = t *** T'.
Proof.
  intros. 
  destruct (Reactive_or_Silent (ST s T H)).
  left. 
  change (forever_reactive step ge (state_of_State (ST s T H)) (traceinf_of_State (ST s T H))).
  apply Reactive_forever_reactive. auto.
  destruct H0 as [S' [A B]].
  exploit Steps_star; eauto. intros [t [C D]]. simpl in *.
  right. exists t; exists (state_of_State S'); exists (traceinf_of_State S').
  split. auto. 
  split. apply Silent_forever_silent. auto.
  auto.
Qed.

End INF_SEQ_DECOMP.


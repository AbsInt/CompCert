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

(** Corollaries of the main semantic preservation theorem. *)

Require Import Classical.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Behaviors.
Require Import Csyntax.
Require Import Csem.
Require Import Cstrategy.
Require Import Clight.
Require Import Cminor.
Require Import RTL.
Require Import Asm.
Require Import Compiler.
Require Import Errors.

(** * Preservation of whole-program behaviors *)

(** From the simulation diagrams proved in file [Compiler]. it follows that
  whole-program observable behaviors are preserved in the following sense.
  First, every behavior of the generated assembly code is matched by
  a behavior of the source C code. *)

Theorem transf_c_program_preservation:
  forall p tp beh,
  transf_c_program p = OK tp ->
  program_behaves (Asm.semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh.
Proof.
  intros. eapply backward_simulation_behavior_improves; eauto. 
  apply transf_c_program_correct; auto.
Qed.

(** As a corollary, if the source C code cannot go wrong, the behavior of the
  generated assembly code is one of the possible behaviors of the source C code. *)

Theorem transf_c_program_is_refinement:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Csem.semantics p) beh -> not_wrong beh) ->
  (forall beh, program_behaves (Asm.semantics tp) beh -> program_behaves (Csem.semantics p) beh).
Proof.
  intros. eapply backward_simulation_same_safe_behavior; eauto.
  apply transf_c_program_correct; auto.
Qed.

(** If we consider the C evaluation strategy implemented by the compiler,
  we get stronger preservation results. *)

Theorem transf_cstrategy_program_preservation:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Cstrategy.semantics p) beh ->
     exists beh', program_behaves (Asm.semantics tp) beh' /\ behavior_improves beh beh')
/\(forall beh, program_behaves (Asm.semantics tp) beh ->
     exists beh', program_behaves (Cstrategy.semantics p) beh' /\ behavior_improves beh' beh)
/\(forall beh, not_wrong beh ->
     program_behaves (Cstrategy.semantics p) beh -> program_behaves (Asm.semantics tp) beh)
/\(forall beh,
     (forall beh', program_behaves (Cstrategy.semantics p) beh' -> not_wrong beh') ->
     program_behaves (Asm.semantics tp) beh ->
     program_behaves (Cstrategy.semantics p) beh).
Proof.
  assert (WBT: forall p, well_behaved_traces (Cstrategy.semantics p)).
    intros. eapply ssr_well_behaved. apply Cstrategy.semantics_strongly_receptive.
  intros. intuition.
  eapply forward_simulation_behavior_improves; eauto. 
    apply (fst (transf_cstrategy_program_correct _ _ H)).
  exploit backward_simulation_behavior_improves.
    apply (snd (transf_cstrategy_program_correct _ _ H)).
    eauto.
  intros [beh1 [A B]]. exists beh1; split; auto. rewrite atomic_behaviors; auto.
  eapply forward_simulation_same_safe_behavior; eauto.
    apply (fst (transf_cstrategy_program_correct _ _ H)).
  exploit backward_simulation_same_safe_behavior.
    apply (snd (transf_cstrategy_program_correct _ _ H)).
    intros. rewrite <- atomic_behaviors in H2; eauto. eauto.
    intros. rewrite atomic_behaviors; auto. 
Qed.

(** We can also use the alternate big-step semantics for [Cstrategy]
  to establish behaviors of the generated assembly code. *)

Theorem bigstep_cstrategy_preservation:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall t r,
     Cstrategy.bigstep_program_terminates p t r ->
     program_behaves (Asm.semantics tp) (Terminates t r))
/\(forall T,
     Cstrategy.bigstep_program_diverges p T ->
       program_behaves (Asm.semantics tp) (Reacts T)
    \/ exists t, program_behaves (Asm.semantics tp) (Diverges t) /\ traceinf_prefix t T).
Proof.
  intuition.
  apply transf_cstrategy_program_preservation with p; auto. red; auto.
  apply behavior_bigstep_terminates with (Cstrategy.bigstep_semantics p); auto.
  apply Cstrategy.bigstep_semantics_sound.
  exploit (behavior_bigstep_diverges (Cstrategy.bigstep_semantics_sound p)). eassumption.
  intros [A | [t [A B]]]. 
  left. apply transf_cstrategy_program_preservation with p; auto. red; auto.
  right; exists t; split; auto. apply transf_cstrategy_program_preservation with p; auto. red; auto.
Qed.

(** * Satisfaction of specifications *)

(** The second additional results shows that if all executions
  of the source C program satisfies a given specification
  (a predicate on the observable behavior of the program),
  then all executions of the produced Asm program satisfy
  this specification as well.  

  We first show this result for specifications that are stable
  under the [behavior_improves] relation. *) 

Section SPECS_PRESERVED.

Variable spec: program_behavior -> Prop.

Hypothesis spec_stable:
  forall beh1 beh2, behavior_improves beh1 beh2 -> spec beh1 -> spec beh2.

Theorem transf_c_program_preserves_spec:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Csem.semantics p) beh -> spec beh) ->
  (forall beh, program_behaves (Asm.semantics tp) beh -> spec beh).
Proof.
  intros.
  exploit transf_c_program_preservation; eauto. intros [beh' [A B]].
  apply spec_stable with beh'; auto. 
Qed.

End SPECS_PRESERVED.

(** As a corollary, we obtain preservation of safety specifications:
  specifications that exclude "going wrong" behaviors. *)

Section SAFETY_PRESERVED.

Variable spec: program_behavior -> Prop.

Hypothesis spec_safety:
  forall beh, spec beh -> not_wrong beh.

Theorem transf_c_program_preserves_safety_spec:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Csem.semantics p) beh -> spec beh) ->
  (forall beh, program_behaves (Asm.semantics tp) beh -> spec beh).
Proof.
  intros. eapply transf_c_program_preserves_spec; eauto. 
  intros. destruct H2. congruence. destruct H2 as [t [EQ1 EQ2]]. 
  subst beh1. elim (spec_safety _ H3). 
Qed.

End SAFETY_PRESERVED.

(** We also have preservation of liveness specifications:
  specifications that assert the existence of a prefix of the observable
  trace satisfying some conditions. *)

Section LIVENESS_PRESERVED.

Variable spec: trace -> Prop.

Definition liveness_spec_satisfied (b: program_behavior) : Prop :=
  exists t, behavior_prefix t b /\ spec t.

Theorem transf_c_program_preserves_liveness_spec:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Csem.semantics p) beh -> liveness_spec_satisfied beh) ->
  (forall beh, program_behaves (Asm.semantics tp) beh -> liveness_spec_satisfied beh).
Proof.
  intros. eapply transf_c_program_preserves_spec; eauto.
  intros. destruct H3 as [t1 [A B]]. destruct H2.
  subst. exists t1; auto.
  destruct H2 as [t [C D]]. subst.
  destruct A as [b1 E]. destruct D as [b2 F].
  destruct b1; simpl in E; inv E.
  exists t1; split; auto. 
  exists (behavior_app t0 b2); apply behavior_app_assoc. 
Qed.

End LIVENESS_PRESERVED.


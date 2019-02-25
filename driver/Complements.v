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
Require Import Coqlib Errors.
Require Import AST Linking Events Smallstep Behaviors.
Require Import Csyntax Csem Cstrategy Asm.
Require Import Compiler.

(** * Preservation of whole-program behaviors *)

(** From the simulation diagrams proved in file [Compiler]. it follows that
  whole-program observable behaviors are preserved in the following sense.
  First, every behavior of the generated assembly code is matched by
  a behavior of the source C code.  The behavior [beh] of the assembly
  code is either identical to the behavior [beh'] of the source C code
  or ``improves upon'' [beh']  by replacing a ``going wrong'' behavior
  with a more defined behavior. *)

Theorem transf_c_program_preservation:
  forall p tp beh,
  transf_c_program p = OK tp ->
  program_behaves (Asm.semantics tp) beh ->
  exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh.
Proof.
  intros. eapply backward_simulation_behavior_improves; eauto.
  apply transf_c_program_correct; auto.
Qed.

(** As a corollary, if the source C code cannot go wrong, i.e. is free of
  undefined behaviors, the behavior of the generated assembly code is
  one of the possible behaviors of the source C code. *)

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
  intros.
  assert (MATCH: match_prog p tp) by (apply transf_c_program_match; auto).
  intuition auto.
  eapply forward_simulation_behavior_improves; eauto.
    apply (proj1 (cstrategy_semantic_preservation _ _ MATCH)).
  exploit backward_simulation_behavior_improves.
    apply (proj2 (cstrategy_semantic_preservation _ _ MATCH)).
    eauto.
  intros [beh1 [A B]]. exists beh1; split; auto. rewrite atomic_behaviors; auto.
  eapply forward_simulation_same_safe_behavior; eauto.
    apply (proj1 (cstrategy_semantic_preservation _ _ MATCH)).
  exploit backward_simulation_same_safe_behavior.
    apply (proj2 (cstrategy_semantic_preservation _ _ MATCH)).
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
  of the source C program satisfies a given specification,
  then all executions of the produced Asm program satisfy
  this specification as well.  *)

(** The specifications we consider here are sets of observable
  behaviors, representing the good behaviors a program is expected
  to have.  A specification can be as simple as
  ``the program does not go wrong'' or as precise as
  ``the program prints a prime number then terminates with code 0''.
  As usual in Coq, sets of behaviors are represented as predicates
  [program_behavior -> Prop]. *)

Definition specification := program_behavior -> Prop.

(** A program satisfies a specification if all its observable behaviors
  are in the specification. *)

Definition c_program_satisfies_spec (p: Csyntax.program) (spec: specification): Prop :=
  forall beh,  program_behaves (Csem.semantics p) beh -> spec beh.
Definition asm_program_satisfies_spec (p: Asm.program) (spec: specification): Prop :=
  forall beh,  program_behaves (Asm.semantics p) beh -> spec beh.
  
(** It is not always the case that if the source program satisfies a
  specification, then the generated assembly code satisfies it as
  well.  For example, if the specification is ``the program goes wrong
  on an undefined behavior'', a C source that goes wrong satisfies
  this specification but can be compiled into Asm code that does not
  go wrong and therefore does not satisfy the specification.

  For this reason, we restrict ourselves to safety-enforcing specifications:
  specifications that exclude ``going wrong'' behaviors and are satisfied
  only by programs that execute safely. *)

Definition safety_enforcing_specification (spec: specification): Prop :=
  forall beh, spec beh -> not_wrong beh.

(** As the main result of this section, we show that CompCert
  compilation preserves safety-enforcing specifications: 
  any such specification that is satisfied by the source C program is
  always satisfied by the generated assembly code. *)

Theorem transf_c_program_preserves_spec:
  forall p tp spec,
  transf_c_program p = OK tp ->
  safety_enforcing_specification spec ->
  c_program_satisfies_spec p spec ->
  asm_program_satisfies_spec tp spec.
Proof.
  intros p tp spec TRANSF SES CSAT; red; intros beh AEXEC.
  exploit transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
  apply CSAT in CEXEC. destruct IMPR as [EQ | [t [A B]]].
- congruence.
- subst beh'. apply SES in CEXEC. contradiction. 
Qed.

(** Safety-enforcing specifications are not the only good properties
  of source programs that are preserved by compilation.  Another example
  of a property that is preserved is the ``initial trace'' property:
  all executions of the program start by producing an expected trace
  of I/O actions, representing the good behavior expected from the program.
  After that, the program may terminate, or continue running, or go wrong
  on an undefined behavior.  What matters is that the program produced
  the expected trace at the beginning of its execution.  This is a typical
  liveness property, and it is preserved by compilation. *)

Definition c_program_has_initial_trace (p: Csyntax.program) (t: trace): Prop :=
  forall beh, program_behaves (Csem.semantics p) beh -> behavior_prefix t beh.
Definition asm_program_has_initial_trace (p: Asm.program) (t: trace): Prop :=
  forall beh, program_behaves (Asm.semantics p) beh -> behavior_prefix t beh.

Theorem transf_c_program_preserves_initial_trace:
  forall p tp t,
  transf_c_program p = OK tp ->
  c_program_has_initial_trace p t ->
  asm_program_has_initial_trace tp t.
Proof.
  intros p tp t TRANSF CTRACE; red; intros beh AEXEC.
  exploit transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
  apply CTRACE in CEXEC. destruct IMPR as [EQ | [t' [A B]]].
- congruence.
- destruct CEXEC as (beh1' & EQ').
  destruct B as (beh1 & EQ).
  subst beh'. destruct beh1'; simpl in A; inv A. 
  exists (behavior_app t0 beh1). apply behavior_app_assoc.
Qed.

(** * Extension to separate compilation *)

(** The results above were given in terms of whole-program compilation.
    They also extend to separate compilation followed by linking. *)

Section SEPARATE_COMPILATION.

(** The source: a list of C compilation units *)
Variable c_units: nlist Csyntax.program.

(** The compiled code: a list of Asm compilation units, obtained by separate compilation *)
Variable asm_units: nlist Asm.program.
Hypothesis separate_compilation_succeeds: 
  nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units.

(** We assume that the source C compilation units can be linked together
    to obtain a monolithic C program [c_program]. *)
Variable c_program: Csyntax.program.
Hypothesis source_linking: link_list c_units = Some c_program.

(** Then, linking the Asm units obtained by separate compilation succeeds. *)
Lemma compiled_linking_succeeds:
  { asm_program | link_list asm_units = Some asm_program }.
Proof.
  destruct (link_list asm_units) eqn:E. 
- exists p; auto.
- exfalso. 
  exploit separate_transf_c_program_correct; eauto. intros (a & P & Q).
  congruence.
Qed.

(** Let asm_program be the result of linking the Asm units. *)
Let asm_program: Asm.program := proj1_sig compiled_linking_succeeds.
Let compiled_linking: link_list asm_units = Some asm_program := proj2_sig compiled_linking_succeeds.

(** Then, [asm_program] preserves the semantics and the specifications of
  [c_program], in the following sense.
  First, every behavior of [asm_program] improves upon one of the possible
  behaviors of [c_program]. *)

Theorem separate_transf_c_program_preservation:
  forall beh,
  program_behaves (Asm.semantics asm_program) beh ->
  exists beh', program_behaves (Csem.semantics c_program) beh' /\ behavior_improves beh' beh.
Proof.
  intros. exploit separate_transf_c_program_correct; eauto. intros (a & P & Q).
  assert (a = asm_program) by congruence. subst a. 
  eapply backward_simulation_behavior_improves; eauto.
Qed.

(** As a corollary, if [c_program] is free of undefined behaviors, 
  the behavior of [asm_program] is one of the possible behaviors of [c_program]. *)

Theorem separate_transf_c_program_is_refinement:
  (forall beh, program_behaves (Csem.semantics c_program) beh -> not_wrong beh) ->
  (forall beh, program_behaves (Asm.semantics asm_program) beh -> program_behaves (Csem.semantics c_program) beh).
Proof.
  intros. exploit separate_transf_c_program_preservation; eauto. intros (beh' & P & Q).
  assert (not_wrong beh') by auto.
  inv Q.
- auto.
- destruct H2 as (t & U & V). subst beh'. elim H1. 
Qed.

(** We now show that if all executions of [c_program] satisfy a specification,
  then all executions of [asm_program] also satisfy the specification, provided
  the specification is of the safety-enforcing kind. *)

Theorem separate_transf_c_program_preserves_spec:
  forall spec,
  safety_enforcing_specification spec ->
  c_program_satisfies_spec c_program spec ->
  asm_program_satisfies_spec asm_program spec.
Proof.
  intros spec SES CSAT; red; intros beh AEXEC.
  exploit separate_transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
  apply CSAT in CEXEC. destruct IMPR as [EQ | [t [A B]]].
- congruence.
- subst beh'. apply SES in CEXEC. contradiction. 
Qed.

(** As another corollary of [separate_transf_c_program_preservation],
  if all executions of [c_program] have a trace [t] as initial trace,
  so do all executions of [asm_program]. *)

Theorem separate_transf_c_program_preserves_initial_trace:
  forall t,
  c_program_has_initial_trace c_program t ->
  asm_program_has_initial_trace asm_program t.
Proof.
  intros t CTRACE; red; intros beh AEXEC.
  exploit separate_transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
  apply CTRACE in CEXEC. destruct IMPR as [EQ | [t' [A B]]].
- congruence.
- destruct CEXEC as (beh1' & EQ').
  destruct B as (beh1 & EQ).
  subst beh'. destruct beh1'; simpl in A; inv A. 
  exists (behavior_app t0 beh1). apply behavior_app_assoc.
Qed.

End SEPARATE_COMPILATION.

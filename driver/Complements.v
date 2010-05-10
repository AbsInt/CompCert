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
Require Import Determinism.
Require Import Csyntax.
Require Import Csem.
Require Import Asm.
Require Import Compiler.
Require Import Errors.

(** * Determinism of Asm semantics *)

(** In this section, we show that the semantics for the Asm language
  are deterministic, provided that the program is executed against a
  deterministic world, as formalized in module [Determinism]. *)

Remark extcall_arguments_deterministic:
  forall rs m sg args args',
  extcall_arguments rs m sg args ->
  extcall_arguments rs m sg args' -> args = args'.
Proof.
  assert (
    forall rs m ll args,
    extcall_args rs m ll args ->
    forall args', extcall_args rs m ll args' -> args = args').
  induction 1; intros.
  inv H. auto.
  inv H1. decEq; eauto.
  inv H; inv H4; congruence.
  unfold extcall_arguments; intros; eauto.
Qed.

Lemma step_internal_deterministic:
  forall ge s t1 s1 t2 s2,
  Asm.step ge s t1 s1 -> Asm.step ge s t2 s2 -> matching_traces t1 t2 ->
  s1 = s2 /\ t1 = t2.
Proof.
  intros. inv H; inv H0.
  assert (c0 = c) by congruence.
  assert (i0 = i) by congruence.
  assert (rs'0 = rs') by congruence.
  assert (m'0 = m') by congruence.
  subst. auto. 
  congruence.
  congruence.
  assert (ef0 = ef) by congruence. subst ef0.
  assert (args0 = args). eapply extcall_arguments_deterministic; eauto. subst args0.
  exploit external_call_determ. 
  instantiate (1 := Genv.find_symbol ge). exact (Genv.genv_vars_inj ge). 
  eexact H4. eexact H9. auto. 
  intros [A [B C]]. subst. 
  intuition congruence.
Qed.

Lemma initial_state_deterministic:
  forall p s1 s2,
  initial_state p s1 -> initial_state p s2 -> s1 = s2.
Proof.
  intros. inv H; inv H0. f_equal. congruence.
Qed.

Lemma final_state_not_step:
  forall ge st r, final_state st r -> nostep step ge st.
Proof.
  unfold nostep. intros. red; intros. inv H. inv H0.
  unfold Vzero in H1. congruence.
  unfold Vzero in H1. congruence. 
Qed.

Lemma final_state_deterministic:
  forall st r1 r2, final_state st r1 -> final_state st r2 -> r1 = r2.
Proof.
  intros. inv H; inv H0. congruence.
Qed.

Theorem asm_exec_program_deterministic:
  forall p w beh1 beh2,
  Asm.exec_program p beh1 -> Asm.exec_program p beh2 ->
  possible_behavior w beh1 -> possible_behavior w beh2 ->
  beh1 = beh2.
Proof.
  intros. 
  eapply (program_behaves_deterministic _ _ step (initial_state p) final_state); eauto.
  exact step_internal_deterministic.
  exact (initial_state_deterministic p).
  exact final_state_deterministic.
  exact final_state_not_step.
Qed.

(** * Additional semantic preservation property *)

(** Combining the semantic preservation theorem from module [Compiler]
  with the determinism of Asm executions, we easily obtain
  additional, stronger semantic preservation properties.
  The first property states that, when compiling a Clight
  program that has well-defined semantics, all possible executions
  of the resulting Asm code correspond to an execution of
  the source Clight program. *)

Theorem transf_c_program_is_refinement:
  forall p tp w,
  transf_c_program p = OK tp ->
  (exists b, Csem.exec_program p b /\ possible_behavior w b /\ not_wrong b) ->
  (forall b, Asm.exec_program tp b -> possible_behavior w b -> Csem.exec_program p b).
Proof.
  intros. destruct H0 as [b0 [A [B C]]]. 
  assert (Asm.exec_program tp b0).
    eapply transf_c_program_correct; eauto.
  assert (b = b0). eapply asm_exec_program_deterministic; eauto.
  subst b0. auto.
Qed.

Section SPECS_PRESERVED.

(** The second additional results shows that if one execution
  of the source Clight program satisfies a given specification
  (a predicate on the observable behavior of the program),
  then all executions of the produced Asm program satisfy
  this specification as well.  *) 

Variable spec: program_behavior -> Prop.

Hypothesis spec_not_wrong: forall b, spec b -> not_wrong b.

Theorem transf_c_program_preserves_spec:
  forall p tp w,
  transf_c_program p = OK tp ->
  (exists b, Csem.exec_program p b /\ possible_behavior w b /\ spec b) ->
  (forall b, Asm.exec_program tp b -> possible_behavior w b -> spec b).
Proof.
  intros. destruct H0 as [b1 [A [B C]]].
  assert (Asm.exec_program tp b1).
    eapply transf_c_program_correct; eauto.
  assert (b1 = b). eapply asm_exec_program_deterministic; eauto. 
  subst b1. auto.
Qed.

End SPECS_PRESERVED.

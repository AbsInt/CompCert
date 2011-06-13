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
Require Import Cstrategy.
Require Import Asm.
Require Import Compiler.
Require Import Errors.

(** * Integrating a deterministic external world *)

(** We now integrate a deterministic external world in the semantics
  of Compcert C and Asm. *)

Section WORLD.

Variable initial_world: world.

Definition exec_C_program (p: Csyntax.program) (beh: program_behavior) : Prop :=
  wprogram_behaves _ _
      Csem.step (Csem.initial_state p) Csem.final_state
      initial_world (Genv.globalenv p) beh.

Definition exec_asm_program (p: Asm.program) (beh: program_behavior) : Prop :=
  wprogram_behaves _ _
      Asm.step (Asm.initial_state p) Asm.final_state
      initial_world (Genv.globalenv p) beh.

(** ** Safety of C programs. *)

(** We show that a C program is safe (in the sense of [Cstrategy.safeprog])
  if it cannot go wrong in the world-aware semantics. *)

Lemma notwrong_safeprog:
  forall p,
  (forall beh, exec_C_program p beh -> not_wrong beh) ->
  Cstrategy.safeprog p initial_world.
Proof.
  intros; red.
  assert (exists beh1, exec_C_program p beh1).
    unfold exec_C_program. apply program_behaves_exists. 
  destruct H0 as [beh1 A].
  assert (B: not_wrong beh1) by auto.
  split.
  inv A; simpl in B.
  destruct H0. exists (fst s); auto.
  destruct H0. exists (fst s); auto.
  destruct H0. exists (fst s); auto.
  contradiction.
  contradiction.
  intros; red; intros.
  destruct (classic (exists r, Csem.final_state s' r)).
  (* 1. Final state.  This is immsafe. *)
  destruct H3 as [r F]. eapply immsafe_final; eauto. 
  (* 2. Not a final state. *)
  destruct (classic (nostep (wstep _ _ Csem.step) (Genv.globalenv p) (s', w'))).
  (* 2.1 No step possible -> going wrong *)
  elim (H (Goes_wrong t)). 
  eapply program_goes_wrong.
  instantiate (1 := (s, initial_world)). split; auto.
  instantiate (1 := (s', w')). apply Determinism.inject_star; auto. 
  auto.
  intros; red; intros. elim H3. exists r; auto. 
  (* 2.2 One step possible -> this is immsafe *)
  unfold nostep in H4. 
  generalize (not_all_ex_not _ _ H4). clear H4. intros [t' P].
  generalize (not_all_ex_not _ _ P). clear P. intros [s'' Q].
  generalize (NNPP _ Q). clear Q. intros R. destruct R as [R1 R2]. simpl in *.
  eapply immsafe_step. eauto. eauto. 
Qed.

(** ** Determinism of Asm semantics *)

Remark extcall_arguments_deterministic:
  forall rs m sg args args',
  extcall_arguments rs m sg args ->
  extcall_arguments rs m sg args' -> args = args'.
Proof.
  unfold extcall_arguments; intros. 
  revert args H args' H0. generalize (Conventions1.loc_arguments sg); induction 1; intros.
  inv H0; auto.
  inv H1; decEq; auto. inv H; inv H4; congruence. 
Qed.

Remark annot_arguments_deterministic:
  forall rs m pl args args',
  annot_arguments rs m pl args ->
  annot_arguments rs m pl args' -> args = args'.
Proof.
  unfold annot_arguments; intros. 
  revert pl args H args' H0. induction 1; intros.
  inv H0; auto.
  inv H1; decEq; auto. inv H; inv H4; congruence. 
Qed.

Lemma step_internal_deterministic:
  forall ge s t1 s1 t2 s2,
  Asm.step ge s t1 s1 -> Asm.step ge s t2 s2 -> matching_traces t1 t2 ->
  s1 = s2 /\ t1 = t2.
Proof.

Ltac InvEQ :=
  match goal with
  | [ H1: ?x = ?y, H2: ?x = ?z |- _ ] => rewrite H1 in H2; inv H2; InvEQ
  | _ => idtac
  end.

  intros. inv H; inv H0; InvEQ.
(* regular, regular *)
  split; congruence.
(* regular, builtin *)
  simpl in H5; inv H5.
(* regular, annot *)
  simpl in H5; inv H5.
(* builtin, regular *)
  simpl in H12; inv H12.
(* builtin, builtin *)
  exploit external_call_determ. eexact H5. eexact H12. auto. intros [A [B C]]. subst.
  auto.
(* annot, regular *)
  simpl in H13. inv H13.
(* annot, annot *)
  exploit annot_arguments_deterministic. eexact H5. eexact H11. intros EQ; subst. 
  exploit external_call_determ. eexact H6. eexact H14. auto. intros [A [B C]]. subst.
  auto.
(* extcall, extcall *)
  exploit extcall_arguments_deterministic. eexact H5. eexact H10. intros EQ; subst.
  exploit external_call_determ. eexact H4. eexact H9. auto. intros [A [B C]]. subst.
  auto.
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
  unfold nostep. intros. red; intros. inv H. inv H0; unfold Vzero in H1; congruence.
Qed.

Lemma final_state_deterministic:
  forall st r1 r2, final_state st r1 -> final_state st r2 -> r1 = r2.
Proof.
  intros. inv H; inv H0. congruence.
Qed.

Theorem asm_exec_program_deterministic:
  forall p beh1 beh2,
  exec_asm_program p beh1 -> exec_asm_program p beh2 ->
  beh1 = beh2.
Proof.
  intros. hnf in H; hnf in H0.
  eapply (program_behaves_deterministic _ _
             (wstep _ _ step)
             (winitial_state _ (initial_state p) initial_world)
             (wfinal_state _ final_state));
  eauto.
  apply wstep_deterministic. apply step_internal_deterministic.
  apply winitial_state_determ. apply initial_state_deterministic.
  apply wfinal_state_determ. apply final_state_deterministic.
  apply wfinal_state_nostep. apply final_state_not_step.
Qed.

(** * Additional semantic preservation property *)

(** Combining the semantic preservation theorem from module [Compiler]
  with the determinism of Asm executions, we easily obtain
  additional, stronger semantic preservation properties.
  The first property states that, when compiling a Compcert C
  program that has well-defined semantics, all possible executions
  of the resulting Asm code correspond to an execution of
  the source program. *)

Theorem transf_c_program_is_refinement:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, exec_C_program p beh -> not_wrong beh) ->
  (forall beh, exec_asm_program tp beh -> exec_C_program p beh).
Proof.
  intros. 
  exploit Cstrategy.strategy_behavior.
  apply notwrong_safeprog. eauto. 
  intros [beh1 [A [B [C D]]]].
  assert (Asm.exec_program tp beh1).
    eapply transf_c_program_correct; eauto.
  assert (exec_asm_program tp beh1).
    red. apply inject_behaviors; auto.
  assert (beh = beh1). eapply asm_exec_program_deterministic; eauto.
  subst beh.
  red. apply inject_behaviors; auto.
Qed.

Section SPECS_PRESERVED.

(** The second additional results shows that if one execution
  of the source C program satisfies a given specification
  (a predicate on the observable behavior of the program),
  then all executions of the produced Asm program satisfy
  this specification as well.  *) 

Variable spec: program_behavior -> Prop.

Hypothesis spec_not_wrong: forall b, spec b -> not_wrong b.

Theorem transf_c_program_preserves_spec:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, exec_C_program p beh -> spec beh) ->
  (forall beh, exec_asm_program tp beh -> spec beh).
Proof.
  intros. apply H0. apply transf_c_program_is_refinement with tp; auto. 
Qed.

End SPECS_PRESERVED.

End WORLD.


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

(** Type preservation for the CleanupLabels pass *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Op.
Require Import Locations.
Require Import LTLin.
Require Import CleanupLabels.
Require Import LTLintyping.

Lemma in_remove_unused_labels:
  forall bto i c, In i (remove_unused_labels bto c) -> In i c.
Proof.
  induction c; simpl.
  auto.
  destruct a; simpl; intuition.
  destruct (Labelset.mem l bto); simpl in H; intuition.
Qed.

Lemma wt_transf_function:
  forall f,
  wt_function f ->
  wt_function (transf_function f).
Proof.
  intros. inv H. constructor; simpl; auto.
  unfold cleanup_labels; red; intros.
  apply wt_instrs. eapply in_remove_unused_labels; eauto.
Qed.

Lemma wt_transf_fundef:
  forall f,
  wt_fundef f ->
  wt_fundef (transf_fundef f). 
Proof.
  induction 1. constructor. constructor. apply wt_transf_function; auto.
Qed.

Lemma program_typing_preserved:
  forall p,
  wt_program p ->
  wt_program (transf_program p).
Proof.
  intros; red; intros.
  exploit transform_program_function; eauto. intros [f1 [A B]]. subst f.
  apply wt_transf_fundef. eapply H; eauto.
Qed.

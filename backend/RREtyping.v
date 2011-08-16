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

(** Proof of type preservation for the [RRE] pass. *)

Require Import Coqlib.
Require Import AST.
Require Import Locations.
Require Import Linear.
Require Import Lineartyping.
Require Import Conventions.
Require Import RRE.
Require Import RREproof.

Remark wt_cons:
  forall f c i, wt_instr f i -> wt_code f c -> wt_code f (i::c).
Proof.
  intros; red; intros. simpl in H1; destruct H1. congruence. auto.
Qed.

Hint Constructors wt_instr : linearty.
Hint Resolve wt_cons: linearty.

Definition wt_eqs (eqs: equations) :=
  forall e, In e eqs -> slot_type (e_slot e) = mreg_type (e_reg e).

Lemma wt_eqs_nil:
  wt_eqs nil.
Proof. red; simpl; tauto. Qed.

Lemma wt_eqs_cons:
  forall r s eqs,
  slot_type s = mreg_type r -> wt_eqs eqs -> wt_eqs (mkeq r s :: eqs).
Proof.
  intros; red; simpl; intros. destruct H1. subst; simpl; auto. auto.
Qed.
  
Lemma wt_kill_loc:
  forall l eqs,
  wt_eqs eqs -> wt_eqs (kill_loc l eqs).
Proof.
  intros; red; intros. exploit In_kill_loc; eauto. intros [A B]. auto.
Qed.

Lemma wt_kill_locs:
  forall ll eqs,
  wt_eqs eqs -> wt_eqs (kill_locs ll eqs).
Proof.
  intros; red; intros. exploit In_kill_locs; eauto. intros [A B]. auto.
Qed.

Lemma wt_kill_temps:
  forall eqs, wt_eqs eqs -> wt_eqs (kill_temps eqs).
Proof.
  exact (wt_kill_locs temporaries).
Qed.

Lemma wt_kill_at_move:
  forall eqs, wt_eqs eqs -> wt_eqs (kill_at_move eqs).
Proof.
  exact (wt_kill_locs destroyed_at_move).
Qed.

Hint Resolve wt_eqs_nil wt_eqs_cons wt_kill_loc wt_kill_locs
             wt_kill_temps wt_kill_at_move: linearty.

Lemma wt_kill_op:
  forall op eqs, wt_eqs eqs -> wt_eqs (kill_op op eqs).
Proof.
  intros; destruct op; simpl; apply wt_kill_locs; auto.
Qed.

Hint Resolve wt_kill_op: linearty.

Lemma wt_transf_code:
  forall f c eqs, wt_code f c -> wt_eqs eqs ->
  wt_code (transf_function f) (transf_code eqs c).
Proof.
  induction c; intros; simpl.
  red; simpl; tauto.
  assert (WI: wt_instr f a) by auto with coqlib.
  assert (WC: wt_code f c) by (red; auto with coqlib).
  clear H.
  inv WI; auto 10 with linearty.
  destruct (is_incoming s) as []_eqn. auto with linearty.
  destruct (contains_equation s r eqs). auto with linearty.
  destruct (find_reg_containing s eqs) as [r'|]_eqn; auto with linearty.
  assert (mreg_type r' = mreg_type r).
  exploit H0. eapply find_reg_containing_sound; eauto. simpl. congruence.
  destruct (safe_move_insertion c); auto 10 with linearty.
Qed.

Lemma program_typing_preserved:
  forall p, wt_program p -> wt_program (transf_program p).
Proof.
  intros. red; intros. exploit transform_program_function; eauto. 
  intros [f0 [A B]]. subst f. exploit H; eauto. intros WTFD.
  inv WTFD; simpl; constructor.  red; simpl. 
  apply wt_transf_code; auto with linearty.
Qed.

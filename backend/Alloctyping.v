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

(** Preservation of typing during register allocation. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Locations.
Require Import LTL.
Require Import Coloring.
Require Import Coloringproof.
Require Import Allocation.
Require Import Allocproof.
Require Import RTLtyping.
Require Import LTLtyping.
Require Import Conventions.

(** This file proves that register allocation (the translation from
  RTL to LTL defined in file [Allocation]) preserves typing:
  given a well-typed RTL input, it produces LTL code that is
  well-typed. *)

Section TYPING_FUNCTION.

Variable f: RTL.function.
Variable env: regenv.
Variable live: PMap.t Regset.t.
Variable alloc: reg -> loc.
Variable tf: LTL.function.

Hypothesis TYPE_RTL: type_function f = OK env.
Hypothesis LIVE: analyze f = Some live.
Hypothesis ALLOC: regalloc f live (live0 f live) env = Some alloc.
Hypothesis TRANSL: transf_function f = OK tf.

Lemma wt_rtl_function: RTLtyping.wt_function f env.
Proof.
  apply type_function_correct; auto.
Qed.

Lemma alloc_type: forall r, Loc.type (alloc r) = env r.
Proof.
  intro. eapply regalloc_preserves_types; eauto.
Qed.

Lemma alloc_types:
  forall rl, List.map Loc.type (List.map alloc rl) = List.map env rl.
Proof.
  intros. rewrite list_map_compose. apply list_map_exten.
  intros. symmetry. apply alloc_type. 
Qed.

Lemma alloc_acceptable: 
  forall r, loc_acceptable (alloc r).
Proof.
  intros. eapply regalloc_acceptable; eauto.
Qed.

Lemma allocs_acceptable:
  forall rl, locs_acceptable (List.map alloc rl).
Proof.
  intros. eapply regsalloc_acceptable; eauto.
Qed.

Remark transf_unroll:
  tf = transf_fun f live alloc.
Proof.
  generalize TRANSL. unfold transf_function.
  rewrite TYPE_RTL. rewrite LIVE. rewrite ALLOC. congruence.
Qed.

Lemma valid_successor_transf:
  forall s,
  RTLtyping.valid_successor f s ->
  LTLtyping.valid_successor tf s.
Proof.
  unfold RTLtyping.valid_successor, LTLtyping.valid_successor.
  intros s [i AT].
  rewrite transf_unroll; simpl. rewrite PTree.gmap. 
  rewrite AT. exists (transf_instr f live alloc s i). auto.
Qed.  

Hint Resolve alloc_acceptable allocs_acceptable: allocty.
Hint Rewrite alloc_type alloc_types: allocty.
Hint Resolve valid_successor_transf: allocty.

(** * Type preservation during translation from RTL to LTL *)

Ltac WT := 
  constructor; auto with allocty; autorewrite with allocty; auto.

Lemma wt_transf_instr:
  forall pc instr,
  RTLtyping.wt_instr env f instr ->
  f.(RTL.fn_code)!pc = Some instr ->
  wt_instr tf (transf_instr f live alloc pc instr).
Proof.
  intros. inv H; simpl.
  (* nop *)
  WT.
  (* move *)
  destruct (Regset.mem r live!!pc).
  destruct (is_redundant_move Omove (r1 :: nil) r alloc); WT.
  WT.
  (* other ops *)
  destruct (Regset.mem res live!!pc).
  destruct (is_redundant_move op args res alloc); WT.
  WT.
  (* load *)
  destruct (Regset.mem dst live!!pc); WT.
  (* store *)
  WT.
  (* call *)
  exploit regalloc_correct_1; eauto. unfold correct_alloc_instr. 
  intros [A1 [A2 A3]]. 
  WT.
  destruct ros; simpl; auto. 
  split. autorewrite with allocty; auto.
  split. auto with allocty. auto.
  (* tailcall *)
  exploit regalloc_correct_1; eauto. unfold correct_alloc_instr. 
  intro A1.
  WT.
  destruct ros; simpl; auto. 
  split. autorewrite with allocty; auto.
  split. auto with allocty. auto.
  rewrite transf_unroll; auto.
  (* builtin *)
  WT.
  (* cond *)
  WT.
  (* jumptable *)
  WT. 
  (* return *)
  WT.
  rewrite transf_unroll; simpl. 
  destruct optres; simpl. autorewrite with allocty. auto. auto.
  destruct optres; simpl; auto with allocty.
Qed.

End TYPING_FUNCTION.

Lemma wt_transf_function:
  forall f tf,
  transf_function f = OK tf -> wt_function tf.
Proof.
  intros. generalize H; unfold transf_function.
  caseEq (type_function f). intros env TYP. 
  caseEq (analyze f). intros live ANL.
  change (transfer f (RTL.fn_entrypoint f)
                     live!!(RTL.fn_entrypoint f))
    with (live0 f live).
  caseEq (regalloc f live (live0 f live) env).
  intros alloc ALLOC.
  intro EQ; injection EQ; intro.
  assert (RTLtyping.wt_function f env). apply type_function_correct; auto.
  inversion H1.
  constructor; rewrite <- H0; simpl.
  rewrite (alloc_types _ _ _ _ ALLOC). auto.
  eapply regsalloc_acceptable; eauto.
  eapply regalloc_norepet_norepet; eauto.
  eapply regalloc_correct_2; eauto.
  intros until instr. rewrite PTree.gmap. 
  caseEq (RTL.fn_code f)!pc; simpl; intros.
  inversion H3. eapply wt_transf_instr; eauto. congruence. discriminate.
  eapply valid_successor_transf; eauto. congruence. 
  congruence. congruence. congruence.
Qed.

Lemma wt_transf_fundef:
  forall f tf,
  transf_fundef f = OK tf -> wt_fundef tf.
Proof.
  intros until tf; destruct f; simpl. 
  caseEq (transf_function f); simpl. intros g TF EQ. inversion EQ.
  constructor. eapply wt_transf_function; eauto.
  congruence.
  intros. inversion H. constructor. 
Qed.

Lemma program_typing_preserved:
  forall (p: RTL.program) (tp: LTL.program),
  transf_program p = OK tp ->
  LTLtyping.wt_program tp.
Proof.
  intros; red; intros.
  generalize (transform_partial_program_function transf_fundef p i f H H0).
  intros [f0 [IN TRANSF]].
  apply wt_transf_fundef with f0; auto.
Qed.

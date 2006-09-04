(** Type preservation for the Tunneling pass *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import LTLtyping.
Require Import Tunneling.

(** Tunneling preserves typing. *)

Lemma wt_tunnel_block:
  forall f b,
  wt_block f b ->
  wt_block (tunnel_function f) (tunnel_block f b).
Proof.
  induction 1; simpl; econstructor; eauto.
Qed.

Lemma wt_tunnel_function:
  forall f, wt_function f -> wt_function (tunnel_function f).
Proof.
  unfold wt_function; intros until b.
  simpl. rewrite PTree.gmap. unfold option_map. 
  caseEq (fn_code f)!pc. intros b0 AT EQ. 
  injection EQ; intros; subst b. 
  apply wt_tunnel_block. eauto. 
  intros; discriminate.
Qed.

Lemma wt_tunnel_fundef:
  forall f, wt_fundef f -> wt_fundef (tunnel_fundef f).
Proof.
  intros. inversion H; simpl. constructor; auto. 
  constructor. apply wt_tunnel_function; auto.
Qed.

Lemma program_typing_preserved:
  forall (p: LTL.program),
  wt_program p -> wt_program (tunnel_program p).
Proof.
  intros; red; intros.
  generalize (transform_program_function tunnel_fundef p i f H0).
  intros [f0 [IN TRANSF]].
  subst f. apply wt_tunnel_fundef. eauto.
Qed.

(** Type preservation for the Linearize pass *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import LTLtyping.
Require Import LTLin.
Require Import Linearize.
Require Import LTLintyping.
Require Import Conventions.

(** * Type preservation for the linearization pass *)

Lemma wt_add_instr:
  forall f i k, wt_instr f i -> wt_code f k -> wt_code f (i :: k).
Proof.
  intros; red; intros. elim H1; intro. subst i0; auto. auto.
Qed.

Lemma wt_add_branch:
  forall f s k, wt_code f k -> wt_code f (add_branch s k).
Proof.
  intros; unfold add_branch. destruct (starts_with s k).
  auto. apply wt_add_instr; auto. constructor.
Qed.

Lemma wt_linearize_instr:
  forall f instr,
  LTLtyping.wt_instr f instr ->
  forall k,
  wt_code f.(LTL.fn_sig) k ->
  wt_code f.(LTL.fn_sig) (linearize_instr instr k).
Proof.
  induction 1; simpl; intros.
  apply wt_add_branch; auto.
  apply wt_add_instr. constructor; auto. apply wt_add_branch; auto.
  apply wt_add_instr. constructor; auto. apply wt_add_branch; auto.
  apply wt_add_instr. constructor; auto. apply wt_add_branch; auto.
  apply wt_add_instr. constructor; auto. apply wt_add_branch; auto.
  apply wt_add_instr. constructor; auto. apply wt_add_branch; auto.
  apply wt_add_instr. constructor; auto. auto.
  apply wt_add_instr. constructor; auto. apply wt_add_branch; auto.
  destruct (starts_with s1 k); apply wt_add_instr.
  constructor; auto. rewrite H. destruct cond; auto. 
  apply wt_add_branch; auto.
  constructor; auto. apply wt_add_branch; auto.
  apply wt_add_instr. constructor; auto. auto.
Qed.

Lemma wt_linearize_body:
  forall f,
  (forall pc instr, 
     f.(LTL.fn_code)!pc = Some instr -> LTLtyping.wt_instr f instr) ->
  forall enum,
  wt_code f.(LTL.fn_sig) (linearize_body f enum).
Proof.
  induction enum; simpl.
  red; simpl; intros; contradiction.
  caseEq ((LTL.fn_code f)!a); intros.
  apply wt_add_instr. constructor. apply wt_linearize_instr; eauto with coqlib.
  auto.
Qed.

Lemma wt_transf_function:
  forall f,
  LTLtyping.wt_function f ->
  wt_function (transf_function f). 
Proof.
  intros. inv H. constructor; auto.
  simpl. apply wt_add_branch. 
  apply wt_linearize_body. auto. 
Qed.

Lemma wt_transf_fundef:
  forall f,
  LTLtyping.wt_fundef f ->
  wt_fundef (transf_fundef f). 
Proof.
  induction 1; simpl.
  constructor; assumption.
  constructor; apply wt_transf_function; assumption.
Qed.

Lemma program_typing_preserved:
  forall (p: LTL.program),
  LTLtyping.wt_program p ->
  LTLintyping.wt_program (transf_program p).
Proof.
  intros; red; intros.
  generalize (transform_program_function transf_fundef p i f H0).
  intros [f0 [IN TR]].
  subst f. apply wt_transf_fundef; auto. 
  apply (H i f0 IN).
Qed.

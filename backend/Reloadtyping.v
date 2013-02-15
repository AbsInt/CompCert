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

(** Proof of type preservation for Reload and of
    correctness of computation of stack bounds for Linear. *)

Require Import Coqlib.
Require Import AST.
Require Import Op.
Require Import Locations.
Require Import LTLin.
Require Import LTLintyping.
Require Import Linear.
Require Import Lineartyping.
Require Import Conventions.
Require Import Parallelmove.
Require Import Reload.
Require Import Reloadproof.

(** * Typing Linear constructors *)

(** We show that the Linear constructor functions defined in [Reload]
  generate well-typed instruction sequences,
  given sufficient typing and well-formedness hypotheses over the locations involved. *)

Hint Constructors wt_instr: reloadty.

Remark wt_code_cons:
  forall f i c, wt_instr f i -> wt_code f c -> wt_code f (i :: c).
Proof.
  intros; red; simpl; intros. elim H1; intro.
  subst i; auto. auto.
Qed.

Hint Resolve wt_code_cons: reloadty.

Definition loc_valid (f: function) (l: loc) :=
  match l with R _ => True | S s => slot_valid f s end.

Lemma loc_acceptable_valid:
  forall f l, loc_acceptable l -> loc_valid f l.
Proof.
  destruct l; simpl; intro. auto.
  destruct s; simpl. omega. tauto. tauto.
Qed.

Definition loc_writable (l: loc) :=
  match l with R _ => True | S s => slot_writable s end.

Lemma loc_acceptable_writable:
  forall l, loc_acceptable l -> loc_writable l.
Proof.
  destruct l; simpl; intro. auto.
  destruct s; simpl; tauto.
Qed.

Hint Resolve loc_acceptable_valid loc_acceptable_writable: reloadty.

Definition locs_valid (f: function) (ll: list loc) :=
  forall l, In l ll -> loc_valid f l.
Definition locs_writable (ll: list loc) :=
  forall l, In l ll -> loc_writable l.

Lemma locs_acceptable_valid:
  forall f ll, locs_acceptable ll -> locs_valid f ll.
Proof.
  unfold locs_acceptable, locs_valid. auto with reloadty.
Qed.

Lemma locs_acceptable_writable:
  forall ll, locs_acceptable ll -> locs_writable ll.
Proof.
  unfold locs_acceptable, locs_writable. auto with reloadty.
Qed.

Hint Resolve locs_acceptable_valid locs_acceptable_writable: reloadty.

Lemma wt_add_reload:
  forall f src dst k,
  loc_valid f src -> Loc.type src = mreg_type dst ->
  wt_code f k -> wt_code f (add_reload src dst k).
Proof.
  intros; unfold add_reload.
  destruct src; eauto with reloadty.
  destruct (mreg_eq m dst); eauto with reloadty.
Qed.

Hint Resolve wt_add_reload: reloadty.

Lemma wt_add_reloads:
  forall f srcs dsts k,
  locs_valid f srcs -> map Loc.type srcs = map mreg_type dsts ->
  wt_code f k -> wt_code f (add_reloads srcs dsts k).
Proof.
  induction srcs; destruct dsts; simpl; intros; try congruence.
  auto. inv H0. apply wt_add_reload; auto with coqlib reloadty.
  apply IHsrcs; auto. red; intros; auto with coqlib.
Qed.

Hint Resolve wt_add_reloads: reloadty.

Lemma wt_add_spill:
  forall f src dst k,
  loc_valid f dst -> loc_writable dst -> Loc.type dst = mreg_type src ->
  wt_code f k -> wt_code f (add_spill src dst k).
Proof.
  intros; unfold add_spill.
  destruct dst; eauto with reloadty.
  destruct (mreg_eq src m); eauto with reloadty.
Qed.

Hint Resolve wt_add_spill: reloadty.

Lemma wt_add_move:
  forall f src dst k,
  loc_valid f src -> loc_valid f dst -> loc_writable dst ->
  Loc.type dst = Loc.type src ->
  wt_code f k -> wt_code f (add_move src dst k).
Proof.
  intros. unfold add_move.
  destruct (Loc.eq src dst); auto.
  destruct src; auto with reloadty.
  destruct dst; auto with reloadty.
  set (tmp := match slot_type s with
                    | Tint => IT1
                    | Tfloat => FT1
                    end).
  assert (mreg_type tmp = Loc.type (S s)).
    simpl. destruct (slot_type s); reflexivity.
  apply wt_add_reload; auto with reloadty. 
  apply wt_add_spill; auto. congruence.
Qed.

Hint Resolve wt_add_move: reloadty.

Lemma wt_add_moves:
  forall f b moves,
  (forall s d, In (s, d) moves ->
      loc_valid f s /\ loc_valid f d /\ loc_writable d /\ Loc.type s = Loc.type d) ->
  wt_code f b ->
  wt_code f 
    (List.fold_right (fun p k => add_move (fst p) (snd p) k) b moves).
Proof.
  induction moves; simpl; intros.
  auto.
  destruct a as [s d]. simpl.
  destruct (H s d) as [A [B [C D]]]. auto.
  auto with reloadty.
Qed.

Theorem wt_parallel_move:
 forall f srcs dsts b,
 List.map Loc.type srcs = List.map Loc.type dsts ->
 locs_valid f srcs -> locs_valid f dsts -> locs_writable dsts ->
 wt_code f b ->  wt_code f (parallel_move srcs dsts b).
Proof.
  intros. unfold parallel_move. apply wt_add_moves; auto.
  intros. 
  elim (parmove_prop_2 _ _ _ _ H4); intros A B.
  split. destruct A as [C|[C|C]]; auto; subst s; exact I.
  split. destruct B as [C|[C|C]]; auto; subst d; exact I.
  split. destruct B as [C|[C|C]]; auto; subst d; exact I.
  eapply parmove_prop_3; eauto.
Qed.
Hint Resolve wt_parallel_move: reloadty.

Lemma wt_reg_for:
  forall l, mreg_type (reg_for l) = Loc.type l.
Proof.
  intros. destruct l; simpl. auto.
  case (slot_type s); reflexivity.
Qed.
Hint Resolve wt_reg_for: reloadty.

Lemma wt_regs_for_rec:
  forall locs itmps ftmps,
  enough_temporaries_rec locs itmps ftmps = true ->
  (forall r, In r itmps -> mreg_type r = Tint) ->
  (forall r, In r ftmps -> mreg_type r = Tfloat) ->
  List.map mreg_type (regs_for_rec locs itmps ftmps) = List.map Loc.type locs.
Proof.
  induction locs; intros.
  simpl. auto.
  simpl in H. simpl. 
  destruct a. 
  simpl. decEq. eauto. 
  caseEq (slot_type s); intro SLOTTYPE; rewrite SLOTTYPE in H.
  destruct itmps. discriminate.
  simpl. decEq. 
  rewrite SLOTTYPE. auto with coqlib.
  apply IHlocs; auto with coqlib.
  destruct ftmps. discriminate. simpl. decEq.
  rewrite SLOTTYPE. auto with coqlib.
  apply IHlocs; auto with coqlib.
Qed.

Lemma wt_regs_for:
  forall locs,
  enough_temporaries locs = true ->
  List.map mreg_type (regs_for locs) = List.map Loc.type locs.
Proof.
  intros. unfold regs_for. apply wt_regs_for_rec.
  auto.
  simpl; intros; intuition; subst r; reflexivity.
  simpl; intros; intuition; subst r; reflexivity.
Qed.
Hint Resolve wt_regs_for: reloadty.

Hint Resolve enough_temporaries_op_args enough_temporaries_cond enough_temporaries_addr: reloadty.

Hint Extern 4 (_ = _) => congruence : reloadty.

Lemma wt_transf_instr:
  forall f instr k,
  LTLintyping.wt_instr (LTLin.fn_sig f) instr ->
  wt_code (transf_function f) k ->
  wt_code (transf_function f) (transf_instr f instr k).
Proof.
  Opaque reg_for regs_for.
  intros. inv H; simpl; auto with reloadty.
  caseEq (is_move_operation op args); intros.
  destruct (is_move_operation_correct _ _ H). congruence.
  assert (map mreg_type (regs_for args) = map Loc.type args).
    eauto with reloadty.
  assert (mreg_type (reg_for res) = Loc.type res). eauto with reloadty.
  auto with reloadty.

  assert (map mreg_type (regs_for args) = map Loc.type args).
    eauto with reloadty.
  assert (mreg_type (reg_for dst) = Loc.type dst). eauto with reloadty.
  auto with reloadty.

  caseEq (enough_temporaries (src :: args)); intro ENOUGH.
  caseEq (regs_for (src :: args)); intros. auto.
  assert (map mreg_type (regs_for (src :: args)) = map Loc.type (src :: args)).
    apply wt_regs_for. auto. 
  rewrite H in H5. injection H5; intros.
  auto with reloadty.
  apply wt_add_reloads; auto with reloadty.
  symmetry. apply wt_regs_for. eauto with reloadty.
  assert (op_for_binary_addressing addr <> Omove).
    unfold op_for_binary_addressing; destruct addr; congruence.
  assert (type_of_operation (op_for_binary_addressing addr) = (type_of_addressing addr, Tint)).
    apply type_op_for_binary_addressing. 
    rewrite <- H1. rewrite list_length_map.
    eapply not_enough_temporaries_length; eauto. 
  apply wt_code_cons.
  constructor; auto. rewrite H5. decEq. rewrite <- H1. eauto with reloadty.
  apply wt_add_reload; auto with reloadty. 
  apply wt_code_cons; auto. constructor. reflexivity.
  rewrite <- H2. eauto with reloadty.

  assert (locs_valid (transf_function f) (loc_arguments sig)).
    red; intros. generalize (loc_arguments_acceptable sig l H).
    destruct l; simpl; auto. destruct s; simpl; intuition.
  assert (locs_writable (loc_arguments sig)).
    red; intros. generalize (loc_arguments_acceptable sig l H6).
    destruct l; simpl; auto. destruct s; simpl; intuition.
  assert (map Loc.type args = map Loc.type (loc_arguments sig)).
    rewrite loc_arguments_type; auto.
  assert (Loc.type res = mreg_type (loc_result sig)).
    rewrite H2. unfold loc_result. unfold proj_sig_res. 
    destruct (sig_res sig); auto. destruct t; auto.
  destruct ros.
  destruct H3 as [A [B C]].
  apply wt_parallel_move; eauto with reloadty.
  apply wt_add_reload; eauto with reloadty. 
  apply wt_code_cons; eauto with reloadty. 
  constructor. rewrite <- A. auto with reloadty. 
  auto with reloadty.

  assert (locs_valid (transf_function f) (loc_arguments sig)).
    red; intros. generalize (loc_arguments_acceptable sig l H).
    destruct l; simpl; auto. destruct s; simpl; intuition.
  assert (locs_writable (loc_arguments sig)).
    red; intros. generalize (loc_arguments_acceptable sig l H6).
    destruct l; simpl; auto. destruct s; simpl; intuition.
  assert (map Loc.type args = map Loc.type (loc_arguments sig)).
    rewrite loc_arguments_type; auto.
  destruct ros. destruct H2 as [A [B C]]. auto 10 with reloadty. 
  auto 10 with reloadty.
  destruct (ef_reloads ef) eqn:?.
  assert (arity_ok (sig_args (ef_sig ef)) = true) by intuition congruence.
  assert (map mreg_type (regs_for args) = map Loc.type args).
    apply wt_regs_for. apply arity_ok_enough. congruence.
  assert (mreg_type (reg_for res) = Loc.type res). eauto with reloadty.
  auto 10 with reloadty.
  auto with reloadty.

  assert (map mreg_type (regs_for args) = map Loc.type args).
    eauto with reloadty.
  auto with reloadty.

  assert (mreg_type (reg_for arg) = Loc.type arg).
    eauto with reloadty.
  auto with reloadty.

  destruct optres; simpl in *; auto with reloadty.
  apply wt_add_reload; auto with reloadty. 
  unfold loc_result. rewrite <- H1.
  destruct (Loc.type l); reflexivity.
Qed.

Lemma wt_transf_code:
  forall f  c,
  LTLintyping.wt_code (LTLin.fn_sig f) c ->
  Lineartyping.wt_code (transf_function f) (transf_code f c).
Proof.
  induction c; simpl; intros.
  red; simpl; tauto.
  apply wt_transf_instr; auto with coqlib. 
  apply IHc. red; auto with coqlib. 
Qed.

Lemma wt_transf_fundef:
  forall fd,
  LTLintyping.wt_fundef fd ->
  Lineartyping.wt_fundef (transf_fundef fd).
Proof.
  intros. destruct fd; simpl.
  inv H. inv H1. constructor. unfold wt_function. simpl. 
  apply wt_parallel_move; auto with reloadty.
    rewrite loc_parameters_type. auto.
    red; intros.
    destruct (list_in_map_inv _ _ _ H) as [r [A B]].
    generalize (loc_arguments_acceptable _ _ B).
    destruct r; intro.
    rewrite A. simpl. auto.
    red in H0. destruct s; try tauto.
    simpl in A. subst l. simpl. auto.
  apply wt_transf_code; auto.
  constructor.
Qed.

Lemma program_typing_preserved:
  forall p,
  LTLintyping.wt_program p ->
  Lineartyping.wt_program (transf_program p).
Proof.
  intros; red; intros. 
  destruct (transform_program_function _ _ _ _ H0) as [f0 [A B]].
  subst f; apply wt_transf_fundef. eauto.
Qed.

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

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import AST.
Require Import Locations.
Require Export Conventions1.

(** The processor-dependent and EABI-dependent definitions are in
    [arch/abi/Conventions1.v].  This file adds various processor-independent
    definitions and lemmas. *)

Lemma loc_arguments_acceptable_2:
  forall s l,
  In l (regs_of_rpairs (loc_arguments s)) -> loc_argument_acceptable l.
Proof.
  intros until l. generalize (loc_arguments_acceptable s). generalize (loc_arguments s).
  induction l0 as [ | p pl]; simpl; intros.
- contradiction.
- rewrite in_app_iff in H0. destruct H0.
  exploit H; eauto. destruct p; simpl in *; intuition congruence.
  apply IHpl; auto.
Qed.

(** ** Stack size of function arguments *)

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Definition max_outgoing_1 (accu: Z) (l: loc) : Z :=
  match l with
  | S Outgoing ofs ty => Z.max accu (ofs + typesize ty)
  | _ => accu
  end.

Definition max_outgoing_2 (accu: Z) (rl: rpair loc) : Z :=
  match rl with
  | One l => max_outgoing_1 accu l
  | Twolong l1 l2 => max_outgoing_1 (max_outgoing_1 accu l1) l2
  end.

Definition size_arguments (s: signature) : Z :=
  List.fold_left max_outgoing_2 (loc_arguments s) 0.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark fold_max_outgoing_above:
  forall l n, fold_left max_outgoing_2 l n >= n.
Proof.
  assert (A: forall n l, max_outgoing_1 n l >= n).
  { intros; unfold max_outgoing_1. destruct l as [_ | []]; extlia. }
  induction l; simpl; intros. 
  - lia.
  - eapply Zge_trans. eauto.
    destruct a; simpl. apply A. eapply Zge_trans; eauto.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros. apply fold_max_outgoing_above.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments s)) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros until ty.
  assert (A: forall n l, n <= max_outgoing_1 n l).
  { intros; unfold max_outgoing_1. destruct l as [_ | []]; extlia. }
  assert (B: forall p n,
             In (S Outgoing ofs ty) (regs_of_rpair p) ->
             ofs + typesize ty <= max_outgoing_2 n p).
  { intros. destruct p; simpl in H; intuition; subst; simpl.
  - extlia.
  - eapply Z.le_trans. 2: apply A. extlia.
  - extlia. }
  assert (C: forall l n,
             In (S Outgoing ofs ty) (regs_of_rpairs l) ->
             ofs + typesize ty <= fold_left max_outgoing_2 l n).
  { induction l; simpl; intros.
  - contradiction.
  - rewrite in_app_iff in H. destruct H.
  + eapply Z.le_trans. eapply B; eauto.
    apply Z.ge_le. apply fold_max_outgoing_above.
  + apply IHl; auto.
  }
  apply C. 
Qed.

(** ** Location of function parameters *)

(** A function finds the values of its parameter in the same locations
  where its caller stored them, except that the stack-allocated arguments,
  viewed as [Outgoing] slots by the caller, are accessed via [Incoming]
  slots (at the same offsets and types) in the callee. *)

Definition parameter_of_argument (l: loc) : loc :=
  match l with
  | S Outgoing n ty => S Incoming n ty
  | _ => l
  end.

Definition loc_parameters (s: signature) : list (rpair loc) :=
  List.map (map_rpair parameter_of_argument) (loc_arguments s).

Lemma incoming_slot_in_parameters:
  forall ofs ty sg,
  In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters sg)) ->
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)).
Proof.
  intros.
  replace (regs_of_rpairs (loc_parameters sg)) with (List.map parameter_of_argument (regs_of_rpairs (loc_arguments sg))) in H.
  change (S Incoming ofs ty) with (parameter_of_argument (S Outgoing ofs ty)) in H.
  exploit list_in_map_inv. eexact H. intros [x [A B]]. simpl in A.
  exploit loc_arguments_acceptable_2; eauto. unfold loc_argument_acceptable; intros.
  destruct x; simpl in A; try discriminate.
  destruct sl; try contradiction.
  inv A. auto.
  unfold loc_parameters. generalize (loc_arguments sg). induction l as [ | p l]; simpl; intros.
  auto.
  rewrite map_app. f_equal; auto. destruct p; auto.
Qed.

(** * Tail calls *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (regs_of_rpairs (loc_arguments s)) ->
  match l with R _ => True | S _ _ _ => False end.

(** Decide whether a tailcall is possible. *)

Definition tailcall_is_possible (sg: signature) : bool :=
  List.forallb
    (fun l => match l with R _ => true | S _ _ _ => false end)
    (regs_of_rpairs (loc_arguments sg)).

Lemma tailcall_is_possible_correct:
  forall s, tailcall_is_possible s = true -> tailcall_possible s.
Proof.
  unfold tailcall_is_possible; intros. rewrite forallb_forall in H.
  red; intros. apply H in H0. destruct l; [auto|discriminate].
Qed.

Lemma zero_size_arguments_tailcall_possible:
  forall sg, size_arguments sg = 0 -> tailcall_possible sg.
Proof.
  intros; red; intros. exploit loc_arguments_acceptable_2; eauto.
  unfold loc_argument_acceptable.
  destruct l; intros. auto. destruct sl; try contradiction. destruct H1.
  generalize (loc_arguments_bounded _ _ _ H0).
  generalize (typesize_pos ty). lia.
Qed.


(** * Callee-save locations *)

(** We classify locations as either
- callee-save, i.e. preserved across function calls:
  callee-save registers, [Local] and [Incoming] stack slots;
- caller-save, i.e. possibly modified by a function call:
  non-callee-save registers, [Outgoing] stack slots.

Concerning [Outgoing] stack slots: several ABIs allow a function to modify
the stack slots used for passing parameters to this function.
The code currently generated by CompCert never does so, but the code
generated by other compilers often does so (e.g. GCC for x86-32).
Hence, CompCert-generated code must not assume that [Outgoing] stack slots
are preserved across function calls, because they might not be preserved
if the called function was compiled by another compiler. 
*)

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => is_callee_save r = true
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: Locmap.t) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

(** * Assigning result locations *)

(** Useful lemmas to reason about the result of an external call. *)

Lemma locmap_get_set_loc_result:
  forall sg v rs l,
  match l with R r => is_callee_save r = true | S _ _ _ => True end ->
  Locmap.setpair (loc_result sg) v rs l = rs l.
Proof.
  intros. apply Locmap.gpo. 
  assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
  { intros. destruct l; simpl. congruence. auto. }
  generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto.
Qed.

Lemma locmap_get_set_loc_result_callee_save:
  forall sg v rs l,
  callee_save_loc l ->
  Locmap.setpair (loc_result sg) v rs l = rs l.
Proof.
  intros. apply locmap_get_set_loc_result. 
  red in H; destruct l; auto.
Qed.

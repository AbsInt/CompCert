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

Definition loc_parameters (s: signature) :=
  List.map parameter_of_argument (loc_arguments s).

Lemma incoming_slot_in_parameters:
  forall ofs ty sg,
  In (S Incoming ofs ty) (loc_parameters sg) ->
  In (S Outgoing ofs ty) (loc_arguments sg).
Proof.
  intros.
  unfold loc_parameters in H.
  change (S Incoming ofs ty) with (parameter_of_argument (S Outgoing ofs ty)) in H.
  exploit list_in_map_inv. eexact H. intros [x [A B]]. simpl in A.
  exploit loc_arguments_acceptable; eauto. unfold loc_argument_acceptable; intros.
  destruct x; simpl in A; try discriminate.
  destruct sl; try contradiction.
  inv A. auto.
Qed.

(** * Tail calls *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (loc_arguments s) ->
  match l with R _ => True | S _ _ _ => False end.

(** Decide whether a tailcall is possible. *)

Definition tailcall_is_possible (sg: signature) : bool :=
  let fix tcisp (l: list loc) :=
    match l with
    | nil => true
    | R _ :: l' => tcisp l'
    | S _ _ _ :: l' => false
    end
  in tcisp (loc_arguments sg).

Lemma tailcall_is_possible_correct:
  forall s, tailcall_is_possible s = true -> tailcall_possible s.
Proof.
  intro s. unfold tailcall_is_possible, tailcall_possible.
  generalize (loc_arguments s). induction l; simpl; intros.
  elim H0.
  destruct a.
  destruct H0. subst l0. auto. apply IHl. auto. auto. discriminate.
Qed.

Lemma zero_size_arguments_tailcall_possible:
  forall sg, size_arguments sg = 0 -> tailcall_possible sg.
Proof.
  intros; red; intros. exploit loc_arguments_acceptable; eauto.
  unfold loc_argument_acceptable.
  destruct l; intros. auto. destruct sl; try contradiction. destruct H1.
  generalize (loc_arguments_bounded _ _ _ H0).
  generalize (typesize_pos ty). omega.
Qed.

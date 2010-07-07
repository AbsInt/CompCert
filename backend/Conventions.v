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

(** * Acceptable locations for register allocation *)

(** The following predicate describes the locations that can be assigned
  to an RTL pseudo-register during register allocation: a non-temporary
  machine register or a [Local] stack slot are acceptable. *)

Definition loc_acceptable (l: loc) : Prop :=
  match l with
  | R r => ~(In l temporaries)
  | S (Local ofs ty) => ofs >= 0
  | S (Incoming _ _) => False
  | S (Outgoing _ _) => False
  end.

Definition locs_acceptable (ll: list loc) : Prop :=
  forall l, In l ll -> loc_acceptable l.

Lemma temporaries_not_acceptable:
  forall l, loc_acceptable l -> Loc.notin l temporaries.
Proof.
  unfold loc_acceptable; destruct l.
  simpl. intuition congruence.
  destruct s; try contradiction. 
  intro. simpl. tauto.
Qed.
Hint Resolve temporaries_not_acceptable: locs.

Lemma locs_acceptable_disj_temporaries:
  forall ll, locs_acceptable ll -> Loc.disjoint ll temporaries.
Proof.
  intros. apply Loc.notin_disjoint. intros.
  apply temporaries_not_acceptable. auto. 
Qed.

Lemma loc_acceptable_noteq_diff:
  forall l1 l2,
  loc_acceptable l1 -> l1 <> l2 -> Loc.diff l1 l2.
Proof.
  unfold loc_acceptable, Loc.diff; destruct l1; destruct l2;
  try (destruct s); try (destruct s0); intros; auto; try congruence.
  case (zeq z z0); intro. 
  compare t t0; intro.
  subst z0; subst t0; tauto.
  tauto. tauto.
  contradiction. contradiction.
Qed.

Lemma loc_acceptable_notin_notin:
  forall r ll,
  loc_acceptable r ->
  ~(In r ll) -> Loc.notin r ll.
Proof.
  induction ll; simpl; intros.
  auto.
  split. apply loc_acceptable_noteq_diff. assumption. 
  apply sym_not_equal. tauto. 
  apply IHll. assumption. tauto. 
Qed.

(** * Additional properties of result and argument locations *)

(** The result location is not a callee-save register. *)

Lemma loc_result_not_callee_save:
  forall (s: signature),
  ~(In (loc_result s) int_callee_save_regs \/ In (loc_result s) float_callee_save_regs).
Proof.
  intros. generalize (loc_result_caller_save s).
  generalize (int_callee_save_not_destroyed (loc_result s)).
  generalize (float_callee_save_not_destroyed (loc_result s)).
  tauto.
Qed.

(** Callee-save registers do not overlap with argument locations. *)

Lemma arguments_not_preserved:
  forall sig l,
  Loc.notin l destroyed_at_call -> loc_acceptable l ->
  Loc.notin l (loc_arguments sig).
Proof.
  intros. destruct l; red in H0. 
  apply Loc.reg_notin. red; intros. 
  exploit Loc.notin_not_in; eauto. eapply arguments_caller_save; eauto.
  destruct s; try contradiction.
  unfold loc_arguments. apply loc_arguments_rec_notin_local. 
Qed.

(** There is no partial overlap between arguments and acceptable locations. *)

Lemma no_overlap_arguments:
  forall args sg,
  locs_acceptable args ->
  Loc.no_overlap args (loc_arguments sg).
Proof.
  unfold Loc.no_overlap; intros.
  generalize (H r H0).
  generalize (loc_arguments_acceptable _ _ H1).
  destruct s; destruct r; simpl.
  intros. case (mreg_eq m0 m); intro. left; congruence. tauto.
  intros. right; destruct s; auto.
  intros. right. auto.
  destruct s; try tauto. destruct s0; tauto.
Qed.

(** ** Location of function parameters *)

(** A function finds the values of its parameter in the same locations
  where its caller stored them, except that the stack-allocated arguments,
  viewed as [Outgoing] slots by the caller, are accessed via [Incoming]
  slots (at the same offsets and types) in the callee. *)

Definition parameter_of_argument (l: loc) : loc :=
  match l with
  | S (Outgoing n ty) => S (Incoming n ty)
  | _ => l
  end.

Definition loc_parameters (s: signature) :=
  List.map parameter_of_argument (loc_arguments s).

Lemma loc_parameters_type:
  forall sig, List.map Loc.type (loc_parameters sig) = sig.(sig_args).
Proof.
  intros. unfold loc_parameters.
  rewrite list_map_compose. 
  rewrite <- loc_arguments_type.
  apply list_map_exten.
  intros. destruct x; simpl. auto. 
  destruct s; reflexivity.
Qed.

Lemma loc_parameters_length:
  forall sg, List.length (loc_parameters sg) = List.length sg.(sig_args).
Proof.
  intros. unfold loc_parameters. rewrite list_length_map. 
  apply loc_arguments_length.
Qed.

Lemma loc_parameters_not_temporaries:
  forall sig, Loc.disjoint (loc_parameters sig) temporaries.
Proof.
  intro; red; intros.
  unfold loc_parameters in H. 
  elim (list_in_map_inv _ _ _ H). intros y [EQ IN].
  generalize (loc_arguments_not_temporaries sig y x2 IN H0).
  subst x1. destruct x2.
  destruct y; simpl. auto. destruct s; auto.
  byContradiction. generalize H0. simpl. NotOrEq.
Qed.

Lemma no_overlap_parameters:
  forall params sg,
  locs_acceptable params ->
  Loc.no_overlap (loc_parameters sg) params.
Proof.
  unfold Loc.no_overlap; intros.
  unfold loc_parameters in H0. 
  elim (list_in_map_inv _ _ _ H0). intros t [EQ IN].
  rewrite EQ. 
  generalize (loc_arguments_acceptable _ _ IN).
  generalize (H s H1).
  destruct s; destruct t; simpl.
  intros. case (mreg_eq m0 m); intro. left; congruence. tauto.
  intros. right; destruct s; simpl; auto.
  intros; right; auto.
  destruct s; try tauto. destruct s0; try tauto. 
  intros; simpl. tauto.
Qed.

(** * Tail calls *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (loc_arguments s) ->
  match l with R _ => True | S _ => False end.

(** Decide whether a tailcall is possible. *)

Definition tailcall_is_possible (sg: signature) : bool :=
  let fix tcisp (l: list loc) :=
    match l with
    | nil => true
    | R _ :: l' => tcisp l'
    | S _ :: l' => false
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

(** * Counting temporaries *)

(** Given a list [tys] of types representing arguments to an operator,
  [arity_ok tys] returns [true] if there are enough temporaries to
  reload all arguments into temporaries. *)

Fixpoint arity_ok_rec (tys: list typ) (itmps ftmps: list mreg)
                      {struct tys} : bool :=
  match tys with
  | nil => true
  | Tint :: ts =>
      match itmps with
      | nil => false
      | it1 :: its => arity_ok_rec ts its ftmps
      end
  | Tfloat :: ts =>
      match ftmps with
      | nil => false
      | ft1 :: fts => arity_ok_rec ts itmps fts
      end
  end.

Definition arity_ok (tys: list typ) :=
  arity_ok_rec tys int_temporaries float_temporaries.





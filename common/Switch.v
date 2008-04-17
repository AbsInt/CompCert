(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Multi-way branches (``[switch]'') and their compilation
    to 2-way comparison trees. *)

Require Import EqNat.
Require Import Coqlib.
Require Import Integers.

(** A multi-way branch is composed of a list of (key, action) pairs,
  plus a default action.  *)

Definition table : Set := list (int * nat).

Fixpoint switch_target (n: int) (dfl: nat) (cases: table)
                       {struct cases} : nat :=
  match cases with
  | nil => dfl
  | (key, action) :: rem =>
      if Int.eq n key then action else switch_target n dfl rem
  end.

(** Multi-way branches are translated to a 2-way comparison tree.
    Each node of the tree performs an equality test or a less-than
    test against one of the keys. *)

Inductive comptree : Set :=
  | CTaction: nat -> comptree
  | CTifeq: int -> nat -> comptree -> comptree
  | CTiflt: int -> comptree -> comptree -> comptree.

Fixpoint comptree_match (n: int) (t: comptree) {struct t}: nat :=
  match t with
  | CTaction act => act
  | CTifeq key act t' =>
      if Int.eq n key then act else comptree_match n t'
  | CTiflt key t1 t2 =>
      if Int.ltu n key then comptree_match n t1 else comptree_match n t2
  end.

(** The translation from a table to a comparison tree is performed
  by untrusted Caml code (function [compile_switch] in
  file [RTLgenaux.ml]).  In Coq, we validate a posteriori the
  result of this function.  In other terms, we now develop
  and prove correct Coq functions that take a table and a comparison
  tree, and check that their semantics are equivalent. *)

Fixpoint split_lt (pivot: int) (cases: table)
                  {struct cases} : table * table :=
  match cases with
  | nil => (nil, nil)
  | (key, act) :: rem =>
      let (l, r) := split_lt pivot rem in
      if Int.ltu key pivot
      then ((key, act) :: l, r)
      else (l, (key, act) :: r)
  end.

Fixpoint split_eq (pivot: int) (cases: table)
                  {struct cases} : option nat * table :=
  match cases with
  | nil => (None, nil)
  | (key, act) :: rem =>
      let (same, others) := split_eq pivot rem in
      if Int.eq key pivot
      then (Some act, others)
      else (same, (key, act) :: others)
  end.

Definition refine_low_bound (v lo: Z) :=
  if zeq v lo then lo + 1 else lo.

Definition refine_high_bound (v hi: Z) :=
  if zeq v hi then hi - 1 else hi.

Fixpoint validate (default: nat) (cases: table) (t: comptree)
                  (lo hi: Z) {struct t} : bool :=
  match t with
  | CTaction act =>
      match cases with
      | nil =>
          beq_nat act default
      | (key1, act1) :: _ =>
          zeq (Int.unsigned key1) lo && zeq lo hi && beq_nat act act1
      end
  | CTifeq pivot act t' =>
      match split_eq pivot cases with
      | (None, _) =>
          false
      | (Some act', others) =>
          beq_nat act act' 
          && validate default others t'
                      (refine_low_bound (Int.unsigned pivot) lo)
                      (refine_high_bound (Int.unsigned pivot) hi)
      end
  | CTiflt pivot t1 t2 =>
      match split_lt pivot cases with
      | (lcases, rcases) =>
          validate default lcases t1 lo (Int.unsigned pivot - 1)
          && validate default rcases t2 (Int.unsigned pivot) hi
      end
  end.

Definition validate_switch (default: nat) (cases: table) (t: comptree) :=
  validate default cases t 0 Int.max_unsigned.

(** Correctness proof for validation. *)

Lemma split_eq_prop:
  forall v default n cases optact cases',
  split_eq n cases = (optact, cases') ->
  switch_target v default cases =
   (if Int.eq v n
    then match optact with Some act => act | None => default end
    else switch_target v default cases').
Proof.
  induction cases; simpl; intros until cases'.
  intros. inversion H; subst. simpl. 
  destruct (Int.eq v n); auto.
  destruct a as [key act]. 
  case_eq (split_eq n cases). intros same other SEQ.
  rewrite (IHcases _ _ SEQ).
  predSpec Int.eq Int.eq_spec key n; intro EQ; inversion EQ; simpl.
  subst n. destruct (Int.eq v key). auto. auto.
  predSpec Int.eq Int.eq_spec v key. 
  subst v. predSpec Int.eq Int.eq_spec key n. congruence. auto.
  auto.
Qed.

Lemma split_lt_prop:
  forall v default n cases lcases rcases,
  split_lt n cases = (lcases, rcases) ->
  switch_target v default cases =
    (if Int.ltu v n
     then switch_target v default lcases
     else switch_target v default rcases).
Proof.
  induction cases; intros until rcases; simpl.
  intro. inversion H; subst. simpl.
  destruct (Int.ltu v n); auto.
  destruct a as [key act]. 
  case_eq (split_lt n cases). intros lc rc SEQ.
  rewrite (IHcases _ _ SEQ).
  case_eq (Int.ltu key n); intros; inv H0; simpl.
  predSpec Int.eq Int.eq_spec v key. 
  subst v. rewrite H. auto.
  auto.
  predSpec Int.eq Int.eq_spec v key. 
  subst v. rewrite H. auto.
  auto.
Qed.

Lemma validate_correct_rec:
  forall default v t cases lo hi,
  validate default cases t lo hi = true ->
  lo <= Int.unsigned v <= hi ->
  switch_target v default cases = comptree_match v t.
Proof.
  induction t; simpl; intros until hi.
  (* base case *)
  destruct cases as [ | [key1 act1] cases1]; intros.
  replace n with default. reflexivity. 
  symmetry. apply beq_nat_eq. auto.
  destruct (andb_prop _ _ H). destruct (andb_prop _ _ H1). clear H H1.
  assert (Int.unsigned key1 = lo). eapply proj_sumbool_true; eauto.
  assert (lo = hi). eapply proj_sumbool_true; eauto.
  assert (Int.unsigned v = Int.unsigned key1). omega.
  replace n with act1.
  simpl. unfold Int.eq. rewrite H5. rewrite zeq_true. auto.
  symmetry. apply beq_nat_eq. auto.
  (* eq node *)
  case_eq (split_eq i cases). intros optact cases' EQ. 
  destruct optact as [ act | ]. 2: congruence.
  intros. destruct (andb_prop _ _ H). clear H.
  rewrite (split_eq_prop v default _ _ _ _ EQ).
  predSpec Int.eq Int.eq_spec v i.
  symmetry. apply beq_nat_eq; auto.
  eapply IHt. eauto.
  assert (Int.unsigned v <> Int.unsigned i).
    rewrite <- (Int.repr_unsigned v) in H.
    rewrite <- (Int.repr_unsigned i) in H.
    congruence.
  split.
  unfold refine_low_bound. destruct (zeq (Int.unsigned i) lo); omega.
  unfold refine_high_bound. destruct (zeq (Int.unsigned i) hi); omega.
  (* lt node *)
  case_eq (split_lt i cases). intros lcases rcases EQ V RANGE.
  destruct (andb_prop _ _ V). clear V.
  rewrite (split_lt_prop v default _ _ _ _ EQ). 
  unfold Int.ltu. destruct (zlt (Int.unsigned v) (Int.unsigned i)).
  eapply IHt1. eauto. omega.
  eapply IHt2. eauto. omega.
Qed.

Definition table_tree_agree
    (default: nat) (cases: table) (t: comptree) : Prop :=
  forall v, switch_target v default cases = comptree_match v t.

Theorem validate_switch_correct:
  forall default t cases,
  validate_switch default cases t = true ->
  table_tree_agree default cases t.
Proof.
  unfold validate_switch, table_tree_agree; intros.
  eapply validate_correct_rec; eauto. 
  apply Int.unsigned_range_2.
Qed.

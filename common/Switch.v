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

(** Multi-way branches (``switch'' statements) and their compilation
    to comparison trees. *)

Require Import EqNat.
Require Import FMaps.
Require FMapAVL.
Require Import Coqlib.
Require Import Integers.
Require Import Ordered.

Module IntMap := FMapAVL.Make(OrderedInt).
Module IntMapF := FMapFacts.Facts(IntMap).

(** A multi-way branch is composed of a list of (key, action) pairs,
  plus a default action.  *)

Definition table : Type := list (int * nat).

Fixpoint switch_target (n: int) (dfl: nat) (cases: table)
                       {struct cases} : nat :=
  match cases with
  | nil => dfl
  | (key, action) :: rem =>
      if Int.eq n key then action else switch_target n dfl rem
  end.

(** Multi-way branches are translated to comparison trees.
    Each node of the tree performs either
- an equality against one of the keys;
- or a "less than" test against one of the keys;
- or a computed branch (jump table) against a range of key values. *)

Inductive comptree : Type :=
  | CTaction: nat -> comptree
  | CTifeq: int -> nat -> comptree -> comptree
  | CTiflt: int -> comptree -> comptree -> comptree
  | CTjumptable: int -> int -> list nat -> comptree -> comptree.

Fixpoint comptree_match (n: int) (t: comptree) {struct t}: option nat :=
  match t with
  | CTaction act => Some act
  | CTifeq key act t' =>
      if Int.eq n key then Some act else comptree_match n t'
  | CTiflt key t1 t2 =>
      if Int.ltu n key then comptree_match n t1 else comptree_match n t2
  | CTjumptable ofs sz tbl t' =>
      if Int.ltu (Int.sub n ofs) sz
      then list_nth_z tbl (Int.signed (Int.sub n ofs))
      else comptree_match n t'
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

Fixpoint split_between (ofs sz: int) (cases: table)
                       {struct cases} : IntMap.t nat * table :=
  match cases with
  | nil => (IntMap.empty nat, nil)
  | (key, act) :: rem =>
      let (inside, outside) := split_between ofs sz rem in
      if Int.ltu (Int.sub key ofs) sz
      then (IntMap.add key act inside, outside)
      else (inside, (key, act) :: outside)
  end.

Definition refine_low_bound (v lo: Z) :=
  if zeq v lo then lo + 1 else lo.

Definition refine_high_bound (v hi: Z) :=
  if zeq v hi then hi - 1 else hi.

Fixpoint validate_jumptable (cases: IntMap.t nat) (default: nat)
                            (tbl: list nat) (n: int) {struct tbl} : bool :=
  match tbl with
  | nil => true
  | act :: rem =>
      beq_nat act (match IntMap.find n cases with Some a => a | None => default end)
      && validate_jumptable cases default rem (Int.add n Int.one)
  end.

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
  | CTjumptable ofs sz tbl t' =>
      let tbl_len := list_length_z tbl in
      match split_between ofs sz cases with
      | (inside, outside) =>
          zle (Int.unsigned sz) tbl_len
          && zle tbl_len Int.max_signed
          && validate_jumptable inside default tbl ofs
          && validate default outside t' lo hi
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

Lemma split_between_prop:
  forall v default ofs sz cases inside outside,
  split_between ofs sz cases = (inside, outside) ->
  switch_target v default cases =
    (if Int.ltu (Int.sub v ofs) sz
     then match IntMap.find v inside with Some a => a | None => default end
     else switch_target v default outside).
Proof.
  induction cases; intros until outside; simpl.
  intros. inv H. simpl. destruct (Int.ltu (Int.sub v ofs) sz); auto.
  destruct a as [key act]. case_eq (split_between ofs sz cases). intros ins outs SEQ.
  rewrite (IHcases _ _ SEQ). 
  case_eq (Int.ltu (Int.sub key ofs) sz); intros; inv H0; simpl.
  rewrite IntMapF.add_o. 
  predSpec Int.eq Int.eq_spec v key. 
  subst v. rewrite H. rewrite dec_eq_true. auto.
  rewrite dec_eq_false; auto.
  case_eq (Int.ltu (Int.sub v ofs) sz); intros; auto.
  predSpec Int.eq Int.eq_spec v key. 
  subst v. congruence.
  auto.
Qed.

Lemma validate_jumptable_correct_rec:
  forall cases default tbl base v,
  validate_jumptable cases default tbl base = true ->
  0 <= Int.signed v < list_length_z tbl -> Int.signed v <= Int.max_signed ->
  list_nth_z tbl (Int.signed v) =
  Some(match IntMap.find (Int.add base v) cases with Some a => a | None => default end).
Proof.
  induction tbl; intros until v; simpl.
  unfold list_length_z; simpl. intros. omegaContradiction.
  rewrite list_length_z_cons. intros. destruct (andb_prop _ _ H). clear H.
  generalize (beq_nat_eq _ _ (sym_equal H2)). clear H2. intro. subst a.
  destruct (zeq (Int.signed v) 0).
  rewrite Int.add_signed. rewrite e. rewrite Zplus_0_r. rewrite Int.repr_signed. auto.
  assert (Int.signed (Int.sub v Int.one) = Int.signed v - 1).
    rewrite Int.sub_signed. change (Int.signed Int.one) with 1. 
    apply Int.signed_repr. split. apply Zle_trans with 0. 
    vm_compute; congruence. omega. omega.
    replace (Int.add base v) with (Int.add (Int.add base Int.one) (Int.sub v Int.one)).
  rewrite <- IHtbl. rewrite H. auto. auto. rewrite H. omega. 
  rewrite H. omega. 
  rewrite Int.sub_add_opp. rewrite Int.add_permut. rewrite Int.add_assoc. 
  replace (Int.add Int.one (Int.neg Int.one)) with Int.zero.
  rewrite Int.add_zero. apply Int.add_commut.
  apply Int.mkint_eq. reflexivity.
Qed.

Lemma validate_jumptable_correct:
  forall cases default tbl ofs v sz,
  validate_jumptable cases default tbl ofs = true ->
  Int.ltu (Int.sub v ofs) sz = true ->
  Int.unsigned sz <= list_length_z tbl <= Int.max_signed ->
  list_nth_z tbl (Int.signed (Int.sub v ofs)) =
  Some(match IntMap.find v cases with Some a => a | None => default end).
Proof.
  intros.
  exploit Int.ltu_range_test; eauto. omega. intros. 
  rewrite (validate_jumptable_correct_rec cases default tbl ofs).
  rewrite Int.sub_add_opp. rewrite Int.add_permut. rewrite <- Int.sub_add_opp. 
  rewrite Int.sub_idem. rewrite Int.add_zero. auto. 
  auto.
  omega. 
  omega.
Qed.

Lemma validate_correct_rec:
  forall default v t cases lo hi,
  validate default cases t lo hi = true ->
  lo <= Int.unsigned v <= hi ->
  comptree_match v t = Some (switch_target v default cases).
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
  f_equal. apply beq_nat_eq; auto.
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
  (* jumptable node *)
  case_eq (split_between i i0 cases). intros ins outs EQ V RANGE.
  destruct (andb_prop _ _ V). clear V.
  destruct (andb_prop _ _ H). clear H.
  destruct (andb_prop _ _ H1). clear H1.
  rewrite (split_between_prop v _ _ _ _ _ _ EQ).
  case_eq (Int.ltu (Int.sub v i) i0); intros.
  eapply validate_jumptable_correct; eauto. 
  split; eapply proj_sumbool_true; eauto.
  eapply IHt; eauto. 
Qed.

Definition table_tree_agree
    (default: nat) (cases: table) (t: comptree) : Prop :=
  forall v, comptree_match v t = Some(switch_target v default cases).

Theorem validate_switch_correct:
  forall default t cases,
  validate_switch default cases t = true ->
  table_tree_agree default cases t.
Proof.
  unfold validate_switch, table_tree_agree; intros.
  eapply validate_correct_rec; eauto. 
  apply Int.unsigned_range_2.
Qed.

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
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.

(** A multi-way branch is composed of a list of (key, action) pairs,
  plus a default action.  *)

Definition table : Type := list (Z * nat).

Fixpoint switch_target (n: Z) (dfl: nat) (cases: table)
                       {struct cases} : nat :=
  match cases with
  | nil => dfl
  | (key, action) :: rem =>
      if zeq n key then action else switch_target n dfl rem
  end.

Inductive switch_argument: bool -> val -> Z -> Prop :=
  | switch_argument_32: forall i,
      switch_argument false (Vint i) (Int.unsigned i)
  | switch_argument_64: forall i,
      switch_argument true (Vlong i) (Int64.unsigned i).

(** Multi-way branches are translated to comparison trees.
    Each node of the tree performs either
- an equality against one of the keys;
- or a "less than" test against one of the keys;
- or a computed branch (jump table) against a range of key values. *)

Inductive comptree : Type :=
  | CTaction (act: nat)
  | CTifeq (key: Z) (act: nat) (cne: comptree)
  | CTiflt (key: Z) (clt: comptree) (cge: comptree)
  | CTjumptable (ofs: Z) (sz: Z) (acts: list nat) (cother: comptree).

Section COMPTREE.

Variable modulus: Z.
Hypothesis modulus_pos: modulus > 0.

Fixpoint comptree_match (n: Z) (t: comptree) {struct t}: option nat :=
  match t with
  | CTaction act => Some act
  | CTifeq key act t' =>
      if zeq n key then Some act else comptree_match n t'
  | CTiflt key t1 t2 =>
      if zlt n key then comptree_match n t1 else comptree_match n t2
  | CTjumptable ofs sz tbl t' =>
      let delta := (n - ofs) mod modulus in
      if zlt delta sz
      then list_nth_z tbl (delta mod Int.modulus)
      else comptree_match n t'
  end.

(** The translation from a table to a comparison tree is performed
  by untrusted Caml code (function [compile_switch] in
  file [RTLgenaux.ml]).  In Coq, we validate a posteriori the
  result of this function.  In other terms, we now develop
  and prove correct Coq functions that take a table and a comparison
  tree, and check that their semantics are equivalent. *)

Fixpoint split_lt (pivot: Z) (cases: table)
                  {struct cases} : table * table :=
  match cases with
  | nil => (nil, nil)
  | (key, act) :: rem =>
      let (l, r) := split_lt pivot rem in
      if zlt key pivot
      then ((key, act) :: l, r)
      else (l, (key, act) :: r)
  end.

Fixpoint split_eq (pivot: Z) (cases: table)
                  {struct cases} : option nat * table :=
  match cases with
  | nil => (None, nil)
  | (key, act) :: rem =>
      let (same, others) := split_eq pivot rem in
      if zeq key pivot
      then (Some act, others)
      else (same, (key, act) :: others)
  end.

Fixpoint split_between (dfl: nat) (ofs sz: Z) (cases: table)
                       {struct cases} : ZMap.t nat * table :=
  match cases with
  | nil => (ZMap.init dfl, nil)
  | (key, act) :: rem =>
      let (inside, outside) := split_between dfl ofs sz rem in
      if zlt ((key - ofs) mod modulus) sz
      then (ZMap.set key act inside, outside)
      else (inside, (key, act) :: outside)
  end.

Definition refine_low_bound (v lo: Z) :=
  if zeq v lo then lo + 1 else lo.

Definition refine_high_bound (v hi: Z) :=
  if zeq v hi then hi - 1 else hi.

Fixpoint validate_jumptable (cases: ZMap.t nat)
                            (tbl: list nat) (n: Z) {struct tbl} : bool :=
  match tbl with
  | nil => true
  | act :: rem =>
      Nat.eqb act (ZMap.get n cases)
      && validate_jumptable cases rem (Z.succ n)
  end.

Fixpoint validate (default: nat) (cases: table) (t: comptree)
                  (lo hi: Z) {struct t} : bool :=
  match t with
  | CTaction act =>
      match cases with
      | nil =>
          Nat.eqb act default
      | (key1, act1) :: _ =>
          zeq key1 lo && zeq lo hi && Nat.eqb act act1
      end
  | CTifeq pivot act t' =>
      zle 0 pivot && zlt pivot modulus &&
      match split_eq pivot cases with
      | (None, _) =>
          false
      | (Some act', others) =>
          Nat.eqb act act'
          && validate default others t'
                      (refine_low_bound pivot lo)
                      (refine_high_bound pivot hi)
      end
  | CTiflt pivot t1 t2 =>
      zle 0 pivot && zlt pivot modulus &&
      match split_lt pivot cases with
      | (lcases, rcases) =>
          validate default lcases t1 lo (pivot - 1)
          && validate default rcases t2 pivot hi
      end
  | CTjumptable ofs sz tbl t' =>
      let tbl_len := list_length_z tbl in
      zle 0 ofs && zlt ofs modulus &&
      zle 0 sz && zlt sz modulus &&
      zle (ofs + sz) modulus && zle sz tbl_len && zlt sz Int.modulus &&
      match split_between default ofs sz cases with
      | (inside, outside) =>
          validate_jumptable inside tbl ofs
          && validate default outside t' lo hi
     end
  end.

Definition validate_switch (default: nat) (cases: table) (t: comptree) :=
  validate default cases t 0 (modulus - 1).

(** Structural properties checked by validation *)

Inductive wf_comptree: comptree -> Prop :=
  | wf_action: forall act,
      wf_comptree (CTaction act)
  | wf_ifeq: forall key act cne,
      0 <= key < modulus -> wf_comptree cne -> wf_comptree (CTifeq key act cne)
  | wf_iflt: forall key clt cge,
      0 <= key < modulus -> wf_comptree clt -> wf_comptree cge -> wf_comptree (CTiflt key clt cge)
  | wf_jumptable: forall ofs sz acts cother,
      0 <= ofs < modulus -> 0 <= sz < modulus ->
      wf_comptree cother ->
      wf_comptree (CTjumptable ofs sz acts cother).

Lemma validate_wf:
  forall default t cases lo hi,
  validate default cases t lo hi = true ->
  wf_comptree t.
Proof.
  induction t; simpl; intros; InvBooleans.
- constructor.
- destruct (split_eq key cases) as [[act'|] others]; try discriminate; InvBooleans.
  constructor; eauto.
- destruct (split_lt key cases) as [lc rc]; InvBooleans.
  constructor; eauto.
- destruct (split_between default ofs sz cases) as [ins out]; InvBooleans.
  constructor; eauto.
Qed.

(** Semantic correctness proof for validation. *)

Lemma split_eq_prop:
  forall v default n cases optact cases',
  split_eq n cases = (optact, cases') ->
  switch_target v default cases =
   (if zeq v n
    then match optact with Some act => act | None => default end
    else switch_target v default cases').
Proof.
  induction cases; simpl; intros until cases'.
- intros. inv H. simpl. destruct (zeq v n); auto.
- destruct a as [key act].
  destruct (split_eq n cases) as [same other] eqn:SEQ.
  rewrite (IHcases same other) by auto.
  destruct (zeq key n); intros EQ; inv EQ.
+ destruct (zeq v n); auto.
+ simpl. destruct (zeq v key).
  * subst v. rewrite zeq_false by auto. auto.
  * auto.
Qed.

Lemma split_lt_prop:
  forall v default n cases lcases rcases,
  split_lt n cases = (lcases, rcases) ->
  switch_target v default cases =
    (if zlt v n
     then switch_target v default lcases
     else switch_target v default rcases).
Proof.
  induction cases; intros until rcases; simpl.
- intros. inv H. simpl. destruct (zlt v n); auto.
- destruct a as [key act].
  destruct (split_lt n cases) as [lc rc] eqn:SEQ.
  rewrite (IHcases lc rc) by auto.
  destruct (zlt key n); intros EQ; inv EQ; simpl.
+ destruct (zeq v key). rewrite zlt_true by omega. auto. auto.
+ destruct (zeq v key). rewrite zlt_false by omega. auto. auto.
Qed.

Lemma split_between_prop:
  forall v default ofs sz cases inside outside,
  split_between default ofs sz cases = (inside, outside) ->
  switch_target v default cases =
    (if zlt ((v - ofs) mod modulus) sz
     then ZMap.get v inside
     else switch_target v default outside).
Proof.
  induction cases; intros until outside; simpl; intros SEQ.
- inv SEQ. rewrite ZMap.gi. simpl. destruct (zlt ((v - ofs) mod modulus) sz); auto.
- destruct a as [key act].
  destruct (split_between default ofs sz cases) as [ins outs].
  erewrite IHcases; eauto.
  destruct (zlt ((key - ofs) mod modulus) sz); inv SEQ.
+ rewrite ZMap.gsspec. unfold ZIndexed.eq.
  destruct (zeq v key).
  subst v. rewrite zlt_true by auto. auto.
  auto.
+ simpl. destruct (zeq v key).
  subst v. rewrite zlt_false by auto. auto.
  auto.
Qed.

Lemma validate_jumptable_correct_rec:
  forall cases tbl base v,
  validate_jumptable cases tbl base = true ->
  0 <= v < list_length_z tbl ->
  list_nth_z tbl v = Some(ZMap.get (base + v) cases).
Proof.
  induction tbl; simpl; intros.
- unfold list_length_z in H0. simpl in H0. omegaContradiction.
- InvBooleans. rewrite list_length_z_cons in H0. apply beq_nat_true in H1.
  destruct (zeq v 0).
  + replace (base + v) with base by omega. congruence.
  + replace (base + v) with (Z.succ base + Z.pred v) by omega.
    apply IHtbl. auto. omega.
Qed.

Lemma validate_jumptable_correct:
  forall cases tbl ofs v sz,
  validate_jumptable cases tbl ofs = true ->
  (v - ofs) mod modulus < sz ->
  0 <= sz -> 0 <= ofs -> ofs + sz <= modulus ->
  0 <= v < modulus ->
  sz <= list_length_z tbl ->
  list_nth_z tbl ((v - ofs) mod modulus) = Some(ZMap.get v cases).
Proof.
  intros.
  rewrite (validate_jumptable_correct_rec cases tbl ofs); auto.
- f_equal. f_equal. rewrite Zmod_small. omega.
  destruct (zle ofs v). omega.
  assert (M: ((v - ofs) + 1 * modulus) mod modulus = (v - ofs) + modulus).
  { rewrite Zmod_small. omega. omega. }
  rewrite Z_mod_plus in M by auto. rewrite M in H0. omega.
- generalize (Z_mod_lt (v - ofs) modulus modulus_pos). omega.
Qed.

Lemma validate_correct_rec:
  forall default v,
  0 <= v < modulus ->
  forall t cases lo hi,
  validate default cases t lo hi = true ->
  lo <= v <= hi ->
  comptree_match v t = Some (switch_target v default cases).
Proof.
  intros default v VRANGE. induction t; simpl; intros until hi.
- (* base case *)
  destruct cases as [ | [key1 act1] cases1]; intros.
+ apply beq_nat_true in H. subst act. reflexivity.
+ InvBooleans. apply beq_nat_true in H2. subst. simpl.
  destruct (zeq v hi). auto. omegaContradiction.
- (* eq node *)
  destruct (split_eq key cases) as [optact others] eqn:EQ. intros.
  destruct optact as [act1|]; InvBooleans; try discriminate.
  apply beq_nat_true in H.
  rewrite (split_eq_prop v default _ _ _ _ EQ).
  destruct (zeq v key).
  + congruence.
  + eapply IHt; eauto.
    unfold refine_low_bound, refine_high_bound. split.
    destruct (zeq key lo); omega.
    destruct (zeq key hi); omega.
- (* lt node *)
  destruct (split_lt key cases) as [lcases rcases] eqn:EQ; intros; InvBooleans.
  rewrite (split_lt_prop v default _ _ _ _ EQ). destruct (zlt v key).
  eapply IHt1. eauto. omega.
  eapply IHt2. eauto. omega.
- (* jumptable node *)
  destruct (split_between default ofs sz cases) as [ins outs] eqn:EQ; intros; InvBooleans.
  rewrite (split_between_prop v _ _ _ _ _ _ EQ).
  assert (0 <= (v - ofs) mod modulus < modulus) by (apply Z_mod_lt; omega).
  destruct (zlt ((v - ofs) mod modulus) sz).
  rewrite Zmod_small by omega. eapply validate_jumptable_correct; eauto.
  eapply IHt; eauto.
Qed.

Definition table_tree_agree
    (default: nat) (cases: table) (t: comptree) : Prop :=
  forall v, 0 <= v < modulus -> comptree_match v t = Some(switch_target v default cases).

Theorem validate_switch_correct:
  forall default t cases,
  validate_switch default cases t = true ->
  wf_comptree t /\ table_tree_agree default cases t.
Proof.
  unfold validate_switch, table_tree_agree; split.
  eapply validate_wf; eauto.
  intros; eapply validate_correct_rec; eauto. omega.
Qed.

End COMPTREE.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and INRIA                  *)
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

From Coq Require Import Recdef FMaps FMapFacts Zwf.
From Coq Require FMapAVL.
Require Import Coqlib Ordered Integers Values.

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

(** ** Compilation of multi-way branches *)

(** *** Normalization of a multi-way branch *)

(** Normalization performs the following steps, which do not change
    the semantics of a switch (according to [switch_target], but
    facilitate compilation:
-     remove duplicate cases, keeping only the first case for each key;
-     eliminate cases that are beyond the range of values of the scrutinee;
-     sort cases by increasing key.
*)

Module ZMap := FMapAVL.Make OrderedZ.
Module ZMapF := FMapFacts.Facts ZMap.

Fixpoint map_of_table (modulus: Z) (tbl: table) : ZMap.t nat :=
  match tbl with
  | nil => ZMap.empty nat
  | (k1, a1) :: tbl =>
      let tbl' := map_of_table modulus tbl in
      if zle 0 k1 && zlt k1 modulus then ZMap.add k1 a1 tbl' else tbl'
  end.

Definition normalize_table (modulus: Z) (tbl: table) : table :=
  ZMap.elements (map_of_table modulus tbl).

(** *** Compile a multi-way branch as a jump table *)

Section JUMP_TABLE.

Variable dfl: nat.
Variable max: Z.

Function jump_table (min: Z) (l: list (Z * nat))
                    {wf (Zwf_up (max + 1)) min} : list nat :=
  if zle min max then
    match l with
    | nil => dfl :: jump_table (min + 1) nil
    | (k, d) :: l' =>
        if zeq k min
        then d :: jump_table (min + 1) l'
        else dfl :: jump_table (min + 1) l
    end
  else nil.
Proof.
- intros; red; lia.
- intros; red; lia.
- intros; red; lia.
- apply Zwf_up_well_founded.
Defined.

End JUMP_TABLE.

Definition compile_jumptable (dfl: nat) (tbl: table) (min max: Z) :=
  CTjumptable min (max - min + 1) (jump_table dfl max min tbl) (CTaction dfl).

(** *** Compile a multi-way branch as a binary decision tree *)

(** Split a list in two halves of approximately the same length.
    (The second half can have one more element than the first half.)   *)

Section LIST_SPLIT.

Context {A: Type}.

Fixpoint split_rec (before: list A) (after: list A) (cursor: list A) :=
  match after, cursor with
  | a1 :: al, c1 :: c2 :: cl => split_rec (a1 :: before) al cl
  | _, _ => (List.rev' before, after)
  end.

Definition split_in_half (l: list A) : list A * list A :=
  split_rec nil l l.

Lemma split_rec_eq:
  forall after before cursor,
  fst (split_rec before after cursor) ++ snd (split_rec before after cursor)
  = List.rev before ++ after.
Proof.
  induction after as [|a1 al]; simpl; intros.
- rewrite List.rev_alt; auto. 
- destruct cursor as [| c1 [ |c2 cl]]; simpl.
  + rewrite List.rev_alt; auto. 
  + rewrite List.rev_alt; auto.
  + rewrite IHal. simpl. rewrite app_ass. auto.
Qed.

Lemma split_in_half_eq:
  forall l, fst (split_in_half l) ++ snd (split_in_half l) = l.
Proof.
  unfold split_in_half; intros. rewrite split_rec_eq. auto.
Qed.

Lemma split_rec_length:
  forall after before cursor,
  (  length (fst (split_rec before after cursor)) * 2 <= length before * 2 + length cursor
  /\ length (snd (split_rec before after cursor)) * 2 <= length after * 2 - length cursor + 1)%nat.
Proof.
  assert (length_rev': forall (l: list A), length (rev' l) = length l).
  { intros. unfold rev'; rewrite <- rev_alt. apply rev_length. }
  induction after as [ | a1 after]; intros before cursor; simpl.
- rewrite length_rev'; lia.
- destruct cursor as [ | c1 [ | c2 cursor' ]]; simpl.
  + rewrite length_rev'; lia.  
  + rewrite length_rev'; lia.  
  + specialize (IHafter (a1 :: before) cursor'). simpl length in IHafter. lia.
Qed.

Lemma split_in_half_length:
  forall l,
  (  length (fst (split_in_half l)) * 2 <= length l
  /\ length (snd (split_in_half l)) * 2 <= length l + 1)%nat.
Proof.
  intros. unfold split_in_half.
  specialize (split_rec_length l nil l). simpl; lia.
Qed.

Lemma split_in_half_length':
  forall a1 a2 al,
  let l := a1 :: a2 :: al in
  (  0 < length (fst (split_in_half l)) < length l
  /\ 0 < length (snd (split_in_half l)) < length l)%nat.
Proof.
  intros.
  set (l1 := fst (split_in_half l)).
  set (l2 := snd (split_in_half l)).
  assert (L: (length l1 + length l2 = length l)%nat).
  { rewrite <- app_length. unfold l1, l2; rewrite split_in_half_eq; auto. }
  specialize (split_in_half_length l). fold l1; fold l2.
  unfold l in *. simpl length in *. lia.
Qed.

End LIST_SPLIT.

(** Compile a multi-way branch to a binary decision tree, using a variant
    of binary search.  The base cases are branches with one, two, or three
    branches, which are compiled to the minimal number of equality tests. *)

Definition compile_tree_1 (dfl: nat) (k1: Z) (a1: nat) (min max: Z) : comptree :=
  if zeq max min then
    CTaction a1
  else
    CTifeq k1 a1 (CTaction dfl).

Definition compile_tree_2 (dfl: nat) (k1: Z) (a1: nat) (k2: Z) (a2: nat) (min max: Z) : comptree :=
  CTifeq k1 a1
    (if zeq (max - min) 1 then
      CTaction a2
     else
      CTifeq k2 a2 (CTaction dfl)).

Definition compile_tree_3 (dfl: nat) (k1: Z) (a1: nat) (k2: Z) (a2: nat) (k3: Z) (a3: nat) (min max: Z) : comptree :=
  CTifeq k1 a1
    (CTifeq k2 a2
      (if zeq (max - min) 2 then
         CTaction a3
       else
         CTifeq k3 a3 (CTaction dfl))).

Definition first_key (tbl: table) : Z :=
  match tbl with
  | nil => 0   (**r should not happen *)
  | (key, act) :: tbl => key
  end.

Function compile_tree (dfl: nat) (tbl: table) (min max: Z)
                      { measure length tbl } : comptree :=
  match tbl with
  | nil => CTaction dfl
  | (k1, a1) :: nil =>
       compile_tree_1 dfl k1 a1 min max
  | (k1, a1) :: (k2, a2) :: nil =>
       compile_tree_2 dfl k1 a1 k2 a2 min max
  | (k1, a1) :: (k2, a2) :: (k3, a3) :: nil =>
       compile_tree_3 dfl k1 a1 k2 a2 k3 a3 min max
  | _ =>
     let (tbl1, tbl2) := split_in_half tbl in
     let pivot := first_key tbl2 in
     CTiflt pivot (compile_tree dfl tbl1 min (pivot - 1))
                  (compile_tree dfl tbl2 pivot max)
  end.
Proof.
- intros.
  destruct (split_in_half_length' (k1, a1) (k2, a2) ((k3, a3) :: p2 :: l2)) as [P Q].
  rewrite teq6 in Q; tauto.
- intros.
  destruct (split_in_half_length' (k1, a1) (k2, a2) ((k3, a3) :: p2 :: l2)) as [P Q].
  rewrite teq6 in P; tauto.
Defined.

(** *** Normalization and compilation to a decision tree *)

(** Heuristic to choose between the two compilation strategies.
    We estimate the code size (including the size of the jump table)
    for the two strategies and choose the one with the smaller size.
    Also, small jump tables are not efficient, so we always use
    decision trees for 6 cases or less. *)

Definition dense_enough (numcases span: Z) : bool :=
  let tree_size := numcases * 4 in
  let table_size := span + 8 in
  zle 7 numcases
  && zle table_size tree_size
  && zlt span Int.modulus.

(** The entry point: normalize and compile to a decision tree. *)

Definition compile_switch (modulus: Z) (dfl: nat) (tbl: table) :=
  let tbl1 := normalize_table modulus tbl in
  match tbl1 with
  | nil =>  CTaction dfl
  | (kmin, _) as cmin :: _ =>
      let (kmax, _) := List.last tbl1 cmin in
      let numcases := list_length_z tbl1 in
      if dense_enough numcases (kmax - kmin + 1)
      then compile_jumptable dfl tbl1 kmin kmax
      else compile_tree dfl tbl1 0 (modulus - 1)
  end.

(** ** Correctness proof *)

Section COMPTREE.

Variable modulus: Z.
Hypothesis modulus_pos: modulus > 0.

(** Semantics of decision trees.  The "modulo" computations in the [CTjumptable]
  case reflect the use of machine integer arithmetic in the compiled code. *)

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

(** Well-formedness conditions on decision trees.  The integer literals mentioned
  must be representable as machine integers. *)

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

(** Tables that are sorted by strictly increasing keys. *)

Inductive sorted: table -> Prop :=
  | sorted_nil: sorted nil
  | sorted_cons: forall k a tbl,
      sorted tbl ->
      (forall k' a', In (k', a') tbl -> k < k') ->
      sorted ((k, a) :: tbl).

Lemma sorted_app_inv:
  forall tbl1 tbl2,
  sorted (tbl1 ++ tbl2) ->
  sorted tbl1 /\ sorted tbl2 /\
  forall k1 a1 k2 a2, In (k1, a1) tbl1 -> In (k2, a2) tbl2 -> k1 < k2.
Proof.
  induction tbl1 as [ | [k a] tbl1]; simpl; intros.
- intuition auto. constructor.
- inv H. exploit IHtbl1; eauto. intros (P & Q & R).
  intuition eauto.
  constructor. auto. eauto using in_or_app. inv H1; eauto using in_or_app. 
Qed.

Lemma in_sorted_le:
  forall k a l k' a',
  sorted ((k, a) :: l) -> In (k', a') ((k, a) :: l) -> k <= k'.
Proof.
  intros. inv H. simpl in H0; destruct H0.
- inv H; lia.
- assert (k < k') by eauto. lia.
Qed.

Lemma in_sorted_ge:
  forall k a l k' a',
  sorted (l ++ (k, a) :: nil) -> In (k', a') (l ++ (k, a) :: nil) -> k' <= k.
Proof.
  intros. exploit sorted_app_inv; eauto. intros (P & Q & R).
  rewrite in_app_iff in H0. destruct H0.
  assert (k' < k) by eauto with coqlib. lia.
  simpl in H0; intuition auto. inv H1; lia.
Qed.

(** Properties of [switch_target] *)

Lemma switch_target_app_2:
  forall n dfl tbl2 tbl1,
  (forall k a, In (k, a) tbl1 -> n <> k) ->
  switch_target n dfl (tbl1 ++ tbl2) = switch_target n dfl tbl2.
Proof.
  induction tbl1; simpl; intros.
- auto.
- destruct a as [k1 a1]. rewrite zeq_false; eauto.
Qed.

Lemma switch_target_outside:
  forall n dfl cases,
  (forall k d, In (k, d) cases -> n <> k) ->
  switch_target n dfl cases = dfl.
Proof.
  intros. rewrite <- (List.app_nil_r cases). apply switch_target_app_2; auto. 
Qed.

Lemma switch_target_app_1:
  forall n dfl tbl2,
  (forall k a, In (k, a) tbl2 -> n <> k) ->
  forall tbl1,
  switch_target n dfl (tbl1 ++ tbl2) = switch_target n dfl tbl1.
Proof.
  induction tbl1; simpl.
- apply switch_target_outside; auto.
- destruct a as (k1, a1). destruct (zeq n k1); auto.
Qed.

Lemma switch_target_sorted:
  forall k a dfl tbl, sorted tbl -> In (k, a) tbl -> switch_target k dfl tbl = a.
Proof.
  induction 1; simpl; intros.
- contradiction.
- destruct H1.
  + inv H1. apply zeq_true.
  + rewrite zeq_false. eauto. apply H0 in H1; lia. 
Qed.

(** Correctness of normalization *)

Lemma map_of_table_charact:
  forall n dfl tbl,
  0 <= n < modulus ->
  match ZMap.find n (map_of_table modulus tbl) with
  | Some a => a
  | None => dfl
  end = switch_target n dfl tbl.
Proof.
  induction tbl as [ | [k1 a1] tbl ]; simpl; intros.
- auto.
- destruct (zle 0 k1 && zlt k1 modulus) eqn:R; destruct (zeq n k1).
  + subst n. rewrite ZMapF.add_eq_o; auto.
  + rewrite ZMapF.add_neq_o; auto. 
  + subst k1. unfold proj_sumbool in R; rewrite zle_true in R by tauto; rewrite zlt_true in R by tauto. discriminate.
  + auto.
Qed.

Lemma map_of_table_wf:
  forall k a tbl, ZMap.MapsTo k a (map_of_table modulus tbl) -> 0 <= k < modulus.
Proof.
  induction tbl as [ | [k1 a1] tbl]; simpl; intros.
- eelim ZMap.empty_1; eauto.
- destruct (zle 0 k1 && zlt k1 modulus) eqn:R; eauto.
  rewrite ZMapF.add_mapsto_iff in H. destruct H as [[P Q] | [P Q]].
  + subst k. InvBooleans. auto.
  + eauto.
Qed.

Lemma normalize_table_wf:
  forall tbl k a, In (k, a) (normalize_table modulus tbl) -> 0 <= k < modulus.
Proof.
  unfold normalize_table; intros.
  apply map_of_table_wf with a tbl. 
  apply ZMap.elements_2. rewrite InA_alt. exists (k, a); split; auto. 
  hnf; auto.
Qed.

Lemma zmap_elements_sorted:
  forall m, sorted (ZMap.elements m).
Proof.
  assert (forall l, Sorted (ZMap.lt_key (elt := nat)) l -> sorted l).
  {
    induction 1.
  - constructor.
  - destruct a as [k a]. inv H0.
    + constructor. constructor. simpl; tauto.
    + destruct b as [k' a']. assert (k < k') by auto. 
      constructor; auto. intros k'' a'' IN. 
      assert (k' <= k'') by (eapply in_sorted_le; eauto). 
      lia.
  }
  intros. apply H. apply ZMap.elements_3. 
Qed.

Lemma normalize_table_sorted:
  forall tbl, sorted (normalize_table modulus tbl).
Proof.
  intros; apply zmap_elements_sorted.
Qed.

Lemma switch_target_elements:
  forall n dfl m,
  switch_target n dfl (ZMap.elements m) = 
  match ZMap.find n m with None => dfl | Some a => a end.
Proof.
  intros. destruct (ZMap.find n m) as [a|] eqn:F.
- apply switch_target_sorted. apply zmap_elements_sorted. 
  exploit ZMap.elements_1. apply ZMap.find_2; eauto. 
  rewrite InA_alt. intros [[k2 a2] [[P Q] R]]. simpl in *; subst; auto.
- apply switch_target_outside. intros. 
  assert (ZMap.find k m = Some d). 
  { apply ZMap.find_1. apply ZMap.elements_2. apply InA_alt.
    exists (k,d); split; auto. reflexivity. }
  congruence.
Qed.

Lemma normalize_table_correct:
  forall n dfl tbl,
  0 <= n < modulus ->
  switch_target n dfl (normalize_table modulus tbl) = switch_target n dfl tbl.
Proof.
  intros. unfold normalize_table. rewrite switch_target_elements. 
  apply map_of_table_charact; auto.
Qed.

(** Correctness of compilation to a jump table. *)

Lemma nth_jump_table:
  forall max n min dfl l,
  sorted l ->
  (forall k d, In (k, d) l -> min <= k <= max) ->
  min <= n <= max ->
  list_nth_z (jump_table dfl max min l) (n - min) = Some (switch_target n dfl l).
Proof.
  intros until l.
  functional induction (jump_table dfl max min l); intros SS R1 R2.
- simpl list_nth_z. destruct (zeq (n - min) 0); auto.
  replace (Z.pred (n - min)) with (n - (min + 1)) by lia.
  apply IHl0. auto. simpl; tauto. lia.
- simpl. inv SS. destruct (zeq (n - min) 0).
+ replace n with min by lia. rewrite zeq_true. auto.
+ rewrite zeq_false by lia.
  replace (Z.pred (n - min)) with (n - (min + 1)) by lia.
  apply IHl0. auto. 
  intros. 
  assert (min <= k <= max) by eauto with coqlib.
  assert (min < k) by eauto.
  lia.
  lia.
- simpl list_nth_z. destruct (zeq (n - min) 0).
+ inv SS. rewrite switch_target_outside; auto.
  intros. 
  replace n with min by lia.
  assert (min <= k <= max) by eauto with coqlib. 
  simpl in H. destruct H. inv H. lia. 
  exploit H3; eauto. lia.
+ replace (Z.pred (n - min)) with (n - (min + 1)) by lia.
  apply IHl0. auto. 
  intros. exploit R1; eauto. intros.
  simpl in H; destruct H.
  inv H. lia.
  inv SS. apply H5 in H. 
  assert (min <= k <= max) by eauto with coqlib.
  lia.
  lia.
- lia.
Qed.

Lemma compile_jumptable_correct:
  forall n dfl tbl min max,
  sorted tbl ->
  (forall k a, In (k, a) tbl -> min <= k <= max) ->
  0 <= min -> min <= max -> max < modulus -> 
  max - min + 1 < Int.modulus ->
  0 <= n < modulus ->
  comptree_match n (compile_jumptable dfl tbl min max) = Some(switch_target n dfl tbl).
Proof.
  intros until max; intros SRT R1 R2 R3 R4 R5 R6.
  unfold compile_jumptable. simpl. 
  set (delta := n - min).
  assert (-modulus < delta < modulus) by (unfold delta; lia).
  destruct (zle 0 delta).
- assert (E: delta mod modulus = delta).
  { apply Zmod_small. lia. }
  rewrite E. 
  destruct (zlt delta (max - min + 1)).
+ assert (F: delta mod Int.modulus = delta).
  { apply Zmod_small. lia. }
  rewrite F. 
  apply nth_jump_table; auto. unfold delta in *; lia. 
+ rewrite switch_target_outside; auto. 
  intros. assert (min <= k <= max) by eauto. unfold delta in *; lia.
- assert (E: delta mod modulus = delta + modulus).
  { apply Zmod_unique with (-1). ring. lia. }
  rewrite E.
  assert (F: delta + modulus >= max - min + 1).
  { unfold delta in *; lia. }
  rewrite zlt_false by auto. rewrite switch_target_outside; auto.
  intros. assert (min <= k <= max) by eauto. unfold delta in *; lia.
Qed.

Lemma compile_jumptable_wf:
  forall dfl tbl min max,
  0 <= min -> min <= max -> max < modulus -> 
  max - min + 1 < Int.modulus -> Int.modulus <= modulus ->
  wf_comptree (compile_jumptable dfl tbl min max).
Proof.
  intros; unfold compile_jumptable. constructor. lia. lia. constructor.
Qed.

(** Correctness of compilation to a decision tree *)

Lemma compile_tree_1_correct:
  forall dfl k1 a1 min max n,
  (forall k a, In (k, a) ((k1, a1) :: nil) -> min <= k <= max) ->
  min <= n <= max ->
  comptree_match n (compile_tree_1 dfl k1 a1 min max) =
  Some (switch_target n dfl ((k1, a1) :: nil)).
Proof.
  unfold compile_tree_1; intros.
  assert (min <= k1 <= max) by eauto with coqlib.
  destruct (zeq max min); simpl.
  replace n with k1 by lia. rewrite zeq_true; auto.
  destruct (zeq n k1); auto.
Qed.

Lemma compile_tree_2_correct:
  forall dfl k1 a1 k2 a2 min max n,
  sorted ((k1, a1) :: (k2, a2) :: nil) ->
  (forall k a, In (k, a) ((k1, a1) :: (k2, a2) :: nil) -> min <= k <= max) ->
  min <= n <= max ->
  comptree_match n (compile_tree_2 dfl k1 a1 k2 a2 min max) =
  Some (switch_target n dfl ((k1, a1) :: (k2, a2) :: nil)).
Proof.
  intros. inv H.
  assert (min <= k1 <= max) by eauto with coqlib.
  assert (min <= k2 <= max) by eauto with coqlib.
  assert (k1 < k2) by eauto with coqlib.
  unfold compile_tree_2; simpl.
  destruct (zeq n k1). auto.
  destruct (zeq (max - min) 1).
  replace n with k2 by lia. rewrite zeq_true; auto.
  simpl. destruct (zeq n k2); auto.
Qed.

Lemma compile_tree_3_correct:
  forall dfl k1 a1 k2 a2 k3 a3 min max n,
  sorted ((k1, a1) :: (k2, a2) :: (k3, a3) :: nil) ->
  (forall k a, In (k, a) ((k1, a1) :: (k2, a2) :: (k3, a3) :: nil) -> min <= k <= max) ->
  min <= n <= max ->
  comptree_match n (compile_tree_3 dfl k1 a1 k2 a2 k3 a3 min max) =
  Some (switch_target n dfl ((k1, a1) :: (k2, a2) :: (k3, a3) :: nil)).
Proof.
  intros. inv H. inv H4.
  assert (min <= k1 <= max) by eauto with coqlib.
  assert (min <= k2 <= max) by eauto with coqlib.
  assert (min <= k3 <= max) by eauto with coqlib.
  assert (k1 < k2) by eauto with coqlib.
  assert (k2 < k3) by eauto with coqlib.
  unfold compile_tree_3; simpl.
  destruct (zeq n k1). auto.
  destruct (zeq n k2). auto.
  destruct (zeq (max - min) 2).
  replace n with k3 by lia. rewrite zeq_true; auto.
  simpl. destruct (zeq n k3); auto.
Qed.

Lemma compile_tree_correct:
  forall n dfl tbl min max,
  sorted tbl ->
  (forall k a, In (k, a) tbl -> min <= k <= max) ->
  min <= n <= max ->
  comptree_match n (compile_tree dfl tbl min max) = Some(switch_target n dfl tbl).
Proof.
  intros until max. functional induction (compile_tree dfl tbl min max); intros SS R1 R2.
- (* empty *)
  simpl. auto.
- (* one case *)
  apply compile_tree_1_correct; auto.
- (* two cases *)
  apply compile_tree_2_correct; auto.
- (* three cases *)
  apply compile_tree_3_correct; auto.
- (* N cases *)
  set (pivot := first_key tbl2) in *.
  assert (TBL2: tbl2 <> nil).
  { destruct tbl as [ | [k1 a1] tbl]; try contradiction.
    destruct tbl as [ | [k2 a2] tbl]; try contradiction.
    destruct (split_in_half_length' (k1,a1) (k2,a2) tbl) as [P Q].
    rewrite e0 in Q. destruct tbl2; simpl in Q. lia. congruence. }
  assert (A: exists apivot tbl3, tbl2 = (pivot, apivot) :: tbl3).
  { destruct tbl2 as [ | [k a] tbl3]. congruence. unfold pivot; simpl. exists a, tbl3; auto. }
  destruct A as (apivot & tbl3 & EQ2).   
  clear y.
  generalize (split_in_half_eq tbl). rewrite e0; simpl. intros EQ.
  destruct (sorted_app_inv tbl1 tbl2) as (SS1 & SS2 & SEP).
  rewrite EQ; auto.
  assert (R11: forall k a, In (k, a) tbl1 -> min <= k <= pivot - 1).
  { intros. 
    assert (min <= k <= max).
    { apply R1 with a. rewrite <- EQ. apply in_or_app; auto. }
    assert (k < pivot).
    { eapply SEP. eauto. rewrite EQ2; eauto with coqlib. }
    lia. }
  assert (R12: forall k a, In (k, a) tbl2 -> pivot <= k <= max).
  { intros. 
    assert (min <= k <= max).
    { apply R1 with a. rewrite <- EQ. apply in_or_app; auto. }
    assert (pivot <= k).
    { eapply in_sorted_le. rewrite EQ2 in SS2. eexact SS2. rewrite <- EQ2. eexact H. }
    lia. }
  simpl. destruct (zlt n pivot).
  + assert (min <= n <= pivot - 1) by lia. rewrite IHc by eauto.
    f_equal. symmetry; rewrite <- EQ. apply switch_target_app_1. 
    intros. apply R12 in H0. lia.
  + assert (pivot <= n <= max) by lia. rewrite IHc0 by eauto.
    f_equal. symmetry; rewrite <- EQ. apply switch_target_app_2.
    intros. apply R11 in H0. lia.
Qed.

Lemma compile_tree_wf:
  forall dfl tbl min max,
  (forall k a, In (k, a) tbl -> 0 <= k < modulus) ->
  wf_comptree (compile_tree dfl tbl min max).
Proof.
  intros until max.  functional induction (compile_tree dfl tbl min max); intros R.
- constructor.
- unfold compile_tree_1. destruct (zeq max min); eauto using wf_comptree with coqlib.
- unfold compile_tree_2. constructor. eauto with coqlib.
  destruct (zeq (max - min) 1); eauto using wf_comptree with coqlib.
- unfold compile_tree_3. constructor. eauto with coqlib.
  constructor. eauto with coqlib.
  destruct (zeq (max - min) 2); eauto using wf_comptree with coqlib.
- clear y. generalize (split_in_half_eq tbl). rewrite e0; simpl. intros EQ.
  constructor.
  destruct tbl2 as [ | [key2 act2] tbl2 ]; simpl. lia.
  apply R with act2. rewrite <- EQ; apply in_or_app; auto with coqlib.
  apply IHc. intros; eapply R; rewrite <- EQ; apply in_or_app; eauto.
  apply IHc0. intros; eapply R; rewrite <- EQ; apply in_or_app; eauto.
Qed.

(** Final results *)

Theorem compile_switch_correct:
  forall dfl tbl n,
  0 <= n < modulus ->
  comptree_match n (compile_switch modulus dfl tbl) = Some(switch_target n dfl tbl).
Proof.
  intros until n. intros RANGE. unfold compile_switch.
  set (tbl1 := normalize_table modulus tbl).
  assert (SRT: sorted tbl1) by (apply normalize_table_sorted).
  assert (R1: forall k a, In (k, a) tbl1 -> 0 <= k < modulus) by (apply normalize_table_wf).
  rewrite <- normalize_table_correct by auto. fold tbl1.
  destruct tbl1 as [ | [kmin amin] l ].
- (* empty table *)
  reflexivity.
- (* nonempty table *)
  clear tbl. set (tbl := (kmin, amin) :: l) in *.
  assert (E: tbl = removelast tbl ++ last tbl (kmin, amin) :: nil).
  { apply app_removelast_last. unfold tbl; congruence. }
  destruct (last tbl (kmin, amin)) as [kmax amax].
  assert (R2: forall k a, In (k, a) tbl -> kmin <= k <= kmax).
  { intros; split. 
    eapply in_sorted_le; eassumption.
    eapply in_sorted_ge. rewrite E in SRT; eauto. rewrite E in H; eauto. }
  destruct (dense_enough (list_length_z tbl) (kmax - kmin + 1)) eqn:D.
+ apply compile_jumptable_correct; auto. 
  eapply R1. unfold tbl; eauto with coqlib. 
  eapply R2. unfold tbl; eauto with coqlib. 
  eapply R1. rewrite E. apply in_or_app. eauto with coqlib.
  unfold dense_enough in D. InvBooleans. auto. 
+ apply compile_tree_correct; auto.
  intros. exploit R1; eauto. lia. 
  lia.
Qed.

Theorem compile_switch_wf:
  forall dfl tbl, 
  Int.modulus <= modulus ->
  wf_comptree (compile_switch modulus dfl tbl).
Proof.
  intros until tbl; intros MOD. unfold compile_switch.
  set (tbl1 := normalize_table modulus tbl).
  assert (SRT: sorted tbl1) by (apply normalize_table_sorted).
  assert (R1: forall k a, In (k, a) tbl1 -> 0 <= k < modulus) by (apply normalize_table_wf).
  destruct tbl1 as [ | [kmin amin] l ].
- (* empty table *)
  constructor.
- (* nonempty table *)
  clear tbl. set (tbl := (kmin, amin) :: l) in *.
  assert (E: tbl = removelast tbl ++ last tbl (kmin, amin) :: nil).
  { apply app_removelast_last. unfold tbl; congruence. }
  destruct (last tbl (kmin, amin)) as [kmax amax].
  assert (R2: forall k a, In (k, a) tbl -> kmin <= k <= kmax).
  { intros; split.
    eapply in_sorted_le; eassumption.
    eapply in_sorted_ge. rewrite E in SRT; eauto. rewrite E in H; eauto. }
  destruct (dense_enough (list_length_z tbl) (kmax - kmin + 1)) eqn:D.
+ apply compile_jumptable_wf; auto.
  eapply R1. unfold tbl; eauto with coqlib. 
  eapply R2. unfold tbl; eauto with coqlib. 
  eapply R1. rewrite E. apply in_or_app. eauto with coqlib.
  unfold dense_enough in D. InvBooleans. auto. 
+ apply compile_tree_wf; auto.
Qed.

End COMPTREE.

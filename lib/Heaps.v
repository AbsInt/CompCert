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

(** A heap data structure. *)

(** The implementation uses splay heaps, following C. Okasaki,
    "Purely functional data structures", section 5.4.
    One difference: we eliminate duplicate elements.
    (If an element is already in a heap, inserting it again does nothing.)
*)

Require Import Coqlib.
Require Import FSets.
Require Import Ordered.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module SplayHeapSet(E: OrderedType).

(** "Raw" implementation.  The "is a binary search tree" invariant
    is proved separately. *)

Module R.

Inductive heap: Type :=
  | Empty
  | Node (l: heap) (x: E.t) (r: heap).

Fixpoint partition (pivot: E.t) (h: heap) { struct h } : heap * heap :=
  match h with
  | Empty => (Empty, Empty)
  | Node a x b =>
      match E.compare x pivot with
      | EQ _ => (a, b)
      | LT _ =>
        match b with
        | Empty => (h, Empty)
        | Node b1 y b2 =>
            match E.compare y pivot with
            | EQ _ => (Node a x b1, b2)
            | LT _ =>
              let (small, big) := partition pivot b2
              in (Node (Node a x b1) y small, big)
            | GT _ =>
              let (small, big) := partition pivot b1
              in (Node a x small, Node big y b2)
            end
        end
     | GT _ =>
        match a with
        | Empty => (Empty, h)
        | Node a1 y a2 =>
            match E.compare y pivot with
            | EQ _ => (a1, Node a2 x b)
            | LT _ =>
              let (small, big) := partition pivot a2
              in (Node a1 y small, Node big x b)
            | GT _ =>
              let (small, big) := partition pivot a1
              in (small, Node big y (Node a2 x b))
            end
        end
    end
  end.

Definition insert (x: E.t) (h: heap) : heap :=
  let (a, b) := partition x h in Node a x b.

Fixpoint findMin (h: heap) : option E.t :=
  match h with
  | Empty => None
  | Node Empty x b => Some x
  | Node a x b => findMin a
  end.

Fixpoint deleteMin (h: heap) : heap :=
  match h with
  | Empty => Empty
  | Node Empty x b => b
  | Node (Node Empty x b) y c => Node b y c
  | Node (Node a x b) y c => Node (deleteMin a) x (Node b y c)
  end.

Fixpoint findMax (h: heap) : option E.t :=
  match h with
  | Empty => None
  | Node a x Empty => Some x
  | Node a x b => findMax b
  end.

Fixpoint deleteMax (h: heap) : heap :=
  match h with
  | Empty => Empty
  | Node b x Empty => b
  | Node b x (Node c y Empty) => Node b x c
  | Node a x (Node b y c) => Node (Node a x b) y (deleteMax c)
  end.

(** Induction principles for some of the operators. *)

Scheme heap_ind := Induction for heap Sort Prop.
Functional Scheme partition_ind := Induction for partition Sort Prop.
Functional Scheme deleteMin_ind := Induction for deleteMin Sort Prop.
Functional Scheme deleteMax_ind := Induction for deleteMax Sort Prop.

(** Specification *)

Fixpoint In (x: E.t) (h: heap) : Prop :=
  match h with
  | Empty => False
  | Node a y b => In x a \/ E.eq x y \/ In x b
  end.

(** Invariants *)

Fixpoint lt_heap (h: heap) (x: E.t) : Prop :=
  match h with
  | Empty => True
  | Node a y b => lt_heap a x /\ E.lt y x /\ lt_heap b x
  end.

Fixpoint gt_heap (h: heap) (x: E.t) : Prop :=
  match h with
  | Empty => True
  | Node a y b => gt_heap a x /\ E.lt x y /\ gt_heap b x
  end.

Fixpoint bst (h: heap) : Prop :=
  match h with
  | Empty => True
  | Node a x b => bst a /\ bst b /\ lt_heap a x /\ gt_heap b x
  end.

Definition le (x y: E.t) := E.eq x y \/ E.lt x y.

Lemma le_lt_trans:
  forall x1 x2 x3, le x1 x2 -> E.lt x2 x3 -> E.lt x1 x3.
Proof.
  unfold le; intros; intuition.
  destruct (E.compare x1 x3).
    auto. 
    elim (@E.lt_not_eq x2 x3). auto. apply E.eq_trans with x1. apply E.eq_sym; auto. auto.
    elim (@E.lt_not_eq x2 x1). eapply E.lt_trans; eauto. apply E.eq_sym; auto.
    eapply E.lt_trans; eauto.
Qed.

Lemma lt_le_trans:
  forall x1 x2 x3, E.lt x1 x2 -> le x2 x3 -> E.lt x1 x3.
Proof.
  unfold le; intros; intuition.
  destruct (E.compare x1 x3).
    auto. 
    elim (@E.lt_not_eq x1 x2). auto. apply E.eq_trans with x3. auto. apply E.eq_sym; auto.
    elim (@E.lt_not_eq x3 x2). eapply E.lt_trans; eauto. apply E.eq_sym; auto.
    eapply E.lt_trans; eauto.
Qed.

Lemma le_trans:
  forall x1 x2 x3, le x1 x2 -> le x2 x3 -> le x1 x3.
Proof.
  intros. destruct H. destruct H0. red; left; eapply E.eq_trans; eauto. 
  red. right. eapply le_lt_trans; eauto. red; auto.
  red. right. eapply lt_le_trans; eauto.
Qed.

Lemma lt_heap_trans:
  forall x y, le x y ->
  forall h, lt_heap h x -> lt_heap h y.
Proof.
  induction h; simpl; intros. 
  auto.
  intuition. eapply lt_le_trans; eauto.
Qed.

Lemma gt_heap_trans:
  forall x y, le y x ->
  forall h, gt_heap h x -> gt_heap h y.
Proof.
  induction h; simpl; intros. 
  auto.
  intuition. eapply le_lt_trans; eauto.
Qed.

(** Properties of [partition] *)

Lemma In_partition:
  forall x pivot, ~E.eq x pivot ->
  forall h, bst h -> (In x h <-> In x (fst (partition pivot h)) \/ In x (snd (partition pivot h))).
Proof.
  intros x pivot NEQ h0. functional induction (partition pivot h0); simpl; intros.
- tauto.
- tauto.
- rewrite e3 in *; simpl in *; intuition.
- intuition. elim NEQ. eapply E.eq_trans; eauto. 
- rewrite e3 in *; simpl in *; intuition.
- intuition. elim NEQ. eapply E.eq_trans; eauto. 
- intuition. 
- rewrite e3 in *; simpl in *; intuition.
- intuition. elim NEQ. eapply E.eq_trans; eauto. 
- rewrite e3 in *; simpl in *; intuition.
Qed.

Lemma partition_lt:
  forall x pivot h,
  lt_heap h x -> lt_heap (fst (partition pivot h)) x /\ lt_heap (snd (partition pivot h)) x.
Proof.
  intros x pivot h0. functional induction (partition pivot h0); simpl; try tauto.
- rewrite e3 in *; simpl in *; tauto.
- rewrite e3 in *; simpl in *; tauto.
- rewrite e3 in *; simpl in *; tauto.
- rewrite e3 in *; simpl in *; tauto.
Qed.
 
Lemma partition_gt:
  forall x pivot h,
  gt_heap h x -> gt_heap (fst (partition pivot h)) x /\ gt_heap (snd (partition pivot h)) x.
Proof.
  intros x pivot h0. functional induction (partition pivot h0); simpl; try tauto.
- rewrite e3 in *; simpl in *; tauto.
- rewrite e3 in *; simpl in *; tauto.
- rewrite e3 in *; simpl in *; tauto.
- rewrite e3 in *; simpl in *; tauto.
Qed.

Lemma partition_split:
  forall pivot h,
  bst h -> lt_heap (fst (partition pivot h)) pivot /\ gt_heap (snd (partition pivot h)) pivot.
Proof.
  intros pivot h0. functional induction (partition pivot h0); simpl.
- tauto.
- intuition. eapply lt_heap_trans; eauto. red; auto.
- rewrite e3 in *; simpl in *. intuition.
  eapply lt_heap_trans; eauto. red; auto.
  eapply lt_heap_trans; eauto. red; auto.
- intuition.
  eapply lt_heap_trans; eauto. red; auto.
  eapply lt_heap_trans; eauto. red; auto.
  eapply gt_heap_trans with y; eauto. red. left. apply E.eq_sym; auto. 
- rewrite e3 in *; simpl in *; intuition.
  eapply lt_heap_trans; eauto. red; auto.
  eapply gt_heap_trans with y; eauto. red; auto.
- intuition. 
  eapply lt_heap_trans; eauto. red; auto.
  eapply gt_heap_trans; eauto. red; auto.
- intuition. eapply gt_heap_trans; eauto. red; auto. 
- rewrite e3 in *; simpl in *. intuition.
  eapply lt_heap_trans with y; eauto. red; auto.
  eapply gt_heap_trans; eauto. red; auto.
- intuition. 
  eapply lt_heap_trans with y; eauto. red; auto.
  eapply gt_heap_trans; eauto. red; auto.
  eapply gt_heap_trans with x; eauto. red; auto.
- rewrite e3 in *; simpl in *; intuition.
  eapply gt_heap_trans; eauto. red; auto.
  eapply gt_heap_trans; eauto. red; auto.
Qed.

Lemma partition_bst:
  forall pivot h,
  bst h ->
  bst (fst (partition pivot h)) /\ bst (snd (partition pivot h)).
Proof.
  intros pivot h0. functional induction (partition pivot h0); simpl; try tauto.
- rewrite e3 in *; simpl in *. intuition. 
    apply lt_heap_trans with x; auto. red; auto.
    generalize (partition_gt y pivot b2 H7). rewrite e3; simpl. tauto.
- rewrite e3 in *; simpl in *. intuition. 
    generalize (partition_gt x pivot b1 H3). rewrite e3; simpl. tauto.
    generalize (partition_lt y pivot b1 H4). rewrite e3; simpl. tauto.
- rewrite e3 in *; simpl in *. intuition.
    generalize (partition_gt y pivot a2 H6). rewrite e3; simpl. tauto.
    generalize (partition_lt x pivot a2 H8). rewrite e3; simpl. tauto.
- rewrite e3 in *; simpl in *. intuition. 
    generalize (partition_lt y pivot a1 H3). rewrite e3; simpl. tauto.
    apply gt_heap_trans with x; auto. red; auto.
Qed.

(** Properties of [insert] *)

Lemma insert_bst:
  forall x h, bst h -> bst (insert x h).
Proof.
  intros. 
  unfold insert. case_eq (partition x h). intros a b EQ; simpl. 
  generalize (partition_bst x h H).
  generalize (partition_split x h H).
  rewrite EQ; simpl. tauto.
Qed.

Lemma In_insert:
  forall x h y, bst h -> (In y (insert x h) <-> E.eq y x \/ In y h).
Proof.
  intros. unfold insert.
  case_eq (partition x h). intros a b EQ; simpl. 
  assert (E.eq y x \/ ~E.eq y x).
    destruct (E.compare y x); auto.
    right; red; intros. elim (E.lt_not_eq l). apply E.eq_sym; auto.
  destruct H0.
  tauto.
  generalize (In_partition y x H0 h H). rewrite EQ; simpl. tauto. 
Qed.

(** Properties of [findMin] and [deleteMin] *)

Lemma deleteMin_lt:
  forall x h, lt_heap h x -> lt_heap (deleteMin h) x.
Proof.
Opaque deleteMin.
  intros x h0. functional induction (deleteMin h0) ; simpl; intros.
  auto.
  tauto.
  tauto.
  intuition. apply IHh. simpl. tauto.  
Qed.

Lemma deleteMin_bst:
  forall h, bst h -> bst (deleteMin h).
Proof.
  intros h0. functional induction (deleteMin h0); simpl; intros.
  auto.
  tauto.
  tauto.
  intuition.
  apply IHh. simpl; auto.
  apply deleteMin_lt; auto. simpl; auto.  
  apply gt_heap_trans with y; auto. red; auto. 
Qed.

Lemma In_deleteMin:
  forall y x h,
  findMin h = Some x ->
  (In y h <-> E.eq y x \/ In y (deleteMin h)).
Proof.
Transparent deleteMin.
  intros y x h0. functional induction (deleteMin h0); simpl; intros.
  discriminate. 
  inv H. tauto.
  inv H. tauto. 
  destruct _x. inv H. simpl. tauto. generalize (IHh H). simpl. tauto.
Qed.

Lemma gt_heap_In:
  forall x y h, gt_heap h x -> In y h -> E.lt x y.
Proof.
  induction h; simpl; intros. 
  contradiction.
  intuition. apply lt_le_trans with x0; auto. red. left. apply E.eq_sym; auto.
Qed.

Lemma findMin_min:
  forall x h, findMin h = Some x -> bst h -> forall y, In y h -> le x y.
Proof.
  induction h; simpl; intros.
  contradiction.
  destruct h1.
  inv H. simpl in *. intuition.
  red; left; apply E.eq_sym; auto.
  red; right. eapply gt_heap_In; eauto.
  assert (le x x1).
    apply IHh1; auto. tauto. simpl. right; left; apply E.eq_refl.
  intuition.
  apply le_trans with x1. auto.  apply le_trans with x0. simpl in H4. red; tauto. 
  red; left; apply E.eq_sym; auto.
  apply le_trans with x1. auto. apply le_trans with x0. simpl in H4. red; tauto.
  red; right. eapply gt_heap_In; eauto.
Qed.

Lemma findMin_empty:
  forall h, h <> Empty -> findMin h <> None.
Proof.
  induction h; simpl; intros.
  congruence.
  destruct h1. congruence. apply IHh1. congruence.
Qed.

(** Properties of [findMax] and [deleteMax]. *)

Lemma deleteMax_gt:
  forall x h, gt_heap h x -> gt_heap (deleteMax h) x.
Proof.
Opaque deleteMax.
  intros x h0. functional induction (deleteMax h0); simpl; intros.
  auto.
  tauto.
  tauto. 
  intuition. apply IHh. simpl. tauto.  
Qed.

Lemma deleteMax_bst:
  forall h, bst h -> bst (deleteMax h).
Proof.
  intros h0. functional induction (deleteMax h0); simpl; intros.
  auto.
  tauto.
  tauto.
  intuition.
    apply IHh. simpl; auto.
    apply lt_heap_trans with x; auto. red; auto.
    apply deleteMax_gt; auto. simpl; auto. 
Qed.

Lemma In_deleteMax:
  forall y x h,
  findMax h = Some x ->
  (In y h <-> E.eq y x \/ In y (deleteMax h)).
Proof.
Transparent deleteMax.
  intros y x h0. functional induction (deleteMax h0); simpl; intros.
  congruence.
  inv H. tauto.
  inv H. tauto. 
  destruct _x1. inv H. simpl. tauto. generalize (IHh H). simpl. tauto.
Qed.

Lemma lt_heap_In:
  forall x y h, lt_heap h x -> In y h -> E.lt y x.
Proof.
  induction h; simpl; intros. 
  contradiction.
  intuition. apply le_lt_trans with x0; auto. red. left. apply E.eq_sym; auto.
Qed.

Lemma findMax_max:
  forall x h, findMax h = Some x -> bst h -> forall y, In y h -> le y x.
Proof.
  induction h; simpl; intros.
  contradiction.
  destruct h2.
  inv H. simpl in *. intuition.
  red; right. eapply lt_heap_In; eauto.
  red; left. auto.
  assert (le x1 x).
    apply IHh2; auto. tauto. simpl. right; left; apply E.eq_refl.
  intuition.
  apply le_trans with x1; auto.  apply le_trans with x0.
  red; right. eapply lt_heap_In; eauto.
  simpl in H6. red; tauto. 
  apply le_trans with x1; auto. apply le_trans with x0.
  red; auto.
  simpl in H6. red; tauto.
Qed.

Lemma findMax_empty:
  forall h, h <> Empty -> findMax h <> None.
Proof.
  induction h; simpl; intros.
  congruence.
  destruct h2. congruence. apply IHh2. congruence.
Qed.

End R.

(** Wrapping in a dependent type *)

Definition t := { h: R.heap | R.bst h }.

(** Operations *)

Program Definition empty : t := R.Empty.

Program Definition insert (x: E.t) (h: t) : t := R.insert x h.
Next Obligation. apply R.insert_bst. apply proj2_sig. Qed.

Program Definition findMin (h: t) : option E.t := R.findMin h.

Program Definition deleteMin (h: t) : t := R.deleteMin h.
Next Obligation. apply R.deleteMin_bst. apply proj2_sig. Qed.

Program Definition findMax (h: t) : option E.t := R.findMax h.

Program Definition deleteMax (h: t) : t := R.deleteMax h.
Next Obligation. apply R.deleteMax_bst. apply proj2_sig. Qed.

(** Membership (for specification) *)

Program Definition In (x: E.t) (h: t) : Prop := R.In x h.

(** Properties of [empty] *)

Lemma In_empty: forall x, ~In x empty.
Proof.
  intros; red; intros.
  red in H. simpl in H. tauto.
Qed.

(** Properties of [insert] *)

Lemma In_insert:
  forall x h y,
  In y (insert x h) <-> E.eq y x \/ In y h.
Proof.
  intros. unfold In, insert; simpl. apply R.In_insert. apply proj2_sig.
Qed.

(** Properties of [findMin] *)

Lemma findMin_empty:
  forall h y, findMin h = None -> ~In y h.
Proof.
  unfold findMin, In; intros; simpl. 
  destruct (proj1_sig h). 
  simpl. tauto.
  exploit R.findMin_empty; eauto. congruence.
Qed.

Lemma findMin_min:
  forall h x y, findMin h = Some x -> In y h -> E.eq x y \/ E.lt x y.
Proof.
  unfold findMin, In; simpl. intros.
  change (R.le x y). eapply R.findMin_min; eauto. apply proj2_sig.
Qed.

(** Properties of [deleteMin]. *)

Lemma In_deleteMin:
  forall h x y,
  findMin h = Some x ->
  (In y h <-> E.eq y x \/ In y (deleteMin h)).
Proof.
  unfold findMin, In; simpl; intros.
  apply R.In_deleteMin. auto.
Qed.

(** Properties of [findMax] *)

Lemma findMax_empty:
  forall h y, findMax h = None -> ~In y h.
Proof.
  unfold findMax, In; intros; simpl. 
  destruct (proj1_sig h). 
  simpl. tauto.
  exploit R.findMax_empty; eauto. congruence.
Qed.

Lemma findMax_max:
  forall h x y, findMax h = Some x -> In y h -> E.eq y x \/ E.lt y x.
Proof.
  unfold findMax, In; simpl. intros.
  change (R.le y x). eapply R.findMax_max; eauto. apply proj2_sig.
Qed.

(** Properties of [deleteMax]. *)

Lemma In_deleteMax:
  forall h x y,
  findMax h = Some x ->
  (In y h <-> E.eq y x \/ In y (deleteMax h)).
Proof.
  unfold findMax, In; simpl; intros.
  apply R.In_deleteMax. auto.
Qed.

End SplayHeapSet.

(** Instantiation over type [positive] *)

Module PHeap := SplayHeapSet(OrderedPositive).



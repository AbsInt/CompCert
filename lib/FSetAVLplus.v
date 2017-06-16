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

(** An extension of [FSetAVL] (finite sets as balanced binary search trees)
  with extra interval-based operations, more efficient than standard
  operations. *)

Require Import FSetInterface.
Require FSetAVL.
Require Import Coqlib.

Module Make(X: OrderedType).

Include FSetAVL.Make(X).

Module Raw := MSet.Raw.

Section MEM_BETWEEN.

(** [mem_between above below s] is [true] iff there exists an element of [s]
  that belongs to the interval described by the predicates [above] and [below].
  Using the monotonicity of [above] and [below], the implementation of
  [mem_between] avoids traversing the subtrees of [s] that
  lie entirely outside the interval of interest. *)

Variable above_low_bound: elt -> bool.
Variable below_high_bound: elt -> bool.

Fixpoint raw_mem_between (m: Raw.tree) : bool :=
  match m with
  | Raw.Leaf => false
  | Raw.Node _ l x r =>
      if above_low_bound x
      then if below_high_bound x
           then true
           else raw_mem_between l
      else raw_mem_between r
  end.

Definition mem_between (m: t) : bool := raw_mem_between m.(MSet.this).

Hypothesis above_monotone:
  forall x1 x2, X.eq x1 x2 \/ X.lt x1 x2 -> above_low_bound x1 = true -> above_low_bound x2 = true.
Hypothesis below_monotone:
  forall x1 x2, X.eq x1 x2 \/ X.lt x2 x1 -> below_high_bound x1 = true -> below_high_bound x2 = true.

Lemma raw_mem_between_1:
  forall m,
  raw_mem_between m = true ->
  exists x, Raw.In x m /\ above_low_bound x = true /\ below_high_bound x = true.
Proof.
  induction m; simpl; intros.
- discriminate.
- destruct (above_low_bound t1) eqn: LB; [destruct (below_high_bound t1) eqn: HB | idtac].
  + (* in interval *)
    exists t1; split; auto.  apply Raw.IsRoot. auto.
  + (* above interval *)
    exploit IHm1; auto. intros [x' [A B]]. exists x'; split; auto. apply Raw.InLeft; auto.
  + (* below interval *)
    exploit IHm2; auto. intros [x' [A B]]. exists x'; split; auto. apply Raw.InRight; auto.
Qed.

Lemma raw_mem_between_2:
  forall x m,
  Raw.bst m ->
  Raw.In x m -> above_low_bound x = true -> below_high_bound x = true ->
  raw_mem_between m = true.
Proof.
  induction 1; simpl; intros.
- inv H.
- rewrite Raw.In_node_iff in H1.
  destruct (above_low_bound x0) eqn: LB; [destruct (below_high_bound x0) eqn: HB | idtac].
  + (* in interval *)
    auto.
  + (* above interval *)
    assert (X.eq x x0 \/ X.lt x0 x -> False).
    { intros. exploit below_monotone; eauto. congruence. }
    intuition.
  + assert (X.eq x x0 \/ X.lt x x0 -> False).
    { intros. exploit above_monotone; eauto. congruence. }
    intuition.
Qed.

Theorem mem_between_1:
  forall s,
  mem_between s = true ->
  exists x, In x s /\ above_low_bound x = true /\ below_high_bound x = true.
Proof.
  intros. apply raw_mem_between_1. auto.
Qed.

Theorem mem_between_2:
  forall x s,
  In x s -> above_low_bound x = true -> below_high_bound x = true ->
  mem_between s = true.
Proof.
  unfold mem_between; intros. apply raw_mem_between_2 with x; auto. apply MSet.is_ok.
Qed.

End MEM_BETWEEN.

Section ELEMENTS_BETWEEN.

(** [elements_between above below s] returns the set of elements of [s]
  that belong to the interval [above,below]. *)

Variable above_low_bound: elt -> bool.
Variable below_high_bound: elt -> bool.

Fixpoint raw_elements_between (m: Raw.tree) : Raw.tree :=
  match m with
  | Raw.Leaf => Raw.Leaf
  | Raw.Node _ l x r =>
      if above_low_bound x then
        if below_high_bound x then
          Raw.join (raw_elements_between l) x (raw_elements_between r)
        else
          raw_elements_between l
      else
        raw_elements_between r
  end.

Remark In_raw_elements_between_1:
  forall x m,
  Raw.In x (raw_elements_between m) -> Raw.In x m.
Proof.
  induction m; simpl; intros.
- inv H.
- rewrite Raw.In_node_iff.
  destruct (above_low_bound t1) eqn:LB; [destruct (below_high_bound t1) eqn: RB | idtac]; simpl in H.
  + rewrite Raw.join_spec in H. intuition.
  + left; apply IHm1; auto.
  + right; right; apply IHm2; auto.
Qed.

Lemma raw_elements_between_ok:
  forall m, Raw.bst m -> Raw.bst (raw_elements_between m).
Proof.
  induction 1; simpl.
- constructor.
- destruct (above_low_bound x) eqn:LB; [destruct (below_high_bound x) eqn: RB | idtac]; simpl.
  + apply Raw.join_ok; auto.
    red; intros. apply l0. apply In_raw_elements_between_1; auto.
    red; intros. apply g. apply In_raw_elements_between_1; auto.
  + auto.
  + auto.
Qed.

Definition elements_between (s: t) : t :=
  @MSet.Mkt (raw_elements_between s.(MSet.this)) (raw_elements_between_ok s.(MSet.this) s.(MSet.is_ok)).

Hypothesis above_monotone:
  forall x1 x2, X.eq x1 x2 \/ X.lt x1 x2 -> above_low_bound x1 = true -> above_low_bound x2 = true.
Hypothesis below_monotone:
  forall x1 x2, X.eq x1 x2 \/ X.lt x2 x1 -> below_high_bound x1 = true -> below_high_bound x2 = true.

Remark In_raw_elements_between_2:
  forall x m,
  Raw.In x (raw_elements_between m) -> above_low_bound x = true /\ below_high_bound x = true.
Proof.
  induction m; simpl; intros.
- inv H.
- destruct (above_low_bound t1) eqn:LB; [destruct (below_high_bound t1) eqn: RB | idtac]; simpl in H.
  + rewrite Raw.join_spec in H. intuition.
    apply above_monotone with t1; auto.
    apply below_monotone with t1; auto.
  + auto.
  + auto.
Qed.

Remark In_raw_elements_between_3:
  forall x m,
  Raw.bst m ->
  Raw.In x m -> above_low_bound x = true -> below_high_bound x = true ->
  Raw.In x (raw_elements_between m).
Proof.
  induction 1; simpl; intros.
- auto.
- rewrite Raw.In_node_iff in H1.
  destruct (above_low_bound x0) eqn:LB; [destruct (below_high_bound x0) eqn: RB | idtac].
  + rewrite Raw.join_spec. intuition.
  + assert (X.eq x x0 \/ X.lt x0 x -> False).
    { intros. exploit below_monotone; eauto. congruence. }
    intuition. elim H7. apply g. auto.
  + assert (X.eq x x0 \/ X.lt x x0 -> False).
    { intros. exploit above_monotone; eauto. congruence. }
    intuition. elim H7. apply l0. auto.
Qed.

Theorem elements_between_iff:
  forall x s,
  In x (elements_between s) <-> In x s /\ above_low_bound x = true /\ below_high_bound x = true.
Proof.
  intros. unfold elements_between, In; simpl. split.
  intros. split. apply In_raw_elements_between_1; auto. eapply In_raw_elements_between_2; eauto.
  intros [A [B C]]. apply In_raw_elements_between_3; auto. apply MSet.is_ok.
Qed.

End ELEMENTS_BETWEEN.

Section FOR_ALL_BETWEEN.

(** [for_all_between pred above below s] is [true] iff all elements of [s]
  in a given variation interval satisfy predicate [pred].
  The variation interval is given by two predicates [above] and [below]
  which must both hold if the element is part of the interval.
  Using the monotonicity of [above] and [below], the implementation of
  [for_all_between] avoids traversing the subtrees of [s] that
  lie entirely outside the interval of interest. *)

Variable pred: elt -> bool.
Variable above_low_bound: elt -> bool.
Variable below_high_bound: elt -> bool.

Fixpoint raw_for_all_between (m: Raw.tree) : bool :=
  match m with
  | Raw.Leaf => true
  | Raw.Node _ l x r =>
      if above_low_bound x
      then if below_high_bound x
           then raw_for_all_between l && pred x && raw_for_all_between r
           else raw_for_all_between l
      else raw_for_all_between r
  end.

Definition for_all_between (m: t) : bool := raw_for_all_between m.(MSet.this).

Hypothesis pred_compat:
  forall x1 x2, X.eq x1 x2 -> pred x1 = pred x2.
Hypothesis above_monotone:
  forall x1 x2, X.eq x1 x2 \/ X.lt x1 x2 -> above_low_bound x1 = true -> above_low_bound x2 = true.
Hypothesis below_monotone:
  forall x1 x2, X.eq x1 x2 \/ X.lt x2 x1 -> below_high_bound x1 = true -> below_high_bound x2 = true.

Lemma raw_for_all_between_1:
  forall x m,
  Raw.bst m ->
  raw_for_all_between m = true ->
  Raw.In x m ->
  above_low_bound x = true ->
  below_high_bound x = true ->
  pred x = true.
Proof.
  induction 1; simpl; intros.
- inv H0.
- destruct (above_low_bound x0) eqn: LB; [destruct (below_high_bound x0) eqn: HB | idtac].
  + (* in interval *)
    destruct (andb_prop _ _ H1) as [P C]. destruct (andb_prop _ _ P) as [A B]. clear H1 P.
    inv H2.
    * erewrite pred_compat; eauto.
    * apply IHbst1; auto.
    * apply IHbst2; auto.
  + (* above interval *)
    inv H2.
    * assert (below_high_bound x0 = true) by (apply below_monotone with x; auto).
      congruence.
    * apply IHbst1; auto.
    * assert (below_high_bound x0 = true) by (apply below_monotone with x; auto).
      congruence.
  + (* below interval *)
    inv H2.
    * assert (above_low_bound x0 = true) by (apply above_monotone with x; auto).
      congruence.
    * assert (above_low_bound x0 = true) by (apply above_monotone with x; auto).
      congruence.
    * apply IHbst2; auto.
Qed.

Lemma raw_for_all_between_2:
  forall m,
  Raw.bst m ->
  (forall x, Raw.In x m -> above_low_bound x = true -> below_high_bound x = true -> pred x = true) ->
  raw_for_all_between m = true.
Proof.
  induction 1; intros; simpl.
- auto.
- destruct (above_low_bound x) eqn: LB; [destruct (below_high_bound x) eqn: HB | idtac].
  + (* in interval *)
    rewrite IHbst1. rewrite (H1 x). rewrite IHbst2. auto.
    intros. apply H1; auto. apply Raw.InRight; auto.
    apply Raw.IsRoot. reflexivity. auto. auto.
    intros. apply H1; auto. apply Raw.InLeft; auto.
  + (* above interval *)
    apply IHbst1. intros. apply H1; auto. apply Raw.InLeft; auto.
  + (* below interval *)
    apply IHbst2. intros. apply H1; auto. apply Raw.InRight; auto.
Qed.

Theorem for_all_between_iff:
  forall s,
  for_all_between s = true <-> (forall x, In x s -> above_low_bound x = true -> below_high_bound x = true -> pred x = true).
Proof.
  unfold for_all_between; intros; split; intros.
- eapply raw_for_all_between_1; eauto. apply MSet.is_ok.
- apply raw_for_all_between_2; auto. apply MSet.is_ok.
Qed.

End FOR_ALL_BETWEEN.

Section PARTITION_BETWEEN.

Variable above_low_bound: elt -> bool.
Variable below_high_bound: elt -> bool.

Fixpoint raw_partition_between (m: Raw.tree) : Raw.tree * Raw.tree :=
  match m with
  | Raw.Leaf => (Raw.Leaf, Raw.Leaf)
  | Raw.Node _ l x r =>
      if above_low_bound x then
        if below_high_bound x then
          (let (l1, l2) := raw_partition_between l in
           let (r1, r2) := raw_partition_between r in
           (Raw.join l1 x r1, Raw.concat l2 r2))
        else
          (let (l1, l2) := raw_partition_between l in
           (l1, Raw.join l2 x r))
      else
        (let (r1, r2) := raw_partition_between r in
         (r1, Raw.join l x r2))
  end.

Remark In_raw_partition_between_1:
  forall x m,
  Raw.In x (fst (raw_partition_between m)) -> Raw.In x m.
Proof.
  induction m; simpl; intros.
- inv H.
- destruct (raw_partition_between m1) as [l1 l2] eqn:LEQ; simpl in *.
  destruct (raw_partition_between m2) as [r1 r2] eqn:REQ; simpl in *.
  destruct (above_low_bound t1) eqn:LB; [destruct (below_high_bound t1) eqn: RB | idtac]; simpl in H.
  + rewrite Raw.join_spec in H. rewrite Raw.In_node_iff. intuition.
  + rewrite Raw.In_node_iff. intuition.
  + rewrite Raw.In_node_iff. intuition.
Qed.

Remark In_raw_partition_between_2:
  forall x m,
  Raw.In x (snd (raw_partition_between m)) -> Raw.In x m.
Proof.
  induction m; simpl; intros.
- inv H.
- destruct (raw_partition_between m1) as [l1 l2] eqn:LEQ; simpl in *.
  destruct (raw_partition_between m2) as [r1 r2] eqn:REQ; simpl in *.
  destruct (above_low_bound t1) eqn:LB; [destruct (below_high_bound t1) eqn: RB | idtac]; simpl in H.
  + rewrite Raw.concat_spec in H. rewrite Raw.In_node_iff. intuition.
  + rewrite Raw.join_spec in H. rewrite Raw.In_node_iff. intuition.
  + rewrite Raw.join_spec in H. rewrite Raw.In_node_iff. intuition.
Qed.

Lemma raw_partition_between_ok:
  forall m, Raw.bst m -> Raw.bst (fst (raw_partition_between m)) /\ Raw.bst (snd (raw_partition_between m)).
Proof.
  induction 1; simpl.
- split; constructor.
- destruct IHbst1 as [L1 L2]. destruct IHbst2 as [R1 R2].
  destruct (raw_partition_between l) as [l1 l2] eqn:LEQ; simpl in *.
  destruct (raw_partition_between r) as [r1 r2] eqn:REQ; simpl in *.
  destruct (above_low_bound x) eqn:LB; [destruct (below_high_bound x) eqn: RB | idtac]; simpl.
  + split.
    apply Raw.join_ok; auto.
    red; intros. apply l0. apply In_raw_partition_between_1. rewrite LEQ; auto.
    red; intros. apply g. apply In_raw_partition_between_1. rewrite REQ; auto.
    apply Raw.concat_ok; auto.
    intros. transitivity x.
    apply l0. apply In_raw_partition_between_2. rewrite LEQ; auto.
    apply g. apply In_raw_partition_between_2. rewrite REQ; auto.
  + split.
    auto.
    apply Raw.join_ok; auto.
    red; intros. apply l0. apply In_raw_partition_between_2. rewrite LEQ; auto.
  + split.
    auto.
    apply Raw.join_ok; auto.
    red; intros. apply g. apply In_raw_partition_between_2. rewrite REQ; auto.
Qed.

Hypothesis above_monotone:
  forall x1 x2, X.eq x1 x2 \/ X.lt x1 x2 -> above_low_bound x1 = true -> above_low_bound x2 = true.
Hypothesis below_monotone:
  forall x1 x2, X.eq x1 x2 \/ X.lt x2 x1 -> below_high_bound x1 = true -> below_high_bound x2 = true.

Remark In_raw_partition_between_3:
  forall x m,
  Raw.In x (fst (raw_partition_between m)) -> above_low_bound x = true /\ below_high_bound x = true.
Proof.
  induction m; simpl; intros.
- inv H.
- destruct (raw_partition_between m1) as [l1 l2] eqn:LEQ; simpl in *.
  destruct (raw_partition_between m2) as [r1 r2] eqn:REQ; simpl in *.
  destruct (above_low_bound t1) eqn:LB; [destruct (below_high_bound t1) eqn: RB | idtac]; simpl in H.
  + rewrite Raw.join_spec in H. intuition.
    apply above_monotone with t1; auto.
    apply below_monotone with t1; auto.
  + auto.
  + auto.
Qed.

Remark In_raw_partition_between_4:
  forall x m,
  Raw.bst m ->
  Raw.In x (snd (raw_partition_between m)) -> above_low_bound x = false \/ below_high_bound x = false.
Proof.
  induction 1; simpl; intros.
- inv H.
- destruct (raw_partition_between l) as [l1 l2] eqn:LEQ; simpl in *.
  destruct (raw_partition_between r) as [r1 r2] eqn:REQ; simpl in *.
  destruct (above_low_bound x0) eqn:LB; [destruct (below_high_bound x0) eqn: RB | idtac]; simpl in H.
  + simpl in H1. rewrite Raw.concat_spec in H1. intuition.
  + assert (forall y, X.eq y x0 \/ X.lt x0 y -> below_high_bound y = false).
    { intros. destruct (below_high_bound y) eqn:E; auto.
      assert (below_high_bound x0 = true) by (apply below_monotone with y; auto).
      congruence. }
    simpl in H1. rewrite Raw.join_spec in H1. intuition.
  + assert (forall y, X.eq y x0 \/ X.lt y x0 -> above_low_bound y = false).
    { intros. destruct (above_low_bound y) eqn:E; auto.
      assert (above_low_bound x0 = true) by (apply above_monotone with y; auto).
      congruence. }
    simpl in H1. rewrite Raw.join_spec in H1. intuition.
Qed.

Remark In_raw_partition_between_5:
  forall x m,
  Raw.bst m ->
  Raw.In x m -> above_low_bound x = true -> below_high_bound x = true ->
  Raw.In x (fst (raw_partition_between m)).
Proof.
  induction 1; simpl; intros.
- inv H.
- destruct (raw_partition_between l) as [l1 l2] eqn:LEQ; simpl in *.
  destruct (raw_partition_between r) as [r1 r2] eqn:REQ; simpl in *.
  destruct (above_low_bound x0) eqn:LB; [destruct (below_high_bound x0) eqn: RB | idtac]; simpl in H.
  + simpl. rewrite Raw.join_spec. inv H1.
    auto.
    right; left; apply IHbst1; auto.
    right; right; apply IHbst2; auto.
  + simpl. inv H1.
    assert (below_high_bound x0 = true) by (apply below_monotone with x; auto).
    congruence.
    auto.
    assert (below_high_bound x0 = true) by (apply below_monotone with x; auto).
    congruence.
  + simpl. inv H1.
    assert (above_low_bound x0 = true) by (apply above_monotone with x; auto).
    congruence.
    assert (above_low_bound x0 = true) by (apply above_monotone with x; auto).
    congruence.
    eauto.
Qed.

Remark In_raw_partition_between_6:
  forall x m,
  Raw.bst m ->
  Raw.In x m -> above_low_bound x = false \/ below_high_bound x = false ->
  Raw.In x (snd (raw_partition_between m)).
Proof.
  induction 1; simpl; intros.
- inv H.
- destruct (raw_partition_between l) as [l1 l2] eqn:LEQ; simpl in *.
  destruct (raw_partition_between r) as [r1 r2] eqn:REQ; simpl in *.
  destruct (above_low_bound x0) eqn:LB; [destruct (below_high_bound x0) eqn: RB | idtac]; simpl in H.
  + simpl. rewrite Raw.concat_spec. inv H1.
    assert (below_high_bound x = true) by (apply below_monotone with x0; auto; left; symmetry; auto).
    assert (above_low_bound x = true) by (apply above_monotone with x0; auto; left; symmetry; auto).
    destruct H2; congruence.
    left; apply IHbst1; auto.
    right; apply IHbst2; auto.
  + simpl. rewrite Raw.join_spec. inv H1.
    auto.
    right; left; apply IHbst1; auto.
    auto.
  + simpl. rewrite Raw.join_spec. inv H1.
    auto.
    auto.
    right; right; apply IHbst2; auto.
Qed.

Definition partition_between (s: t) : t * t :=
  let p := raw_partition_between s.(MSet.this) in
  (@MSet.Mkt (fst p) (proj1 (raw_partition_between_ok s.(MSet.this) s.(MSet.is_ok))),
   @MSet.Mkt (snd p) (proj2 (raw_partition_between_ok s.(MSet.this) s.(MSet.is_ok)))).

Theorem partition_between_iff_1:
  forall x s,
  In x (fst (partition_between s)) <->
  In x s /\ above_low_bound x = true /\ below_high_bound x = true.
Proof.
  intros. unfold partition_between, In; simpl. split.
  intros. split. apply In_raw_partition_between_1; auto. eapply In_raw_partition_between_3; eauto.
  intros [A [B C]]. apply In_raw_partition_between_5; auto. apply MSet.is_ok.
Qed.

Theorem partition_between_iff_2:
  forall x s,
  In x (snd (partition_between s)) <->
  In x s /\ (above_low_bound x = false \/ below_high_bound x = false).
Proof.
  intros. unfold partition_between, In; simpl. split.
  intros. split. apply In_raw_partition_between_2; auto. eapply In_raw_partition_between_4; eauto. apply MSet.is_ok.
  intros [A B]. apply In_raw_partition_between_6; auto. apply MSet.is_ok.
Qed.

End PARTITION_BETWEEN.

End Make.

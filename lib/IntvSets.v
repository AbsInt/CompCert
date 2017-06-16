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

(** Finite sets of integer intervals *)

Require Import Coqlib.

Module ISet.

(** "Raw", non-dependent implementation.  A set of intervals is a
  list of nonempty semi-open intervals [(lo, hi)],
  sorted in increasing order of the low bound,
  and with no overlap nor adjacency between elements.
  In particular, if the list contains [(lo1, hi1)] followed by [(lo2, hi2)],
  we have [lo1 < hi1 < lo2 < hi2]. *)

Module R.

Inductive t : Type := Nil | Cons (lo hi: Z) (tl: t).

Fixpoint In (x: Z) (s: t) :=
  match s with
  | Nil => False
  | Cons l h s' => l <= x < h \/ In x s'
  end.

Inductive ok: t -> Prop :=
  | ok_nil: ok Nil
  | ok_cons: forall l h s
      (BOUNDS: l < h)
      (BELOW: forall x, In x s -> h < x)
      (OK: ok s),
      ok (Cons l h s).

Fixpoint mem (x: Z) (s: t) : bool :=
  match s with
  | Nil => false
  | Cons l h s' => if zlt x h then zle l x else mem x s'
  end.

Lemma mem_In:
  forall x s, ok s -> (mem x s = true <-> In x s).
Proof.
  induction 1; simpl.
- intuition congruence.
- destruct (zlt x h).
+ destruct (zle l x); simpl.
  * tauto.
  * split; intros. congruence.
    exfalso. destruct H0. omega. exploit BELOW; eauto. omega.
+ rewrite IHok. intuition.
Qed.

Fixpoint contains (L H: Z) (s: t) : bool :=
  match s with
  | Nil => false
  | Cons l h s' => (zle H h && zle l L) || contains L H s'
  end.

Lemma contains_In:
  forall l0 h0, l0 < h0 -> forall s, ok s ->
  (contains l0 h0 s = true <-> (forall x, l0 <= x < h0 -> In x s)).
Proof.
  induction 2; simpl.
- intuition. elim (H0 l0); omega.
- destruct (zle h0 h); simpl.
  destruct (zle l l0); simpl.
  intuition.
  rewrite IHok. intuition. destruct (H3 x); auto. exfalso.
  destruct (H3 l0). omega. omega. exploit BELOW; eauto. omega.
  rewrite IHok. intuition. destruct (H3 x); auto. exfalso.
  destruct (H3 h). omega. omega. exploit BELOW; eauto. omega.
Qed.

Fixpoint add (L H: Z) (s: t) {struct s} : t :=
  match s with
  | Nil => Cons L H Nil
  | Cons l h s' =>
      if zlt h L then Cons l h (add L H s')
      else if zlt H l then Cons L H s
      else add (Z.min l L) (Z.max h H) s'
  end.

Lemma In_add:
  forall x s, ok s -> forall l0 h0, (In x (add l0 h0 s) <-> l0 <= x < h0 \/ In x s).
Proof.
  induction 1; simpl; intros.
  tauto.
  destruct (zlt h l0).
  simpl. rewrite IHok. tauto.
  destruct (zlt h0 l).
  simpl. tauto.
  rewrite IHok. intuition.
  assert (l0 <= x < h0 \/ l <= x < h) by xomega. tauto.
  left; xomega.
  left; xomega.
Qed.

Lemma add_ok:
  forall s, ok s -> forall l0 h0, l0 < h0 -> ok (add l0 h0 s).
Proof.
  induction 1; simpl; intros.
  constructor. auto. intros. inv H0. constructor.
  destruct (zlt h l0).
  constructor; auto. intros. rewrite In_add in H1; auto.
  destruct H1. omega. auto.
  destruct (zlt h0 l).
  constructor. auto. simpl; intros. destruct H1. omega. exploit BELOW; eauto. omega.
  constructor. omega. auto. auto.
  apply IHok. xomega.
Qed.

Fixpoint remove (L H: Z) (s: t) {struct s} : t :=
  match s with
  | Nil => Nil
  | Cons l h s' =>
      if zlt h L then Cons l h (remove L H s')
      else if zlt H l then s
      else if zlt l L then
        if zlt H h then Cons l L (Cons H h s') else Cons l L (remove L H s')
      else
        if zlt H h then Cons H h s' else remove L H s'
  end.

Lemma In_remove:
  forall x l0 h0 s, ok s ->
  (In x (remove l0 h0 s) <-> ~(l0 <= x < h0) /\ In x s).
Proof.
  induction 1; simpl.
  tauto.
  destruct (zlt h l0).
  simpl. rewrite IHok. intuition omega.
  destruct (zlt h0 l).
  simpl. intuition. exploit BELOW; eauto. omega.
  destruct (zlt l l0).
  destruct (zlt h0 h); simpl. clear IHok. split.
  intros [A | [A | A]].
  split. omega. left; omega.
  split. omega. left; omega.
  split. exploit BELOW; eauto. omega. auto.
  intros [A [B | B]].
  destruct (zlt x l0). left; omega. right; left; omega.
  auto.
  intuition omega.
  destruct (zlt h0 h); simpl.
  intuition. exploit BELOW; eauto. omega.
  rewrite IHok. intuition. omegaContradiction.
Qed.

Lemma remove_ok:
  forall l0 h0, l0 < h0 -> forall s, ok s -> ok (remove l0 h0 s).
Proof.
  induction 2; simpl.
  constructor.
  destruct (zlt h l0).
  constructor; auto. intros; apply BELOW. rewrite In_remove in H1; tauto.
  destruct (zlt h0 l).
  constructor; auto.
  destruct (zlt l l0).
  destruct (zlt h0 h).
  constructor. omega. intros. inv H1. omega. exploit BELOW; eauto. omega.
  constructor. omega. auto. auto.
  constructor; auto. intros. rewrite In_remove in H1 by auto. destruct H1. exploit BELOW; eauto. omega.
  destruct (zlt h0 h).
  constructor; auto.
  auto.
Qed.

Fixpoint inter (s1 s2: t) {struct s1} : t :=
  let fix intr (s2: t) : t :=
    match s1, s2 with
    | Nil, _ => Nil
    | _, Nil => Nil
    | Cons l1 h1 s1', Cons l2 h2 s2' =>
        if zle h1 l2 then inter s1' s2
        else if zle h2 l1 then intr s2'
        else if zle l1 l2 then
          if zle h2 h1 then Cons l2 h2 (intr s2') else Cons l2 h1 (inter s1' s2)
        else
          if zle h1 h2 then Cons l1 h1 (inter s1' s2) else Cons l1 h2 (intr s2')
    end
  in intr s2.

Lemma In_inter:
  forall x s1, ok s1 -> forall s2, ok s2 ->
  (In x (inter s1 s2) <-> In x s1 /\ In x s2).
Proof.
  induction 1.
  simpl. induction 1; simpl. tauto. tauto.
  assert (ok (Cons l h s)) by (constructor; auto).
  induction 1; simpl.
  tauto.
  assert (ok (Cons l0 h0 s0)) by (constructor; auto).
  destruct (zle h l0).
  rewrite IHok; auto. simpl. intuition. omegaContradiction.
  exploit BELOW0; eauto. intros. omegaContradiction.
  destruct (zle h0 l).
  simpl in IHok0; rewrite IHok0. intuition. omegaContradiction.
  exploit BELOW; eauto. intros; omegaContradiction.
  destruct (zle l l0).
  destruct (zle h0 h).
  simpl. simpl in IHok0; rewrite IHok0. intuition.
  simpl. rewrite IHok; auto. simpl. intuition.  exploit BELOW0; eauto. intros; omegaContradiction.
  destruct (zle h h0).
  simpl. rewrite IHok; auto. simpl. intuition.
  simpl. simpl in IHok0; rewrite IHok0. intuition.
  exploit BELOW; eauto. intros; omegaContradiction.
Qed.

Lemma inter_ok:
  forall s1, ok s1 -> forall s2, ok s2 -> ok (inter s1 s2).
Proof.
  induction 1.
  intros; simpl. destruct s2; constructor.
  assert (ok (Cons l h s)). constructor; auto.
  induction 1; simpl.
  constructor.
  assert (ok (Cons l0 h0 s0)). constructor; auto.
  destruct (zle h l0).
  auto.
  destruct (zle h0 l).
  auto.
  destruct (zle l l0).
  destruct (zle h0 h).
  constructor; auto. intros.
  assert (In x (inter (Cons l h s) s0)) by exact H3.
  rewrite In_inter in H4; auto. apply BELOW0. tauto.
  constructor. omega. intros. rewrite In_inter in H3; auto. apply BELOW. tauto.
  auto.
  destruct (zle h h0).
  constructor. omega. intros. rewrite In_inter in H3; auto. apply BELOW. tauto.
  auto.
  constructor. omega. intros.
  assert (In x (inter (Cons l h s) s0)) by exact H3.
  rewrite In_inter in H4; auto. apply BELOW0. tauto.
  auto.
Qed.

Fixpoint union (s1 s2: t) : t :=
  match s1, s2 with
  | Nil, _ => s2
  | _, Nil => s1
  | Cons l1 h1 s1', Cons l2 h2 s2' => add l1 h1 (add l2 h2 (union s1' s2'))
  end.

Lemma In_ok_union:
  forall s1, ok s1 -> forall s2, ok s2 ->
  ok (union s1 s2) /\ (forall x, In x s1 \/ In x s2 <-> In x (union s1 s2)).
Proof.
  induction 1; destruct 1; simpl.
  split. constructor. tauto.
  split. constructor; auto. tauto.
  split. constructor; auto. tauto.
  destruct (IHok s0) as [A B]; auto.
  split. apply add_ok; auto. apply add_ok; auto.
  intros. rewrite In_add. rewrite In_add. rewrite <- B. tauto. auto. apply add_ok; auto.
Qed.

Fixpoint beq (s1 s2: t) : bool :=
  match s1, s2 with
  | Nil, Nil => true
  | Cons l1 h1 t1, Cons l2 h2 t2 => zeq l1 l2 && zeq h1 h2 && beq t1 t2
  | _, _ => false
  end.

Lemma beq_spec:
  forall s1, ok s1 -> forall s2, ok s2 ->
  (beq s1 s2 = true <-> (forall x, In x s1 <-> In x s2)).
Proof.
  induction 1; destruct 1; simpl.
- tauto.
- split; intros. discriminate. exfalso. apply (H0 l). left; omega.
- split; intros. discriminate. exfalso. apply (H0 l). left; omega.
- split; intros.
+ InvBooleans. subst. rewrite IHok in H3 by auto. rewrite H3. tauto.
+ destruct (zeq l l0). destruct (zeq h h0). simpl. subst.
  apply IHok. auto. intros; split; intros.
  destruct (proj1 (H1 x)); auto. exfalso. exploit BELOW; eauto. omega.
  destruct (proj2 (H1 x)); auto. exfalso. exploit BELOW0; eauto. omega.
  exfalso. subst l0. destruct (zlt h h0).
  destruct (proj2 (H1 h)). left; omega. omega. exploit BELOW; eauto. omega.
  destruct (proj1 (H1 h0)). left; omega. omega. exploit BELOW0; eauto. omega.
  exfalso. destruct (zlt l l0).
  destruct (proj1 (H1 l)). left; omega. omega. exploit BELOW0; eauto. omega.
  destruct (proj2 (H1 l0)). left; omega. omega. exploit BELOW; eauto. omega.
Qed.

End R.

(** Exported interface, wrapping the [ok] invariant in a dependent type. *)

Definition t := { r: R.t | R.ok r }.

Program Definition In (x: Z) (s: t) := R.In x s.

Program Definition empty : t := R.Nil.
Next Obligation. constructor. Qed.

Theorem In_empty: forall x, ~(In x empty).
Proof.
  unfold In; intros; simpl. tauto.
Qed.

Program Definition interval (l h: Z) : t :=
  if zlt l h then R.Cons l h R.Nil else R.Nil.
Next Obligation.
  constructor; auto. simpl; tauto. constructor.
Qed.
Next Obligation.
  constructor.
Qed.

Theorem In_interval: forall x l h, In x (interval l h) <-> l <= x < h.
Proof.
  intros. unfold In, interval; destruct (zlt l h); simpl.
  intuition.
  intuition.
Qed.

Program Definition add (l h: Z) (s: t) : t :=
  if zlt l h then R.add l h s else s.
Next Obligation.
  apply R.add_ok. apply proj2_sig. auto.
Qed.

Theorem In_add: forall x l h s, In x (add l h s) <-> l <= x < h \/ In x s.
Proof.
  unfold add, In; intros.
  destruct (zlt l h).
  simpl. apply R.In_add. apply proj2_sig.
  intuition. omegaContradiction.
Qed.

Program Definition remove (l h: Z) (s: t) : t :=
  if zlt l h then R.remove l h s else s.
Next Obligation.
  apply R.remove_ok. auto. apply proj2_sig.
Qed.

Theorem In_remove: forall x l h s, In x (remove l h s) <-> ~(l <= x < h) /\ In x s.
Proof.
  unfold remove, In; intros.
  destruct (zlt l h).
  simpl. apply R.In_remove. apply proj2_sig.
  intuition.
Qed.

Program Definition inter (s1 s2: t) : t := R.inter s1 s2.
Next Obligation. apply R.inter_ok; apply proj2_sig. Qed.

Theorem In_inter: forall x s1 s2, In x (inter s1 s2) <-> In x s1 /\ In x s2.
Proof.
  unfold inter, In; intros; simpl. apply R.In_inter; apply proj2_sig.
Qed.

Program Definition union (s1 s2: t) : t := R.union s1 s2.
Next Obligation.
  destruct (R.In_ok_union _ (proj2_sig s1) _ (proj2_sig s2)). auto.
Qed.

Theorem In_union: forall x s1 s2, In x (union s1 s2) <-> In x s1 \/ In x s2.
Proof.
  unfold union, In; intros; simpl.
  destruct (R.In_ok_union _ (proj2_sig s1) _ (proj2_sig s2)).
  generalize (H0 x); tauto.
Qed.

Program Definition mem (x: Z) (s: t) := R.mem x s.

Theorem mem_spec: forall x s, mem x s = true <-> In x s.
Proof.
  unfold mem, In; intros. apply R.mem_In. apply proj2_sig.
Qed.

Program Definition contains (l h: Z) (s: t) :=
  if zlt l h then R.contains l h s else true.

Theorem contains_spec:
  forall l h s, contains l h s = true <-> (forall x, l <= x < h -> In x s).
Proof.
  unfold contains, In; intros. destruct (zlt l h).
  apply R.contains_In. auto. apply proj2_sig.
  split; intros. omegaContradiction. auto.
Qed.

Program Definition beq (s1 s2: t) : bool := R.beq s1 s2.

Theorem beq_spec:
  forall s1 s2, beq s1 s2 = true <-> (forall x, In x s1 <-> In x s2).
Proof.
  unfold mem, In; intros. apply R.beq_spec; apply proj2_sig.
Qed.

End ISet.





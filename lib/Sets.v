(** Finite sets.  This module implements finite sets over any type
  that is equipped with a tree (partial finite mapping) structure.
  The set structure forms a semi-lattice, ordered by set inclusion.

  It would have been better to use the [FSet] library, which provides
  sets over any totally ordered type.  However, there are technical
  mismatches between the [FSet] export signature and our signature for
  semi-lattices.  For now, we keep this somewhat redundant
  implementation of sets.
*)

Require Import Relations.
Require Import Coqlib.
Require Import Maps.
Require Import Lattice.

Set Implicit Arguments.

Module MakeSet (P: TREE) <: SEMILATTICE.

(** Sets of elements of type [P.elt] are implemented as a partial mapping
  from [P.elt] to the one-element type [unit]. *)

  Definition elt := P.elt.

  Definition t := P.t unit.

  Lemma eq: forall (a b: t), {a=b} + {a<>b}.
  Proof.
    unfold t; intros. apply P.eq. 
    intros. left. destruct x; destruct y; auto.
  Qed.

  Definition empty := P.empty unit.

  Definition mem (r: elt) (s: t) :=
    match P.get r s with None => false | Some _ => true end.

  Definition add (r: elt) (s: t) := P.set r tt s.

  Definition remove (r: elt) (s: t) := P.remove r s.

  Definition union (s1 s2: t) :=
    P.combine
      (fun e1 e2 =>
        match e1, e2 with
        | None, None => None
        | _, _ => Some tt
        end)
      s1 s2.

  Lemma mem_empty:
    forall r, mem r empty = false.
  Proof.
    intro; unfold mem, empty. rewrite P.gempty. auto.
  Qed.

  Lemma mem_add_same:
    forall r s, mem r (add r s) = true.
  Proof.
    intros; unfold mem, add. rewrite P.gss. auto.
  Qed.

  Lemma mem_add_other:
    forall r r' s, r <> r' -> mem r' (add r s) = mem r' s.
  Proof.
    intros; unfold mem, add. rewrite P.gso; auto.
  Qed.

  Lemma mem_remove_same:
    forall r s, mem r (remove r s) = false.
  Proof.
    intros; unfold mem, remove. rewrite P.grs; auto.
  Qed.

  Lemma mem_remove_other:
    forall r r' s, r <> r' -> mem r' (remove r s) = mem r' s.
  Proof.
    intros; unfold mem, remove. rewrite P.gro; auto.
  Qed.

  Lemma mem_union:
    forall r s1 s2, mem r (union s1 s2) = (mem r s1 || mem r s2).
  Proof.
    intros; unfold union, mem. rewrite P.gcombine. 
    case (P.get r s1); case (P.get r s2); auto.
    auto.
  Qed.

  Definition elements (s: t) :=
    List.map (@fst elt unit) (P.elements s).

  Lemma elements_correct:
    forall r s, mem r s = true -> In r (elements s).
  Proof.
    intros until s. unfold mem, elements. caseEq (P.get r s).
    intros. change r with (fst (r, u)). apply in_map. 
    apply P.elements_correct. auto.
    intros; discriminate.
  Qed.
    
  Lemma elements_complete:
    forall r s, In r (elements s) -> mem r s = true.
  Proof.
    unfold mem, elements. intros. 
    generalize (list_in_map_inv _ _ _ H).
    intros [p [EQ IN]].
    destruct p. simpl in EQ. subst r.
    rewrite (P.elements_complete _ _ _ IN). auto.
  Qed.

  Definition fold (A: Set) (f: A -> elt -> A) (s: t) (x: A) :=
    P.fold (fun (x: A) (r: elt) (z: unit) => f x r) s x.

  Lemma fold_spec:
    forall (A: Set) (f: A -> elt -> A) (s: t) (x: A),
    fold f s x = List.fold_left f (elements s) x.
  Proof.
    intros. unfold fold. rewrite P.fold_spec.
    unfold elements. generalize x; generalize (P.elements s).
    induction l; simpl; auto.
  Qed.

  Definition for_all (f: elt -> bool) (s: t) :=
    fold (fun b x => andb b (f x)) s true.

  Lemma for_all_spec:
    forall f s x,
    for_all f s = true -> mem x s = true -> f x = true.
  Proof.
    intros until x. unfold for_all. rewrite fold_spec.
    assert (forall l b0,
      fold_left (fun (b : bool) (x : elt) => b && f x) l b0 = true ->
      b0 = true).
    induction l; simpl; intros.
    auto.
    generalize (IHl _ H). intro.
    elim (andb_prop _ _ H0); intros. auto.
    assert (forall l,
      fold_left (fun (b : bool) (x : elt) => b && f x) l true = true ->
      In x l -> f x = true).
    induction l; simpl; intros.
    elim H1.
    generalize (H _ _ H0); intro. 
    elim H1; intros.
    subst x. auto.
    apply IHl. rewrite H2 in H0; auto. auto.
    intros. eapply H0; eauto.
    apply elements_correct. auto.
  Qed.

  Definition ge (s1 s2: t) : Prop :=
    forall r, mem r s2 = true -> mem r s1 = true.

  Lemma ge_refl: forall x, ge x x.
  Proof.
    unfold ge; intros. auto.
  Qed.

  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; intros. auto.
  Qed.

  Definition bot := empty.
  Definition lub := union.

  Lemma ge_bot: forall (x:t), ge x bot.
  Proof.
    unfold ge; intros. rewrite mem_empty in H. discriminate.
  Qed.

  Lemma lub_commut: forall (x y: t), lub x y = lub y x.
  Proof.
    intros. unfold lub; unfold union. apply P.combine_commut.
    intros; case i; case j; auto.
  Qed.

  Lemma ge_lub_left: forall (x y: t), ge (lub x y) x.
  Proof.
    unfold ge, lub; intros. 
    rewrite mem_union. rewrite H. reflexivity.
  Qed.

  Lemma ge_lub_right: forall (x y: t), ge (lub x y) y.
  Proof.
    intros. rewrite lub_commut. apply ge_lub_left.
  Qed.

End MakeSet.

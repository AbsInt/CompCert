(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Int31.
Require Import Cyclic31.
Require Import Omega.
Require Import List.
Require Import Syntax.
Require Import Relations.
Require Import RelationClasses.

Local Obligation Tactic := intros.

(** A comparable type is equiped with a [compare] function, that define an order
   relation. **)
Class Comparable (A:Type) := {
  compare : A -> A -> comparison;
  compare_antisym : forall x y, CompOpp (compare x y) = compare y x;
  compare_trans :  forall x y z c,
    (compare x y) = c -> (compare y z) = c -> (compare x z) = c
}.

Theorem compare_refl {A:Type} (C: Comparable A) :
  forall x, compare x x = Eq.
Proof.
intros.
pose proof (compare_antisym x x).
destruct (compare x x); intuition; try discriminate.
Qed.

(** The corresponding order is a strict order. **)
Definition comparableLt {A:Type} (C: Comparable A) : relation A :=
  fun x y => compare x y = Lt.

Instance ComparableLtStrictOrder {A:Type} (C: Comparable A) :
  StrictOrder (comparableLt C).
Proof.
apply Build_StrictOrder.
unfold Irreflexive, Reflexive, complement, comparableLt.
intros.
pose proof H.
rewrite <- compare_antisym in H.
rewrite H0 in H.
discriminate H.
unfold Transitive, comparableLt.
intros x y z.
apply compare_trans.
Qed.

(** nat is comparable. **)
Program Instance natComparable : Comparable nat :=
  { compare := Nat.compare }.
Next Obligation.
symmetry.
destruct (Nat.compare x y)  as [] eqn:?.
rewrite Nat.compare_eq_iff in Heqc.
destruct Heqc.
rewrite Nat.compare_eq_iff.
trivial.
rewrite <- nat_compare_lt in *.
rewrite <- nat_compare_gt in *.
trivial.
rewrite <- nat_compare_lt in *.
rewrite <- nat_compare_gt in *.
trivial.
Qed.
Next Obligation.
destruct c.
rewrite Nat.compare_eq_iff in *; destruct H; assumption.
rewrite <- nat_compare_lt in *.
apply (Nat.lt_trans _ _ _ H H0).
rewrite <- nat_compare_gt in *.
apply (gt_trans _ _ _ H H0).
Qed.

(** A pair of comparable is comparable. **)
Program Instance PairComparable {A:Type} (CA:Comparable A) {B:Type} (CB:Comparable B) :
  Comparable (A*B) :=
  { compare := fun x y =>
      let (xa, xb) := x in let (ya, yb) := y in
      match compare xa ya return comparison with
        | Eq => compare xb yb
        | x => x
      end }.
Next Obligation.
destruct x, y.
rewrite <- (compare_antisym a a0).
rewrite <- (compare_antisym b b0).
destruct (compare a a0); intuition.
Qed.
Next Obligation.
destruct x, y, z.
destruct (compare a a0) as [] eqn:?, (compare a0 a1) as [] eqn:?;
try (rewrite <- H0 in H; discriminate);
try (destruct (compare a a1) as [] eqn:?;
  try (rewrite <- compare_antisym in Heqc0;
         rewrite CompOpp_iff in Heqc0;
         rewrite (compare_trans _ _ _  _ Heqc0 Heqc2) in Heqc1;
         discriminate);
  try (rewrite <- compare_antisym in Heqc1;
         rewrite CompOpp_iff in Heqc1;
         rewrite (compare_trans _ _ _ _ Heqc2 Heqc1) in Heqc0;
         discriminate);
  assumption);
rewrite (compare_trans _ _ _ _ Heqc0 Heqc1);
try assumption.
apply (compare_trans _ _ _ _ H H0).
Qed.

(** Special case of comparable, where equality is usual equality. **)
Class ComparableUsualEq {A:Type} (C: Comparable A) :=
  compare_eq : forall x y, compare x y = Eq -> x = y.

(** Boolean equality for a [Comparable]. **)
Definition compare_eqb {A:Type} {C:Comparable A} (x y:A) :=
  match compare x y with
    | Eq => true
    | _ => false
  end.

Theorem compare_eqb_iff {A:Type} {C:Comparable A} {U:ComparableUsualEq C} :
  forall x y, compare_eqb x y = true <-> x = y.
Proof.
unfold compare_eqb.
intuition.
apply compare_eq.
destruct (compare x y); intuition; discriminate.
destruct H.
rewrite compare_refl; intuition.
Qed.

(** [Comparable] provides a decidable equality. **)
Definition compare_eqdec {A:Type} {C:Comparable A} {U:ComparableUsualEq C} (x y:A):
  {x = y} + {x <> y}.
Proof.
destruct (compare x y) as [] eqn:?; [left; apply compare_eq; intuition | ..];
  right; intro; destruct H; rewrite compare_refl in Heqc; discriminate.
Defined.

Instance NComparableUsualEq : ComparableUsualEq natComparable := Nat.compare_eq.

(** A pair of ComparableUsualEq is ComparableUsualEq **)
Instance PairComparableUsualEq
  {A:Type} {CA:Comparable A} (UA:ComparableUsualEq CA)
  {B:Type} {CB:Comparable B} (UB:ComparableUsualEq CB) :
    ComparableUsualEq (PairComparable CA CB).
Proof.
intros x y; destruct x, y; simpl.
pose proof (compare_eq a a0); pose proof (compare_eq b b0).
destruct (compare a a0); try discriminate.
intuition.
destruct H2, H0.
reflexivity.
Qed.

(** An [Finite] type is a type with the list of all elements. **)
Class Finite (A:Type) := {
  all_list : list A;
  all_list_forall : forall x:A, In x all_list
}.

(** An alphabet is both [ComparableUsualEq] and [Finite]. **)
Class Alphabet (A:Type) := {
  AlphabetComparable :> Comparable A;
  AlphabetComparableUsualEq :> ComparableUsualEq AlphabetComparable;
  AlphabetFinite :> Finite A
}.

(** The [Numbered] class provides a conveniant way to build [Alphabet] instances,
   with a good computationnal complexity. It is mainly a injection from it to
   [Int31] **)
Class Numbered (A:Type) := {
  inj : A -> int31;
  surj : int31 -> A;
  surj_inj_compat : forall x, surj (inj x) = x;
  inj_bound : int31;
  inj_bound_spec : forall x, (phi (inj x) < phi inj_bound)%Z
}.

Program Instance NumberedAlphabet {A:Type} (N:Numbered A) : Alphabet A :=
  { AlphabetComparable :=
      {| compare := fun x y => compare31 (inj x) (inj y) |};
    AlphabetFinite :=
      {| all_list := fst (iter_int31 inj_bound _
        (fun p => (cons (surj (snd p)) (fst p), incr (snd p))) ([], 0%int31)) |} }.
Next Obligation. apply Zcompare_antisym. Qed.
Next Obligation.
destruct c. unfold compare31 in *.
rewrite Z.compare_eq_iff in *. congruence.
eapply Zcompare_Lt_trans. apply H. apply H0.
eapply Zcompare_Gt_trans. apply H. apply H0.
Qed.
Next Obligation.
intros x y H. unfold compare, compare31 in H.
rewrite Z.compare_eq_iff in *.
rewrite <- surj_inj_compat, <- phi_inv_phi with (inj y), <- H.
rewrite phi_inv_phi, surj_inj_compat; reflexivity.
Qed.
Next Obligation.
rewrite iter_int31_iter_nat.
pose proof (inj_bound_spec x).
match goal with |- In x (fst ?p) => destruct p as [] eqn:? end.
replace inj_bound with i in H.
revert l i Heqp x H.
induction (Z.abs_nat (phi inj_bound)); intros.
inversion Heqp; clear Heqp; subst.
rewrite spec_0 in H. pose proof (phi_bounded (inj x)). omega.
simpl in Heqp.
destruct nat_rect; specialize (IHn _ _ (eq_refl _) x); simpl in *.
inversion Heqp. subst. clear Heqp.
rewrite phi_incr in H.
pose proof (phi_bounded i0).
pose proof (phi_bounded (inj x)).
destruct (Z_lt_le_dec (Z.succ (phi i0)) (2 ^ Z.of_nat size)%Z).
rewrite Zmod_small in H by omega.
apply Zlt_succ_le, Zle_lt_or_eq in H.
destruct H; simpl; auto. left.
rewrite <- surj_inj_compat, <- phi_inv_phi with (inj x), H, phi_inv_phi; reflexivity.
replace (Z.succ (phi i0)) with (2 ^ Z.of_nat size)%Z in H by omega.
rewrite Z_mod_same_full in H.
exfalso; omega.
rewrite <- phi_inv_phi with i, <- phi_inv_phi with inj_bound; f_equal.
pose proof (phi_bounded inj_bound); pose proof (phi_bounded i).
rewrite <- Z.abs_eq with (phi i), <- Z.abs_eq with (phi inj_bound) by omega.
clear H H0 H1.
do 2 rewrite <- Zabs2Nat.id_abs.
f_equal.
revert l i Heqp.
assert (Z.abs_nat (phi inj_bound) < Z.abs_nat (2^31)).
apply Zabs_nat_lt, phi_bounded.
induction (Z.abs_nat (phi inj_bound)); intros.
inversion Heqp; reflexivity.
inversion Heqp; clear H1 H2 Heqp.
match goal with |- _ (_ (_ (snd ?p))) = _ => destruct p end.
pose proof (phi_bounded i0).
erewrite <- IHn, <- Zabs2Nat.inj_succ in H |- *; eauto; try omega.
rewrite phi_incr, Zmod_small; intuition; try omega.
apply inj_lt in H.
pose proof Z.le_le_succ_r.
do 2 rewrite Zabs2Nat.id_abs, Z.abs_eq in H; now eauto.
Qed.

(** Previous class instances for [option A] **)
Program Instance OptionComparable {A:Type} (C:Comparable A) : Comparable (option A) :=
  { compare := fun x y =>
      match x, y return comparison with
        | None, None => Eq
        | None, Some _ => Lt
        | Some _, None => Gt
        | Some x, Some y => compare x y
      end }.
Next Obligation.
destruct x, y; intuition.
apply compare_antisym.
Qed.
Next Obligation.
destruct x, y, z; try now intuition;
try (rewrite <- H in H0; discriminate).
apply (compare_trans _ _ _ _ H H0).
Qed.

Instance OptionComparableUsualEq {A:Type} {C:Comparable A} (U:ComparableUsualEq C) :
  ComparableUsualEq (OptionComparable C).
Proof.
intros x y.
destruct x, y; intuition; try discriminate.
rewrite (compare_eq a a0); intuition.
Qed.

Program Instance OptionFinite {A:Type} (E:Finite A) : Finite (option A) :=
  { all_list := None :: map Some all_list }.
Next Obligation.
destruct x; intuition.
right.
apply in_map.
apply all_list_forall.
Defined.

(** Definitions of [FSet]/[FMap] from [Comparable] **)
Require Import OrderedTypeAlt.
Require FSetAVL.
Require FMapAVL.
Import OrderedType.

Module Type ComparableM.
  Parameter t : Type.
  Declare Instance tComparable : Comparable t.
End ComparableM.

Module OrderedTypeAlt_from_ComparableM (C:ComparableM) <: OrderedTypeAlt.
  Definition t := C.t.
  Definition compare : t -> t -> comparison := compare.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym x y : (y?=x) = CompOpp (x?=y).
  Proof. exact (Logic.eq_sym (compare_antisym x y)). Qed.
  Lemma compare_trans c x y z :
    (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
  apply compare_trans.
  Qed.
End OrderedTypeAlt_from_ComparableM.

Module OrderedType_from_ComparableM (C:ComparableM) <: OrderedType.
  Module Alt := OrderedTypeAlt_from_ComparableM C.
  Include (OrderedType_from_Alt Alt).
End OrderedType_from_ComparableM.

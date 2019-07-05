(****************************************************************************)
(*                                                                          *)
(*                                   Menhir                                 *)
(*                                                                          *)
(*           Jacques-Henri Jourdan, CNRS, LRI, Université Paris Sud         *)
(*                                                                          *)
(*  Copyright Inria. All rights reserved. This file is distributed under    *)
(*  the terms of the GNU Lesser General Public License as published by the  *)
(*  Free Software Foundation, either version 3 of the License, or (at your  *)
(*  option) any later version, as described in the file LICENSE.            *)
(*                                                                          *)
(****************************************************************************)

From Coq Require Import List.
From Coq.ssr Require Import ssreflect.
Require Import Alphabet.

Class IsValidator (P : Prop) (b : bool) :=
  is_validator : b = true -> P.
Hint Mode IsValidator + - : typeclass_instances.

Instance is_validator_true : IsValidator True true.
Proof. done. Qed.

Instance is_validator_false : IsValidator False false.
Proof. done. Qed.

Instance is_validator_eq_true b :
  IsValidator (b = true) b.
Proof. done. Qed.

Instance is_validator_and P1 b1 P2 b2 `{IsValidator P1 b1} `{IsValidator P2 b2}:
  IsValidator (P1 /\ P2) (if b1 then b2 else false).
Proof. by split; destruct b1, b2; apply is_validator. Qed.

Instance is_validator_comparable_leibniz_eq A (C:Comparable A) (x y : A) :
  ComparableLeibnizEq C ->
  IsValidator (x = y) (compare_eqb x y).
Proof. intros ??. by apply compare_eqb_iff. Qed.

Instance is_validator_comparable_eq_impl A `(Comparable A) (x y : A) P b :
  IsValidator P b ->
  IsValidator (x = y -> P) (if compare_eqb x y then b else true).
Proof.
  intros Hval Val ->. rewrite /compare_eqb compare_refl in Val. auto.
Qed.

Lemma is_validator_forall_finite A P b `(Finite A) :
  (forall (x : A), IsValidator (P x) (b x)) ->
  IsValidator (forall (x : A), P x) (forallb b all_list).
Proof.
  move=> ? /forallb_forall Hb ?.
  apply is_validator, Hb, all_list_forall.
Qed.

(* We do not use an instance directly here, because we need somehow to
   force Coq to instantiate b with a lambda. *)
Hint Extern 2 (IsValidator (forall x : ?A, _) _) =>
    eapply (is_validator_forall_finite _ _ (fun (x:A) => _))
  : typeclass_instances.

(* Hint for synthetizing pattern-matching. *)
Hint Extern 2 (IsValidator (match ?u with _ => _ end) ?b0) =>
    let b := fresh "b" in
    unshelve notypeclasses refine (let b : bool := _ in _);
      [destruct u; intros; shelve|];    (* Synthetize `match .. with` in the validator. *)
    unify b b0;
    unfold b; destruct u; clear b
  : typeclass_instances.

(* Hint for unfolding definitions. This is necessary because many
  hints for IsValidator use [Hint Extern], which do not automatically
  unfold identifiers. *)
Hint Extern 100 (IsValidator ?X _) => unfold X
  : typeclass_instances.

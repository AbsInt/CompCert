(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                Xavier Leroy, INRIA Paris                            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This library provides type classes and tactics to decide logical
  propositions by reflection into computable Boolean equalities.
  It extends the [DecidableClass] module from the standard library
  of Coq 8.5 with more instances of decidable properties, including
  universal and existential quantification over finite types. *)

Require Export DecidableClass.
Require Import Coqlib.

Ltac decide_goal := eapply Decidable_sound; reflexivity.

(** Deciding logical connectives *)

Program Instance Decidable_not (P: Prop) (dP: Decidable P) : Decidable (~ P) := {
  Decidable_witness := negb (@Decidable_witness P dP)
}.
Next Obligation.
  rewrite negb_true_iff. split. apply Decidable_complete_alt. apply Decidable_sound_alt.
Qed.

Program Instance Decidable_equiv (P Q: Prop) (dP: Decidable P) (dQ: Decidable Q) : Decidable (P <-> Q) := {
  Decidable_witness := Bool.eqb (@Decidable_witness P dP) (@Decidable_witness Q dQ)
}.
Next Obligation.
  rewrite eqb_true_iff.
  split; intros.
  split; intros; eapply Decidable_sound; [rewrite <- H | rewrite H]; eapply Decidable_complete; eauto.
  destruct (@Decidable_witness Q dQ) eqn:D.
  eapply Decidable_complete; rewrite H; eapply Decidable_sound; eauto.
  eapply Decidable_sound_alt; rewrite H; eapply Decidable_complete_alt; eauto.
Qed.

Program Instance Decidable_and (P Q: Prop) (dP: Decidable P) (dQ: Decidable Q) : Decidable (P /\ Q) := {
  Decidable_witness := @Decidable_witness P dP && @Decidable_witness Q dQ
}.
Next Obligation.
  rewrite andb_true_iff. rewrite ! Decidable_spec. tauto.
Qed.

Program Instance Decidable_or (P Q: Prop) (dP: Decidable P) (dQ: Decidable Q) : Decidable (P \/ Q) := {
  Decidable_witness := @Decidable_witness P dP || @Decidable_witness Q dQ
}.
Next Obligation.
  rewrite orb_true_iff. rewrite ! Decidable_spec. tauto.
Qed.

Program Instance Decidable_implies (P Q: Prop) (dP: Decidable P) (dQ: Decidable Q) : Decidable (P -> Q) := {
  Decidable_witness := if @Decidable_witness P dP then @Decidable_witness Q dQ else true
}.
Next Obligation.
  split.
- intros. rewrite Decidable_complete in H by auto. eapply Decidable_sound; eauto.
- intros. destruct (@Decidable_witness P dP) eqn:WP; auto.
  eapply Decidable_complete. apply H. eapply Decidable_sound; eauto.
Qed.

(** Deciding equalities. *)

Program Definition Decidable_eq {A: Type} (eqdec: forall (x y: A), {x=y} + {x<>y}) (x y: A) : Decidable (eq x y) := {|
  Decidable_witness := proj_sumbool (eqdec x y)
|}.
Next Obligation.
  split; intros. InvBooleans. auto. subst y. apply dec_eq_true.
Qed.

Program Instance Decidable_eq_bool : forall (x y : bool), Decidable (eq x y) := {
  Decidable_witness := Bool.eqb x y
}.
Next Obligation.
  apply eqb_true_iff.
Qed.

Program Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y) := {
  Decidable_witness := Nat.eqb x y
}.
Next Obligation.
  apply Nat.eqb_eq.
Qed.

Program Instance Decidable_eq_positive : forall (x y : positive), Decidable (eq x y) := {
  Decidable_witness := Pos.eqb x y
}.
Next Obligation.
  apply Pos.eqb_eq.
Qed.

Program Instance Decidable_eq_Z : forall (x y : Z), Decidable (eq x y) := {
  Decidable_witness := Z.eqb x y
}.
Next Obligation.
  apply Z.eqb_eq.
Qed.

(** Deciding order on Z *)

Program Instance Decidable_le_Z : forall (x y: Z), Decidable (x <= y) := {
  Decidable_witness := Z.leb x y
}.
Next Obligation.
  apply Z.leb_le.
Qed.

Program Instance Decidable_lt_Z : forall (x y: Z), Decidable (x < y) := {
  Decidable_witness := Z.ltb x y
}.
Next Obligation.
  apply Z.ltb_lt.
Qed.

Program Instance Decidable_ge_Z : forall (x y: Z), Decidable (x >= y) := {
  Decidable_witness := Z.geb x y
}.
Next Obligation.
  rewrite Z.geb_le. intuition omega.
Qed.

Program Instance Decidable_gt_Z : forall (x y: Z), Decidable (x > y) := {
  Decidable_witness := Z.gtb x y
}.
Next Obligation.
  rewrite Z.gtb_lt. intuition omega.
Qed.

Program Instance Decidable_divides : forall (x y: Z), Decidable (x | y) := {
  Decidable_witness := Z.eqb y ((y / x) * x)%Z
}.
Next Obligation.
  split.
  intros. apply Z.eqb_eq in H. exists (y / x). auto.
  intros [k EQ]. apply Z.eqb_eq.
  destruct (Z.eq_dec x 0).
  subst x. rewrite Z.mul_0_r in EQ. subst y. reflexivity.
  assert (k = y / x).
  { apply Zdiv_unique_full with 0. red; omega. rewrite EQ; ring. }
  congruence.
Qed.

(** Deciding properties over lists *)

Program Instance Decidable_forall_in_list :
      forall (A: Type) (l: list A) (P: A -> Prop) (dP: forall x:A, Decidable (P x)),
      Decidable (forall x:A, In x l -> P x) := {
  Decidable_witness := List.forallb (fun x => @Decidable_witness (P x) (dP x)) l
}.
Next Obligation.
  rewrite List.forallb_forall. split; intros.
- eapply Decidable_sound; eauto.
- eapply Decidable_complete; eauto.
Qed.

Program Instance Decidable_exists_in_list :
      forall (A: Type) (l: list A) (P: A -> Prop) (dP: forall x:A, Decidable (P x)),
      Decidable (exists x:A, In x l /\ P x) := {
  Decidable_witness := List.existsb (fun x => @Decidable_witness (P x) (dP x)) l
}.
Next Obligation.
  rewrite List.existsb_exists. split.
- intros (x & U & V). exists x; split; auto. eapply Decidable_sound; eauto.
- intros (x & U & V). exists x; split; auto. eapply Decidable_complete; eauto.
Qed.

(** Types with finitely many elements. *)

Class Finite (T: Type) := {
  Finite_elements: list T;
  Finite_elements_spec: forall x:T, In x Finite_elements
}.

(** Deciding forall and exists quantification over finite types. *)

Program Instance Decidable_forall : forall (T: Type) (fT: Finite T) (P: T -> Prop) (dP: forall x:T, Decidable (P x)), Decidable (forall x, P x) := {
  Decidable_witness := List.forallb (fun x => @Decidable_witness (P x) (dP x)) (@Finite_elements T fT)
}.
Next Obligation.
  rewrite List.forallb_forall. split; intros.
- eapply Decidable_sound; eauto. apply H. apply Finite_elements_spec.
- eapply Decidable_complete; eauto.
Qed.

Program Instance Decidable_exists : forall (T: Type) (fT: Finite T) (P: T -> Prop) (dP: forall x:T, Decidable (P x)), Decidable (exists x, P x) := {
  Decidable_witness := List.existsb (fun x => @Decidable_witness (P x) (dP x)) (@Finite_elements T fT)
}.
Next Obligation.
  rewrite List.existsb_exists. split.
- intros (x & A & B). exists x. eapply Decidable_sound; eauto.
- intros (x & A). exists x; split. eapply Finite_elements_spec. eapply Decidable_complete; eauto.
Qed.

(** Some examples of finite types. *)

Program Instance Finite_bool : Finite bool := {
  Finite_elements := false :: true :: nil
}.
Next Obligation.
  destruct x; auto.
Qed.

Program Instance Finite_pair : forall (A B: Type) (fA: Finite A) (fB: Finite B), Finite (A * B) := {
  Finite_elements := list_prod (@Finite_elements A fA) (@Finite_elements B fB)
}.
Next Obligation.
  apply List.in_prod; eapply Finite_elements_spec.
Qed.

Program Instance Finite_option : forall (A: Type) (fA: Finite A), Finite (option A) := {
  Finite_elements := None :: List.map (@Some A) (@Finite_elements A fA)
}.
Next Obligation.
  destruct x; auto. right; apply List.in_map; eapply Finite_elements_spec.
Qed.

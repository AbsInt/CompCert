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

(** Defining recursive functions by Noetherian induction.  This is a simplified
  interface to the [Wf] module of Coq's standard library, where the functions
  to be defined have non-dependent types, and function extensionality is assumed. *)

Require Import Axioms.
Require Import Init.Wf.
Require Import Wf_nat.

Set Implicit Arguments.

Section FIX.

Variables A B: Type.
Variable R: A -> A -> Prop.
Hypothesis Rwf: well_founded R.
Variable F: forall (x: A), (forall (y: A), R y x -> B) -> B.

Definition Fix (x: A) : B := Wf.Fix Rwf (fun (x: A) => B) F x.

Theorem unroll_Fix:
  forall x, Fix x = F (fun (y: A) (P: R y x) => Fix y).
Proof.
  unfold Fix; intros. apply Wf.Fix_eq with (P := fun (x: A) => B).
  intros. assert (f = g). apply functional_extensionality_dep; intros.
  apply functional_extensionality; intros. auto.
  subst g; auto.
Qed.

End FIX.

(** Same, with a nonnegative measure instead of a well-founded ordering *)

Section FIXM.

Variables A B: Type.
Variable measure: A -> nat.
Variable F: forall (x: A), (forall (y: A), measure y < measure x -> B) -> B.

Definition Fixm (x: A) : B := Wf.Fix (well_founded_ltof A measure) (fun (x: A) => B) F x.

Theorem unroll_Fixm:
  forall x, Fixm x = F (fun (y: A) (P: measure y < measure x) => Fixm y).
Proof.
  unfold Fixm; intros. apply Wf.Fix_eq with (P := fun (x: A) => B).
  intros. assert (f = g). apply functional_extensionality_dep; intros.
  apply functional_extensionality; intros. auto.
  subst g; auto.
Qed.

End FIXM.



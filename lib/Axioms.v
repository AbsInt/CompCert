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

(** This file collects some axioms used throughout the CompCert development. *)

Require ClassicalFacts.

(** * Extensionality axioms *)

(** The following [Require Export] gives us functional extensionality for dependent function types:
<<
Axiom functional_extensionality_dep : forall {A} {B : A -> Type}, 
  forall (f g : forall x : A, B x), 
  (forall x, f x = g x) -> f = g.
>> 
and, as a corollary, functional extensionality for non-dependent functions:
<<
Lemma functional_extensionality {A B} (f g : A -> B) : 
  (forall x, f x = g x) -> f = g.
>>
*)
Require Export FunctionalExtensionality.

(** For compatibility with earlier developments, [extensionality]
  is an alias for [functional_extensionality]. *)

Lemma extensionality:
  forall (A B: Type) (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof. intros; apply functional_extensionality. auto. Qed.

Implicit Arguments extensionality.

(** We also assert propositional extensionality. *)

Axiom prop_ext: ClassicalFacts.prop_extensionality.
Implicit Arguments prop_ext.

(** * Proof irrelevance *)

(** We also use proof irrelevance, which is a consequence of propositional
    extensionality. *)

Lemma proof_irr: ClassicalFacts.proof_irrelevance.
Proof.
  exact (ClassicalFacts.ext_prop_dep_proof_irrel_cic prop_ext).
Qed.
Implicit Arguments proof_irr.

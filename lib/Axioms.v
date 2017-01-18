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
Require FunctionalExtensionality.

(** * Extensionality axioms *)

(** The [Require FunctionalExtensionality] gives us functional
    extensionality for dependent function types: *)

Lemma functional_extensionality_dep:
  forall {A: Type} {B : A -> Type} (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
Proof @FunctionalExtensionality.functional_extensionality_dep.

(** and, as a corollary, functional extensionality for non-dependent functions:
*)

Lemma functional_extensionality:
  forall {A B: Type} (f g : A -> B), (forall x, f x = g x) -> f = g.
Proof @FunctionalExtensionality.functional_extensionality.

(** For compatibility with earlier developments, [extensionality]
  is an alias for [functional_extensionality]. *)

Lemma extensionality:
  forall {A B: Type} (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof @functional_extensionality.

(** * Proof irrelevance *)

(** We also use proof irrelevance. *)

Axiom proof_irr: ClassicalFacts.proof_irrelevance.

Arguments proof_irr [A].

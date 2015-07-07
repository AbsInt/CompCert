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

Require Import List.
Require Import Coq.Program.Syntax.
Require Import Equality.

(** A curryfied function with multiple parameters **)
Definition arrows_left: list Type -> Type -> Type :=
  fold_left (fun A B => B -> A).

(** A curryfied function with multiple parameters **)
Definition arrows_right: Type -> list Type -> Type :=
  fold_right (fun A B => A -> B).

(** A tuple is a heterogeneous list. For convenience, we use pairs. **)
Fixpoint tuple (types : list Type) : Type :=
  match types with
  | nil => unit
  | t::q => prod t (tuple q)
  end.

Fixpoint uncurry {args:list Type} {res:Type}:
  arrows_left args res -> tuple args -> res :=
  match args return forall res, arrows_left args res -> tuple args -> res with
    | [] => fun _ f _ => f
    | t::q => fun res f p => let (d, t) := p in
      (@uncurry q _ f t) d
  end res.

Lemma JMeq_eqrect:
  forall (U:Type) (a b:U) (P:U -> Type) (x:P a) (e:a=b),
    eq_rect a P x b e ~= x.
Proof.
destruct e.
reflexivity.
Qed.

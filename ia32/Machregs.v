(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AST.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Floating-point registers that can be allocated to RTL pseudo-registers 
  ([Fxx]).
- Two integer registers, not allocatable, reserved as temporaries for
  spilling and reloading ([IT1, IT2]).
- Two float registers, not allocatable, reserved as temporaries for
  spilling and reloading ([FT1, FT2]).

  The type [mreg] does not include special-purpose or reserved
  machine registers such as the stack pointer and the condition codes. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | AX: mreg | BX: mreg | SI: mreg | DI: mreg | BP: mreg
  (** Allocatable float regs *)
  | X0: mreg | X1: mreg | X2: mreg | X3: mreg | X4: mreg | X5: mreg
  (** Integer temporaries *)
  | IT1: mreg (* DX *) | IT2: mreg (* CX *)
  (** Float temporaries *)
  | FT1: mreg (* X6 *) | FT2: mreg (* X7 *) | FP0: mreg (* top of FP stack *).

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition mreg_type (r: mreg): typ :=
  match r with
  | AX => Tint | BX => Tint | SI => Tint | DI => Tint | BP => Tint
  (** Allocatable float regs *)
  | X0 => Tfloat | X1 => Tfloat | X2 => Tfloat
  | X3 => Tfloat | X4 => Tfloat | X5 => Tfloat
  (** Integer temporaries *)
  | IT1 => Tint | IT2 => Tint
  (** Float temporaries *)
  | FT1 => Tfloat | FT2 => Tfloat | FP0 => Tfloat
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | AX => 1 | BX => 2 | SI => 3 | DI => 4 | BP => 5
    | X0 => 6 | X1 => 7 | X2 => 8
    | X3 => 9 | X4 => 10 | X5 => 11
    | IT1 => 12 | IT2 => 13
    | FT1 => 14 | FT2 => 15 | FP0 => 16
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; simpl; intro; discriminate || reflexivity.
  Qed.
End IndexedMreg.


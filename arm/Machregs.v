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
  spilling and reloading ([ITx]).
- Two float registers, not allocatable, reserved as temporaries for
  spilling and reloading ([FTx]).

  The type [mreg] does not include special-purpose machine registers
  such as the stack pointer and the condition codes. *)

Inductive mreg: Set :=
  (** Allocatable integer regs *)
  | R0: mreg  | R1: mreg  | R2: mreg  | R3: mreg
  | R4: mreg  | R5: mreg  | R6: mreg  | R7: mreg
  | R8: mreg  | R9: mreg  | R11: mreg
  (** Allocatable float regs *)
  | F0: mreg  | F1: mreg  | F4: mreg  | F5: mreg
  | F6: mreg  | F7: mreg
  (** Integer temporaries *)
  | IT1: mreg (* R10 *) | IT2: mreg (* R12 *)
  (** Float temporaries *)
  | FT1: mreg (* F2 *) | FT2: mreg (* F3 *).

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Qed.

Definition mreg_type (r: mreg): typ :=
  match r with
  | R0 => Tint  | R1 => Tint  | R2 => Tint  | R3 => Tint
  | R4 => Tint  | R5 => Tint  | R6 => Tint  | R7 => Tint
  | R8 => Tint  | R9 => Tint  | R11 => Tint
  | F0 => Tfloat  | F1 => Tfloat  | F4 => Tfloat  | F5 => Tfloat
  | F6 => Tfloat  | F7 => Tfloat
  | IT1 => Tint | IT2 => Tint
  | FT1 => Tfloat | FT2 => Tfloat
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0 => 1  | R1 => 2  | R2 => 3  | R3 => 4
    | R4 => 5  | R5 => 6  | R6 => 7  | R7 => 8
    | R8 => 9  | R9 => 10 | R11 => 11
    | F0 => 12 | F1 => 13 | F4 => 14  | F5 => 15
    | F6 => 16 | F7 => 17
    | IT1 => 18 | IT2 => 19
    | FT1 => 20 | FT2 => 21
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; simpl; intro; discriminate || reflexivity.
  Qed.
End IndexedMreg.


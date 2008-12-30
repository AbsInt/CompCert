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

  The type [mreg] does not include special-purpose machine registers
  such as the stack pointer and the condition codes. *)

Inductive mreg: Set :=
  (** Allocatable integer regs *)
  | R3: mreg  | R4: mreg  | R5: mreg  | R6: mreg
  | R7: mreg  | R8: mreg  | R9: mreg  | R10: mreg
  | R13: mreg | R14: mreg | R15: mreg | R16: mreg
  | R17: mreg | R18: mreg | R19: mreg | R20: mreg
  | R21: mreg | R22: mreg | R23: mreg | R24: mreg
  | R25: mreg | R26: mreg | R27: mreg | R28: mreg
  | R29: mreg | R30: mreg | R31: mreg
  (** Allocatable float regs *)
  | F1: mreg  | F2: mreg  | F3: mreg  | F4: mreg
  | F5: mreg  | F6: mreg  | F7: mreg  | F8: mreg
  | F9: mreg  | F10: mreg | F14: mreg | F15: mreg
  | F16: mreg | F17: mreg | F18: mreg | F19: mreg
  | F20: mreg | F21: mreg | F22: mreg | F23: mreg
  | F24: mreg | F25: mreg | F26: mreg | F27: mreg
  | F28: mreg | F29: mreg | F30: mreg | F31: mreg
  (** Integer temporaries *)
  | IT1: mreg (* R11 *) | IT2: mreg (* R0 *)
  (** Float temporaries *)
  | FT1: mreg (* F11 *) | FT2: mreg (* F12 *) | FT3: mreg (* F0 *).

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Qed.

Definition mreg_type (r: mreg): typ :=
  match r with
  | R3 => Tint  | R4 => Tint  | R5 => Tint  | R6 => Tint
  | R7 => Tint  | R8 => Tint  | R9 => Tint  | R10 => Tint
  | R13 => Tint | R14 => Tint | R15 => Tint | R16 => Tint
  | R17 => Tint | R18 => Tint | R19 => Tint | R20 => Tint
  | R21 => Tint | R22 => Tint | R23 => Tint | R24 => Tint
  | R25 => Tint | R26 => Tint | R27 => Tint | R28 => Tint
  | R29 => Tint | R30 => Tint | R31 => Tint
  | F1 => Tfloat  | F2 => Tfloat  | F3 => Tfloat  | F4 => Tfloat
  | F5 => Tfloat  | F6 => Tfloat  | F7 => Tfloat  | F8 => Tfloat
  | F9 => Tfloat  | F10 => Tfloat | F14 => Tfloat | F15 => Tfloat
  | F16 => Tfloat | F17 => Tfloat | F18 => Tfloat | F19 => Tfloat
  | F20 => Tfloat | F21 => Tfloat | F22 => Tfloat | F23 => Tfloat
  | F24 => Tfloat | F25 => Tfloat | F26 => Tfloat | F27 => Tfloat
  | F28 => Tfloat | F29 => Tfloat | F30 => Tfloat | F31 => Tfloat
  | IT1 => Tint | IT2 => Tint
  | FT1 => Tfloat | FT2 => Tfloat | FT3 => Tfloat
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R3 => 1  | R4 => 2  | R5 => 3  | R6 => 4
    | R7 => 5  | R8 => 6  | R9 => 7  | R10 => 8
    | R13 => 9 | R14 => 10 | R15 => 11 | R16 => 12
    | R17 => 13 | R18 => 14 | R19 => 15 | R20 => 16
    | R21 => 17 | R22 => 18 | R23 => 19 | R24 => 20
    | R25 => 21 | R26 => 22 | R27 => 23 | R28 => 24
    | R29 => 25 | R30 => 26 | R31 => 27
    | F1 => 28  | F2 => 29  | F3 => 30  | F4 => 31
    | F5 => 32  | F6 => 33  | F7 => 34  | F8 => 35
    | F9 => 36  | F10 => 37 | F14 => 38 | F15 => 39
    | F16 => 40 | F17 => 41 | F18 => 42 | F19 => 43
    | F20 => 44 | F21 => 45 | F22 => 46 | F23 => 47
    | F24 => 48 | F25 => 49 | F26 => 50 | F27 => 51
    | F28 => 52 | F29 => 53 | F30 => 54 | F31 => 55
    | IT1 => 56 | IT2 => 57
    | FT1 => 58 | FT2 => 59 | FT3 => 60
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; simpl; intro; discriminate || reflexivity.
  Qed.
End IndexedMreg.


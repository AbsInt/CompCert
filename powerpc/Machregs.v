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
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Floating-point registers that can be allocated to RTL pseudo-registers 
  ([Fxx]).

  The type [mreg] does not include special-purpose or reserved
  machine registers such as the stack pointer (GPR1), the small data area
  pointers (GPR2, GPR13), and the condition codes. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | R3: mreg  | R4: mreg  | R5: mreg  | R6: mreg
  | R7: mreg  | R8: mreg  | R9: mreg  | R10: mreg
  | R11: mreg | R12: mreg
  | R14: mreg | R15: mreg | R16: mreg
  | R17: mreg | R18: mreg | R19: mreg | R20: mreg
  | R21: mreg | R22: mreg | R23: mreg | R24: mreg
  | R25: mreg | R26: mreg | R27: mreg | R28: mreg
  | R29: mreg | R30: mreg | R31: mreg
  (** Allocatable float regs *)
  | F0: mreg
  | F1: mreg  | F2: mreg  | F3: mreg  | F4: mreg
  | F5: mreg  | F6: mreg  | F7: mreg  | F8: mreg
  | F9: mreg  | F10: mreg | F11: mreg | F12: mreg
  | F13: mreg | F14: mreg | F15: mreg
  | F16: mreg | F17: mreg | F18: mreg | F19: mreg
  | F20: mreg | F21: mreg | F22: mreg | F23: mreg
  | F24: mreg | F25: mreg | F26: mreg | F27: mreg
  | F28: mreg | F29: mreg | F30: mreg | F31: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition mreg_type (r: mreg): typ :=
  match r with
  | R3 => Tint  | R4 => Tint  | R5 => Tint  | R6 => Tint
  | R7 => Tint  | R8 => Tint  | R9 => Tint  | R10 => Tint
  | R11 => Tint | R12 => Tint
  | R14 => Tint | R15 => Tint | R16 => Tint
  | R17 => Tint | R18 => Tint | R19 => Tint | R20 => Tint
  | R21 => Tint | R22 => Tint | R23 => Tint | R24 => Tint
  | R25 => Tint | R26 => Tint | R27 => Tint | R28 => Tint
  | R29 => Tint | R30 => Tint | R31 => Tint
  | F0 => Tfloat
  | F1 => Tfloat  | F2 => Tfloat  | F3 => Tfloat  | F4 => Tfloat
  | F5 => Tfloat  | F6 => Tfloat  | F7 => Tfloat  | F8 => Tfloat
  | F9 => Tfloat  | F10 => Tfloat | F11 => Tfloat | F12 => Tfloat
  | F13 => Tfloat | F14 => Tfloat | F15 => Tfloat
  | F16 => Tfloat | F17 => Tfloat | F18 => Tfloat | F19 => Tfloat
  | F20 => Tfloat | F21 => Tfloat | F22 => Tfloat | F23 => Tfloat
  | F24 => Tfloat | F25 => Tfloat | F26 => Tfloat | F27 => Tfloat
  | F28 => Tfloat | F29 => Tfloat | F30 => Tfloat | F31 => Tfloat
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R3 => 1  | R4 => 2  | R5 => 3  | R6 => 4
    | R7 => 5  | R8 => 6  | R9 => 7  | R10 => 8
    | R11 => 9 | R12 => 10
    | R14 => 11 | R15 => 12 | R16 => 13
    | R17 => 14 | R18 => 15 | R19 => 16 | R20 => 17
    | R21 => 18 | R22 => 19 | R23 => 20 | R24 => 21
    | R25 => 22 | R26 => 23 | R27 => 24 | R28 => 25
    | R29 => 26 | R30 => 27 | R31 => 28
    | F0 => 29
    | F1 => 30  | F2 => 31  | F3 => 32  | F4 => 33
    | F5 => 34  | F6 => 35  | F7 => 36  | F8 => 37
    | F9 => 38  | F10 => 39 | F11 => 40 | F12 => 41
    | F13 => 42 | F14 => 43 | F15 => 44
    | F16 => 45 | F17 => 46 | F18 => 47 | F19 => 48
    | F20 => 49 | F21 => 50 | F22 => 51 | F23 => 52
    | F24 => 53 | F25 => 54 | F26 => 55 | F27 => 56
    | F28 => 57 | F29 => 58 | F30 => 59 | F31 => 60
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; simpl; intro; discriminate || reflexivity.
  Qed.
End IndexedMreg.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Ofloatconst _ => R12 :: nil
  | Ointoffloat => F13 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  R12 :: nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg :=
  match chunk with
  | Mfloat32 => R11 :: R12 :: F13 :: nil
  | _ => R11 :: R12 :: nil
  end.

Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.

Definition destroyed_by_jumptable: list mreg :=
  R12 :: nil.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_builtin _ _ => F13 :: nil
  | EF_vload _ => nil
  | EF_vstore Mfloat32 => F13 :: nil
  | EF_vstore _ => nil
  | EF_vload_global _ _ _ => R11 :: nil
  | EF_vstore_global Mint64 _ _ => R10 :: R11 :: R12 :: nil
  | EF_vstore_global Mfloat32 _ _ => R11 :: R12 :: F13 :: nil
  | EF_vstore_global _ _ _ => R11 :: R12 :: nil
  | EF_memcpy _ _ => R11 :: R12 :: F13 :: nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg :=
  match ty with
  | Tsingle => F13 :: nil
  | _ => nil
  end.

Definition destroyed_at_function_entry: list mreg :=
  nil.

Definition temp_for_parent_frame: mreg :=
  R11.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  (nil, None).

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list (option mreg) :=
  (nil, nil).

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation]. There is only one: rotate-mask-insert. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Oroli _ _ => true
  | _ => false
  end.

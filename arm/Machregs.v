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

  The type [mreg] does not include reserved machine registers
  such as the stack pointer, the link register, and the condition codes. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | R0: mreg  | R1: mreg  | R2: mreg  | R3: mreg
  | R4: mreg  | R5: mreg  | R6: mreg  | R7: mreg
  | R8: mreg  | R9: mreg  | R10: mreg | R11: mreg
  | R12: mreg
  (** Allocatable double-precision float regs *)
  | F0: mreg  | F1: mreg  | F2: mreg  | F3: mreg
  | F4: mreg  | F5: mreg  | F6: mreg  | F7: mreg
  | F8: mreg  | F9: mreg  | F10: mreg | F11: mreg
  | F12: mreg | F13: mreg | F14: mreg | F15: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition mreg_type (r: mreg): typ :=
  match r with
  | R0  | R1  | R2  | R3   | R4  | R5  | R6  | R7 
  | R8  | R9  | R10 | R11  | R12 => Tany32
  | F0  | F1  | F2  | F3   | F4 | F5   | F6  | F7 
  | F8  | F9  | F10  | F11 | F12  | F13  | F14  | F15 => Tany64
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0 => 1  | R1 => 2  | R2 => 3  | R3 => 4
    | R4 => 5  | R5 => 6  | R6 => 7  | R7 => 8
    | R8 => 9  | R9 => 10 | R10 => 11 | R11 => 12
    | R12 => 13
    | F0 => 14 | F1 => 15 | F2 => 16  | F3 => 17
    | F4 => 18 | F5 => 19 | F6 => 20  | F7 => 21
    | F8 => 22 | F9 => 23 | F10 => 24 | F11 => 25
    | F12 => 26 | F13 => 27 | F14 => 28 | F15 => 29
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; simpl; intro; discriminate || reflexivity.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Odiv | Odivu => R0 :: R1 :: R2 :: R3 :: R12 :: nil
  | Ointoffloat | Ointuoffloat | Ointofsingle | Ointuofsingle => F6 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.

Definition destroyed_by_jumptable: list mreg :=
  nil.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_memcpy sz al => if zle sz 32 then nil else R2 :: R3 :: R12 :: nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg :=
  R12 :: nil.

Definition temp_for_parent_frame: mreg :=
  R12.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  match op with
  | Odiv | Odivu => (Some R0 :: Some R1 :: nil, Some R0)
  | _ => (nil, None)
  end.

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  match ef with
  | EF_memcpy sz al =>
      if zle sz 32 then (nil, nil) else (Some R3 :: Some R2 :: nil, nil)
  | _ => (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are none for ARM. *)

Definition two_address_op (op: operation) : bool :=
  false.

Global Opaque two_address_op.


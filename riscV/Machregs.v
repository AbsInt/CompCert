(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Floating-point registers that can be allocated to RTL pseudo-registers
  ([Fxx]).

  The type [mreg] does not include reserved machine registers such as
  the zero register (x0), the link register (x1), the stack pointer
  (x2), the global pointer (x3), and the thread pointer (x4).
  Finally, register x31 is reserved for use as a temporary by the
  assembly-code generator [Asmgen].
*)

Inductive mreg: Type :=
 (** Allocatable integer regs. *)
              | R5:  mreg | R6:  mreg | R7:  mreg
  | R8:  mreg | R9:  mreg | R10: mreg | R11: mreg
  | R12: mreg | R13: mreg | R14: mreg | R15: mreg
  | R16: mreg | R17: mreg | R18: mreg | R19: mreg
  | R20: mreg | R21: mreg | R22: mreg | R23: mreg
  | R24: mreg | R25: mreg | R26: mreg | R27: mreg
  | R28: mreg | R29: mreg | R30: mreg
  (** Allocatable double-precision float regs *)
  | F0:  mreg | F1:  mreg | F2:  mreg | F3:  mreg
  | F4:  mreg | F5:  mreg | F6:  mreg | F7:  mreg
  | F8:  mreg | F9:  mreg | F10: mreg | F11: mreg
  | F12: mreg | F13: mreg | F14: mreg | F15: mreg
  | F16: mreg | F17: mreg | F18: mreg | F19: mreg
  | F20: mreg | F21: mreg | F22: mreg | F23: mreg
  | F24: mreg | F25: mreg | F26: mreg | F27: mreg
  | F28: mreg | F29: mreg | F30: mreg | F31: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
    R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: R11 :: R12 :: R13 :: R14 :: R15
 :: R16 :: R17 :: R18 :: R19 :: R20 :: R21 :: R22 :: R23
 :: R24 :: R25 :: R26 :: R27 :: R28 :: R29 :: R30
 :: F0 :: F1 :: F2 :: F3 :: F4 :: F5 :: F6 :: F7
 :: F8 :: F9 :: F10 :: F11 :: F12 :: F13 :: F14 :: F15
 :: F16 :: F17 :: F18 :: F19 :: F20 :: F21 :: F22 :: F23
 :: F24 :: F25 :: F26 :: F27 :: F28 :: F29 :: F30 :: F31
 :: nil.

Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.

Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.
  
Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ :=
  match r with
        | R5  | R6  | R7  | R8  | R9  | R10 | R11
  | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19
  | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27
  | R28 | R29 | R30 => if Archi.ptr64 then Tany64 else Tany32

  | F0  | F1  | F2  | F3  | F4  | F5  | F6  | F7
  | F8  | F9  | F10 | F11 | F12 | F13 | F14 | F15
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31 => Tany64
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
                | R5  =>  1 | R6  =>  2 | R7  =>  3
    | R8  =>  4 | R9  =>  5 | R10 =>  6 | R11 =>  7
    | R12 =>  8 | R13 =>  9 | R14 => 10 | R15 => 11
    | R16 => 12 | R17 => 13 | R18 => 14 | R19 => 15
    | R20 => 16 | R21 => 17 | R22 => 18 | R23 => 19
    | R24 => 20 | R25 => 21 | R26 => 22 | R27 => 23
    | R28 => 24 | R29 => 25 | R30 => 26

    | F0  => 28 | F1  => 29 | F2  => 30 | F3  => 31
    | F4  => 32 | F5  => 33 | F6  => 34 | F7  => 35
    | F8  => 36 | F9  => 37 | F10 => 38 | F11 => 39
    | F12 => 40 | F13 => 41 | F14 => 42 | F15 => 43
    | F16 => 44 | F17 => 45 | F18 => 46 | F19 => 47
    | F20 => 48 | F21 => 49 | F22 => 50 | F23 => 51
    | F24 => 52 | F25 => 53 | F26 => 54 | F27 => 55
    | F28 => 56 | F29 => 57 | F30 => 58 | F31 => 59
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
                  ("X5",  R5)  :: ("X6",  R6)  :: ("X7",  R7)  ::
  ("X8",  R8)  :: ("X9",  R9)  :: ("X10", R10) :: ("X11", R11) ::
  ("X12", R12) :: ("X13", R13) :: ("X14", R14) :: ("X15", R15) ::
  ("X16", R16) :: ("X17", R17) :: ("X18", R18) :: ("X19", R19) ::
  ("X20", R20) :: ("X21", R21) :: ("X22", R22) :: ("X23", R23) ::
  ("X24", R24) :: ("X25", R25) :: ("X26", R26) :: ("X27", R27) ::
  ("X28", R28) :: ("X29", R29) :: ("X30", R30) ::

  ("F0",  F0)  :: ("F1",  F1)  :: ("F2",  F2)  :: ("F3",  F3)  ::
  ("F4",  F4)  :: ("F5",  F5)  :: ("F6",  F6)  :: ("F7",  F7)  ::
  ("F8",  F8)  :: ("F9",  F9)  :: ("F10", F10) :: ("F11", F11) ::
  ("F12", F12) :: ("F13", F13) :: ("F14", F14) :: ("F15", F15) ::
  ("F16", F16) :: ("F17", F17) :: ("F18", F18) :: ("F19", F19) ::
  ("F20", F20) :: ("F21", F21) :: ("F22", F22) :: ("F23", F23) ::
  ("F24", F24) :: ("F25", F25) :: ("F26", F26) :: ("F27", F27) ::
  ("F28", F28) :: ("F29", F29) :: ("F30", F30) :: ("F31", F31) ::
  nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Ointoffloat | Ointuoffloat | Ointofsingle | Ointuofsingle
  | Olongoffloat | Olonguoffloat | Olongofsingle | Olonguofsingle
      => F6 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg := nil.

Definition destroyed_by_jumptable: list mreg := R5 :: nil.

Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | EF_memcpy sz al => R5 :: R6 :: R7 :: F0 :: nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := R30 :: nil.

Definition temp_for_parent_frame: mreg := R30.

Definition destroyed_at_indirect_call: list mreg :=
  R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: R16 :: R17 :: nil.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg := (nil, None).

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  match ef with
  | EF_builtin name sg =>
      if (negb Archi.ptr64) && string_dec name "__builtin_bswap64" then
        (Some R6 :: Some R5 :: nil, Some R5 :: Some R6 :: nil)
      else
        (nil, nil)
  | _ =>
    (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are two: the pseudo [Ocast32signed],
  because it expands to a no-op owing to the representation of 32-bit
  integers as their 64-bit sign extension; and [Ocast32unsigned],
  because it builds on the same magic no-op. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Ocast32signed | Ocast32unsigned => true
  | _ => false
  end.

(** Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_builtin id sg => nil
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.

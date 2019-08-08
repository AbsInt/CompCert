(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import String.
Require Import Coqlib Decidableplus Maps.
Require Import AST Op.

(** ** Machine registers *)

(** Integer register 16 is reserved as temporary and for call veeners.
    Integer register 18 is reserved as the platform register.
    Integer register 30 is reserved for the return address. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15
  | R17 | R19 | R20 | R21 |  R22 | R23
  | R24 | R25 | R26 | R27 | R28 | R29
  (** Allocatable floating-point regs *)
  | F0  | F1  | F2  | F3  | F4  | F5  | F6  | F7
  | F8  | F9  | F10 | F11 | F12 | F13 | F14 | F15
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
     R0  :: R1  :: R2  :: R3  :: R4  :: R5  ::  R6  :: R7
  :: R8  :: R9  :: R10 :: R11 :: R12 :: R13 ::  R14 :: R15
  :: R17 :: R19 :: R20 :: R21 ::  R22 :: R23
  :: R24 :: R25 :: R26 :: R27 :: R28 :: R29
  :: F0  :: F1  :: F2  :: F3  :: F4  :: F5  ::  F6  :: F7
  :: F8  :: F9  :: F10 :: F11 :: F12 :: F13 ::  F14 :: F15
  :: F16 :: F17 :: F18 :: F19 :: F20 :: F21 ::  F22 :: F23
  :: F24 :: F25 :: F26 :: F27 :: F28 :: F29 ::  F30 :: F31
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

Definition mreg_type (r: mreg): typ := Tany64.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0 => 1   | R1 => 2   | R2 => 3   | R3 => 4
    | R4 => 5   | R5 => 6   | R6 => 7   | R7 => 8
    | R8 => 9   | R9 => 10  | R10 => 11 | R11 => 12
    | R12 => 13 | R13 => 14 | R14 => 15 | R15 => 16
    | R17 => 17 | R19 => 19
    | R20 => 20 | R21 => 21 | R22 => 22 | R23 => 23
    | R24 => 24 | R25 => 25 | R26 => 26 | R27 => 27
    | R28 => 28 | R29 => 29
    | F0 => 32  | F1 => 33  | F2 => 34  | F3 => 35
    | F4 => 36  | F5 => 37  | F6 => 38  | F7 => 39
    | F8 => 40  | F9 => 41  | F10 => 42 | F11 => 43
    | F12 => 44 | F13 => 45 | F14 => 46 | F15 => 47
    | F16 => 48 | F17 => 49 | F18 => 50 | F19 => 51
    | F20 => 52 | F21 => 53 | F22 => 54 | F23 => 55
    | F24 => 56 | F25 => 57 | F26 => 58 | F27 => 59
    | F28 => 60 | F29 => 61 | F30 => 62 | F31 => 63
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
     ("X0", R0)  :: ("X1", R1)  :: ("X2", R2)  :: ("X3", R3)
  :: ("X4", R4)  :: ("X5", R5)  :: ("X6", R6)  :: ("X7", R7)
  :: ("X8", R8)  :: ("X9", R9)  :: ("X10", R10) :: ("X11", R11)
  :: ("X12", R12) :: ("X13", R13) :: ("X14", R14) :: ("X15", R15)
  :: ("X17", R17) :: ("X19", R19)
  :: ("X20", R20) :: ("X21", R21) :: ("X22", R22) :: ("X23", R23)
  :: ("X24", R24) :: ("X25", R25) :: ("X26", R26) :: ("X27", R27)
  :: ("X28", R28) :: ("X29", R29)
  :: ("D0", F0)  :: ("D1", F1)  :: ("D2", F2)  :: ("D3", F3)
  :: ("D4", F4)  :: ("D5", F5)  :: ("D6", F6)  :: ("D7", F7)
  :: ("D8", F8)  :: ("D9", F9)  :: ("D10", F10) :: ("D11", F11)
  :: ("D12", F12) :: ("D13", F13) :: ("D14", F14) :: ("D15", F15)
  :: ("D16", F16) :: ("D17", F17) :: ("D18", F18) :: ("D19", F19)
  :: ("D20", F20) :: ("D21", F21) :: ("D22", F22) :: ("D23", F23)
  :: ("D24", F24) :: ("D25", F25) :: ("D26", F26) :: ("D27", F27)
  :: ("D28", F28) :: ("D29", F29) :: ("D30", F30) :: ("D31", F31)
  :: nil.

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
  | Oshrximm _ | Oshrlximm _ => R17 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg := nil.

Definition destroyed_by_jumptable: list mreg := R17 :: nil.

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
  | EF_memcpy sz al => R15 :: R17 :: R29 :: nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := R29 :: nil.

Definition destroyed_at_indirect_call: list mreg := nil.

Definition temp_for_parent_frame: mreg := R29.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  (nil, None).

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  (nil, nil).

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    destroyed_at_indirect_call
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There is one for AArch64: [Olowlong],
  which is actually a no-operation in the generated asm code. *)

Definition two_address_op (op: operation) : bool := 
  match op with
  | Olowlong => true
  | _ => false
  end.

Global Opaque two_address_op.

(* Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.


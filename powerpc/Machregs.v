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

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
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

Definition all_mregs :=
     R3  :: R4  :: R5  :: R6  :: R7  :: R8  :: R9  :: R10
  :: R11 :: R12 :: R14 :: R15 :: R16 :: R17 :: R18 :: R19 :: R20
  :: R21 :: R22 :: R23 :: R24 :: R25 :: R26 :: R27 :: R28
  :: R29 :: R30 :: R31
  :: F0  :: F1  :: F2  :: F3  :: F4
  :: F5  :: F6  :: F7  :: F8
  :: F9  :: F10 :: F11 :: F12
  :: F13 :: F14 :: F15
  :: F16 :: F17 :: F18 :: F19
  :: F20 :: F21 :: F22 :: F23
  :: F24 :: F25 :: F26 :: F27
  :: F28 :: F29 :: F30 :: F31 :: nil.

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
  | R3  | R4  | R5  | R6  | R7  | R8  | R9  | R10  | R11 | R12
  | R14 | R15 | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23 | R24
  | R25 | R26 | R27 | R28 | R29 | R30 | R31 => if Archi.ppc64 then Tany64 else Tany32
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
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
  ("R3", R3) ::  ("R4", R4) ::  ("R5", R5) ::  ("R6", R6) ::
  ("R7", R7) ::  ("R8", R8) ::  ("R9", R9) ::  ("R10", R10) ::
  ("R11", R11) :: ("R12", R12) ::
  ("R14", R14) :: ("R15", R15) :: ("R16", R16) ::
  ("R17", R17) :: ("R18", R18) :: ("R19", R19) :: ("R20", R20) ::
  ("R21", R21) :: ("R22", R22) :: ("R23", R23) :: ("R24", R24) ::
  ("R25", R25) :: ("R26", R26) :: ("R27", R27) :: ("R28", R28) ::
  ("R29", R29) :: ("R30", R30) :: ("R31", R31) ::
  ("F0", F0) :: ("F1", F1) ::  ("F2", F2) ::  ("F3", F3) ::  ("F4", F4) ::
  ("F5", F5) ::  ("F6", F6) ::  ("F7", F7) ::  ("F8", F8) ::
  ("F9", F9) ::  ("F10", F10) :: ("F11", F11) :: ("F12", F12) ::
  ("F13", F13) :: ("F14", F14) :: ("F15", F15) ::
  ("F16", F16) :: ("F17", F17) :: ("F18", F18) :: ("F19", F19) ::
  ("F20", F20) :: ("F21", F21) :: ("F22", F22) :: ("F23", F23) ::
  ("F24", F24) :: ("F25", F25) :: ("F26", F26) :: ("F27", F27) ::
  ("F28", F28) :: ("F29", F29) :: ("F30", F30) :: ("F31", F31) :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_cond (cond: condition): list mreg :=
  match cond with
  | Ccomplimm _ _ | Ccompluimm _ _ => R12 :: nil
  | _ => nil
  end.

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Ofloatconst _ => R12 :: nil
  | Osingleconst _ => R12 :: nil
  | Olongconst _ => R12 :: nil
  | Ointoffloat | Ointuoffloat => F13 :: nil
  | Olongoffloat => F13 :: nil
  | Oaddlimm _ => R12 :: nil
  | Oandlimm _ => R12 :: nil
  | Oorlimm _ => R12 :: nil
  | Oxorlimm _ => R12 :: nil
  | Orolml _ _ => R12 :: nil
  | Ocmp c => destroyed_by_cond c
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  R12 :: nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg :=
  R11 :: R12 :: nil.

Definition destroyed_by_jumptable: list mreg :=
  R12 :: nil.

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
  | EF_builtin id sg =>
    if string_dec id "__builtin_set_spr64" then R10::nil
    else if string_dec id "__builtin_atomic_exchange" then R10::nil
    else if string_dec id "__builtin_atomic_compare_exchange" then R10::R11::nil
    else F13 :: nil
  | EF_vload _ => R11 :: nil
  | EF_vstore Mint64 => R10 :: R11 :: R12 :: nil
  | EF_vstore _ => R11 :: R12 :: nil
  | EF_memcpy _ _ => R11 :: R12 :: F13 :: nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg :=
  nil.

Definition destroyed_at_function_entry: list mreg :=
  nil.

Definition destroyed_at_indirect_call: list mreg :=
  nil.

Definition temp_for_parent_frame: mreg :=
  R11.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  (nil, None).


Definition mregs_for_builtin (ef: external_function): list (option mreg) * list (option mreg) :=
  match ef with
    | EF_builtin id sg =>
      if string_dec id "__builtin_atomic_exchange" then ((Some R3)::(Some R4)::(Some R5)::nil,nil)
      else if string_dec id "__builtin_sync_fetch_and_add" then ((Some R4)::(Some R5)::nil,(Some R3)::nil)
      else if string_dec id "___builtin_atomic_compare_exchange" then ((Some R4)::(Some R5)::(Some R6)::nil, (Some R3):: nil)
      else (nil, nil)
    | _ => (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_at_indirect_call
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation]. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Oroli _ _ => true
  | Olowlong => true
  | Ofloatofsingle => true
  | _ => false
  end.

(* Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_builtin id sg =>
      if string_dec id "__builtin_get_spr" then OK_const :: nil
      else if string_dec id "__builtin_get_spr64" then OK_const :: nil
      else if string_dec id "__builtin_set_spr" then OK_const :: OK_default :: nil
      else if string_dec id "__builtin_set_spr64" then OK_const :: OK_default :: nil
      else if string_dec id "__builtin_prefetch" then OK_default :: OK_const :: OK_const :: nil
      else if string_dec id "__builtin_dcbtls" then OK_default :: OK_const :: nil
      else if string_dec id "__builtin_icbtls" then OK_default :: OK_const :: nil
      else if string_dec id "__builtin_mbar" then OK_const :: nil
      else if string_dec id "__builtin_mr" then OK_const :: OK_const :: nil
      else nil
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.

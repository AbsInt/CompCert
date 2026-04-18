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

From Coq Require Import String.
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

Global Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.

Global Instance Finite_mreg : Finite mreg := {
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

Definition register_aliases :=
     ("W0", R0)   :: ("W1", R1)   :: ("W2", R2)   :: ("W3", R3)
  :: ("W4", R4)   :: ("W5", R5)   :: ("W6", R6)   :: ("W7", R7)
  :: ("W8", R8)   :: ("W9", R9)   :: ("W10", R10) :: ("W11", R11)
  :: ("W12", R12) :: ("W13", R13) :: ("W14", R14) :: ("W15", R15)
  :: ("W17", R17) :: ("W19", R19)
  :: ("W20", R20) :: ("W21", R21) :: ("W22", R22) :: ("W23", R23)
  :: ("W24", R24) :: ("W25", R25) :: ("W26", R26) :: ("W27", R27)
  :: ("W28", R28) :: ("W29", R29)
  :: ("V0", F0)   :: ("V1", F1)   :: ("V2", F2)   :: ("V3", F3)
  :: ("V4", F4)   :: ("V5", F5)   :: ("V6", F6)   :: ("V7", F7)
  :: ("V8", F8)   :: ("V9", F9)   :: ("V10", F10) :: ("V11", F11)
  :: ("V12", F12) :: ("V13", F13) :: ("V14", F14) :: ("V15", F15)
  :: ("V16", F16) :: ("V17", F17) :: ("V18", F18) :: ("V19", F19)
  :: ("V20", F20) :: ("V21", F21) :: ("V22", F22) :: ("V23", F23)
  :: ("V24", F24) :: ("V25", F25) :: ("V26", F26) :: ("V27", F27)
  :: ("V28", F28) :: ("V29", F29) :: ("V30", F30) :: ("V31", F31)
  :: ("Q0", F0)   :: ("Q1", F1)   :: ("Q2", F2)   :: ("Q3", F3)
  :: ("Q4", F4)   :: ("Q5", F5)   :: ("Q6", F6)   :: ("Q7", F7)
  :: ("Q8", F8)   :: ("Q9", F9)   :: ("Q10", F10) :: ("Q11", F11)
  :: ("Q12", F12) :: ("Q13", F13) :: ("Q14", F14) :: ("Q15", F15)
  :: ("Q16", F16) :: ("Q17", F17) :: ("Q18", F18) :: ("Q19", F19)
  :: ("Q20", F20) :: ("Q21", F21) :: ("Q22", F22) :: ("Q23", F23)
  :: ("Q24", F24) :: ("Q25", F25) :: ("Q26", F26) :: ("Q27", F27)
  :: ("Q28", F28) :: ("Q29", F29) :: ("Q30", F30) :: ("Q31", F31)
  :: ("S0", F0)   :: ("S1", F1)   :: ("S2", F2)   :: ("S3", F3)
  :: ("S4", F4)   :: ("S5", F5)   :: ("S6", F6)   :: ("S7", F7)
  :: ("S8", F8)   :: ("S9", F9)   :: ("S10", F10) :: ("S11", F11)
  :: ("S12", F12) :: ("S13", F13) :: ("S14", F14) :: ("S15", F15)
  :: ("S16", F16) :: ("S17", F17) :: ("S18", F18) :: ("S19", F19)
  :: ("S20", F20) :: ("S21", F21) :: ("S22", F22) :: ("S23", F23)
  :: ("S24", F24) :: ("S25", F25) :: ("S26", F26) :: ("S27", F27)
  :: ("S28", F28) :: ("S29", F29) :: ("S30", F30) :: ("S31", F31)
  :: ("H0", F0)   :: ("H1", F1)   :: ("H2", F2)   :: ("H3", F3)
  :: ("H4", F4)   :: ("H5", F5)   :: ("H6", F6)   :: ("H7", F7)
  :: ("H8", F8)   :: ("H9", F9)   :: ("H10", F10) :: ("H11", F11)
  :: ("H12", F12) :: ("H13", F13) :: ("H14", F14) :: ("H15", F15)
  :: ("H16", F16) :: ("H17", F17) :: ("H18", F18) :: ("H19", F19)
  :: ("H20", F20) :: ("H21", F21) :: ("H22", F22) :: ("H23", F23)
  :: ("H24", F24) :: ("H25", F25) :: ("H26", F26) :: ("H27", F27)
  :: ("H28", F28) :: ("H29", F29) :: ("H30", F30) :: ("H31", F31)
  :: ("B0", F0)   :: ("B1", F1)   :: ("B2", F2)   :: ("B3", F3)
  :: ("B4", F4)   :: ("B5", F5)   :: ("B6", F6)   :: ("B7", F7)
  :: ("B8", F8)   :: ("B9", F9)   :: ("B10", F10) :: ("B11", F11)
  :: ("B12", F12) :: ("B13", F13) :: ("B14", F14) :: ("B15", F15)
  :: ("B16", F16) :: ("B17", F17) :: ("B18", F18) :: ("B19", F19)
  :: ("B20", F20) :: ("B21", F21) :: ("B22", F22) :: ("B23", F23)
  :: ("B24", F24) :: ("B25", F25) :: ("B26", F26) :: ("B27", F27)
  :: ("B28", F28) :: ("B29", F29) :: ("B30", F30) :: ("B31", F31)
  :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in
    match assoc register_names with
    | Some res => Some res
    | None => assoc register_aliases
    end.

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
  | EF_memcpy sz al => R14 :: R15 :: R17 :: nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := R15 :: nil.

Definition destroyed_at_indirect_call: list mreg := nil.

Definition temp_for_parent_frame: mreg := R15.

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


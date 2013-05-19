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
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers.
- Floating-point registers that can be allocated to RTL pseudo-registers.
- The special [FP0] register denoting the top of the X87 float stack.

  The type [mreg] does not include special-purpose or reserved
  machine registers such as the stack pointer and the condition codes. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | AX: mreg | BX: mreg | CX: mreg | DX: mreg | SI: mreg | DI: mreg | BP: mreg
  (** Allocatable float regs *)
  | X0: mreg | X1: mreg | X2: mreg | X3: mreg 
  | X4: mreg | X5: mreg | X6: mreg | X7: mreg
  (** Special float reg *)
  | FP0: mreg (**r top of x87 FP stack *).

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition mreg_type (r: mreg): typ :=
  match r with
  | AX => Tint | BX => Tint | CX => Tint | DX => Tint
  | SI => Tint | DI => Tint | BP => Tint
  | X0 => Tfloat | X1 => Tfloat | X2 => Tfloat | X3 => Tfloat
  | X4 => Tfloat | X5 => Tfloat | X6 => Tfloat | X7 => Tfloat
  | FP0 => Tfloat
  end.

Local Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | AX => 1 | BX => 2 | CX => 3 | DX => 4 | SI => 5 | DI => 6 | BP => 7
    | X0 => 8 | X1 => 9 | X2 => 10 | X3 => 11
    | X4 => 12 | X5 => 13 | X6 => 14 | X7 => 15
    | FP0 => 16
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
  | Omove => FP0 :: nil
  | Ocast8signed | Ocast8unsigned | Ocast16signed | Ocast16unsigned => AX :: nil
  | Odiv => AX :: DX :: nil
  | Odivu => AX :: DX :: nil
  | Omod => AX :: DX :: nil
  | Omodu => AX :: DX :: nil
  | Oshrximm _ => CX :: nil
  | Ocmp _ => AX :: CX :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg :=
  match chunk with
  | Mint8signed | Mint8unsigned => AX :: CX :: nil
  | Mint16signed | Mint16unsigned | Mint32 | Mint64 => nil
  | Mfloat32 => X7 :: nil
  | Mfloat64 | Mfloat64al32 => FP0 :: nil
  end.

Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.

Definition destroyed_by_jumptable: list mreg :=
  nil.

Local Open Scope string_scope.

Definition builtin_write16_reversed := ident_of_string "__builtin_write16_reversed".
Definition builtin_write32_reversed := ident_of_string "__builtin_write32_reversed".

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_memcpy sz al =>
      if zle sz 32 then CX :: X7 :: nil else CX :: SI :: DI :: nil
  | EF_vstore (Mint8unsigned|Mint8signed) => AX :: CX :: nil
  | EF_vstore Mfloat32 => X7 :: nil
  | EF_vstore_global (Mint8unsigned|Mint8signed) _ _ => AX :: nil
  | EF_vstore_global Mfloat32 _ _ => X7 :: nil
  | EF_builtin id sg =>
      if ident_eq id builtin_write16_reversed
      || ident_eq id builtin_write32_reversed
      then CX :: DX :: nil else nil
  | _ => nil
  end.

Definition destroyed_at_function_entry: list mreg :=
  DX :: FP0 :: nil.   (* must include destroyed_by_op Omove *)

Definition destroyed_by_setstack (ty: typ): list mreg :=
  match ty with
  | Tfloat => FP0 :: nil
  | Tsingle => X7 :: FP0 :: nil
  | _ => nil
  end.

Definition temp_for_parent_frame: mreg :=
  DX.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  match op with
  | Odiv => (Some AX :: Some CX :: nil, Some AX)
  | Odivu => (Some AX :: Some CX :: nil, Some AX)
  | Omod => (Some AX :: Some CX :: nil, Some DX)
  | Omodu => (Some AX :: Some CX :: nil, Some DX)
  | Oshl => (None :: Some CX :: nil, None)
  | Oshr => (None :: Some CX :: nil, None)
  | Oshru => (None :: Some CX :: nil, None)
  | Oshrximm _ => (Some AX :: nil, Some AX)
  | _ => (nil, None)
  end.

Definition builtin_negl := ident_of_string "__builtin_negl".
Definition builtin_addl := ident_of_string "__builtin_addl".
Definition builtin_subl := ident_of_string "__builtin_subl".
Definition builtin_mull := ident_of_string "__builtin_mull".

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list (option mreg) :=
  match ef with
  | EF_memcpy sz al =>
     if zle sz 32 then (Some AX :: Some DX :: nil, nil) else (Some DI :: Some SI :: nil, nil)
  | EF_builtin id sg =>
     if ident_eq id builtin_negl then
       (Some DX :: Some AX :: nil, Some DX :: Some AX :: nil)
     else if ident_eq id builtin_addl || ident_eq id builtin_subl then
       (Some DX :: Some AX :: Some CX :: Some BX :: nil, Some DX :: Some AX :: nil)
     else if ident_eq id builtin_mull then
       (Some AX :: Some DX :: nil, Some DX :: Some AX :: nil)
     else
       (nil, nil)
  | _ => (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation]. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Omove => false
  | Ointconst _ => false
  | Ofloatconst _ => false
  | Oindirectsymbol _ => false
  | Ocast8signed => false
  | Ocast8unsigned => false
  | Ocast16signed => false
  | Ocast16unsigned => false
  | Oneg => true
  | Osub => true
  | Omul => true
  | Omulimm _ => true
  | Odiv => false
  | Odivu => false
  | Omod => false
  | Omodu => false
  | Oand => true
  | Oandimm _ => true
  | Oor => true
  | Oorimm _ => true
  | Oxor => true
  | Oxorimm _ => true
  | Oshl => true
  | Oshlimm _ => true
  | Oshr => true
  | Oshrimm _ => true
  | Oshrximm _ => false
  | Oshru => true
  | Oshruimm _ => true
  | Ororimm _ => true
  | Oshldimm _ => true
  | Olea addr => false
  | Onegf => true
  | Oabsf => true
  | Oaddf => true
  | Osubf => true
  | Omulf => true
  | Odivf => true
  | Osingleoffloat => false
  | Ointoffloat => false
  | Ofloatofint => false
  | Omakelong => false
  | Olowlong => false
  | Ohighlong => false
  | Ocmp c => false
  end.


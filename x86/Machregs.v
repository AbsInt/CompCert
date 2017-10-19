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
  | AX | BX | CX | DX | SI | DI | BP
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15  (**r only in 64-bit mode *)
  (** Allocatable float regs *)
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7
  | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15  (**r only in 64-bit mode *)
  (** Special float reg *)
  | FP0.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
     AX :: BX :: CX :: DX :: SI :: DI :: BP
  :: R8 :: R9 :: R10 :: R11 :: R12 :: R13 :: R14 :: R15
  :: X0 :: X1 :: X2 :: X3 :: X4 :: X5 :: X6 :: X7
  :: X8 :: X9 :: X10 :: X11 :: X12 :: X13 :: X14 :: X15
  :: FP0 :: nil.

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
  | AX | BX | CX | DX | SI | DI | BP => if Archi.ptr64 then Tany64 else Tany32
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 => Tany64
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 => Tany64
  | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15 => Tany64
  | FP0 => Tany64
  end.

Local Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | AX => 1 | BX => 2 | CX => 3 | DX => 4 | SI => 5 | DI => 6 | BP => 7
    | R8 => 8 | R9 => 9 | R10 => 10 | R11 => 11 | R12 => 12 | R13 => 13 | R14 => 14 | R15 => 15
    | X0 => 16 | X1 => 17 | X2 => 18 | X3 => 19 | X4 => 20 | X5 => 21 | X6 => 22 | X7 => 23
    | X8 => 24 | X9 => 25 | X10 => 26 | X11 => 27 | X12 => 28 | X13 => 29 | X14 => 30 | X15 => 31
    | FP0 => 32
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool :=
  match r with FP0 => true | _ => false end.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
  ("RAX", AX) :: ("RBX", BX) :: ("RCX", CX) :: ("RDX", DX) ::
  ("RSI", SI) :: ("RDI", DI) :: ("RBP", BP) ::
  ("EAX", AX) :: ("EBX", BX) :: ("ECX", CX) :: ("EDX", DX) ::
  ("ESI", SI) :: ("EDI", DI) :: ("EBP", BP) ::
  ("R8", R8) :: ("R9", R9) :: ("R10", R10) :: ("R11", R11) ::
  ("R12", R12) :: ("R13", R13) :: ("R14", R14) :: ("R15", R15) ::
  ("XMM0", X0) :: ("XMM1", X1) :: ("XMM2", X2) :: ("XMM3", X3) ::
  ("XMM4", X4) :: ("XMM5", X5) :: ("XMM6", X6) :: ("XMM7", X7) ::
  ("XMM8", X8) :: ("XMM9", X9) :: ("XMM10", X10) :: ("XMM11", X11) ::
  ("XMM12", X12) :: ("XMM13", X13) :: ("XMM14", X14) :: ("XMM15", X15) ::
  ("ST0", FP0) :: nil.

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
  | Ocast8signed | Ocast8unsigned => AX :: nil
  | Omulhs => AX :: DX :: nil
  | Omulhu => AX :: DX :: nil
  | Odiv => AX :: DX :: nil
  | Odivu => AX :: DX :: nil
  | Omod => AX :: DX :: nil
  | Omodu => AX :: DX :: nil
  | Oshrximm _ => CX :: nil
  | Omullhs => AX :: DX :: nil
  | Omullhu => AX :: DX :: nil
  | Odivl => AX :: DX :: nil
  | Odivlu => AX :: DX :: nil
  | Omodl => AX :: DX :: nil
  | Omodlu => AX :: DX :: nil
  | Oshrxlimm _ => DX :: nil
  | Ocmp _ => AX :: CX :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg :=
  match chunk with
  | Mint8signed | Mint8unsigned => if Archi.ptr64 then nil else AX :: CX :: nil
  | _ => nil
  end.

Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.

Definition destroyed_by_jumptable: list mreg :=
  AX :: DX :: nil.

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
  | EF_memcpy sz al =>
      if zle sz 32 then CX :: X7 :: nil else CX :: SI :: DI :: nil
  | EF_vstore (Mint8unsigned|Mint8signed) =>
      if Archi.ptr64 then nil else AX :: CX :: nil
  | EF_builtin name sg =>
      if string_dec name "__builtin_va_start" then AX :: nil
      else if string_dec name "__builtin_write16_reversed"
           || string_dec name "__builtin_write32_reversed"
      then CX :: DX :: nil
      else nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | _ => nil
  end.

Definition destroyed_at_function_entry: list mreg :=
  (* must include [destroyed_by_setstack ty] *)
  AX :: FP0 :: nil.

Definition destroyed_by_setstack (ty: typ): list mreg :=
  match ty with
  | Tfloat | Tsingle => FP0 :: nil
  | _ => nil
  end.

Definition destroyed_at_indirect_call: list mreg :=
  AX :: nil.

Definition temp_for_parent_frame: mreg :=
  AX.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  match op with
  | Omulhs => (Some AX :: None :: nil, Some DX)
  | Omulhu => (Some AX :: None :: nil, Some DX)
  | Odiv => (Some AX :: Some CX :: nil, Some AX)
  | Odivu => (Some AX :: Some CX :: nil, Some AX)
  | Omod => (Some AX :: Some CX :: nil, Some DX)
  | Omodu => (Some AX :: Some CX :: nil, Some DX)
  | Oshl => (None :: Some CX :: nil, None)
  | Oshr => (None :: Some CX :: nil, None)
  | Oshru => (None :: Some CX :: nil, None)
  | Oshrximm _ => (Some AX :: nil, Some AX)
  | Omullhs => (Some AX :: None :: nil, Some DX)
  | Omullhu => (Some AX :: None :: nil, Some DX)
  | Odivl => (Some AX :: Some CX :: nil, Some AX)
  | Odivlu => (Some AX :: Some CX :: nil, Some AX)
  | Omodl => (Some AX :: Some CX :: nil, Some DX)
  | Omodlu => (Some AX :: Some CX :: nil, Some DX)
  | Oshll => (None :: Some CX :: nil, None)
  | Oshrl => (None :: Some CX :: nil, None)
  | Oshrlu => (None :: Some CX :: nil, None)
  | Oshrxlimm _ => (Some AX :: nil, Some AX)
  | _ => (nil, None)
  end.

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list (option mreg) :=
  match ef with
  | EF_memcpy sz al =>
     if zle sz 32 then (Some AX :: Some DX :: nil, nil) else (Some DI :: Some SI :: nil, nil)
  | EF_builtin name sg =>
     if string_dec name "__builtin_negl" then
       (Some DX :: Some AX :: nil, Some DX :: Some AX :: nil)
     else if string_dec name "__builtin_addl"
          || string_dec name "__builtin_subl" then
       (Some DX :: Some AX :: Some CX :: Some BX :: nil, Some DX :: Some AX :: nil)
     else if string_dec name "__builtin_mull" then
       (Some AX :: Some DX :: nil, Some DX :: Some AX :: nil)
     else if string_dec name "__builtin_va_start" then
       (Some DX :: nil, nil)
     else if (negb Archi.ptr64) && string_dec name "__builtin_bswap64" then
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
  | Olongconst _ => false
  | Ofloatconst _ => false
  | Osingleconst _ => false
  | Oindirectsymbol _ => false
  | Ocast8signed => false
  | Ocast8unsigned => false
  | Ocast16signed => false
  | Ocast16unsigned => false
  | Oneg => true
  | Osub => true
  | Omul => true
  | Omulimm _ => true
  | Omulhs => false
  | Omulhu => false
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
  | Onot => true
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
  | Omakelong => true
  | Olowlong => true
  | Ohighlong => true
  | Ocast32signed => false
  | Ocast32unsigned => false
  | Onegl => true
  | Oaddlimm _ => true
  | Osubl => true
  | Omull => true
  | Omullimm _ => true
  | Omullhs => false
  | Omullhu => false
  | Odivl => false
  | Odivlu => false
  | Omodl => false
  | Omodlu => false
  | Oandl => true
  | Oandlimm _ => true
  | Oorl => true
  | Oorlimm _ => true
  | Oxorl => true
  | Oxorlimm _ => true
  | Onotl => true
  | Oshll => true
  | Oshllimm _ => true
  | Oshrl => true
  | Oshrlimm _ => true
  | Oshrxlimm _ => false
  | Oshrlu => true
  | Oshrluimm _ => true
  | Ororlimm _ => true
  | Oleal addr => false
  | Onegf => true
  | Oabsf => true
  | Oaddf => true
  | Osubf => true
  | Omulf => true
  | Odivf => true
  | Onegfs => true
  | Oabsfs => true
  | Oaddfs => true
  | Osubfs => true
  | Omulfs => true
  | Odivfs => true
  | Osingleoffloat => false
  | Ofloatofsingle => false
  | Ointoffloat => false
  | Ofloatofint => false
  | Ointofsingle => false
  | Osingleofint => false
  | Olongoffloat => false
  | Ofloatoflong => false
  | Olongofsingle => false
  | Osingleoflong => false
  | Ocmp c => false
  end.

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

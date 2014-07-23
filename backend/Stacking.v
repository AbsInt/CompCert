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

(** Layout of activation records; translation from Linear to Mach. *)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import Locations.
Require Import Linear.
Require Import Bounds.
Require Import Mach.
Require Import Conventions.
Require Import Stacklayout.
Require Import Lineartyping.

(** * Layout of activation records *)

(** The machine- and ABI-dependent aspects of the layout are defined
  in module [Stacklayout]. *)

(** Computation the frame offset for the given component of the frame.
  The component is expressed by the following [frame_index] sum type. *)

Inductive frame_index: Type :=
  | FI_link: frame_index
  | FI_retaddr: frame_index
  | FI_local: Z -> typ -> frame_index
  | FI_arg: Z -> typ -> frame_index
  | FI_saved_int: Z -> frame_index
  | FI_saved_float: Z -> frame_index.

Definition offset_of_index (fe: frame_env) (idx: frame_index) :=
  match idx with
  | FI_link => fe.(fe_ofs_link)
  | FI_retaddr => fe.(fe_ofs_retaddr)
  | FI_local x ty => fe.(fe_ofs_local) + 4 * x
  | FI_arg x ty => fe_ofs_arg + 4 * x
  | FI_saved_int x => fe.(fe_ofs_int_callee_save) + 4 * x
  | FI_saved_float x => fe.(fe_ofs_float_callee_save) + 8 * x
  end.

(** * Saving and restoring callee-save registers *)

(** [save_callee_save fe k] adds before [k] the instructions that
  store in the frame the values of callee-save registers used by the
  current function. *)

Definition save_callee_save_reg
    (bound: frame_env -> Z) (number: mreg -> Z) (mkindex: Z -> frame_index)
    (ty: typ) (fe: frame_env) (cs: mreg) (k: Mach.code) :=
  let i := number cs in
  if zlt i (bound fe)
  then Msetstack cs (Int.repr (offset_of_index fe (mkindex i))) ty :: k
  else k.

Definition save_callee_save_regs
    (bound: frame_env -> Z) (number: mreg -> Z) (mkindex: Z -> frame_index)
    (ty: typ) (fe: frame_env) (csl: list mreg) (k: Mach.code) :=
  List.fold_right (save_callee_save_reg bound number mkindex ty fe) k csl.

Definition save_callee_save_int (fe: frame_env) :=
  save_callee_save_regs 
    fe_num_int_callee_save index_int_callee_save FI_saved_int
    Tany32 fe int_callee_save_regs.

Definition save_callee_save_float (fe: frame_env) :=
  save_callee_save_regs
    fe_num_float_callee_save index_float_callee_save FI_saved_float 
    Tany64 fe float_callee_save_regs.

Definition save_callee_save (fe: frame_env) (k: Mach.code) :=
  save_callee_save_int fe (save_callee_save_float fe k).

(** [restore_callee_save fe k] adds before [k] the instructions that
  re-load from the frame the values of callee-save registers used by the
  current function, restoring these registers to their initial values. *)

Definition restore_callee_save_reg
    (bound: frame_env -> Z) (number: mreg -> Z) (mkindex: Z -> frame_index)
    (ty: typ) (fe: frame_env) (cs: mreg) (k: Mach.code) :=
  let i := number cs in
  if zlt i (bound fe)
  then Mgetstack (Int.repr (offset_of_index fe (mkindex i))) ty cs :: k
  else k.

Definition restore_callee_save_regs
    (bound: frame_env -> Z) (number: mreg -> Z) (mkindex: Z -> frame_index)
    (ty: typ) (fe: frame_env) (csl: list mreg) (k: Mach.code) :=
  List.fold_right (restore_callee_save_reg bound number mkindex ty fe) k csl.

Definition restore_callee_save_int (fe: frame_env) :=
  restore_callee_save_regs 
    fe_num_int_callee_save index_int_callee_save FI_saved_int
    Tany32 fe int_callee_save_regs.

Definition restore_callee_save_float (fe: frame_env) :=
  restore_callee_save_regs
    fe_num_float_callee_save index_float_callee_save FI_saved_float 
    Tany64 fe float_callee_save_regs.

Definition restore_callee_save (fe: frame_env) (k: Mach.code) :=
  restore_callee_save_int fe (restore_callee_save_float fe k).

(** * Code transformation. *)

(** Translation of operations and addressing mode.
  The Cminor stack data block starts at offset 0 in Linear,
  but at offset [fe.(fe_stack_data)] in Mach.
  Operations and addressing mode that are relative to the stack pointer
  must therefore be offset by [fe.(fe_stack_data)] to preserve their
  behaviour. *)

Definition transl_op (fe: frame_env) (op: operation) :=
  shift_stack_operation (Int.repr fe.(fe_stack_data)) op.

Definition transl_addr (fe: frame_env) (addr: addressing) :=
  shift_stack_addressing (Int.repr fe.(fe_stack_data)) addr.

(** Translation of an annotation argument. *)

Definition transl_annot_param (fe: frame_env) (l: loc) : annot_param :=
  match l with
  | R r => APreg r
  | S Local ofs ty => APstack (chunk_of_type ty) (offset_of_index fe (FI_local ofs ty))
  | S _ _ _ => APstack Mint32 (-1)     (**r never happens *)
  end.


(** Translation of a Linear instruction.  Prepends the corresponding
  Mach instructions to the given list of instructions.
  [Lgetstack] and [Lsetstack] moves between registers and stack slots
  are turned into [Mgetstack], [Mgetparent] or [Msetstack] instructions
  at offsets determined by the frame environment.
  Instructions and addressing modes are modified as described previously.
  Code to restore the values of callee-save registers is inserted
  before the function returns. *)

Definition transl_instr
    (fe: frame_env) (i: Linear.instruction) (k: Mach.code) : Mach.code :=
  match i with
  | Lgetstack sl ofs ty r =>
      match sl with
      | Local =>
          Mgetstack (Int.repr (offset_of_index fe (FI_local ofs ty))) ty r :: k
      | Incoming =>
          Mgetparam (Int.repr (offset_of_index fe (FI_arg ofs ty))) ty r :: k
      | Outgoing =>
          Mgetstack (Int.repr (offset_of_index fe (FI_arg ofs ty))) ty r :: k
      end
  | Lsetstack r sl ofs ty =>
      match sl with
      | Local =>
          Msetstack r (Int.repr (offset_of_index fe (FI_local ofs ty))) ty :: k
      | Incoming =>
          k (* should not happen *)
      | Outgoing =>
          Msetstack r (Int.repr (offset_of_index fe (FI_arg ofs ty))) ty :: k
      end
  | Lop op args res =>
      Mop (transl_op fe op) args res :: k
  | Lload chunk addr args dst =>
      Mload chunk (transl_addr fe addr) args dst :: k
  | Lstore chunk addr args src =>
      Mstore chunk (transl_addr fe addr) args src :: k
  | Lcall sig ros =>
      Mcall sig ros :: k
  | Ltailcall sig ros =>
      restore_callee_save fe
        (Mtailcall sig ros :: k)
  | Lbuiltin ef args dst =>
      Mbuiltin ef args dst :: k
  | Lannot ef args =>
      Mannot ef (map (transl_annot_param fe) args) :: k
  | Llabel lbl =>
      Mlabel lbl :: k
  | Lgoto lbl =>
      Mgoto lbl :: k
  | Lcond cond args lbl =>
      Mcond cond args lbl :: k
  | Ljumptable arg tbl =>
      Mjumptable arg tbl :: k
  | Lreturn =>
      restore_callee_save fe
        (Mreturn :: k)
  end.

(** Translation of a function.  Code that saves the values of used
  callee-save registers is inserted at function entry, followed
  by the translation of the function body.

  Subtle point: the compiler must check that the frame is no
  larger than [Int.max_unsigned] bytes, otherwise arithmetic overflows
  could occur during frame accesses using unsigned machine integers as
  offsets. *)

Definition transl_code
    (fe: frame_env) (il: list Linear.instruction) : Mach.code :=
  list_fold_right (transl_instr fe) il nil.

Definition transl_body (f: Linear.function) (fe: frame_env) :=
  save_callee_save fe (transl_code fe f.(Linear.fn_code)).

Open Local Scope string_scope.

Definition transf_function (f: Linear.function) : res Mach.function :=
  let fe := make_env (function_bounds f) in
  if negb (wt_function f) then
    Error (msg "Ill-formed Linear code")
  else if zlt Int.max_unsigned fe.(fe_size) then
    Error (msg "Too many spilled variables, stack size exceeded")
  else
    OK (Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Int.repr fe.(fe_ofs_link))
         (Int.repr fe.(fe_ofs_retaddr))).

Definition transf_fundef (f: Linear.fundef) : res Mach.fundef :=
  AST.transf_partial_fundef transf_function f.

Definition transf_program (p: Linear.program) : res Mach.program :=
  transform_partial_program transf_fundef p.

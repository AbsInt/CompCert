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

Require Import Coqlib Errors.
Require Import Integers AST.
Require Import Op Locations Linear Mach.
Require Import Bounds Conventions Stacklayout Lineartyping.

(** * Layout of activation records *)

(** The machine- and ABI-dependent aspects of the layout are defined
  in module [Stacklayout]. *)

(** Offsets (in bytes) corresponding to stack slots. *)

Definition offset_local (fe: frame_env) (x: Z) := fe.(fe_ofs_local) + 4 * x.

Definition offset_arg (x: Z) := fe_ofs_arg + 4 * x.

(** [save_callee_save rl ofs k] adds before [k] the instructions that
  store in the frame the values of callee-save registers [rl],
  starting at offset [ofs]. *)

Fixpoint save_callee_save_rec (rl: list mreg) (ofs: Z) (k: Mach.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      Msetstack r (Ptrofs.repr ofs1) ty :: save_callee_save_rec rl (ofs1 + sz) k
  end.

Definition save_callee_save (fe: frame_env) (k: Mach.code) :=
  save_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

(** [restore_callee_save fe k] adds before [k] the instructions that
  re-load from the frame the values of callee-save registers used by the
  current function, restoring these registers to their initial values. *)

Fixpoint restore_callee_save_rec (rl: list mreg) (ofs: Z) (k: Mach.code) :=
  match rl with
  | nil => k
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let ofs1 := align ofs sz in
      Mgetstack (Ptrofs.repr ofs1) ty r :: restore_callee_save_rec rl (ofs1 + sz) k
  end.

Definition restore_callee_save (fe: frame_env) (k: Mach.code) :=
  restore_callee_save_rec fe.(fe_used_callee_save) fe.(fe_ofs_callee_save) k.

(** * Code transformation. *)

(** Translation of operations and addressing mode.
  The Cminor stack data block starts at offset 0 in Linear,
  but at offset [fe.(fe_stack_data)] in Mach.
  Operations and addressing mode that are relative to the stack pointer
  must therefore be offset by [fe.(fe_stack_data)] to preserve their
  behaviour. *)

Definition transl_op (fe: frame_env) (op: operation) :=
  shift_stack_operation fe.(fe_stack_data) op.

Definition transl_addr (fe: frame_env) (addr: addressing) :=
  shift_stack_addressing fe.(fe_stack_data) addr.

(** Translation of a builtin argument. *)

Fixpoint transl_builtin_arg (fe: frame_env) (a: builtin_arg loc) : builtin_arg mreg :=
  match a with
  | BA (R r) => BA r
  | BA (S Local ofs ty) =>
      BA_loadstack (chunk_of_type ty) (Ptrofs.repr (offset_local fe ofs))
  | BA (S _ _ _) => BA_int Int.zero  (**r never happens *)
  | BA_int n => BA_int n
  | BA_long n => BA_long n
  | BA_float n => BA_float n
  | BA_single n => BA_single n
  | BA_loadstack chunk ofs =>
      BA_loadstack chunk (Ptrofs.add ofs (Ptrofs.repr fe.(fe_stack_data)))
  | BA_addrstack ofs =>
      BA_addrstack (Ptrofs.add ofs (Ptrofs.repr fe.(fe_stack_data)))
  | BA_loadglobal chunk id ofs => BA_loadglobal chunk id ofs
  | BA_addrglobal id ofs => BA_addrglobal id ofs
  | BA_splitlong hi lo =>
      BA_splitlong (transl_builtin_arg fe hi) (transl_builtin_arg fe lo)
  | BA_addptr a1 a2 =>
      BA_addptr (transl_builtin_arg fe a1) (transl_builtin_arg fe a2)
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
          Mgetstack (Ptrofs.repr (offset_local fe ofs)) ty r :: k
      | Incoming =>
          Mgetparam (Ptrofs.repr (offset_arg ofs)) ty r :: k
      | Outgoing =>
          Mgetstack (Ptrofs.repr (offset_arg ofs)) ty r :: k
      end
  | Lsetstack r sl ofs ty =>
      match sl with
      | Local =>
          Msetstack r (Ptrofs.repr (offset_local fe ofs)) ty :: k
      | Incoming =>
          k (* should not happen *)
      | Outgoing =>
          Msetstack r (Ptrofs.repr (offset_arg ofs)) ty :: k
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
      restore_callee_save fe (Mtailcall sig ros :: k)
  | Lbuiltin ef args dst =>
      Mbuiltin ef (map (transl_builtin_arg fe) args) dst :: k
  | Llabel lbl =>
      Mlabel lbl :: k
  | Lgoto lbl =>
      Mgoto lbl :: k
  | Lcond cond args lbl =>
      Mcond cond args lbl :: k
  | Ljumptable arg tbl =>
      Mjumptable arg tbl :: k
  | Lreturn =>
      restore_callee_save fe (Mreturn :: k)
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

Local Open Scope string_scope.

Definition transf_function (f: Linear.function) : res Mach.function :=
  let fe := make_env (function_bounds f) in
  if negb (wt_function f) then
    Error (msg "Ill-formed Linear code")
  else if zlt Ptrofs.max_unsigned fe.(fe_size) then
    Error (msg "Too many spilled variables, stack size exceeded")
  else
    OK (Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr))).

Definition transf_fundef (f: Linear.fundef) : res Mach.fundef :=
  AST.transf_partial_fundef transf_function f.

Definition transf_program (p: Linear.program) : res Mach.program :=
  transform_partial_program transf_fundef p.

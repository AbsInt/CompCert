(** Layout of activation records; translation from Linear to Mach. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import RTL.
Require Import Locations.
Require Import Linear.
Require Import Lineartyping.
Require Import Mach.
Require Import Conventions.

(** * Layout of activation records *)

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- 24 reserved bytes.  The first 4 bytes hold the back pointer to the
  activation record of the caller.  We use the 4 bytes at offset 12
  to store the return address.  (These are reserved by the PowerPC
  application binary interface.)  The remaining bytes are unused.
- Space for outgoing arguments to function calls.
- Local stack slots of integer type.
- Saved values of integer callee-save registers used by the function.
- One word of padding, if necessary to align the following data
  on a 8-byte boundary.
- Local stack slots of float type.
- Saved values of float callee-save registers used by the function.
- Space for the stack-allocated data declared in Cminor.

To facilitate some of the proofs, the Cminor stack-allocated data
starts at offset 0; the preceding areas in the activation record
therefore have negative offsets.  This part (with negative offsets)
is called the ``frame'' (see the [Machabstr] semantics for the Mach
language), by opposition with the ``Cminor stack data'' which is the part
with positive offsets.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)

Record frame_env : Set := mk_frame_env {
  fe_size: Z;
  fe_ofs_int_local: Z;
  fe_ofs_int_callee_save: Z;
  fe_num_int_callee_save: Z;
  fe_ofs_float_local: Z;
  fe_ofs_float_callee_save: Z;
  fe_num_float_callee_save: Z
}.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition make_env (b: bounds) :=
  let oil := 4 * b.(bound_outgoing) in              (* integer locals *)
  let oics := oil + 4 * b.(bound_int_local) in (* integer callee-saves *)
  let oendi := oics + 4 * b.(bound_int_callee_save) in
  let ofl := align oendi 8 in       (* float locals *)
  let ofcs := ofl + 8 * b.(bound_float_local) in (* float callee-saves *)
  let sz := ofcs + 8 * b.(bound_float_callee_save) in (* total frame size *)
  mk_frame_env sz oil oics b.(bound_int_callee_save)
                  ofl ofcs b.(bound_float_callee_save).

(** Computation the frame offset for the given component of the frame.
  The component is expressed by the following [frame_index] sum type. *)

Inductive frame_index: Set :=
  | FI_local: Z -> typ -> frame_index
  | FI_arg: Z -> typ -> frame_index
  | FI_saved_int: Z -> frame_index
  | FI_saved_float: Z -> frame_index.

Definition offset_of_index (fe: frame_env) (idx: frame_index) :=
  match idx with
  | FI_local x Tint => fe.(fe_ofs_int_local) + 4 * x
  | FI_local x Tfloat => fe.(fe_ofs_float_local) + 8 * x
  | FI_arg x ty => 4 * x
  | FI_saved_int x => fe.(fe_ofs_int_callee_save) + 4 * x
  | FI_saved_float x => fe.(fe_ofs_float_callee_save) + 8 * x
  end.

(** * Saving and restoring callee-save registers *)

(** [save_callee_save fe k] adds before [k] the instructions that
  store in the frame the values of callee-save registers used by the
  current function. *)

Definition save_int_callee_save (fe: frame_env) (cs: mreg) (k: Mach.code) :=
  let i := index_int_callee_save cs in
  if zlt i fe.(fe_num_int_callee_save)
  then Msetstack cs (Int.repr (offset_of_index fe (FI_saved_int i))) Tint :: k
  else k.

Definition save_float_callee_save (fe: frame_env) (cs: mreg) (k: Mach.code) :=
  let i := index_float_callee_save cs in
  if zlt i fe.(fe_num_float_callee_save)
  then Msetstack cs (Int.repr (offset_of_index fe (FI_saved_float i))) Tfloat :: k
  else k.

Definition save_callee_save (fe: frame_env) (k: Mach.code) :=
  List.fold_right (save_int_callee_save fe)
    (List.fold_right (save_float_callee_save fe) k float_callee_save_regs)
    int_callee_save_regs.

(** [restore_callee_save fe k] adds before [k] the instructions that
  re-load from the frame the values of callee-save registers used by the
  current function, restoring these registers to their initial values. *)

Definition restore_int_callee_save (fe: frame_env) (cs: mreg) (k: Mach.code) :=
  let i := index_int_callee_save cs in
  if zlt i fe.(fe_num_int_callee_save)
  then Mgetstack (Int.repr (offset_of_index fe (FI_saved_int i))) Tint cs :: k
  else k.

Definition restore_float_callee_save (fe: frame_env) (cs: mreg) (k: Mach.code) :=
  let i := index_float_callee_save cs in
  if zlt i fe.(fe_num_float_callee_save)
  then Mgetstack (Int.repr (offset_of_index fe (FI_saved_float i))) Tfloat cs :: k
  else k.

Definition restore_callee_save (fe: frame_env) (k: Mach.code) :=
  List.fold_right (restore_int_callee_save fe)
    (List.fold_right (restore_float_callee_save fe) k float_callee_save_regs)
    int_callee_save_regs.

(** * Code transformation. *)

(** Translation of operations and addressing mode.
  In Linear, the stack pointer has offset 0, i.e. points to the
  beginning of the Cminor stack data block.  In Mach, the stack
  pointer points to the bottom of the activation record,
  at offset [- fe.(fe_size)] where [fe] is the frame environment.
  Operations and addressing mode that are relative to the stack pointer
  must therefore be offset by [fe.(fe_size)] to preserve their
  behaviour. *)

Definition transl_op (fe: frame_env) (op: operation) :=
  match op with
  | Oaddrstack ofs => Oaddrstack (Int.add (Int.repr fe.(fe_size)) ofs)
  | _ => op
  end.

Definition transl_addr (fe: frame_env) (addr: addressing) :=
  match addr with
  | Ainstack ofs => Ainstack (Int.add (Int.repr fe.(fe_size)) ofs)
  | _ => addr
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
  | Lgetstack s r =>
      match s with
      | Local ofs ty =>
          Mgetstack (Int.repr (offset_of_index fe (FI_local ofs ty))) ty r :: k
      | Incoming ofs ty =>
          Mgetparam (Int.repr (offset_of_index fe (FI_arg ofs ty))) ty r :: k
      | Outgoing ofs ty =>
          Mgetstack (Int.repr (offset_of_index fe (FI_arg ofs ty))) ty r :: k
      end
  | Lsetstack r s =>
      match s with
      | Local ofs ty =>
          Msetstack r (Int.repr (offset_of_index fe (FI_local ofs ty))) ty :: k
      | Incoming ofs ty =>
          k (* should not happen *)
      | Outgoing ofs ty =>
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
  | Lalloc =>
      Malloc :: k
  | Llabel lbl =>
      Mlabel lbl :: k
  | Lgoto lbl =>
      Mgoto lbl :: k
  | Lcond cond args lbl =>
      Mcond cond args lbl :: k
  | Lreturn =>
      restore_callee_save fe (Mreturn :: k)
  end.

(** Translation of a function.  Code that saves the values of used
  callee-save registers is inserted at function entry, followed
  by the translation of the function body.

  Subtle point: the compiler must check that the frame is no
  larger than [- Int.min_signed] bytes, otherwise arithmetic overflows
  could occur during frame accesses using signed machine integers as
  offsets. *)

Definition transl_code
    (fe: frame_env) (il: list Linear.instruction) : Mach.code :=
  List.fold_right (transl_instr fe) nil il.

Definition transl_body (f: Linear.function) (fe: frame_env) :=
  save_callee_save fe (transl_code fe f.(Linear.fn_code)).

Definition transf_function (f: Linear.function) : option Mach.function :=
  let fe := make_env (function_bounds f) in
  if zlt f.(Linear.fn_stacksize) 0 then None else
  if zlt (- Int.min_signed) fe.(fe_size) then None else
  Some (Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         f.(Linear.fn_stacksize)
         fe.(fe_size)).

Definition transf_fundef (f: Linear.fundef) : option Mach.fundef :=
  AST.transf_partial_fundef transf_function f.

Definition transf_program (p: Linear.program) : option Mach.program :=
  transform_partial_program transf_fundef p.

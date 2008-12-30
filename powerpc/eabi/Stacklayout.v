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

(** Machine- and ABI-dependent layout information for activation records. *)

Require Import Coqlib.
Require Import Bounds.

(** In the PowerPC/EABI application binary interface,
  the general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- 8 reserved bytes.  The first 4 bytes hold the back pointer to the
  activation record of the caller.  The next 4 bytes hold the
  return address.
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
is called the ``frame'', by opposition with the ``Cminor stack data''
which is the part with positive offsets.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)

Definition fe_ofs_arg := 8.

Record frame_env : Set := mk_frame_env {
  fe_size: Z;
  fe_ofs_link: Z;
  fe_ofs_retaddr: Z;
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
  let oil := 8 + 4 * b.(bound_outgoing) in    (* integer locals *)
  let oics := oil + 4 * b.(bound_int_local) in (* integer callee-saves *)
  let oendi := oics + 4 * b.(bound_int_callee_save) in
  let ofl := align oendi 8 in       (* float locals *)
  let ofcs := ofl + 8 * b.(bound_float_local) in (* float callee-saves *)
  let sz := ofcs + 8 * b.(bound_float_callee_save) in (* total frame size *)
  mk_frame_env sz 0 4
                  oil oics b.(bound_int_callee_save)
                  ofl ofcs b.(bound_float_callee_save).


Remark align_float_part:
  forall b,
  8 + 4 * bound_outgoing b + 4 * bound_int_local b + 4 * bound_int_callee_save b <=
  align (8 + 4 * bound_outgoing b + 4 * bound_int_local b + 4 * bound_int_callee_save b) 8.
Proof.
  intros. apply align_le. omega.
Qed.


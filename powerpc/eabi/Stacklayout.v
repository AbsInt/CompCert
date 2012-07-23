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
  activation record of the caller.  The next 4 bytes are reserved
  for called functions to store their return addresses.
  Since we would rather store our return address in our own
  frame, we will not use these 4 bytes, and just reserve them.
- Space for outgoing arguments to function calls.
- Local stack slots of integer type.
- Saved return address into caller.
- Saved values of integer callee-save registers used by the function.
- One word of padding, if necessary to align the following data
  on a 8-byte boundary.
- Local stack slots of float type.
- Saved values of float callee-save registers used by the function.
- Space for the stack-allocated data declared in Cminor.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)

Definition fe_ofs_arg := 8.

Record frame_env : Type := mk_frame_env {
  fe_size: Z;
  fe_ofs_link: Z;
  fe_ofs_retaddr: Z;
  fe_ofs_int_local: Z;
  fe_ofs_int_callee_save: Z;
  fe_num_int_callee_save: Z;
  fe_ofs_float_local: Z;
  fe_ofs_float_callee_save: Z;
  fe_num_float_callee_save: Z;
  fe_stack_data: Z
}.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition make_env (b: bounds) :=
  let oil := 8 + 4 * b.(bound_outgoing) in    (* integer locals *)
  let ora := oil + 4 * b.(bound_int_local) in (* saved return address *)
  let oics := ora + 4 in            (* integer callee-saves *)
  let oendi := oics + 4 * b.(bound_int_callee_save) in
  let ofl := align oendi 8 in       (* float locals *)
  let ofcs := ofl + 8 * b.(bound_float_local) in (* float callee-saves *)
  let ostkdata := ofcs + 8 * b.(bound_float_callee_save) in (* stack data *)
  let sz := align (ostkdata + b.(bound_stack_data)) 16 in
  mk_frame_env sz 0 ora
                  oil oics b.(bound_int_callee_save)
                  ofl ofcs b.(bound_float_callee_save)
                  ostkdata.

(** Separation property *)

Remark frame_env_separated:
  forall b,
  let fe := make_env b in
  0 <= fe.(fe_ofs_link)
  /\ fe.(fe_ofs_link) + 4 <= fe_ofs_arg
  /\ fe_ofs_arg + 4 * b.(bound_outgoing) <= fe.(fe_ofs_int_local)
  /\ fe.(fe_ofs_int_local) + 4 * b.(bound_int_local) <= fe.(fe_ofs_retaddr)
  /\ fe.(fe_ofs_retaddr) + 4 <= fe.(fe_ofs_int_callee_save)
  /\ fe.(fe_ofs_int_callee_save) + 4 * b.(bound_int_callee_save) <= fe.(fe_ofs_float_local)
  /\ fe.(fe_ofs_float_local) + 8 * b.(bound_float_local) <= fe.(fe_ofs_float_callee_save)
  /\ fe.(fe_ofs_float_callee_save) + 8 * b.(bound_float_callee_save) <= fe.(fe_stack_data)
  /\ fe.(fe_stack_data) + b.(bound_stack_data) <= fe.(fe_size).
Proof.
  intros.
  generalize (align_le (fe.(fe_ofs_int_callee_save) + 4 * b.(bound_int_callee_save)) 8 (refl_equal _)).
  generalize (align_le (fe.(fe_stack_data) + b.(bound_stack_data)) 16 (refl_equal _)).
  unfold fe, make_env, fe_size, fe_ofs_link, fe_ofs_retaddr,
    fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_num_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save, fe_num_float_callee_save,
    fe_stack_data, fe_ofs_arg.
  intros.
  generalize (bound_int_local_pos b); intro;
  generalize (bound_float_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (bound_stack_data_pos b); intro.
  omega.
Qed.

(** Alignment property *)

Remark frame_env_aligned:
  forall b,
  let fe := make_env b in
  (4 | fe.(fe_ofs_link))
  /\ (4 | fe.(fe_ofs_int_local))
  /\ (4 | fe.(fe_ofs_int_callee_save))
  /\ (8 | fe.(fe_ofs_float_local))
  /\ (8 | fe.(fe_ofs_float_callee_save))
  /\ (4 | fe.(fe_ofs_retaddr))
  /\ (8 | fe.(fe_stack_data))
  /\ (16 | fe.(fe_size)).
Proof.
  intros.
  unfold fe, make_env, fe_size, fe_ofs_link, fe_ofs_retaddr,
    fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_num_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save, fe_num_float_callee_save,
    fe_stack_data.
  set (x1 := 8 + 4 * bound_outgoing b).
  assert (4 | x1). unfold x1; apply Zdivide_plus_r. exists 2; auto. exists (bound_outgoing b); ring.
  set (x2 := x1 + 4 * bound_int_local b).
  assert (4 | x2). unfold x2; apply Zdivide_plus_r; auto. exists (bound_int_local b); ring.
  set (x3 := x2 + 4).
  assert (4 | x3). unfold x3; apply Zdivide_plus_r; auto. exists 1; auto.
  set (x4 := align (x3 + 4 * bound_int_callee_save b) 8).
  assert (8 | x4). unfold x4. apply align_divides. omega.
  set (x5 := x4 + 8 * bound_float_local b).
  assert (8 | x5). unfold x5. apply Zdivide_plus_r; auto. exists (bound_float_local b); ring.
  set (x6 := x5 + 8 * bound_float_callee_save b).
  assert (8 | x6).
    unfold x6. apply Zdivide_plus_r; auto. exists (bound_float_callee_save b); ring.
  set (x7 := align (x6 + bound_stack_data b) 16).
  assert (16 | x7). unfold x7; apply align_divides. omega.
  intuition.
Qed.

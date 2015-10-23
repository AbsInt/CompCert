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

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Local stack slots.
- Saved values of integer callee-save registers used by the function.
- Saved values of float callee-save registers used by the function.
- Saved return address into caller.
- Pointer to activation record of the caller.
- Space for the stack-allocated data declared in Cminor.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)

Definition fe_ofs_arg := 0.

Record frame_env : Type := mk_frame_env {
  fe_size: Z;
  fe_ofs_link: Z;
  fe_ofs_retaddr: Z;
  fe_ofs_local: Z;
  fe_ofs_int_callee_save: Z;
  fe_num_int_callee_save: Z;
  fe_ofs_float_callee_save: Z;
  fe_num_float_callee_save: Z;
  fe_stack_data: Z
}.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition make_env (b: bounds) :=
  let ol := align (4 * b.(bound_outgoing)) 8 in    (* locals *)
  let oics := ol + 4 * b.(bound_local) in (* integer callee-saves *)
  let oendi := oics + 4 * b.(bound_int_callee_save) in
  let ofcs := align oendi 8 in       (* float callee-saves *)
  let ora := ofcs + 8 * b.(bound_float_callee_save) in (* retaddr *)
  let olink := ora + 4 in (* back link *)
  let ostkdata := olink + 4 in (* stack data *)
  let sz := align (ostkdata + b.(bound_stack_data)) 8 in
  mk_frame_env sz olink ora ol
                  oics b.(bound_int_callee_save)
                  ofcs b.(bound_float_callee_save)
                  ostkdata.

(** Separation property *)

Remark frame_env_separated:
  forall b,
  let fe := make_env b in
  0 <= fe_ofs_arg
  /\ fe_ofs_arg + 4 * b.(bound_outgoing) <= fe.(fe_ofs_local)
  /\ fe.(fe_ofs_local) + 4 * b.(bound_local) <= fe.(fe_ofs_int_callee_save)
  /\ fe.(fe_ofs_int_callee_save) + 4 * b.(bound_int_callee_save) <= fe.(fe_ofs_float_callee_save)
  /\ fe.(fe_ofs_float_callee_save) + 8 * b.(bound_float_callee_save) <= fe.(fe_ofs_retaddr)
  /\ fe.(fe_ofs_retaddr) + 4 <= fe.(fe_ofs_link)
  /\ fe.(fe_ofs_link) + 4 <= fe.(fe_stack_data)
  /\ fe.(fe_stack_data) + b.(bound_stack_data) <= fe.(fe_size).
Proof.
  intros.
  generalize (align_le (4 * bound_outgoing b) 8 (refl_equal)).
  generalize (align_le (fe_ofs_int_callee_save fe + 4 * b.(bound_int_callee_save)) 8 (refl_equal _)).
  generalize (align_le (fe_stack_data fe + b.(bound_stack_data)) 8 (refl_equal)).
  unfold fe, make_env, fe_size, fe_ofs_link, fe_ofs_retaddr,
    fe_ofs_local, fe_ofs_int_callee_save, fe_num_int_callee_save,
    fe_ofs_float_callee_save, fe_num_float_callee_save,
    fe_stack_data, fe_ofs_arg.
  intros.
  generalize (bound_local_pos b); intro;
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
  /\ (8 | fe.(fe_ofs_local))
  /\ (4 | fe.(fe_ofs_int_callee_save))
  /\ (8 | fe.(fe_ofs_float_callee_save))
  /\ (4 | fe.(fe_ofs_retaddr))
  /\ (8 | fe.(fe_stack_data))
  /\ (8 | fe.(fe_size)).
Proof.
  intros.
  unfold fe, make_env, fe_size, fe_ofs_link, fe_ofs_retaddr,
    fe_ofs_local, fe_ofs_int_callee_save, fe_num_int_callee_save,
    fe_ofs_float_callee_save, fe_num_float_callee_save,
    fe_stack_data.
  set (x1 := 4 * bound_outgoing b).
  assert (4 | x1). unfold x1; exists (bound_outgoing b); ring.
  set (x2 := align x1 8).
  assert (8 | x2). apply align_divides. omega.
  set (x3 := x2 + 4 * bound_local b).
  assert (4 | x3). apply Zdivide_plus_r. apply Zdivides_trans with 8; auto. exists 2; auto.
  exists (bound_local b); ring.
  set (x4 := align (x3 + 4 * bound_int_callee_save b) 8).
  assert (8 | x4). apply align_divides. omega.
  set (x5 := x4 + 8 * bound_float_callee_save b).
  assert (8 | x5). apply Zdivide_plus_r; auto. exists (bound_float_callee_save b); ring.
  assert (4 | x5). apply Zdivides_trans with 8; auto. exists 2; auto.
  set (x6 := x5 + 4).
  assert (4 | x6). apply Zdivide_plus_r; auto. exists 1; auto.
  set (x7 := x6 + 4).
  assert (8 | x7). unfold x7, x6. replace (x5 + 4 + 4) with (x5 + 8) by omega.
  apply Zdivide_plus_r; auto. exists 1; auto.
  set (x8 := align (x7 + bound_stack_data b) 8).
  assert (8 | x8). apply align_divides. omega.
  tauto.
Qed.

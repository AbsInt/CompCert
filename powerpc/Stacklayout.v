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
Require Import Memory Separation.
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
- Local stack slots.
- Saved values of callee-save registers used by the function.
- Space for the stack-allocated data declared in Cminor.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)

Definition fe_ofs_arg := 8.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition make_env (b: bounds) :=
  let ol := align (8 + 4 * b.(bound_outgoing)) 8 in    (* locals *)
  let ora := ol + 4 * b.(bound_local) in (* saved return address *)
  let ocs := ora + 4 in            (* callee-saves *)
  let oendcs := size_callee_save_area b ocs in
  let ostkdata := align oendcs 8 in (* stack data *)
  let sz := align (ostkdata + b.(bound_stack_data)) 16 in
  {| fe_size := sz;
     fe_ofs_link := 0;
     fe_ofs_retaddr := ora;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := b.(used_callee_save) |}.

(** Separation property *)

Local Open Scope sep_scope.

Lemma frame_env_separated:
  forall b sp m P,
  let fe := make_env b in
  m |= range sp 0 (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
  m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
       ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
       ** range sp (fe_ofs_link fe) (fe_ofs_link fe + 4)
       ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + 4)
       ** range sp (fe_ofs_callee_save fe) (size_callee_save_area b (fe_ofs_callee_save fe))
       ** P.
Proof.
Local Opaque Z.add Z.mul sepconj range.
  intros; simpl.
  set (ol := align (8 + 4 * b.(bound_outgoing)) 8).
  set (ora := ol + 4 * b.(bound_local)).
  set (ocs := ora + 4).
  set (oendcs := size_callee_save_area b ocs).
  set (ostkdata := align oendcs 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  unfold fe_ofs_arg.
  assert (8 + 4 * b.(bound_outgoing) <= ol) by (apply align_le; omega).
  assert (ol <= ora) by (unfold ora; omega).
  assert (ora <= ocs) by (unfold ocs; omega).
  assert (ocs <= oendcs) by (apply size_callee_save_area_incr).
  assert (oendcs <= ostkdata) by (apply align_le; omega).
(* Reorder as:
     back link
     outgoing
     locals
     retaddr
     callee-save *)
  rewrite sep_swap3.
(* Apply range_split and range_split2 repeatedly *)
  apply range_drop_right with 8. omega.
  apply range_split. omega.
  apply range_split_2. fold ol; omega. omega.
  apply range_split. omega.
  apply range_split. omega.
  apply range_drop_right with ostkdata. omega.
  eapply sep_drop2. eexact H.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (ol := align (8 + 4 * b.(bound_outgoing)) 8).
  set (ora := ol + 4 * b.(bound_local)).
  set (ocs := ora + 4).
  set (oendcs := size_callee_save_area b ocs).
  set (ostkdata := align oendcs 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  unfold fe_ofs_arg.
  assert (8 + 4 * b.(bound_outgoing) <= ol) by (apply align_le; omega).
  assert (ol <= ora) by (unfold ora; omega).
  assert (ora <= ocs) by (unfold ocs; omega).
  assert (ocs <= oendcs) by (apply size_callee_save_area_incr).
  assert (oendcs <= ostkdata) by (apply align_le; omega).
  split. omega. apply align_le. omega.
Qed.

Lemma frame_env_aligned:
  forall b,
  let fe := make_env b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
  /\ (4 | fe_ofs_link fe)
  /\ (4 | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (ol := align (8 + 4 * b.(bound_outgoing)) 8).
  set (ora := ol + 4 * b.(bound_local)).
  set (ocs := ora + 4).
  set (oendcs := size_callee_save_area b ocs).
  set (ostkdata := align oendcs 8).
  split. exists (fe_ofs_arg / 8); reflexivity.
  split. apply align_divides; omega.
  split. apply align_divides; omega.
  split. apply Z.divide_0_r.
  apply Z.divide_add_r.
    apply Z.divide_trans with 8. exists 2; auto. apply align_divides; omega.
    apply Z.divide_factor_l.
Qed.

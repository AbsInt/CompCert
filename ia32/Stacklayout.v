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

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Back link to parent frame
- Saved values of integer callee-save registers used by the function.
- Saved values of float callee-save registers used by the function.
- Local stack slots.
- Space for the stack-allocated data declared in Cminor
- Return address.
*)

Definition fe_ofs_arg := 0.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition make_env (b: bounds) : frame_env :=
  let olink := 4 * b.(bound_outgoing) in  (* back link *)
  let ocs := olink + 4 in                 (* callee-saves *)
  let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *)
  let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *)
  let oretaddr := align (ostkdata + b.(bound_stack_data)) 4 in (* return address *)
  let sz := oretaddr + 4 in (* total size *)
  {| fe_size := sz;
     fe_ofs_link := olink;
     fe_ofs_retaddr := oretaddr;
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
  set (olink := 4 * b.(bound_outgoing)).
  set (ocs := olink + 4).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) 4).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= olink) by (unfold olink; omega).
  assert (olink + 4 <= ocs) by (unfold ocs; omega).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
  assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; omega).
(* Reorder as:
     outgoing
     back link
     callee-save
     local
     retaddr *)
  rewrite sep_swap12.
  rewrite sep_swap23.
  rewrite sep_swap45.
  rewrite sep_swap34.
(* Apply range_split and range_split2 repeatedly *)
  unfold fe_ofs_arg.
  apply range_split. omega.
  apply range_split. omega.
  apply range_split_2. fold ol. omega. omega.
  apply range_drop_right with ostkdata. omega.
  rewrite sep_swap.
  apply range_drop_left with (ostkdata + bound_stack_data b). omega.
  rewrite sep_swap. 
  exact H.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (olink := 4 * b.(bound_outgoing)).
  set (ocs := olink + 4).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) 4).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= olink) by (unfold olink; omega).
  assert (olink + 4 <= ocs) by (unfold ocs; omega).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
  assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; omega).
  split. omega. omega. 
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
  set (olink := 4 * b.(bound_outgoing)).
  set (ocs := olink + 4).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) 4).
  split. apply Zdivide_0.
  split. apply align_divides; omega.
  split. apply align_divides; omega.
  split. apply Z.divide_factor_l.
  apply align_divides; omega.
Qed.

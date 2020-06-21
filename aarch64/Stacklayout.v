(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Machine- and ABI-dependent layout information for activation records. *)

Require Import Coqlib.
Require Import AST Memory Separation.
Require Import Bounds.

Local Open Scope sep_scope.

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Back link to parent frame
- Return address
- Saved values of callee-save registers used by the function.
- Local stack slots.
- Space for the stack-allocated data declared in Cminor.

The stack pointer is kept 16-aligned.
*)

Definition fe_ofs_arg := 0.

Definition make_env (b: bounds) : frame_env :=
  let olink := align (4 * b.(bound_outgoing)) 8 in  (* back link *)
  let oretaddr := olink + 8 in                      (* return address *)
  let ocs := oretaddr + 8 in                        (* callee-saves *)
  let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *)
  let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *)
  let sz := align (ostkdata + b.(bound_stack_data)) 16 in
  {| fe_size := sz;
     fe_ofs_link := olink;
     fe_ofs_retaddr := oretaddr;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := b.(used_callee_save) |}.

Lemma frame_env_separated:
  forall b sp m P,
  let fe := make_env b in
  m |= range sp 0 (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
  m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
       ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
       ** range sp (fe_ofs_link fe) (fe_ofs_link fe + size_chunk Mptr)
       ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + size_chunk Mptr)
       ** range sp (fe_ofs_callee_save fe) (size_callee_save_area b (fe_ofs_callee_save fe))
       ** P.
Proof.
Local Opaque Z.add Z.mul sepconj range.
  intros; simpl.
  set (olink := align (4 * b.(bound_outgoing)) 8).
  set (oretaddr := olink + 8).
  set (ocs := oretaddr + 8).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  change (size_chunk Mptr) with 8.
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= 4 * b.(bound_outgoing)) by lia.
  assert (4 * b.(bound_outgoing) <= olink) by (apply align_le; lia).
  assert (olink + 8 <= oretaddr) by (unfold oretaddr; lia).
  assert (oretaddr + 8 <= ocs) by (unfold ocs; lia).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; lia).
(* Reorder as:
     outgoing
     back link
     retaddr
     callee-save
     local *)
  rewrite sep_swap12.
  rewrite sep_swap23.
  rewrite sep_swap34.
  rewrite sep_swap45.
(* Apply range_split and range_split2 repeatedly *)
  unfold fe_ofs_arg.
  apply range_split_2. fold olink; lia. lia.
  apply range_split. lia.
  apply range_split. lia.
  apply range_split_2. fold ol. lia. lia.
  apply range_drop_right with ostkdata. lia.
  eapply sep_drop2. eexact H.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (olink := align (4 * b.(bound_outgoing)) 8).
  set (oretaddr := olink + 8).
  set (ocs := oretaddr + 8).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= 4 * b.(bound_outgoing)) by lia.
  assert (4 * b.(bound_outgoing) <= olink) by (apply align_le; lia).
  assert (olink + 8 <= oretaddr) by (unfold oretaddr; lia).
  assert (oretaddr + 8 <= ocs) by (unfold ocs; lia).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; lia).
  split. lia. apply align_le. lia. 
Qed.

Lemma frame_env_aligned:
  forall b,
  let fe := make_env b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
  /\ (align_chunk Mptr | fe_ofs_link fe)
  /\ (align_chunk Mptr | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (olink := align (4 * b.(bound_outgoing)) 8).
  set (oretaddr := olink + 8).
  set (ocs := oretaddr + 8).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  change (align_chunk Mptr) with 8.
  split. apply Z.divide_0_r.
  split. apply align_divides; lia.
  split. apply align_divides; lia.
  split. apply align_divides; lia.
  apply Z.divide_add_r. apply align_divides; lia. apply Z.divide_refl.
Qed.

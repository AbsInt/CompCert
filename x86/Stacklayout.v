(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
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
Require Archi.

Local Open Scope sep_scope.

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- For the Win64 ABI: 32 reserved bytes
- Space for outgoing arguments to function calls.
- Back link to parent frame
- Saved values of integer callee-save registers used by the function.
- Saved values of float callee-save registers used by the function.
- Local stack slots.
- Space for the stack-allocated data declared in Cminor
- Return address.
*)

Definition fe_ofs_arg := if Archi.win64 then 32 else 0.

Definition make_env (b: bounds) : frame_env :=
  let w := if Archi.ptr64 then 8 else 4 in
  let olink := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w in  (* back link *)
  let ocs := olink + w in                           (* callee-saves *)
  let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *)
  let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *)
  let oretaddr := align (ostkdata + b.(bound_stack_data)) w in (* return address *)
  let sz := oretaddr + w in (* total size *)
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
  set (w := if Archi.ptr64 then 8 else 4).
  set (olink := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
  replace (size_chunk Mptr) with w by (rewrite size_chunk_Mptr; auto).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; lia).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= fe_ofs_arg) by (unfold fe_ofs_arg; destruct Archi.win64; lia).
  assert (0 <= 4 * b.(bound_outgoing)) by lia.
  assert (fe_ofs_arg + 4 * b.(bound_outgoing) <= olink) by (apply align_le; lia).
  assert (olink + w <= ocs) by (unfold ocs; lia).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr).
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; lia).
  assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; lia).
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
  apply range_drop_left with 0. lia. 
  apply range_split_2. fold olink. lia. lia.
  apply range_split. lia.
  apply range_split_2. fold ol. lia. lia.
  apply range_drop_right with ostkdata. lia.
  rewrite sep_swap.
  apply range_drop_left with (ostkdata + bound_stack_data b). lia.
  rewrite sep_swap.
  exact H.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (olink := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; lia).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= fe_ofs_arg) by (unfold fe_ofs_arg; destruct Archi.win64; lia).
  assert (0 <= 4 * b.(bound_outgoing)) by lia.
  assert (fe_ofs_arg + 4 * b.(bound_outgoing) <= olink) by (apply align_le; lia).
  assert (olink + w <= ocs) by (unfold ocs; lia).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr).
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; lia).
  assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; lia).
  split. lia. lia.
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
  set (w := if Archi.ptr64 then 8 else 4).
  set (olink := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; lia).
  replace (align_chunk Mptr) with w by (rewrite align_chunk_Mptr; auto).
  split. exists (fe_ofs_arg / 8). unfold fe_ofs_arg; destruct Archi.win64; reflexivity.
  split. apply align_divides; lia.
  split. apply align_divides; lia.
  split. apply align_divides; lia.
  apply align_divides; lia.
Qed.

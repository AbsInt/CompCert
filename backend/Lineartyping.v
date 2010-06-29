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

(** Typing rules for Linear. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Memdata.
Require Import Op.
Require Import RTL.
Require Import Locations.
Require Import Linear.
Require Import Conventions.

(** The typing rules for Linear are similar to those for LTLin: we check
  that instructions receive the right number of arguments,
  and that the types of the argument and result registers agree
  with what the instruction expects.  Moreover, we  also
  enforces some correctness conditions on the offsets of stack slots
  accessed through [Lgetstack] and [Lsetstack] Linear instructions. *)

Section WT_INSTR.

Variable funct: function.

Definition slot_valid (s: slot) :=
  match s with
  | Local ofs ty => 0 <= ofs
  | Outgoing ofs ty => 0 <= ofs
  | Incoming ofs ty => In (S s) (loc_parameters funct.(fn_sig))
  end.

Definition slot_writable (s: slot) :=
  match s with
  | Local ofs ty => True
  | Outgoing ofs ty => True
  | Incoming ofs ty => False
  end.

Inductive wt_instr : instruction -> Prop :=
  | wt_Lgetstack:
      forall s r,
      slot_type s = mreg_type r ->
      slot_valid s ->
      wt_instr (Lgetstack s r)
  | wt_Lsetstack:
      forall s r,
      slot_type s = mreg_type r ->
      slot_valid s -> slot_writable s ->
      wt_instr (Lsetstack r s)
  | wt_Lopmove:
      forall r1 r,
      mreg_type r1 = mreg_type r ->
      wt_instr (Lop Omove (r1 :: nil) r)
  | wt_Lop:
      forall op args res,
      op <> Omove ->
      (List.map mreg_type args, mreg_type res) = type_of_operation op ->
      wt_instr (Lop op args res)
  | wt_Lload:
      forall chunk addr args dst,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type dst = type_of_chunk chunk ->
      wt_instr (Lload chunk addr args dst)
  | wt_Lstore:
      forall chunk addr args src,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type src = type_of_chunk chunk ->
      wt_instr (Lstore chunk addr args src)
  | wt_Lcall:
      forall sig ros,
      match ros with inl r => mreg_type r = Tint | _ => True end ->
      wt_instr (Lcall sig ros)
  | wt_Ltailcall:
      forall sig ros,
      tailcall_possible sig ->
      match ros with inl r => r = IT1 | _ => True end ->
      wt_instr (Ltailcall sig ros)
  | wt_Lbuiltin:
      forall ef args res,
      List.map mreg_type args = (ef_sig ef).(sig_args) ->
      mreg_type res = proj_sig_res (ef_sig ef) ->
      arity_ok (ef_sig ef).(sig_args) = true ->
      wt_instr (Lbuiltin ef args res)
  | wt_Llabel:
      forall lbl,
      wt_instr (Llabel lbl)
  | wt_Lgoto:
      forall lbl,
      wt_instr (Lgoto lbl)
  | wt_Lcond:
      forall cond args lbl,
      List.map mreg_type args = type_of_condition cond ->
      wt_instr (Lcond cond args lbl)
  | wt_Ljumptable:
      forall arg tbl,
      mreg_type arg = Tint ->
      list_length_z tbl * 4 <= Int.max_signed ->
      wt_instr (Ljumptable arg tbl)
  | wt_Lreturn: 
      wt_instr (Lreturn).

End WT_INSTR.

Definition wt_code (f: function) (c: code) : Prop :=
  forall instr, In instr c -> wt_instr f instr.

Definition wt_function (f: function) : Prop :=
  wt_code f f.(fn_code).

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program) : Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_fundef f.


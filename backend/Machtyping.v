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

(** Type system for the Mach intermediate language. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Mach.

(** * Typing rules *)

Inductive wt_instr : instruction -> Prop :=
  | wt_Mlabel:
     forall lbl,
     wt_instr (Mlabel lbl)
  | wt_Mgetstack:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Mgetstack ofs ty r)
  | wt_Msetstack:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Msetstack r ofs ty)
  | wt_Mgetparam:
     forall ofs ty r,
     mreg_type r = ty ->
     wt_instr (Mgetparam ofs ty r)
  | wt_Mopmove:
     forall r1 r,
     mreg_type r1 = mreg_type r ->
     wt_instr (Mop Omove (r1 :: nil) r)
  | wt_Mop:
     forall op args res,
      op <> Omove ->
      (List.map mreg_type args, mreg_type res) = type_of_operation op ->
      wt_instr (Mop op args res)
  | wt_Mload:
      forall chunk addr args dst,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type dst = type_of_chunk chunk ->
      wt_instr (Mload chunk addr args dst)
  | wt_Mstore:
      forall chunk addr args src,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type src = type_of_chunk chunk ->
      wt_instr (Mstore chunk addr args src)
  | wt_Mcall:
      forall sig ros,
      match ros with inl r => mreg_type r = Tint | inr s => True end ->
      wt_instr (Mcall sig ros)
  | wt_Mtailcall:
      forall sig ros,
      tailcall_possible sig ->
      match ros with inl r => mreg_type r = Tint | inr s => True end ->
      wt_instr (Mtailcall sig ros)
  | wt_Mbuiltin:
     forall ef args res,
      List.map mreg_type args = (ef_sig ef).(sig_args) ->
      mreg_type res = proj_sig_res (ef_sig ef) ->
      wt_instr (Mbuiltin ef args res)
  | wt_Mannot:
      forall ef args,
      ef_reloads ef = false ->
      wt_instr (Mannot ef args)
  | wt_Mgoto:
      forall lbl,
      wt_instr (Mgoto lbl)
  | wt_Mcond:
      forall cond args lbl,
      List.map mreg_type args = type_of_condition cond ->
      wt_instr (Mcond cond args lbl)
  | wt_Mjumptable:
      forall arg tbl,
      mreg_type arg = Tint ->
      list_length_z tbl * 4 <= Int.max_unsigned ->
      wt_instr (Mjumptable arg tbl)
  | wt_Mreturn: 
      wt_instr Mreturn.

Record wt_function (f: function) : Prop := mk_wt_function {
  wt_function_instrs:
    forall instr, In instr f.(fn_code) -> wt_instr instr;
  wt_function_stacksize:
    0 <= f.(fn_stacksize) <= Int.max_unsigned
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program) : Prop :=
  forall i f, In (i, Gfun f) (prog_defs p) -> wt_fundef f.

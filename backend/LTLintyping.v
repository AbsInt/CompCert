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

(** Typing rules for LTLin. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import Locations.
Require Import LTLin.
Require LTLtyping.
Require Import Conventions.

(** The following predicates define a type system for LTLin similar to that
  of LTL. *)

Section WT_INSTR.

Variable funsig: signature.

Inductive wt_instr : instruction -> Prop :=
  | wt_Lopmove:
      forall r1 r,
      Loc.type r1 = Loc.type r -> loc_acceptable r1 -> loc_acceptable r ->
      wt_instr (Lop Omove (r1 :: nil) r)
  | wt_Lop:
      forall op args res,
      op <> Omove ->
      (List.map Loc.type args, Loc.type res) = type_of_operation op ->
      locs_acceptable args -> loc_acceptable res ->
      wt_instr (Lop op args res)
  | wt_Lload:
      forall chunk addr args dst,
      List.map Loc.type args = type_of_addressing addr ->
      Loc.type dst = type_of_chunk chunk ->
      locs_acceptable args -> loc_acceptable dst ->
      wt_instr (Lload chunk addr args dst)
  | wt_Lstore:
      forall chunk addr args src,
      List.map Loc.type args = type_of_addressing addr ->
      Loc.type src = type_of_chunk chunk ->
      locs_acceptable args -> loc_acceptable src ->
      wt_instr (Lstore chunk addr args src)
  | wt_Lcall:
      forall sig ros args res,
      List.map Loc.type args = sig.(sig_args) ->
      Loc.type res = proj_sig_res sig ->
      LTLtyping.call_loc_acceptable sig ros ->
      locs_acceptable args -> loc_acceptable res ->
      wt_instr (Lcall sig ros args res)
  | wt_Ltailcall:
      forall sig ros args,
      List.map Loc.type args = sig.(sig_args) ->
      LTLtyping.call_loc_acceptable sig ros ->
      locs_acceptable args -> 
      sig.(sig_res) = funsig.(sig_res) ->
      tailcall_possible sig ->
      wt_instr (Ltailcall sig ros args)
  | wt_Lbuiltin:
      forall ef args res,
      List.map Loc.type args = (ef_sig ef).(sig_args) ->
      Loc.type res = proj_sig_res (ef_sig ef) ->
      arity_ok (ef_sig ef).(sig_args) = true \/ ef_reloads ef = false ->
      locs_acceptable args -> loc_acceptable res ->
       wt_instr (Lbuiltin ef args res)
  | wt_Llabel: forall lbl,
      wt_instr (Llabel lbl)
  | wt_Lgoto: forall lbl,
      wt_instr (Lgoto lbl)
  | wt_Lcond:
      forall cond args lbl,
      List.map Loc.type args = type_of_condition cond ->
      locs_acceptable args ->
      wt_instr (Lcond cond args lbl)
  | wt_Ljumptable:
      forall arg tbl,
      Loc.type arg = Tint ->
      loc_acceptable arg ->
      list_length_z tbl * 4 <= Int.max_unsigned ->
      wt_instr (Ljumptable arg tbl)
  | wt_Lreturn: 
      forall optres,
      option_map Loc.type optres = funsig.(sig_res) ->
      match optres with None => True | Some r => loc_acceptable r end ->
      wt_instr (Lreturn optres).

Definition wt_code (c: code) : Prop :=
  forall i, In i c -> wt_instr i.

End WT_INSTR.

Record wt_function (f: function): Prop :=
  mk_wt_function {
    wt_params:
      List.map Loc.type f.(fn_params) = f.(fn_sig).(sig_args);
    wt_acceptable:
      locs_acceptable f.(fn_params);
    wt_norepet:
      Loc.norepet f.(fn_params);
    wt_instrs:
      wt_code f.(fn_sig) f.(fn_code)
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program): Prop :=
  forall i f, In (i, Gfun f) (prog_defs p) -> wt_fundef f.

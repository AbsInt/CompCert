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

(* Live range splitting over RTL *)

open Camlcoq
open Coqlib
open Maps
open Kildall
open Registers
open RTL

(* We represent live ranges by the following unification variables.
   Live range inference manipulates only variable live ranges.
   Code rewriting assigns fresh RTL registers to live ranges. *)

type live_range = { source: reg; mutable kind: live_range_kind }

and live_range_kind =
  | Link of live_range
  | Var
  | Reg of reg

let new_range r = { source = r; kind = Var }

let rec repr lr =
  match lr.kind with
  | Link lr' -> let lr'' = repr lr' in lr.kind <- Link lr''; lr''
  | _ -> lr

let same_range lr1 lr2 =
  lr1 == lr2 || (* quick test for speed *)
  repr lr1 == repr lr2 (* the real test *)

let unify lr1 lr2 =
  let lr1 = repr lr1 and lr2 = repr lr2 in
  if lr1 != lr2 then begin
    match lr1.kind, lr2.kind with
    | Var, _ -> lr1.kind <- Link lr2
    | _, Var -> lr2.kind <- Link lr1
    | _, _   -> assert false
  end

let reg_for lr =
  let lr = repr lr in
  match lr.kind with
  | Link _ -> assert false
  | Reg r -> r
  | Var -> let r = XTL.new_reg() in lr.kind <- Reg r; r

(* Live range inference is a variant on liveness analysis.
   At each PC and for each register, liveness analysis determines
   whether the reg is live or not.  Live range inference associates
   a live range to the reg if it is live, and no live range if it
   is dead. *)

module RMap = Map.Make(P)

module LRMap = struct

  type t = live_range RMap.t   (* live register -> live range *)

  let beq m1 m2 = RMap.equal same_range m1 m2

  let bot : t = RMap.empty

  let lub_opt_range r olr1 olr2 =
    match olr1, olr2 with
    | Some lr1, Some lr2 -> unify lr1 lr2; olr1
    | Some _, None -> olr1
    | None, _ -> olr2

  let lub m1 m2 =
    RMap.merge lub_opt_range m1 m2

end

module Solver = Backward_Dataflow_Solver(LRMap)(NodeSetBackward)

(* A cache of live ranges associated to (pc, used reg) pairs. *)

let live_range_cache =
  (Hashtbl.create 123 : (int * int, live_range) Hashtbl.t)

let live_range_for pc r =
  let pc' = P.to_int pc
  and r' = P.to_int r in
  try
    Hashtbl.find live_range_cache (pc',r')
  with Not_found ->
    let lr = new_range r in
    Hashtbl.add live_range_cache (pc', r') lr;
    lr

(* The transfer function *)

let reg_live pc r map =
  if RMap.mem r map
  then map                                    (* already live *)
  else RMap.add r (live_range_for pc r) map   (* becomes live *)

let reg_list_live pc rl map = List.fold_right (reg_live pc) rl map

let reg_dead r map =
  RMap.remove r map

let transfer f pc after =
  match PTree.get pc f.fn_code with
  | None ->
      LRMap.bot
  | Some i ->
      let across =
        match instr_defs i with
        | None -> after
        | Some r -> reg_dead r after in
      reg_list_live pc (instr_uses i) across

(* The live range analysis *)

let analysis f = Solver.fixpoint f.fn_code successors_instr (transfer f)

(* Produce renamed registers for each instruction. *)

let ren_reg map r =
  try
    reg_for (RMap.find r map)
  with Not_found ->
    XTL.new_reg()

let ren_regs map rl =
  List.map (ren_reg map) rl

let ren_ros map ros =
  sum_left_map (ren_reg map) ros

(* Rename in an instruction *)

let ren_instr f maps pc i =
  let after = PMap.get pc maps in
  let before = transfer f pc after in
  match i with
  | Inop s -> Inop s
  | Iop(op, args, res, s) ->
      Iop(op, ren_regs before args, ren_reg after res, s)
  | Iload(chunk, addr, args, dst, s) ->
      Iload(chunk, addr, ren_regs before args, ren_reg after dst, s)
  | Istore(chunk, addr, args, src, s) ->
      Istore(chunk, addr, ren_regs before args, ren_reg before src, s)
  | Icall(sg, ros, args, res, s) ->
      Icall(sg, ren_ros before ros, ren_regs before args, ren_reg after res, s)
  | Itailcall(sg, ros, args) ->
      Itailcall(sg, ren_ros before ros, ren_regs before args)
  | Ibuiltin(ef, args, res, s) ->
      Ibuiltin(ef, List.map (AST.map_builtin_arg (ren_reg before)) args,
                   AST.map_builtin_res (ren_reg after) res, s)
  | Icond(cond, args, s1, s2) ->
      Icond(cond, ren_regs before args, s1, s2)
  | Ijumptable(arg, tbl) ->
      Ijumptable(ren_reg before arg, tbl)
  | Ireturn optarg ->
      Ireturn(option_map (ren_reg before) optarg)

(* Rename live ranges in a function *)

let rename_function f =
  Hashtbl.clear live_range_cache;
  let maps =
    match analysis f with
    | None -> assert false
    | Some maps -> maps in
  let before_entrypoint =
    transfer f f.fn_entrypoint (PMap.get f.fn_entrypoint maps) in
  { fn_sig = f.fn_sig;
    fn_params = ren_regs before_entrypoint f.fn_params;
    fn_stacksize = f.fn_stacksize;
    fn_code = PTree.map (ren_instr f maps) f.fn_code;
    fn_entrypoint = f.fn_entrypoint }

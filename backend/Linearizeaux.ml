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

open BinPos
open Coqlib
open Datatypes
open LTL
open Lattice
open Maps
open Camlcoq

(* Trivial enumeration, in decreasing order of PC *)

(***
let enumerate_aux f reach =
  positive_rec
    Coq_nil
    (fun pc nodes ->
      if PMap.get pc reach
      then Coq_cons (pc, nodes)
      else nodes) 
    f.fn_nextpc
***)

(* More clever enumeration that flattens basic blocks *)

let rec int_of_pos = function
  | Coq_xI p -> (int_of_pos p lsl 1) + 1
  | Coq_xO p -> int_of_pos p lsl 1
  | Coq_xH -> 1

let rec pos_of_int n =
  if n = 0 then assert false else
  if n = 1 then Coq_xH else
  if n land 1 = 0
  then Coq_xO (pos_of_int (n lsr 1))
  else Coq_xI (pos_of_int (n lsr 1))

module IntSet = Set.Make(struct type t = int let compare = compare end)

(* Determine join points: reachable nodes that have > 1 predecessor *)

let join_points f =
  let succs = LTL.successors f in
  let reached = ref IntSet.empty in
  let reached_twice = ref IntSet.empty in
  let rec traverse pc =
    let npc = int_of_pos pc in
    if IntSet.mem npc !reached then begin
      if not (IntSet.mem npc !reached_twice) then
        reached_twice := IntSet.add npc !reached_twice
    end else begin
      reached := IntSet.add npc !reached;
      List.iter traverse (Kildall.successors_list succs pc)
    end
  in traverse f.fn_entrypoint; !reached_twice

(* Cut into reachable basic blocks, annotated with the min value of the PC *)

let basic_blocks f joins =
  let blocks = ref [] in
  let visited = ref IntSet.empty in
  (* start_block:
       pc is the function entry point
          or a join point
          or the successor of a conditional test *)
  let rec start_block pc =
    let npc = int_of_pos pc in
    if not (IntSet.mem npc !visited) then begin
      visited := IntSet.add npc !visited;
      in_block [] max_int pc
    end
  (* in_block: add pc to block and check successors *)
  and in_block blk minpc pc =
    let npc = int_of_pos pc in
    let blk = pc :: blk in
    let minpc = min npc minpc in
    match PTree.get pc f.fn_code with
    | None -> assert false
    | Some i ->
       match i with
         | Lnop s -> next_in_block blk minpc s
         | Lop (op, args, res, s) -> next_in_block blk minpc s
         | Lload (chunk, addr, args, dst, s) -> next_in_block blk minpc s
         | Lstore (chunk, addr, args, src, s) -> next_in_block blk minpc s
         | Lcall (sig0, ros, args, res, s) -> next_in_block blk minpc s
         | Ltailcall (sig0, ros, args) -> end_block blk minpc
         | Lcond (cond, args, ifso, ifnot) ->
             end_block blk minpc; start_block ifso; start_block ifnot
         | Lreturn optarg -> end_block blk minpc
  (* next_in_block: check if join point and either extend block
     or start block *)
  and next_in_block blk minpc pc =
    let npc = int_of_pos pc in
    if IntSet.mem npc joins
    then (end_block blk minpc; start_block pc)
    else in_block blk minpc pc
  (* end_block: record block that we just discovered *)
  and end_block blk minpc =
    blocks := (minpc, List.rev blk) :: !blocks
  in 
    start_block f.fn_entrypoint; !blocks

(* Flatten basic blocks in decreasing order of minpc *)

let flatten_blocks blks =
  let cmp_minpc (mpc1, _) (mpc2, _) =
    if mpc1 = mpc2 then 0 else if mpc1 > mpc2 then -1 else 1
  in
    List.flatten (List.map Pervasives.snd (List.sort cmp_minpc blks))

(* Build the enumeration *)

let enumerate_aux f reach =
  flatten_blocks (basic_blocks f (join_points f))

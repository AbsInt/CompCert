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
open CList
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

(* Build the enumeration *)

module IntSet = Set.Make(struct type t = int let compare = compare end)

let enumerate_aux f reach =
  let enum = ref Coq_nil in
  let emitted = Array.make (int_of_pos f.fn_nextpc) false in
  let rec emit_block pending pc =
    let npc = int_of_pos pc in
    if emitted.(npc)
    then emit_restart pending
    else begin
      enum := Coq_cons(pc, !enum);
      emitted.(npc) <- true;
      match PTree.get pc f.fn_code with
      | None -> assert false
      | Some i ->
         match i with
           | Lnop s -> emit_block pending s
           | Lop (op, args, res, s) -> emit_block pending s
           | Lload (chunk, addr, args, dst, s) -> emit_block pending s
           | Lstore (chunk, addr, args, src, s) -> emit_block pending s
           | Lcall (sig0, ros, args, res, s) -> emit_block pending s
           | Ltailcall (sig0, ros, args) -> emit_restart pending
           | Lalloc (arg, res, s) -> emit_block pending s
           | Lcond (cond, args, ifso, ifnot) ->
               emit_restart (IntSet.add (int_of_pos ifso)
                             (IntSet.add (int_of_pos ifnot) pending))
           | Lreturn optarg -> emit_restart pending
    end
  and emit_restart pending =
    if not (IntSet.is_empty pending) then begin
      let npc = IntSet.max_elt pending in
      emit_block (IntSet.remove npc pending) (pos_of_int npc)
    end in
  emit_block IntSet.empty f.fn_entrypoint;
  CList.rev !enum

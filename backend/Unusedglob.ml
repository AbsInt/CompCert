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

(* Removing unused definitions of static functions and global variables *)

open Camlcoq
open Maps
open AST
open Asm
open Unusedglob1

module IdentSet = Set.Make(struct type t = ident let compare = compare end)

(* The set of globals referenced from a function definition *)

let add_referenced_instr rf i =
  List.fold_right IdentSet.add (referenced_instr i) rf

let referenced_function f =
  List.fold_left add_referenced_instr IdentSet.empty (code_of_function f)

let referenced_fundef = function
  | Internal f -> referenced_function f
  | External ef -> IdentSet.empty

(* The set of globals referenced from a variable definition (initialization) *)

let add_referenced_init_data rf = function
  | Init_addrof(id, ofs) -> IdentSet.add id rf
  | _ -> rf

let referenced_globvar gv =
  List.fold_left add_referenced_init_data IdentSet.empty gv.gvar_init

(* The map global |-> set of globals it references *)

let use_map p =
  List.fold_left (fun m (id, gv) -> PTree.set id (referenced_globvar gv) m)
  (List.fold_left (fun m (id, fd) -> PTree.set id (referenced_fundef fd) m)
   PTree.empty p.prog_funct) p.prog_vars

(* Worklist algorithm computing the set of used globals *)

let rec used_idents usemap used wrk =
  match wrk with
  | [] -> used
  | id :: wrk ->
      if IdentSet.mem id used then used_idents usemap used wrk else
        match PTree.get id usemap with
        | None -> used_idents usemap used wrk
        | Some s -> used_idents usemap (IdentSet.add id used)
                                       (IdentSet.fold (fun id l -> id::l) s wrk)

(* The worklist is initially populated with all nonstatic globals *)

let add_nonstatic wrk id =
  if C2C.atom_is_static id then wrk else id :: wrk

let initial_worklist p =
  List.fold_left (fun wrk (id, gv) -> add_nonstatic wrk id)
   (List.fold_left (fun wrk (id, fd) -> add_nonstatic wrk id)
     [] p.prog_funct) p.prog_vars

(* Eliminate unused definitions *)

let rec filter used = function
  | [] -> []
  | (id, def) :: rem ->
      if IdentSet.mem id used
      then (id, def) :: filter used rem
      else filter used rem

let filter_prog used p =
  { prog_funct = filter used p.prog_funct;
    prog_main = p.prog_main;
    prog_vars = filter used p.prog_vars }

(* Entry point *)

let transf_program p =
  filter_prog (used_idents (use_map p) IdentSet.empty (initial_worklist p)) p


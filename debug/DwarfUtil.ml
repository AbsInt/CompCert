(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(* Utility functions for the dwarf debuging type *)

open DwarfTypes

let id = ref 0

let next_id () = 
  let nid = !id in
  incr id; nid

let reset_id () =
  id := 0

(* Hashtable to from type name to entry id *)
let type_table: (string, int) Hashtbl.t = Hashtbl.create 7

(* Generate a new entry from a given tag *)
let new_entry tag =
  let id = next_id () in
  {
   tag = tag;
   children = [];
   id = id;
 }


(* Add an entry as child to  another entry *)
let add_children entry child =
  {entry with children = child::entry.children;}


(* Iter over the tree in prefix order *)
let rec entry_iter f entry =
  f entry.tag;
  List.iter (entry_iter f) entry.children

(* Iter over the tree in prefix order with passing additional reference to next sibling *)
let entry_iter_sibling f acc entry =
  f None entry.tag;
  let rec aux = (function
    | [] -> ()
    | [last] -> f None last.tag
    | a::b::rest ->  f  (Some b.id) a.tag; aux (b::rest)) in
  aux entry.children


(* Fold over the tree in prefix order *)
let rec entry_fold f acc entry =
  let acc = f acc entry.tag in
  List.fold_left (entry_fold f) acc entry.children

(* Fold over the tree in prefix order with passing additional reference to next sibling *)
let entry_fold_sibling f acc entry =
  let acc = f acc None entry.tag in
  let rec aux acc = (function
    | [] -> acc
    | [last] -> f acc None last.tag
    | a::b::rest -> aux (f acc (Some b.id) a.tag) (b::rest)) in
  aux acc entry.children

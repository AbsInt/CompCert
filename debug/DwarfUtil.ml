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

let new_entry tag =
  let id = next_id () in
  {
   tag = tag;
   children = [];
   id = id;
 }

let add_children entry child =
  {entry with children = child::entry.children;}

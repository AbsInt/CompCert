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

(* Iterated Register Coalescing: George and Appel's graph coloring algorithm *)

open Registers
open Machregs
open Locations
open XTL

(* The abstract type of interference and preference graphs. *)
type graph

(* Information associated to every variable. *)
type var_stats = {
  mutable cost: int;             (* estimated cost of a spill *)
  mutable usedefs: int           (* number of uses and defs *)
}

(* Create an empty graph.  The given function associates statistics to
   every variable. *)
val init: (reg -> var_stats) -> graph

(* Add an interference between two variables. *)
val add_interf: graph -> var -> var -> unit

(* Add a preference between two variables. *)
val add_pref: graph -> var -> var -> unit

(* Color the graph.  Return an assignment of locations to variables. *)
val coloring: graph -> (var -> loc)

(* Machine registers that are reserved and not available for allocation. *)
val reserved_registers: mreg list ref

(* Auxiliaries to deal with register classes *)
val class_of_type: AST.typ -> int
val class_of_loc: loc -> int

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Asm
open AST
open BinNums

(** Auxiliary functions for builtin expansion *)

val emit: instruction -> unit
  (* Emit an instruction *)
val new_label: unit -> label
  (* Compute a fresh label *)
val is_current_function_variadic: unit -> bool
  (* Test wether the current function is a variadic function *)
val get_current_function_args: unit -> typ list
  (* Get the types of the current function arguments *)
val get_current_function_sig: unit -> signature
  (* Get the signature of the current function *)
val set_current_function: coq_function -> unit
  (* Set the current function *)
val get_current_function: unit -> coq_function
  (* Get the current function *)
val expand: positive -> int -> (preg -> int) -> (instruction -> unit) -> instruction list -> unit
  (* Expand the instruction sequence of a function. Takes the function id, the register number of the stackpointer, a
     function to get the dwarf mapping of varibale names and for the expansion of simple instructions *)

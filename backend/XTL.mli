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

(** The XTL intermediate language for register allocation *)

open Datatypes
open Camlcoq
open Maps
open AST
open Registers
open Machregs
open Locations
open Op

type var = V of reg * typ | L of loc

type node = P.t

type instruction =
  | Xmove of var * var
  | Xreload of var * var
  | Xspill of var * var
  | Xparmove of var list * var list * var * var
  | Xop of operation * var list * var
  | Xload of memory_chunk * addressing * var list * var
  | Xstore of memory_chunk * addressing * var list * var
  | Xcall of signature * (var, ident) sum * var list * var list
  | Xtailcall of signature * (var, ident) sum * var list
  | Xbuiltin of external_function * var builtin_arg list * var builtin_res
  | Xbranch of node
  | Xcond of condition * var list * node * node
  | Xjumptable of var * node list
  | Xreturn of var list

type block = instruction list
  (* terminated by one of Xbranch, Xcond, Xjumptable, Xtailcall or Xreturn *)

type code = block PTree.t
  (* mapping node -> block *)

type xfunction = {
  fn_sig: signature;
  fn_stacksize: Z.t;
  fn_code: code;
  fn_entrypoint: node
}

(* Type of a variable *)

val typeof: var -> typ

(* Constructors for type [var] *)

val vloc: loc -> var
val vlocs: loc list -> var list
val vmreg: mreg -> var
val vmregs: mreg list -> var list
val vlocpairs: loc rpair list -> var list

(* Tests over variables *)

val is_stack_reg: var -> bool

(* Sets of variables *)

module VSet: Set.S with type elt = var

(* Generation of fresh registers and fresh register variables *)

val reset_temps: unit -> unit
val new_reg: unit -> reg
val new_temp: typ -> var
val twin_reg: reg -> reg

(* Type checking *)

val type_function: xfunction -> unit
exception Type_error_at of node

(* Successors for dataflow analysis *)

val successors_block: block -> node list

(* A generic framework for transforming extended basic blocks *)

val transform_basic_blocks:
  (node -> block -> 'state -> block * 'state) ->
  'state ->
  xfunction -> xfunction
(* First arg is the transfer function
      (node, block, state before) -> (transformed block, state after).
   Second arg is "top" state, to be used as initial state for
   extended basic block heads. *)



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

open BinNums
open Camlcoq
open DebugTypes
open Sections

val typ_to_string: C.typ -> string

val next_id: unit -> int

val get_type: int -> debug_types

val fold_types: (int -> debug_types -> 'a -> 'a) -> 'a -> 'a

val is_variable_printed: string -> bool

val variable_location: atom -> atom -> var_location

val translate_label: atom -> positive -> int

val get_scope_ranges: int -> scope_range list

val get_local_variable: int -> local_information

val diab_file_loc: string -> string -> int

val section_start: string -> int

val fold_section_start: (string -> int -> 'a -> 'a) -> 'a -> 'a

val section_end: string -> int

val diab_additional_section: string -> int * int

val file_name: string ref

val fold_definitions: (int -> definition_type -> 'a -> 'a) -> 'a -> 'a

val diab_add_fun_addr: atom -> section_name -> (int * int) -> unit

val gnu_add_fun_addr: atom -> section_name -> (int * int) -> unit

val add_diab_info: section_name ->  int -> int  -> int -> unit

val default_debug: Debug.implem

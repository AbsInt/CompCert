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

open AST
open BinNums
open !C
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

val atom_global: ident -> atom -> unit

val set_composite_size: ident -> struct_or_union -> int option -> unit

val set_member_offset: ident -> string -> int -> unit

val set_bitfield_offset: ident -> string -> int -> string -> int -> unit

val insert_global_declaration:  Env.t -> globdecl -> unit

val diab_add_fun_addr: atom -> section_name -> (int * int) -> unit

val gnu_add_fun_addr: atom -> section_name -> (int * int) -> unit

val all_files_iter: (string -> unit) -> unit

val insert_local_declaration: storage -> ident -> typ -> location -> unit

val atom_local_variable: ident -> atom -> unit

val enter_scope: int -> int -> int -> unit

val enter_function_scope: int -> int -> unit

val add_lvar_scope: int -> ident -> int -> unit

val open_scope: atom -> int -> positive -> unit

val close_scope: atom -> int -> positive -> unit

val start_live_range: (atom * atom) -> positive -> (int * int builtin_arg) -> unit

val end_live_range: (atom * atom) -> positive -> unit

val stack_variable: (atom * atom) -> int * int builtin_arg -> unit

val add_label: atom -> positive -> int -> unit

val atom_parameter: ident -> ident -> atom -> unit

val compute_diab_file_enum: (section_name -> int) -> (string-> int) -> (unit -> unit) -> unit

val compute_gnu_file_enum: (string -> unit) -> unit

val exists_section: section_name -> bool

val remove_unused: ident -> unit

val remove_unused_function: ident -> unit

val variable_printed: string -> unit

val add_diab_info: section_name ->  int -> int  -> int -> unit

val init: string -> unit

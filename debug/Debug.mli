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

open C
open Camlcoq
open DwarfTypes
open BinNums
open Sections


(* Record used for storing references to the actual implementation functions *)
type implem =
    {
     init: string -> unit;
     atom_global: ident -> atom -> unit;
     set_composite_size: ident -> struct_or_union -> int option -> unit;
     set_member_offset: ident -> string -> int -> unit;
     set_bitfield_offset: ident -> string -> int -> string -> int -> unit;
     insert_global_declaration: Env.t -> globdecl -> unit;
     add_fun_addr: atom -> section_name -> (int * int) -> unit;
     generate_debug_info: (atom -> string) -> string -> debug_entries option;
     all_files_iter: (string -> unit) -> unit;
     insert_local_declaration:  storage -> ident -> typ -> location -> unit;
     atom_local_variable: ident -> atom -> unit;
     enter_scope: int -> int -> int -> unit;
     enter_function_scope: int -> int -> unit;
     add_lvar_scope: int -> ident -> int -> unit;
     open_scope: atom -> int -> positive -> unit;
     close_scope: atom -> int -> positive -> unit;
     start_live_range: (atom * atom) -> positive -> int * int AST.builtin_arg -> unit;
     end_live_range: (atom * atom) -> positive -> unit;
     stack_variable: (atom * atom) -> int * int AST.builtin_arg -> unit;
     add_label: atom -> positive -> int -> unit;
     atom_parameter: ident -> ident -> atom -> unit;
     compute_diab_file_enum: (section_name -> int) -> (string-> int) -> (unit -> unit) -> unit;
     compute_gnu_file_enum: (string -> unit) -> unit;
     exists_section: section_name -> bool;
     remove_unused: ident -> unit;
     remove_unused_function: ident -> unit;
     variable_printed: string -> unit;
     add_diab_info: section_name ->  int -> int -> int -> unit;
   }

val default_implem: implem

val implem: implem ref

val init_compile_unit: string -> unit
val atom_global: ident -> atom -> unit
val set_composite_size: ident -> struct_or_union -> int option -> unit
val set_member_offset: ident -> string -> int -> unit
val set_bitfield_offset: ident -> string -> int -> string -> int -> unit
val insert_global_declaration:  Env.t -> globdecl -> unit
val add_fun_addr: atom -> section_name -> (int * int) -> unit
val all_files_iter: (string -> unit) -> unit
val insert_local_declaration: storage -> ident -> typ -> location -> unit
val atom_local_variable: ident -> atom -> unit
val enter_scope: int -> int -> int -> unit
val enter_function_scope: int -> int -> unit
val add_lvar_scope: int -> ident -> int -> unit
val open_scope: atom -> int -> positive -> unit
val close_scope: atom -> int -> positive -> unit
val start_live_range: (atom * atom) -> positive -> (int * int AST.builtin_arg) -> unit
val end_live_range: (atom * atom) -> positive -> unit
val stack_variable: (atom * atom) -> int * int AST.builtin_arg -> unit
val add_label: atom -> positive -> int -> unit
val generate_debug_info: (atom -> string) -> string -> debug_entries option
val atom_parameter: ident -> ident -> atom -> unit
val compute_diab_file_enum: (section_name -> int) -> (string-> int) -> (unit -> unit) -> unit
val compute_gnu_file_enum: (string -> unit) -> unit
val exists_section: section_name -> bool
val remove_unused: ident -> unit
val remove_unused_function: ident -> unit
val variable_printed: string -> unit
val add_diab_info: section_name ->  int -> int  -> int -> unit

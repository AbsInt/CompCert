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
open C
open Camlcoq
open DwarfTypes
open BinNums


(* Record used for stroring references to the actual implementation functions *)
type implem = 
    {
     mutable init: string -> unit;
     mutable atom_function: ident -> atom -> unit;
     mutable atom_global_variable: ident -> atom -> unit;
     mutable set_composite_size: ident -> struct_or_union -> int option -> unit;
     mutable set_member_offset: ident -> string -> int -> unit;
     mutable set_bitfield_offset: ident -> string -> int -> string -> int -> unit;
     mutable insert_global_declaration: Env.t -> globdecl -> unit;
     mutable add_fun_addr: atom -> (int * int) -> unit;
     mutable generate_debug_info: (atom -> string) -> string -> debug_entries option;
     mutable all_files_iter: (string -> unit) -> unit;
     mutable insert_local_declaration:  storage -> ident -> typ -> location -> unit;
     mutable atom_local_variable: ident -> atom -> unit;
     mutable enter_scope: int -> int -> int -> unit;
     mutable enter_function_scope: int -> int -> unit;
     mutable add_lvar_scope: int -> ident -> int -> unit;
     mutable open_scope: atom -> int -> positive -> unit;
     mutable close_scope: atom -> int -> positive -> unit;
     mutable start_live_range: atom -> positive -> int * int builtin_arg -> unit;
     mutable end_live_range: atom -> positive -> unit;
     mutable stack_variable: atom -> int * int builtin_arg -> unit;
     mutable function_end: atom -> positive -> unit;
     mutable add_label: atom -> positive -> int -> unit;
     mutable atom_parameter: ident -> ident -> atom -> unit;
     mutable add_compilation_section_start: string -> (int * int * int * string) -> unit;
     mutable compute_file_enum: (string -> int) -> (string-> int) -> (unit -> unit) -> unit;
     mutable exists_section: string -> bool;
     mutable remove_unused: ident -> unit;
     mutable variable_printed: string -> unit;
   }

val implem: implem

val init_compile_unit: string -> unit
val atom_function: ident -> atom -> unit
val atom_global_variable: ident -> atom -> unit
val set_composite_size: ident -> struct_or_union -> int option -> unit
val set_member_offset: ident -> string -> int -> unit
val set_bitfield_offset: ident -> string -> int -> string -> int -> unit
val insert_global_declaration:  Env.t -> globdecl -> unit
val add_fun_addr: atom -> (int * int) -> unit
val all_files_iter: (string -> unit) -> unit
val insert_local_declaration: storage -> ident -> typ -> location -> unit
val atom_local_variable: ident -> atom -> unit
val enter_scope: int -> int -> int -> unit
val enter_function_scope: int -> int -> unit
val add_lvar_scope: int -> ident -> int -> unit
val open_scope: atom -> int -> positive -> unit
val close_scope: atom -> int -> positive -> unit
val start_live_range: atom -> positive -> (int * int builtin_arg) -> unit
val end_live_range: atom -> positive -> unit
val stack_variable: atom -> int * int builtin_arg -> unit
val function_end: atom -> positive -> unit
val add_label: atom -> positive -> int -> unit
val generate_debug_info: (atom -> string) -> string -> debug_entries option
val atom_parameter: ident -> ident -> atom -> unit
val add_compilation_section_start: string -> (int * int * int * string) -> unit
val compute_file_enum: (string -> int) -> (string-> int) -> (unit -> unit) -> unit
val exists_section: string -> bool
val remove_unused: ident -> unit
val variable_printed: string -> unit

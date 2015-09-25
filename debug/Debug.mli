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


val init: unit -> unit
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
val generate_debug_info: unit -> (dw_entry * dw_locations) option

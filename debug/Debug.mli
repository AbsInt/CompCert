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


val init: unit -> unit
val init_compile_unit: string -> unit
val atom_function: ident -> atom -> unit
val atom_global_variable: ident -> atom -> unit
val set_composite_size: ident -> struct_or_union -> int option -> unit
val set_member_offset: ident -> string -> int -> unit
val set_bitfield_offset: ident -> string -> int -> string -> int -> unit
val insert_global_declaration:  Env.t -> globdecl -> unit
val add_fun_addr: atom -> (int * int) -> unit
val generate_debug_info: unit -> dw_entry option
val all_files_iter: (string -> unit) -> unit
val insert_local_declaration: storage -> ident -> typ -> location -> unit
val atom_local_variable: ident -> atom -> unit
val enter_scope: int -> int -> int -> unit
val enter_function_scope: int -> int -> unit
val add_lvar_scope: int -> ident -> int -> unit

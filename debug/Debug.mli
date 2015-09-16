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


val init: unit -> unit
val init_compile_unit: string -> unit
val atom_function: ident -> atom -> unit
val atom_global_variable: ident -> atom -> unit
val set_composite_size: ident -> struct_or_union -> int option -> unit
val set_member_offset: ident -> string -> int -> unit
val set_bitfield_offset: ident -> string -> int -> string -> int -> unit
val insert_global_declaration:  Env.t -> globdecl -> unit
val add_fun_addr: atom -> (int * int) -> unit

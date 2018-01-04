(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

val print_idents_in_full : bool ref
val print_line_numbers : bool ref
val print_debug_idents : bool ref

val location : Format.formatter -> C.location -> unit
val attributes : Format.formatter -> C.attributes -> unit
val typ : Format.formatter -> C.typ -> unit
val typ_raw : Format.formatter -> C.typ -> unit
val simple_decl : Format.formatter -> C.ident * C.typ -> unit
val full_decl: Format.formatter -> C.decl -> unit
val const : Format.formatter -> C.constant -> unit
val exp : Format.formatter -> int * C.exp -> unit
val opt_exp : Format.formatter -> C.stmt -> unit
val stmt : Format.formatter -> C.stmt -> unit
val fundef : Format.formatter -> C.fundef -> unit
val init : Format.formatter -> C.init -> unit
val storage : Format.formatter -> C.storage -> unit
val field : Format.formatter -> C.field -> unit
val globdecl : Format.formatter -> C.globdecl -> unit
val program : Format.formatter -> C.program -> unit

val destination : string option ref
val print_if : C.program -> unit

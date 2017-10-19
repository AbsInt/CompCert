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


(* Handling of linker sections *)

type section_name =
  | Section_text
  | Section_data of bool          (* true = init data, false = uninit data *)
  | Section_small_data of bool
  | Section_const of bool
  | Section_small_const of bool
  | Section_string
  | Section_literal
  | Section_jumptable
  | Section_user of string * bool (*writable*) * bool (*executable*)
  | Section_debug_abbrev
  | Section_debug_info of string option
  | Section_debug_loc
  | Section_debug_line of string option
  | Section_debug_ranges
  | Section_debug_str
  | Section_ais_annotation

type access_mode =
  | Access_default
  | Access_near
  | Access_far

val initialize: unit -> unit

val define_section:
  string -> ?iname:string -> ?uname:string
         -> ?writable:bool -> ?executable:bool -> ?access:access_mode -> unit -> unit
val use_section_for: AST.ident -> string -> bool

val for_variable: Env.t -> AST.ident -> C.typ -> bool ->
                                          section_name * access_mode
val for_function: Env.t -> AST.ident -> C.attributes -> section_name list
val for_stringlit: unit -> section_name

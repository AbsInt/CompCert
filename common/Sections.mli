(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)


(* Handling of linker sections *)

type initialized =
  | Uninit       (* uninitialized data area *)
  | Init         (* initialized with fixed, non-relocatable data *)
  | Init_reloc   (* initialized with relocatable data (symbol addresses) *)

type section_name =
  | Section_text
  | Section_data of initialized
  | Section_small_data of initialized
  | Section_const of initialized
  | Section_small_const of initialized
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

val for_variable: Env.t -> C.location -> AST.ident -> C.typ -> initialized ->
                                          section_name * access_mode
val for_function: Env.t -> C.location -> AST.ident -> C.attributes -> section_name list
val for_stringlit: unit -> section_name

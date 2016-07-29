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

val warn_error : bool ref
val reset : unit -> unit
exception Abort
val fatal_error_raw : ('a, out_channel, unit, 'b) format4 -> 'a
val check_errors : unit -> bool

type warning_type =
  | Unnamed
  | Unknown_attribute
  | Zero_length_array
  | Celeven_extension
  | Gnu_empty_struct
  | Missing_declarations
  | Constant_conversion
  | Int_conversion
  | Varargs
  | Implicit_function_declaration
  | Pointer_type_mismatch
  | Compare_distinct_pointer_types
  | Pedantic
  | Main_return_type
  | Invalid_noreturn
  | Return_type
  | Literal_range
  | Unknown_pragmas

val warning  : (string * int) -> warning_type -> ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a
val error : (string * int) -> ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a
val fatal_error : (string * int) -> ('a, Format.formatter, unit, unit, unit, 'b) format6 -> 'a

val warning_help : string
val warning_options : (Commandline.pattern * Commandline.action) list

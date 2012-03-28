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
val fatal_error : ('a, Format.formatter, unit, unit, unit, 'b) format6 -> 'a
val error : ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a
val warning : ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a
val check_errors : unit -> bool

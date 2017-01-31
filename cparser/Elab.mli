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

val elab_file : Cabs.definition list -> C.program
  (* This is the main entry point.  It transforms a list of toplevel
     definitions as produced by the parser into a program in C abstract
     syntax. *)

val elab_int_constant : Cabs.cabsloc -> string -> int64 * C.ikind
val elab_float_constant : Cabs.floatInfo -> C.float_cst * C.fkind
val elab_char_constant : Cabs.cabsloc -> bool -> int64 list -> int64
  (* These auxiliary functions are exported so that they can be reused
     in other projects that deal with C-style source languages. *)

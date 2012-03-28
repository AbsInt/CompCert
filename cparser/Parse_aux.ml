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

open Format
open Cerrors
open Cabshelper

(* Report parsing errors *)

let parse_error msg =
  error "%a: %s" format_cabsloc (currentLoc()) msg

(* Are we parsing msvc syntax? *)

let msvcMode = ref false

(* We provide here a pointer to a function. It will be set by the lexer and 
 * used by the parser. In Ocaml lexers depend on parsers, so we we have put 
 * such functions in a separate module. *)
let add_identifier: (string -> unit) ref = 
  ref (fun _ -> assert false)

let add_type: (string -> unit) ref = 
  ref (fun _ -> assert false)

let push_context: (unit -> unit) ref = 
  ref (fun _ -> assert false)

let pop_context: (unit -> unit) ref = 
  ref (fun _ -> assert false)

(* Keep here the current pattern for formatparse *)
let currentPattern = ref ""


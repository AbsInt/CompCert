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

(* Entry point for the library: parse, elaborate, and transform *)

val preprocessed_file:
  ?unblock: bool -> 
  ?struct_passing: bool ->
  ?packed_structs: bool ->
  string -> string -> C.program
      (** [preprocessed_file filename sourcetext] performs parsing,
          elaboration, and optional source-to-source transformations.
          [filename] is the name of the source file, for error messages.
          [sourcetext] is the text of the source file after preprocessing.
          The optional arguments indicate which source-to-source
          transformations to perform.  They default to [false] (don't perform).
      *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*        Bernhard Schommer, AbsInt Angewandte Informatik GmbH         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)


val expand_responsefiles: string array -> string array
  (** Expand responsefile arguments contained in the array and return the full
      set of arguments. *)

val write_responsefile: out_channel -> string array -> int -> unit
  (** Write the arguments starting at the given index as repsonsefile on the given
      out_channel. All arguments that contain whitespaces are quoted. *)

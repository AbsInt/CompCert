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


val expandargv: string array -> string array
  (** Expand responsefile arguments contained in the array and return the full
      set of arguments. *)

exception Error of string
  (** Raised by [expandargv] in case of an error *)

val gnu_quote : string -> string
  (** [gnu_quote arg] returns [arg] quoted compatible with the gnu tool chain
      quoting conventions. *)

val diab_quote : string -> string
  (** [diab_quote arg] returns [arg] quoted compatible with the diab tool chain
      quoting conventions. *)

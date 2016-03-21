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

(** Print lines from a file *)

type filebuf
        (** The type of buffers on opened files *)

val openfile: string -> filebuf
        (** Open the file with the given name. *)

val close: filebuf -> unit
        (** Close the file underlying the given buffer. *)

val copy: out_channel -> string -> filebuf -> int -> int -> unit
        (** [copy oc pref buf first last] copies lines number [first]
            to [last], included, to the channel [oc].  Each line is
            prefixed by [pref]. *)

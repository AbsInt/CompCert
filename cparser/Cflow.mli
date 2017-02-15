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

(* A simple control flow analysis for C statements.
   Main purpose: emit warnings for _Noreturn functions. *)

val function_returns: Env.t -> C.stmt -> bool * bool
  (** Given a function body, returns two Booleans:
      - the first says whether the function can return
      - the second says whether the function can return by falling through
        the end of its body.
      Both are over-approximations. *)

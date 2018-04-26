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

val integer_expr : Env.t -> C.exp -> int64 option
val constant_expr : Env.t -> C.typ -> C.exp -> C.constant option
val normalize_int : int64 -> C.ikind -> int64
val is_constant_init: Env.t -> C.init -> bool
val is_constant_expr: Env.t -> C.exp -> bool

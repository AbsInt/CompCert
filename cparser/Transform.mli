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

(* Generic program transformation *)

val reset_temps : unit -> unit
val new_temp_var : ?name:string -> C.typ -> C.ident
val new_temp : ?name:string -> C.typ -> C.exp
val get_temps : unit -> C.decl list

val program :
  ?decl:(Env.t -> C.decl -> C.decl) ->
  ?fundef:(Env.t -> C.fundef -> C.fundef) ->
  ?composite:(Env.t -> C.struct_or_union -> 
                C.ident -> C.attributes -> C.field list -> 
                  C.attributes * C.field list) ->
  ?typedef:(Env.t -> C.ident -> Env.typedef_info -> Env.typedef_info) ->
  ?enum:(Env.t -> C.ident -> (C.ident * C.exp option) list ->
                                       (C.ident * C.exp option) list) ->
  ?pragma:(Env.t -> string -> string) ->
  C.program ->
  C.program

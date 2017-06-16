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

(** Creation of fresh temporary variables. *)
val reset_temps : unit -> unit
val get_temps : unit -> C.decl list
val new_temp_var : ?name:string -> C.typ -> C.ident
val new_temp : ?name:string -> C.typ -> C.exp
val mk_temp : Env.t -> C.typ -> C.exp

(** Avoiding repeated evaluation of a l-value *)

val bind_lvalue: Env.t -> C.exp -> (C.exp -> C.exp) -> C.exp

(* Most transformations over expressions can be optimized if the
   value of the expression is not needed and it is evaluated only
   for its side-effects.  The type [context] records whether
   we are in a side-effects-only position ([Effects]) or not ([Val]). *)

type context = Val | Effects

(** Expansion of assignment expressions *)
val op_for_assignop : C.binary_operator -> C.binary_operator
val op_for_incr_decr : C.unary_operator -> C.binary_operator
val assignop_for_incr_decr : C.unary_operator -> C.binary_operator
val expand_assign :
  write:(C.exp -> C.exp -> C.exp) ->
  Env.t -> context -> C.exp -> C.exp -> C.exp
val expand_assignop :
  read:(C.exp -> C.exp) -> write:(C.exp -> C.exp -> C.exp) ->
  Env.t -> context -> C.binary_operator -> C.exp -> C.exp -> C.typ -> C.exp
val expand_preincrdecr :
  read:(C.exp -> C.exp) -> write:(C.exp -> C.exp -> C.exp) ->
  Env.t -> context -> C.unary_operator -> C.exp -> C.exp
val expand_postincrdecr :
  read:(C.exp -> C.exp) -> write:(C.exp -> C.exp -> C.exp) ->
  Env.t -> context -> C.unary_operator -> C.exp -> C.exp

(** Generic transformation of a statement *)

val stmt :
  expr: (C.location -> Env.t -> context -> C.exp -> C.exp) ->
  ?decl: (Env.t -> C.decl -> C.decl) ->
  Env.t -> C.stmt -> C.stmt

(** Generic transformation of a function definition *)

val fundef : (Env.t -> C.stmt -> C.stmt) -> Env.t -> C.fundef -> C.fundef

(** Generic transformation of a program *)

val program :
  ?decl:(Env.t -> C.decl -> C.decl) ->
  ?fundef:(Env.t -> C.fundef -> C.fundef) ->
  ?composite:(Env.t -> C.struct_or_union ->
                C.ident -> C.attributes -> C.field list ->
                  C.attributes * C.field list) ->
  ?typedef:(Env.t -> C.ident -> C.typ -> C.typ) ->
  ?enum:(Env.t -> C.ident -> C.attributes -> C.enumerator list ->
                  C.attributes * C.enumerator list) ->
  ?pragma:(Env.t -> string -> string) ->
  C.program ->
  C.program

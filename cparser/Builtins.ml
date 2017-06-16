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

(* Compiler built-ins *)

open C
open Cutil

let env = ref Env.empty
let idents = ref []
let decls = ref []

let environment () = !env
let identifiers () = !idents
let declarations () = List.rev !decls

let add_typedef (s, ty) =
  let (id, env') = Env.enter_typedef !env s ty in
  env := env';
  idents := id :: !idents;
  decls := {gdesc = Gtypedef(id, ty); gloc = no_loc} :: !decls

let add_function (s, (res, args, va)) =
  let ty =
    TFun(res,
         Some (List.map (fun ty -> (Env.fresh_ident "", ty)) args),
         va, []) in
  let (id, env') = Env.enter_ident !env s Storage_extern ty in
  env := env';
  idents := id :: !idents;
  decls := {gdesc = Gdecl(Storage_extern, id, ty, None); gloc = no_loc} :: !decls

type t = {
  typedefs: (string * C.typ) list;
  functions: (string * (C.typ * C.typ list * bool)) list
}

let set blt =
  env := Env.empty;
  idents := [];
  List.iter add_typedef blt.typedefs;
  List.iter add_function blt.functions

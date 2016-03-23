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


open Cabs

let cabslu = {lineno = -10;
	      filename = "cabs loc unknown";
	      byteno = -10;
              ident = 0}

(*********** HELPER FUNCTIONS **********)

let rec isStatic = function
    [] -> false
  | (SpecStorage STATIC) :: _ -> true
  | _ :: rest -> isStatic rest

let rec isExtern = function
    [] -> false
  | (SpecStorage EXTERN) :: _ -> true
  | _ :: rest -> isExtern rest

let rec isInline = function
    [] -> false
  | (SpecFunction INLINE) :: _ -> true
  | _ :: rest -> isInline rest

let rec isTypedef = function
    [] -> false
  | SpecStorage TYPEDEF :: _ -> true
  | _ :: rest -> isTypedef rest


let get_definitionloc (d : definition) : cabsloc =
  match d with
  | FUNDEF(_, _, _, _, l) -> l
  | DECDEF(_, l) -> l
  | PRAGMA(_, l) -> l

let get_statementloc (s : statement) : cabsloc =
begin
  match s with
  | NOP(loc) -> loc
  | COMPUTATION(_,loc) -> loc
  | BLOCK(_,loc) -> loc
  | If(_,_,_,loc) -> loc
  | WHILE(_,_,loc) -> loc
  | DOWHILE(_,_,loc) -> loc
  | FOR(_,_,_,_,loc) -> loc
  | BREAK(loc) -> loc
  | CONTINUE(loc) -> loc
  | RETURN(_,loc) -> loc
  | SWITCH(_,_,loc) -> loc
  | CASE(_,_,loc) -> loc
  | DEFAULT(_,loc) -> loc
  | LABEL(_,_,loc) -> loc
  | GOTO(_,loc) -> loc
  | DEFINITION d -> get_definitionloc d
  | ASM(_,_,_,_,_,_,loc) -> loc
end

let string_of_cabsloc l =
  Printf.sprintf "%s:%d" l.filename l.lineno

let format_cabsloc pp l =
  Format.fprintf pp "%s:%d" l.filename l.lineno

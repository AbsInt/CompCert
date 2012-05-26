(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Identifiers referenced from an ARM Asm instruction *)

open Datatypes
open AST
open Asm

let referenced_builtin ef =
  match ef with
  | EF_vload_global(chunk, id, ofs) -> [id]
  | EF_vstore_global(chunk, id, ofs) -> [id]
  | _ -> []

let referenced_instr = function
  | Pbsymb(s, _) -> [s]
  | Pblsymb(s, _) -> [s]
  | Ploadsymbol(_, s, _) -> [s]
  | Pbuiltin(ef, _, _) -> referenced_builtin ef
  | _ -> []

let code_of_function f = f.fn_code

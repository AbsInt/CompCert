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

(* Identifiers referenced from a PowerPC Asm instruction *)

open Datatypes
open AST
open Asm

let referenced_constant = function
  | Cint n -> []
  | Csymbol_low(s, ofs) -> [s]
  | Csymbol_high(s, ofs) -> [s]
  | Csymbol_sda(s, ofs) -> [s]

let referenced_builtin ef =
  match ef with
  | EF_vload_global(chunk, id, ofs) -> [id]
  | EF_vstore_global(chunk, id, ofs) -> [id]
  | _ -> []

let referenced_instr = function
  | Pbl s -> [s]
  | Pbs s -> [s]
  | Paddi(_, _, c)
  | Paddic(_, _, c)
  | Paddis(_, _, c)
  | Pandi_(_, _, c)
  | Pandis_(_, _, c)
  | Pcmplwi(_, c)
  | Pcmpwi(_, c)
  | Plbz(_, c, _)
  | Plfd(_, c, _)
  | Plfs(_, c, _)
  | Plha(_, c, _)
  | Plhz(_, c, _)
  | Plwz(_, c, _)
  | Pmulli(_, _, c)
  | Pori(_, _, c)
  | Poris(_, _, c)
  | Pstb(_, c, _)
  | Pstfd(_, c, _)
  | Pstfs(_, c, _)
  | Psth(_, c, _) 
  | Pstw(_, c, _) 
  | Psubfic(_, _, c)
  | Pxori(_, _, c)
  | Pxoris(_, _, c) -> referenced_constant c
  | Pbuiltin(ef, _, _) -> referenced_builtin ef
  | _ -> []

let code_of_function f = f

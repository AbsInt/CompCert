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

(* Identifiers referenced from an IA32 Asm instruction *)

open Datatypes
open AST
open Asm

let referenced_addr (Addrmode(base, ofs, const)) =
  match const with
  | Coq_inl n -> []
  | Coq_inr(s, ofs) -> [s]

let referenced_builtin ef =
  match ef with
  | EF_vload_global(chunk, id, ofs) -> [id]
  | EF_vstore_global(chunk, id, ofs) -> [id]
  | _ -> []

let referenced_instr = function
  | Pmov_rm (_, a) | Pmov_mr (a, _)
  | Pmov_rm_a (_, a) | Pmov_mr_a (a, _)
  | Pmovsd_fm (_, a) | Pmovsd_mf(a, _)
  | Pmovss_fm (_, a) | Pmovss_mf(a, _)
  | Pfldl_m a | Pflds_m a | Pfstpl_m a | Pfstps_m a
  | Pmovb_mr (a, _) | Pmovw_mr (a, _)
  | Pmovzb_rm (_, a) | Pmovsb_rm (_, a)
  | Pmovzw_rm (_, a) | Pmovsw_rm (_, a)
  | Plea (_, a) -> referenced_addr a
  | Pjmp_s(s, _) -> [s]
  | Pcall_s(s, _) -> [s]
  | Pbuiltin(ef, args, res) -> referenced_builtin ef
  | _ -> []

let code_of_function f = f.fn_code


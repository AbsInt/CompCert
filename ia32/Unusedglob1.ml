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
  | Pmovsd_fm (_, a) | Pmovsd_mf(a, _)
  | Pfld_m a | Pfstp_m a
  | Pmovb_mr (a, _) | Pmovw_mr (a, _)
  | Pmovzb_rm (_, a) | Pmovsb_rm (_, a)
  | Pmovzw_rm (_, a) | Pmovsw_rm (_, a)
  | Pcvtss2sd_fm (_, a) | Pcvtsd2ss_mf (a, _) | Plea (_, a) -> referenced_addr a
  | Pjmp_s s -> [s]
  | Pcall_s s -> [s]
  | Pbuiltin(ef, args, res) -> referenced_builtin ef
  | _ -> []

let code_of_function f = f


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

(** Pretty-printer for Mach code *)

open Printf
open Camlcoq
open Datatypes
open AST
open Machregsaux
open Mach
open PrintAST

let reg pp r =
  match name_of_register r with
  | Some s -> fprintf pp "%s" s
  | None -> fprintf pp "<unknown reg>"

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_instruction pp i =
  match i with
  | Mgetstack(ofs, ty, res) ->
      fprintf pp "\t%a = stack(%ld, %s)\n"
              reg res (camlint_of_coqint ofs) (name_of_type ty)
  | Msetstack(arg, ofs, ty) ->
      fprintf pp "\tstack(%ld, %s) = %a\n"
              (camlint_of_coqint ofs) (name_of_type ty) reg arg
  | Mgetparam(ofs, ty, res) ->
      fprintf pp "\t%a = param(%ld, %s)\n"
              reg res (camlint_of_coqint ofs) (name_of_type ty)
  | Mop(op, args, res) ->
      fprintf pp "\t%a = %a\n"
         reg res (PrintOp.print_operation reg) (op, args)
  | Mload(chunk, addr, args, dst) ->
      fprintf pp "\t%a = %s[%a]\n"
         reg dst (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
  | Mstore(chunk, addr, args, src) ->
      fprintf pp "\t%s[%a] = %a\n"
         (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
         reg src
  | Mcall(sg, fn) ->
      fprintf pp "\tcall %a\n" ros fn
  | Mtailcall(sg, fn) ->
      fprintf pp "\ttailcall %a\n" ros fn
  | Mbuiltin(ef, args, res) ->
      fprintf pp "\t%a = %s(%a)\n"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args
  | Mlabel lbl ->
      fprintf pp "%5d:" (P.to_int lbl)
  | Mgoto lbl ->
      fprintf pp "\tgoto %d\n" (P.to_int lbl)
  | Mcond(cond, args, lbl) ->
      fprintf pp "\tif (%a) goto %d\n"
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int lbl)
  | Mjumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "\tjumptable (%a)\n" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "\t\tcase %d: goto %d\n" i (P.to_int tbl.(i))
      done
  | Mreturn ->
      fprintf pp "\treturn\n"

let print_function pp id f =
  fprintf pp "%s() {\n" (extern_atom id);
  List.iter (print_instruction pp) f.fn_code;
  fprintf pp "}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp prog =
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program oc prog;
      close_out oc

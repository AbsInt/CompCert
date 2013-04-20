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

open Format
open Camlcoq
open Datatypes
open Maps
open AST
open Integers
open Locations
open Machregsaux
open Mach
open PrintAST
open PrintOp

let reg pp r =
  match name_of_register r with
  | Some s -> fprintf pp "%s" s
  | None -> fprintf pp "<unknown reg>"

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let annot_param pp = function
  | APreg r -> reg pp r
  | APstack(chunk, ofs) -> fprintf pp "stack(%s,%ld)" (name_of_chunk chunk) (camlint_of_coqint ofs)

let rec annot_params pp = function
  | [] -> ()
  | [r] -> annot_param pp r
  | r1::rl -> fprintf pp "%a, %a" annot_param r1 annot_params rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_instruction pp i =
  match i with
  | Mgetstack(ofs, ty, res) ->
      fprintf pp "%a = stack(%ld, %s)@ "
              reg res (camlint_of_coqint ofs) (name_of_type ty)
  | Msetstack(arg, ofs, ty) ->
      fprintf pp "stack(%ld, %s) = %a@ "
              (camlint_of_coqint ofs) (name_of_type ty) reg arg
  | Mgetparam(ofs, ty, res) ->
      fprintf pp "%a = param(%ld, %s)@ "
              reg res (camlint_of_coqint ofs) (name_of_type ty)
  | Mop(op, args, res) ->
      fprintf pp "%a = %a@ "
         reg res (PrintOp.print_operation reg) (op, args)
  | Mload(chunk, addr, args, dst) ->
      fprintf pp "%a = %s[%a]@ "
         reg dst (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
  | Mstore(chunk, addr, args, src) ->
      fprintf pp "%s[%a] = %a@ "
         (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
         reg src
  | Mcall(sg, fn) ->
      fprintf pp "call %a@ " ros fn
  | Mtailcall(sg, fn) ->
      fprintf pp "tailcall %a@ " ros fn
  | Mbuiltin(ef, args, res) ->
      fprintf pp "%a = builtin %s(%a)@ "
        regs res (name_of_external ef) regs args
  | Mannot(ef, args) ->
      fprintf pp "%s(%a)@ " (name_of_external ef) annot_params args
  | Mlabel lbl ->
      fprintf pp "%ld:@ " (P.to_int32 lbl)
  | Mgoto lbl ->
      fprintf pp "goto %ld@ " (P.to_int32 lbl)
  | Mcond(cond, args, lbl) ->
      fprintf pp "if (%a) goto %ld@ "
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int32 lbl)
  | Mjumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (P.to_int32 tbl.(i))
      done;
      fprintf pp "@]@ "
  | Mreturn ->
      fprintf pp "return@ "

let print_function pp id f =
  fprintf pp "@[<v 2>%s() {@ " (extern_atom id);
  List.iter (print_instruction pp) f.fn_code;
  fprintf pp "@;<0 -2>}@]@."

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
      let pp = formatter_of_out_channel oc in
      print_program pp prog;
      close_out oc

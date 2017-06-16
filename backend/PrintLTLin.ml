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

(** Pretty-printer for LTLin code *)

open Format
open Camlcoq
open Datatypes
open Maps
open AST
open Integers
open Locations
open Machregsaux
open LTLin
open PrintAST
open PrintOp

let reg pp loc =
  match loc with
  | R r ->
      begin match name_of_register r with
      | Some s -> fprintf pp "%s" s
      | None -> fprintf pp "<unknown reg>"
      end
  | S (Local(ofs, ty)) ->
      fprintf pp "local(%s,%ld)" (name_of_type ty) (camlint_of_coqint ofs)
  | S (Incoming(ofs, ty)) ->
      fprintf pp "incoming(%s,%ld)" (name_of_type ty) (camlint_of_coqint ofs)
  | S (Outgoing(ofs, ty)) ->
      fprintf pp "outgoing(%s,%ld)" (name_of_type ty) (camlint_of_coqint ofs)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_instruction pp i =
  match i with
  | Lop(op, args, res) ->
      fprintf pp "%a = %a@ "
         reg res (PrintOp.print_operation reg) (op, args)
  | Lload(chunk, addr, args, dst) ->
      fprintf pp "%a = %s[%a]@ "
         reg dst (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
  | Lstore(chunk, addr, args, src) ->
      fprintf pp "%s[%a] = %a@ "
         (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
         reg src
  | Lcall(sg, fn, args, res) ->
      fprintf pp "%a = %a(%a)@ "
        reg res ros fn regs args
  | Ltailcall(sg, fn, args) ->
      fprintf pp "tailcall %a(%a)@ "
        ros fn regs args
  | Lbuiltin(ef, args, res) ->
      fprintf pp "%a = builtin %s(%a)@ "
        reg res (name_of_external ef) regs args
  | Llabel lbl ->
      fprintf pp "%ld:@ " (P.to_int32 lbl)
  | Lgoto lbl ->
      fprintf pp "goto %ld@ " (P.to_int32 lbl)
  | Lcond(cond, args, lbl) ->
      fprintf pp "if (%a) goto %ld@ "
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int32 lbl)
  | Ljumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (P.to_int32 tbl.(i))
      done;
      fprintf pp "@]@ "
  | Lreturn None ->
      fprintf pp "return@ "
  | Lreturn (Some arg) ->
      fprintf pp "return %a@ " reg arg

let print_function pp id f =
  fprintf pp "@[<v 2>%s(%a) {@ " (extern_atom id) regs f.fn_params;
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

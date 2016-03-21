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

(** Pretty-printers for RTL code *)

open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open RTL
open PrintAST

(* Printing of RTL code *)

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = P.to_int s in
  if s <> dfl then fprintf pp "\tgoto %d\n" s

let print_instruction pp (pc, i) =
  fprintf pp "%5d:\t" pc;
  match i with
  | Inop s ->
      let s = P.to_int s in
      if s = pc - 1
      then fprintf pp "nop\n"
      else fprintf pp "goto %d\n" s
  | Iop(op, args, res, s) ->
      fprintf pp "%a = %a\n"
         reg res (PrintOp.print_operation reg) (op, args);
      print_succ pp s (pc - 1)
  | Iload(chunk, addr, args, dst, s) ->
      fprintf pp "%a = %s[%a]\n"
         reg dst (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args);
      print_succ pp s (pc - 1)
  | Istore(chunk, addr, args, src, s) ->
      fprintf pp "%s[%a] = %a\n"
         (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
         reg src;
      print_succ pp s (pc - 1)
  | Icall(sg, fn, args, res, s) ->
      fprintf pp "%a = %a(%a)\n"
        reg res ros fn regs args;
      print_succ pp s (pc - 1)
  | Itailcall(sg, fn, args) ->
      fprintf pp "tailcall %a(%a)\n"
        ros fn regs args
  | Ibuiltin(ef, args, res, s) ->
      fprintf pp "%a = %s(%a)\n"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args;
      print_succ pp s (pc - 1)
  | Icond(cond, args, s1, s2) ->
      fprintf pp "if (%a) goto %d else goto %d\n"
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int s1) (P.to_int s2)
  | Ijumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "jumptable (%a)\n" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "\t\tcase %d: goto %d\n" i (P.to_int tbl.(i))
      done
  | Ireturn None ->
      fprintf pp "return\n"
  | Ireturn (Some arg) ->
      fprintf pp "return %a\n" reg arg

let print_function pp id f =
  fprintf pp "%s(%a) {\n" (extern_atom id) regs f.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> Pervasives.compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements f.fn_code)) in
  print_succ pp f.fn_entrypoint
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
  List.iter (print_instruction pp) instrs;
  fprintf pp "}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: RTL.program) =
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if passno prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno) in
      print_program oc prog;
      close_out oc


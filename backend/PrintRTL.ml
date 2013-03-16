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

open Format
open Camlcoq
open Datatypes
open Maps
open AST
open Integers
open RTL
open PrintAST
open PrintOp

(* Printing of RTL code *)

let reg pp r =
  fprintf pp "x%ld" (P.to_int32 r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = P.to_int32 s in
  if s <> dfl then fprintf pp "       goto %ld@ " s

let print_instruction pp (pc, i) =
  fprintf pp "%5ld: " pc;
  match i with
  | Inop s ->
      let s = P.to_int32 s in
      if s = Int32.pred pc
      then fprintf pp "nop@ "
      else fprintf pp "goto %ld@ " s
  | Iop(op, args, res, s) ->
      fprintf pp "%a = %a@ "
         reg res (PrintOp.print_operation reg) (op, args);
      print_succ pp s (Int32.pred pc)
  | Iload(chunk, addr, args, dst, s) ->
      fprintf pp "%a = %s[%a]@ "
         reg dst (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args);
      print_succ pp s (Int32.pred pc)
  | Istore(chunk, addr, args, src, s) ->
      fprintf pp "%s[%a] = %a@ "
         (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
         reg src;
      print_succ pp s (Int32.pred pc)
  | Icall(sg, fn, args, res, s) ->
      fprintf pp "%a = %a(%a)@ "
        reg res ros fn regs args;
      print_succ pp s (Int32.pred pc)
  | Itailcall(sg, fn, args) ->
      fprintf pp "tailcall %a(%a)@ "
        ros fn regs args
  | Ibuiltin(ef, args, res, s) ->
      fprintf pp "%a = builtin %s(%a)@ "
        reg res (name_of_external ef) regs args;
      print_succ pp s (Int32.pred pc)
  | Icond(cond, args, s1, s2) ->
      fprintf pp "if (%a) goto %ld else goto %ld@ "
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int32 s1) (P.to_int32 s2)
  | Ijumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (P.to_int32 tbl.(i))
      done;
      fprintf pp "@]@ "
  | Ireturn None ->
      fprintf pp "return@ "
  | Ireturn (Some arg) ->
      fprintf pp "return %a@ " reg arg

let print_function pp id f =
  fprintf pp "@[<v 2>%s(%a) {@ " (extern_atom id) regs f.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> Pervasives.compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int32 pc, i))
        (PTree.elements f.fn_code)) in
  print_succ pp f.fn_entrypoint 
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1l);
  List.iter (print_instruction pp) instrs;
  fprintf pp "@;<0 -2>}@]@."

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: RTL.program) =
  List.iter (print_globdef pp) prog.prog_defs

let print_if optdest prog =
  match !optdest with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      let pp = formatter_of_out_channel oc in
      print_program pp prog;
      close_out oc

let destination_rtl : string option ref = ref None
let print_rtl = print_if destination_rtl

let destination_tailcall : string option ref = ref None
let print_tailcall = print_if destination_tailcall

let destination_inlining : string option ref = ref None
let print_inlining = print_if destination_inlining

let destination_constprop : string option ref = ref None
let print_constprop = print_if destination_constprop

let destination_cse : string option ref = ref None
let print_cse = print_if destination_cse


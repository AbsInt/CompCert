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
  fprintf pp "x%ld" (camlint_of_positive r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = camlint_of_positive s in
  if s <> dfl then fprintf pp "       goto %ld@ " s

let print_instruction pp (pc, i) =
  fprintf pp "%5ld: " pc;
  match i with
  | Inop s ->
      let s = camlint_of_positive s in
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
        (camlint_of_positive s1) (camlint_of_positive s2)
  | Ijumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (camlint_of_positive tbl.(i))
      done;
      fprintf pp "@]@ "
  | Ireturn None ->
      fprintf pp "return@ "
  | Ireturn (Some arg) ->
      fprintf pp "return %a@ " reg arg

let print_function pp f =
  fprintf pp "@[<v 2>f(%a) {@ " regs f.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> Pervasives.compare pc2 pc1)
      (List.map
        (fun (pc, i) -> (camlint_of_positive pc, i))
        (PTree.elements f.fn_code)) in
  print_succ pp f.fn_entrypoint 
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1l);
  List.iter (print_instruction pp) instrs;
  fprintf pp "@;<0 -2>}@]@."

let print_fundef pp fd =
  match fd with
  | Internal f -> print_function pp f
  | External _ -> ()

let print_if optdest currpp fd =
  match !optdest with
  | None -> ()
  | Some f ->
      let pp =
        match !currpp with
        | Some pp -> pp
        | None ->
            let oc = open_out f in
            let pp = formatter_of_out_channel oc in
            currpp := Some pp;
            pp
      in print_fundef pp fd

let destination_rtl : string option ref = ref None
let pp_rtl : formatter option ref = ref None
let print_rtl = print_if destination_rtl pp_rtl

let destination_tailcall : string option ref = ref None
let pp_tailcall : formatter option ref = ref None
let print_tailcall = print_if destination_tailcall pp_tailcall

let destination_castopt : string option ref = ref None
let pp_castopt : formatter option ref = ref None
let print_castopt = print_if destination_castopt pp_castopt

let destination_constprop : string option ref = ref None
let pp_constprop : formatter option ref = ref None
let print_constprop = print_if destination_constprop pp_constprop

let destination_cse : string option ref = ref None
let pp_cse : formatter option ref = ref None
let print_cse = print_if destination_cse pp_cse


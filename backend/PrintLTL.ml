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
open Locations
open LTL
open PrintAST
open PrintOp
open PrintRTL

let loc pp l =
  match l with
  | R r ->
      begin match Machregsaux.name_of_register r with
      | Some s -> fprintf pp "%s" s
      | None -> fprintf pp "<unknown machreg>"
      end
  | S(Local(ofs, ty)) ->
      fprintf pp "local(%ld,%s)" (camlint_of_coqint ofs) (name_of_typ ty)
  | S(Incoming(ofs, ty)) ->
      fprintf pp "incoming(%ld,%s)" (camlint_of_coqint ofs) (name_of_typ ty)
  | S(Outgoing(ofs, ty)) ->
      fprintf pp "outgoing(%ld,%s)" (camlint_of_coqint ofs) (name_of_typ ty)

let rec locs pp = function
  | [] -> ()
  | [r] -> loc pp r
  | r1::rl -> fprintf pp "%a, %a" loc r1 locs rl

let ros pp = function
  | Coq_inl r -> loc pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = camlint_of_positive s in
  if s <> dfl then fprintf pp "       goto %ld@ " s

let print_instruction pp (pc, i) =
  fprintf pp "%5ld: " pc;
  match i with
  | Lnop s ->
      let s = camlint_of_positive s in
      if s = Int32.pred pc
      then fprintf pp "nop@ "
      else fprintf pp "goto %ld@ " s
  | Lop(op, args, res, s) ->
      fprintf pp "%a = %a@ " loc res (print_operator loc) (op, args);
      print_succ pp s (Int32.pred pc)
  | Lload(chunk, addr, args, dst, s) ->
      fprintf pp "%a = %s[%a]@ "
         loc dst (name_of_chunk chunk) (print_addressing loc) (addr, args);
      print_succ pp s (Int32.pred pc)
  | Lstore(chunk, addr, args, src, s) ->
      fprintf pp "%s[%a] = %a@ "
         (name_of_chunk chunk) (print_addressing loc) (addr, args) loc src;
      print_succ pp s (Int32.pred pc)
  | Lcall(sg, fn, args, res, s) ->
      fprintf pp "%a = %a(%a)@ "
        loc res ros fn locs args;
      print_succ pp s (Int32.pred pc)
  | Ltailcall(sg, fn, args) ->
      fprintf pp "tailcall %a(%a)@ "
        ros fn locs args
  | Lbuiltin(ef, args, res, s) ->
      fprintf pp "%a = builtin %s(%a)@ "
        loc res (name_of_external ef) locs args;
      print_succ pp s (Int32.pred pc)
  | Lcond(cond, args, s1, s2) ->
      fprintf pp "if (%a) goto %ld else goto %ld@ "
        (print_condition loc) (cond, args)
        (camlint_of_positive s1) (camlint_of_positive s2)
  | Ljumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" loc arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (camlint_of_positive tbl.(i))
      done;
      fprintf pp "@]@ "
  | Lreturn None ->
      fprintf pp "return@ "
  | Lreturn (Some arg) ->
      fprintf pp "return %a@ " loc arg

let print_function pp f =
  fprintf pp "@[<v 2>f(%a) {@ " locs f.fn_params;
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

let print_fundef fd =
  begin match fd with
  | Internal f -> print_function std_formatter f
  | External _ -> ()
  end;
  fd



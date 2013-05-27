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

let mreg pp r =
  match Machregsaux.name_of_register r with
  | Some s -> fprintf pp "%s" s
  | None -> fprintf pp "<unknown machreg>"

let rec mregs pp = function
  | [] -> ()
  | [r] -> mreg pp r
  | r1::rl -> fprintf pp "%a, %a" mreg r1 mregs rl

let slot pp (sl, ofs, ty) =
  match sl with
  | Local ->
      fprintf pp "local(%ld,%s)" (camlint_of_coqint ofs) (name_of_type ty)
  | Incoming ->
      fprintf pp "incoming(%ld,%s)" (camlint_of_coqint ofs) (name_of_type ty)
  | Outgoing ->
      fprintf pp "outgoing(%ld,%s)" (camlint_of_coqint ofs) (name_of_type ty)

let loc pp l =
  match l with
  | R r -> mreg pp r
  | S(sl, ofs, ty) -> slot pp (sl, ofs, ty)

let rec locs pp = function
  | [] -> ()
  | [r] -> loc pp r
  | r1::rl -> fprintf pp "%a, %a" loc r1 locs rl

let ros pp = function
  | Coq_inl r -> mreg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = P.to_int32 s in
  if s <> dfl then fprintf pp "goto %ld" s

let print_instruction pp succ = function
  | Lop(op, args, res) ->
      fprintf pp "%a = %a;" mreg res (print_operation mreg) (op, args)
  | Lload(chunk, addr, args, dst) ->
      fprintf pp "%a = %s[%a];"
         mreg dst (name_of_chunk chunk) (print_addressing mreg) (addr, args)
  | Lgetstack(sl, ofs, ty, dst) ->
      fprintf pp "%a = %a;" mreg dst slot (sl, ofs, ty)
  | Lsetstack(src, sl, ofs, ty) ->
      fprintf pp "%a = %a;" slot (sl, ofs, ty) mreg src
  | Lstore(chunk, addr, args, src) ->
      fprintf pp "%s[%a] = %a;"
         (name_of_chunk chunk) (print_addressing mreg) (addr, args) mreg src
  | Lcall(sg, fn) ->
      fprintf pp "call %a;" ros fn
  | Ltailcall(sg, fn) ->
      fprintf pp "tailcall %a;" ros fn
  | Lbuiltin(ef, args, res) ->
      fprintf pp "%a = builtin %s(%a);"
        mregs res (name_of_external ef) mregs args
  | Lannot(ef, args) ->
      fprintf pp "builtin %s(%a);"
        (name_of_external ef) locs args
  | Lbranch s ->
      print_succ pp s succ
  | Lcond(cond, args, s1, s2) ->
      fprintf pp "if (%a) goto %ld else goto %ld"
        (print_condition mreg) (cond, args)
        (P.to_int32 s1) (P.to_int32 s2)
  | Ljumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" mreg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (P.to_int32 tbl.(i))
      done;
      fprintf pp "@]"
  | Lreturn ->
      fprintf pp "return"

let rec print_instructions pp succ = function
  | [] -> ()
  | [i] -> print_instruction pp succ i
  | i :: il ->
      print_instruction pp succ i;
      fprintf pp "@ ";
      print_instructions pp succ il

let print_block pp (pc, blk) =
  fprintf pp "%5ld: @[<hov 0>" pc;
  print_instructions pp (Int32.pred pc) blk;
  fprintf pp "@]@ "

let print_function pp id f =
  fprintf pp "@[<v 2>%s() {@ " (extern_atom id);
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> Pervasives.compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int32 pc, i))
        (PTree.elements f.fn_code)) in
  print_succ pp f.fn_entrypoint 
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1l);
  List.iter (print_block pp) instrs;
  fprintf pp "@;<0 -2>}@]@."

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: LTL.program) =
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

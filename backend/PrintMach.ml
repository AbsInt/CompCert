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
open PrintOp

let name_of_chunk = function
  | Mint8signed -> "int8signed"
  | Mint8unsigned -> "int8unsigned"
  | Mint16signed -> "int16signed"
  | Mint16unsigned -> "int16unsigned"
  | Mint32 -> "int32"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"

let name_of_type = function
  | Tint -> "int"
  | Tfloat -> "float"

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
      fprintf pp "%a = builtin \"%s\"(%a)@ "
        reg res (extern_atom ef.ef_id) regs args
  | Mlabel lbl ->
      fprintf pp "%ld:@ " (camlint_of_positive lbl)
  | Mgoto lbl ->
      fprintf pp "goto %ld@ " (camlint_of_positive lbl)
  | Mcond(cond, args, lbl) ->
      fprintf pp "if (%a) goto %ld@ "
        (PrintOp.print_condition reg) (cond, args)
        (camlint_of_positive lbl)
  | Mjumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (camlint_of_positive tbl.(i))
      done;
      fprintf pp "@]@ "
  | Mreturn ->
      fprintf pp "return@ "

let print_function pp f =
  fprintf pp "@[<v 2>f() {@ ";
  List.iter (print_instruction pp) f.fn_code;
  fprintf pp "@;<0 -2>}@]@."

let print_fundef pp fd =
  match fd with
  | Internal f -> print_function pp f
  | External _ -> ()

let destination : string option ref = ref None
let currpp : formatter option ref = ref None

let print_if fd =
  match !destination with
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

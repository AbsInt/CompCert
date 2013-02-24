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

(* Printing annotations in asm syntax *)

open Printf
open Datatypes
open Integers
open Floats
open Camlcoq
open AST
open Memdata
open Asm

let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"

type arg_value =
  | Reg of preg
  | Stack of memory_chunk * Int.int
  | Intconst of Int.int
  | Floatconst of float

let print_annot_text print_preg sp_reg_name oc txt args =
  let print_fragment = function
  | Str.Text s ->
      output_string oc s
  | Str.Delim "%%" ->
      output_char oc '%'
  | Str.Delim s ->
      let n = int_of_string (String.sub s 1 (String.length s - 1)) in
      try
        match List.nth args (n-1) with
        | Reg r ->
            print_preg oc r
        | Stack(chunk, ofs) ->
            fprintf oc "mem(%s + %ld, %ld)"
               sp_reg_name
               (camlint_of_coqint ofs)
               (camlint_of_coqint (size_chunk chunk))
        | Intconst n ->
            fprintf oc "%ld" (camlint_of_coqint n)
        | Floatconst n ->
            fprintf oc "%.18g" (camlfloat_of_coqfloat n)
      with Failure _ ->
        fprintf oc "<bad parameter %s>" s in
  List.iter print_fragment (Str.full_split re_annot_param txt);
  fprintf oc "\n"

let rec annot_args tmpl args =
  match tmpl, args with
  | [], _ -> []
  | AA_arg _ :: tmpl', APreg r :: args' ->
      Reg r :: annot_args tmpl' args'
  | AA_arg _ :: tmpl', APstack(chunk, ofs) :: args' ->
      Stack(chunk, ofs) :: annot_args tmpl' args'
  | AA_arg _ :: tmpl', [] -> []         (* should never happen *)
  | AA_int n :: tmpl', _ ->
      Intconst n :: annot_args tmpl' args
  | AA_float n :: tmpl', _ ->
      Floatconst n :: annot_args tmpl' args

let print_annot_stmt print_preg sp_reg_name oc txt tmpl args =
  print_annot_text print_preg sp_reg_name oc txt (annot_args tmpl args)

let print_annot_val print_preg oc txt args =
  print_annot_text print_preg "<internal error>" oc txt
    (List.map (fun r -> Reg r) args)

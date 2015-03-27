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

(** Useful functions for pretty-printers *)

open Printf
open Camlcoq
open AST

let name_of_type = function
  | Tint -> "int"
  | Tfloat -> "float"
  | Tlong -> "long"
  | Tsingle -> "single"
  | Tany32 -> "any32"
  | Tany64 -> "any64"

let name_of_chunk = function
  | Mint8signed -> "int8s"
  | Mint8unsigned -> "int8u"
  | Mint16signed -> "int16s"
  | Mint16unsigned -> "int16u"
  | Mint32 -> "int32"
  | Mint64 -> "int64"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"
  | Many32 -> "any32"
  | Many64 -> "any64"

let name_of_external = function
  | EF_external(name, sg) -> sprintf "extern %S" (extern_atom name)
  | EF_builtin(name, sg) -> sprintf "builtin %S" (extern_atom name)
  | EF_vload chunk -> sprintf "volatile load %s" (name_of_chunk chunk)
  | EF_vstore chunk -> sprintf "volatile store %s" (name_of_chunk chunk)
  | EF_vload_global(chunk, id, ofs) ->
      sprintf "volatile load %s global %S %ld"
              (name_of_chunk chunk) (extern_atom id) (camlint_of_coqint ofs)
  | EF_vstore_global(chunk, id, ofs) ->
      sprintf "volatile store %s global %S %ld"
              (name_of_chunk chunk) (extern_atom id) (camlint_of_coqint ofs)
  | EF_malloc -> "malloc"
  | EF_free -> "free"
  | EF_memcpy(sz, al) ->
      sprintf "memcpy size %s align %s " (Z.to_string sz) (Z.to_string al)
  | EF_annot(text, targs) -> sprintf "annot %S" (extern_atom text)
  | EF_annot_val(text, targ) ->  sprintf "annot_val %S" (extern_atom text)
  | EF_inline_asm text -> sprintf "inline_asm %S" (extern_atom text)

let print_annot_arg px oc = function
  | AA_base x -> px oc x
  | AA_int n -> fprintf oc "int %ld" (camlint_of_coqint n)
  | AA_long n -> fprintf oc "long %Ld" (camlint64_of_coqint n)
  | AA_float n -> fprintf oc "float %F" (camlfloat_of_coqfloat n)
  | AA_single n -> fprintf oc "single %F" (camlfloat_of_coqfloat32 n)
  | AA_loadstack(chunk, ofs) -> 
      fprintf oc "%s[sp + %ld]" (name_of_chunk chunk) (camlint_of_coqint ofs)
  | AA_addrstack(ofs) ->
      fprintf oc "sp + %ld" (camlint_of_coqint ofs)
  | AA_loadglobal(chunk, id, ofs) -> 
      fprintf oc "%s[&%s + %ld]"
              (name_of_chunk chunk) (extern_atom id) (camlint_of_coqint ofs)
  | AA_addrglobal(id, ofs) ->
      fprintf oc "&%s + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | AA_longofwords(hi, lo) -> fprintf oc "longofwords %a %a" px hi px lo

let rec print_annot_args px oc = function
  | [] -> ()
  | [a] -> print_annot_arg px oc a
  | a1 :: al ->
      fprintf oc "%a, %a" (print_annot_arg px) a1 (print_annot_args px) al

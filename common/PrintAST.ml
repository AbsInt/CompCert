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

let name_of_chunk = function
  | Mint8signed -> "int8signed"
  | Mint8unsigned -> "int8unsigned"
  | Mint16signed -> "int16signed"
  | Mint16unsigned -> "int16unsigned"
  | Mint32 -> "int32"
  | Mint64 -> "int64"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"
  | Mfloat64al32 -> "float64al32"

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

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
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
  | EF_external(name, sg) -> sprintf "extern %S" (camlstring_of_coqstring name)
  | EF_builtin(name, sg) -> sprintf "builtin %S" (camlstring_of_coqstring name)
  | EF_runtime(name, sg) -> sprintf "runtime %S" (camlstring_of_coqstring name)
  | EF_vload chunk -> sprintf "volatile load %s" (name_of_chunk chunk)
  | EF_vstore chunk -> sprintf "volatile store %s" (name_of_chunk chunk)
  | EF_malloc -> "malloc"
  | EF_free -> "free"
  | EF_memcpy(sz, al) ->
      sprintf "memcpy size %s align %s " (Z.to_string sz) (Z.to_string al)
  | EF_annot(kind,text, targs) -> sprintf "annot %S" (camlstring_of_coqstring text)
  | EF_annot_val(kind,text, targ) ->  sprintf "annot_val %S" (camlstring_of_coqstring text)
  | EF_inline_asm(text, sg, clob) -> sprintf "inline_asm %S" (camlstring_of_coqstring text)
  | EF_debug(kind, text, targs) ->
      sprintf "debug%d %S" (P.to_int kind) (extern_atom text)

let rec print_builtin_arg px oc = function
  | BA x -> px oc x
  | BA_int n -> fprintf oc "int %ld" (camlint_of_coqint n)
  | BA_long n -> fprintf oc "long %Ld" (camlint64_of_coqint n)
  | BA_float n -> fprintf oc "float %.15F" (camlfloat_of_coqfloat n)
  | BA_single n -> fprintf oc "single %.15F" (camlfloat_of_coqfloat32 n)
  | BA_loadstack(chunk, ofs) ->
      fprintf oc "%s[sp + %ld]" (name_of_chunk chunk) (camlint_of_coqint ofs)
  | BA_addrstack(ofs) ->
      fprintf oc "sp + %ld" (camlint_of_coqint ofs)
  | BA_loadglobal(chunk, id, ofs) ->
      fprintf oc "%s[&%s + %ld]"
              (name_of_chunk chunk) (extern_atom id) (camlint_of_coqint ofs)
  | BA_addrglobal(id, ofs) ->
      fprintf oc "&%s + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | BA_splitlong(hi, lo) ->
      fprintf oc "splitlong(%a, %a)"
                 (print_builtin_arg px) hi (print_builtin_arg px) lo
  | BA_addptr(a1, a2) ->
      fprintf oc "addptr(%a, %a)"
                 (print_builtin_arg px) a1 (print_builtin_arg px) a2

let rec print_builtin_args px oc = function
  | [] -> ()
  | [a] -> print_builtin_arg px oc a
  | a1 :: al ->
      fprintf oc "%a, %a" (print_builtin_arg px) a1 (print_builtin_args px) al

let rec print_builtin_res px oc = function
  | BR x -> px oc x
  | BR_none -> fprintf oc "_"
  | BR_splitlong(hi, lo) ->
      fprintf oc "splitlong(%a, %a)"
                 (print_builtin_res px) hi (print_builtin_res px) lo


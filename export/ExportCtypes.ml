(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

open Format
open Camlcoq
open Ctypes
open ExportBase

(* Raw attributes *)

let attribute p a =
  if a = noattr then
    fprintf p "noattr"
  else
    fprintf p "{| attr_volatile := %B; attr_alignas := %a |}"
              a.attr_volatile
              (print_option coqN) a.attr_alignas

(* Raw int size and signedness *)

let intsize p sz =
  fprintf p "%s"
    (match sz with 
     | I8 -> "I8"
     | I16 -> "I16"
     | I32 -> "I32"
     | IBool -> "IBool")

let signedness p sg =
  fprintf p "%s"
    (match sg with
      | Signed -> "Signed"
      | Unsigned -> "Unsigned")

(* Types *)

let rec typ p t =
  match attr_of_type t with
  | { attr_volatile = false; attr_alignas = None} ->
        rtyp p t
  | { attr_volatile = true; attr_alignas = None} ->
        fprintf p "(tvolatile %a)" rtyp t
  | { attr_volatile = false; attr_alignas = Some n} ->
        fprintf p "(talignas %a %a)" coqN n rtyp t
  | { attr_volatile = true; attr_alignas = Some n} ->
        fprintf p "(tvolatile_alignas %a %a)" coqN n rtyp t

and rtyp p = function
  | Tvoid -> fprintf p "tvoid"
  | Ctypes.Tint(sz, sg, _) ->
      fprintf p "%s" (
        match sz, sg with
        | I8, Signed -> "tschar"
        | I8, Unsigned -> "tuchar"
        | I16, Signed -> "tshort"
        | I16, Unsigned -> "tushort"
        | I32, Signed -> "tint"
        | I32, Unsigned -> "tuint"
        | IBool, _ -> "tbool")
  | Ctypes.Tlong(sg, _) ->
      fprintf p "%s" (
        match sg with
        | Signed -> "tlong"
        | Unsigned -> "tulong")
  | Ctypes.Tfloat(sz, _) ->
      fprintf p "%s" (
        match sz with
        | F32 -> "tfloat"
        | F64 -> "tdouble")
  | Tpointer(t, _) ->
      fprintf p "(tptr %a)" typ t
  | Tarray(t, sz, _) ->
      fprintf p "(tarray %a %ld)" typ t (Z.to_int32 sz)
  | Tfunction(targs, tres, cc) ->
      fprintf p "@[<hov 2>(Tfunction@ %a@ %a@ %a)@]"
                typlist targs typ tres callconv cc
  | Tstruct(id, _) ->
      fprintf p "(Tstruct %a noattr)" ident id
  | Tunion(id, _) ->
      fprintf p "(Tunion %a noattr)" ident id

and typlist p = function
  | Tnil ->
      fprintf p "Tnil"
  | Tcons(t, tl) ->
      fprintf p "@[<hov 2>(Tcons@ %a@ %a)@]" typ t typlist tl

(* Access modes for members of structs or unions *)

let bitfield p = function
  | Full ->
      fprintf p "Full"
  | Bits(sz, sg, pos, width) ->
      fprintf p "@[<hov 2>(Bits@ %a@ %a@ %a@ %a)@]"
                intsize sz signedness sg
                coqZ pos coqZ width

(* Composite definitions *)

let print_member p = function
  | Member_plain (id, ty) ->
      fprintf p "@[<hov 2>Member_plain@ %a@ %a@]"
              ident id typ ty
  | Member_bitfield (id, sz, sg, a, width, pad) ->
      fprintf p "@[<hov 2>Member_bitfield@ %a@ %a@ %a@ %a@ %a@ %B@]"
              ident id
              intsize sz
              signedness sg
              attribute a
              coqZ width
              pad

let print_composite_definition p (Composite(id, su, m, a)) =
  fprintf p "@[<hv 2>Composite %a %s@ %a@ %a@]"
    ident id
    (match su with Struct -> "Struct" | Union -> "Union")
    (print_list print_member) m
    attribute a

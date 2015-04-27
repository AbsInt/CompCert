(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(* Simple functions to serialize the C2C information to JSON *)

open C
open C2C
open Camlcoq
open Printf
open Sections

let p_list elem oc l =
  match l with
  | [] -> fprintf oc "null"
  | hd::tail ->
      output_string oc "["; elem oc hd;List.iter (fprintf oc ",%a" elem) tail;output_string oc "]"

let p_int_opt oc = function
  | None -> fprintf oc "null"
  | Some i -> fprintf oc "%d" i

let p_access oc ac =
  let name = match ac with
  | Access_default -> "Default"
  | Access_near -> "Near"
  | Access_far -> "Far" in
  fprintf oc "\"%s\"" name

let p_loc oc (f,l) = fprintf oc "\"%s,%d\"" f l 

let p_storage oc sto =
  let storage = match sto with
  | Storage_default -> "Default"
  | Storage_extern -> "Extern"
  | Storage_static -> "Static"
  | Storage_register -> "Register" in
  fprintf oc "\"%s\"" storage

let p_section oc = function
  | Section_text -> fprintf oc "{\"Section Name\":\"Text\"}"
  | Section_data init -> fprintf oc "{\"Section Name\":\"Data\",\"Init\":%B}" init
  | Section_small_data init -> fprintf oc "{\"Section Name\":\"Small Data\",\"Init\":%B}" init
  | Section_const init -> fprintf oc "{\"Section Name\":\"Const\",\"Init\":%B}" init
  | Section_small_const init -> fprintf oc "{\"Section Name\":\"Small Const\",\"Init\":%B}" init
  | Section_string -> fprintf oc "{\"Section Name\":\"String\"}"
  | Section_literal -> fprintf oc "{\"Section Name\":\"Literal\"}"
  | Section_jumptable -> fprintf oc "{\"Section Name\":\"Jumptable\"}"
  | Section_user (s,w,e) -> fprintf oc "{\"Section Name\":%s,\"Writable\":%B,\"Executable\":%B}" s w e
  | Section_debug_info -> fprintf oc "{\"Section Name\":\"Debug Info\"}"
  | Section_debug_abbrev -> fprintf oc "{\"Section Name\":\"Debug Abbreviation\"}"


let p_atom_info oc info =
  fprintf oc "{\"Storage Class\":%a,\n\"Alignment\":%a,\n\"Sections\":%a,\n\"Access\":%a,\n\"Inline\":%b,\n\"Loc\":%a}"
    p_storage info.a_storage p_int_opt info.a_alignment (p_list p_section) info.a_sections
    p_access info.a_access info.a_inline p_loc info.a_loc

let print_decl_atom oc =
  let first = ref true in
  let sep oc = if !first then first:=false else output_string oc "," in
  output_string oc "{\n";
  Hashtbl.iter (fun id info -> fprintf oc "%t\"%s\":%a\n" sep (extern_atom id) p_atom_info info) decl_atom;
  output_string oc "}"

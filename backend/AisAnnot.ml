(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST
open Camlcoq
open Diagnostics
open Memdata
open Printf

type t =
  | Label of int
  | String of string
  | Symbol of ident

let offset ofs =
  let ofs = camlint_of_coqint ofs in
  if ofs = 0l then "" else sprintf " + %ld" ofs

let size_chunk c =
  sprintf "%ld" (camlint_of_coqint (size_chunk c))

let addr_global id ofs =
  let addr_o = "("
  and addr_e = sprintf "%s)" (offset ofs) in
  [String addr_o;Symbol id;String addr_e]

exception Bad_parameter of string
exception Unknown_parameter of string
exception Unknown_type of char

let ais_expr_arg lval preg_string sp_reg_name arg =
  let preg reg = sprintf "reg(\"%s\")" (preg_string reg)
  and sp = sprintf "reg(\"%s\")" sp_reg_name
  and simple s = [String s]
  and lval ty =
    if lval then
      let msg = sprintf "expected register or memory cell but found %s" ty in
      raise (Bad_parameter msg)
  in
  let rec ais_arg = function
  | BA x -> simple (preg x)
  | BA_int n -> lval "constant"; simple (sprintf "%ld" (camlint_of_coqint n))
  | BA_long n ->lval "constant"; simple (sprintf "%Ld" (camlint64_of_coqint n))
  | BA_float _
  | BA_single _ -> assert false (* Should never occur and be avoided in C2C *)
  | BA_loadstack(chunk, ofs) ->
    let loadstack = sprintf "mem(%s%s, %s)" sp
                       (offset ofs)
                       (size_chunk chunk) in
    simple loadstack
  | BA_addrstack ofs ->
    lval "stack cell";
    let addrstack  = sprintf "(%s%s)" sp (offset ofs) in
    simple addrstack
  | BA_loadglobal(chunk, id, ofs) ->
    let mem_o = "mem("
    and mem_e = sprintf "%s, %s)"
        (offset ofs)
        (size_chunk chunk) in
    [String mem_o;Symbol id;String mem_e]
  | BA_addrglobal(id, ofs) ->
    lval "global address";
    addr_global id ofs
  | BA_splitlong(hi, lo) ->
    combine " * 0x100000000 + " hi lo
  | BA_addptr(a1, a2) ->
    combine " + " a1 a2
  and combine mid arg1 arg2 =
    lval "pointer computation";
    let op_br = simple "("
    and mid = simple mid
    and cl_br = simple ")"
    and arg1 = ais_arg arg1
    and arg2 = ais_arg arg2 in
    op_br@arg1@mid@arg2@cl_br in
  ais_arg arg

let ais_annot_list: (t list) list ref = ref []

let get_ais_annots () =
  let annots = !ais_annot_list in
  ais_annot_list := [];
  List.rev annots

let re_loc_param = Str.regexp "# file:\\([^ ]+\\) line:\\([^ ]+\\)"

let loc_of_txt txt =
  try
    let pos = String.index txt '\n' in
    let txt = String.sub txt 0 (pos -1) in
    if Str.string_partial_match re_loc_param txt 0 then
      let file = Str.matched_group 1 txt
      and line = int_of_string (Str.matched_group 2 txt) in
      file,line
    else
      no_loc
  with _ ->
    no_loc

let re_ais_annot_param = Str.regexp "%%\\|%[aelp][1-9][0-9]*\\|%here\\|\007"

let add_ais_annot lbl preg_string sp_reg_name txt args =
  let fragment = function
    | Str.Delim "%here" ->
      [Label lbl]
    | Str.Text s ->
      [String s]
    | Str.Delim "%%" ->
      [String "%"]
    | Str.Delim "\007" ->
      [String "\007\000"]
    | Str.Delim s ->
      let typ = String.get s 1
      and n = int_of_string (String.sub s 2 (String.length s - 2)) in
      let arg = try
          List.nth args (n-1)
        with _ ->
           raise (Unknown_parameter s) in
      begin match typ with
        | 'e' -> ais_expr_arg false preg_string sp_reg_name arg
        | 'l' -> ais_expr_arg true preg_string sp_reg_name arg
        | _ -> raise (Unknown_type typ)
      end
  in
  let loc = loc_of_txt txt in
  let warn t s =
    warning loc Wrong_ais_parameter "%s %s" t s; []
  in
  let annot  =
    try
      List.concat (List.map fragment (Str.full_split re_ais_annot_param txt))
    with
    | Bad_parameter s ->
      warn "wrong ais parameter" s
    | Unknown_parameter s ->
      warn "unknown parameter" s
    | Unknown_type c ->
      warn "unknown format argument" (String.make 1 c)
  in
  let rec merge acc = function
    | [] -> List.rev acc
    | (Label _ as lbl):: rest ->  merge (lbl::acc) rest
    | (Symbol _ as sym) :: rest -> merge (sym::acc) rest
    | String s1 :: String s2 :: rest ->
      merge acc (String (s1 ^ s2) :: rest)
    | String s:: rest  ->  merge ((String s)::acc) rest
  in
  let annot = merge [] annot in
  if annot <> [] then
    ais_annot_list := (annot)::!ais_annot_list

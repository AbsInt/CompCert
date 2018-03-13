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

let warn_lval_arg  pos arg =
  match arg with
  | BA_int _
  | BA_long _
  | BA_addrstack _
  | BA_addrglobal _
  | BA_splitlong _
  | BA_addptr _ ->
    let msg = sprintf "expected register or memory cell for parameter '%s', skipping generation of ais annotation" pos in
      raise (Bad_parameter msg)
  | BA_float _
  | BA_single _ -> assert false (* Should never occur and be avoided in C2C *)
  | _ -> ()

let ais_expr_arg pos preg_string sp_reg_name arg =
  let preg reg = sprintf "reg(\"%s\")" (preg_string reg)
  and sp = sprintf "reg(\"%s\")" sp_reg_name
  and simple s = [String s]
  in
  let rec ais_arg = function
  | BA x -> simple (preg x)
  | BA_int n -> simple (sprintf "%ld" (camlint_of_coqint n))
  | BA_long n -> simple (sprintf "%Ld" (camlint64_of_coqint n))
  | BA_float _
  | BA_single _ -> assert false (* Should never occur and be avoided in C2C *)
  | BA_loadstack(chunk, ofs) ->
    let loadstack = sprintf "mem(%s%s, %s)" sp
                       (offset ofs)
                       (size_chunk chunk) in
    simple loadstack
  | BA_addrstack ofs ->
    let addrstack  = sprintf "(%s%s)" sp (offset ofs) in
    simple addrstack
  | BA_loadglobal(chunk, id, ofs) ->
    let mem_o = "mem("
    and mem_e = sprintf "%s, %s)"
        (offset ofs)
        (size_chunk chunk) in
    [String mem_o;Symbol id;String mem_e]
  | BA_addrglobal(id, ofs) ->
    addr_global id ofs
  | BA_splitlong(hi, lo) ->
    let arg1 = combine " * " (ais_arg hi) (simple "0x100000000") in
    combine " + " arg1 (ais_arg lo)
  | BA_addptr(a1, a2) ->
    let a1 = ais_arg a1
    and a2 = ais_arg a2 in
    combine " + " a1 a2
  and combine mid arg1 arg2 =
    let op_br = simple "("
    and mid = simple mid
    and cl_br = simple ")" in
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

let re_ais_annot_param = Str.regexp "%%\\|%[el][0-9]+\\|%here\\|\007"

let ais_annot_txt warn lbl preg_string sp_reg_name txt args =
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
      let arg = List.nth args (n-1) in
      begin match typ with
        | 'e' -> ais_expr_arg s preg_string sp_reg_name arg
        | 'l' -> warn_lval_arg s arg; ais_expr_arg s preg_string sp_reg_name arg
        | _ -> assert false
      end
  in
  let annot  =
    try
      List.concat (List.map fragment (Str.full_split re_ais_annot_param txt))
    with
    | Bad_parameter s ->
      if warn then begin
        let loc = loc_of_txt txt in
        warning loc Wrong_ais_parameter "wrong ais parameter: %s" s
      end;
      []
  in
  let rec merge acc = function
    | [] -> acc
    | (Label _ as lbl):: rest ->  merge (lbl::acc) rest
    | (Symbol _ as sym) :: rest -> merge (sym::acc) rest
    | String s1 :: String s2 :: rest ->
      merge acc (String (s1 ^ s2) :: rest)
    | String s:: rest  ->  merge ((String s)::acc) rest
  in
  let rev_annot = match merge [] annot with
    | [] -> []
    | (String s)::rest -> (String (s^"\n"))::rest
    | rest -> (String "\n")::rest in
  List.rev rev_annot

let add_ais_annot lbl preg_string sp_reg_name txt args =
  let annot = ais_annot_txt true lbl preg_string sp_reg_name txt args in
  if annot <> [] then
    ais_annot_list := (annot)::!ais_annot_list

let json_ais_annot preg_string sp_reg_name txt args =
  let txt = ais_annot_txt false 0 preg_string sp_reg_name txt args in
  let t_to_json = function
    | Label _ -> String "%here"
    | String s ->   let buf = Buffer.create (String.length s) in
      String.iter (fun c ->
          begin match c with
            | '\\' | '"' -> Buffer.add_char buf '\\'
            | _ -> () end;
          Buffer.add_char buf c) s;
      String (Buffer.contents buf)
    | Symbol s -> Symbol s in
  (List.map t_to_json txt)

let validate_ais_annot env loc txt args =
  let used_params = Array.make (List.length args) false in
  let fragment arg =
    match arg with
      | Str.Delim "%here"
      | Str.Text _
      | Str.Delim "%%"
      | Str.Delim "\007" -> ()
      | Str.Delim s ->
        let n = int_of_string (String.sub s 2 (String.length s - 2)) in
        try
          let arg = List.nth args (n-1) in
          Array.set used_params (n-1) true;
          if Cutil.is_float_type env arg.C.etyp then
            error loc "floating point types for parameter '%s' are not supported in ais annotations" s
          else if Cutil.is_volatile_variable env arg then begin
            let arg =
              match arg.C.edesc with
              | C.EVar id -> id.C.name
              | _ -> assert false
            in
            error loc "access to volatile variable '%s' for parameter '%s' is not supported in ais annotations" arg s
          end
        with _ ->
          error loc "unknown parameter '%s'" s
  in List.iter fragment (Str.full_split re_ais_annot_param txt);
  Array.iteri (fun pos used -> if not used then warning loc Unused_ais_parameter "unused parameter %d of ais annotation" pos) used_params

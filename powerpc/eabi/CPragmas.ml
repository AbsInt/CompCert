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

(* Platform-dependent handling of pragmas *)

open Printf
open Cil
open Camlcoq

type section_info = {
  sec_name_init: string;
  sec_name_uninit: string;
  sec_near_access: bool
}

let section_table : (string, section_info) Hashtbl.t =
  Hashtbl.create 17

let use_section_table : (AST.ident, section_info) Hashtbl.t =
  Hashtbl.create 51

let process_section_pragma classname istring ustring addrmode accmode =
  let is_near = (addrmode = "near-absolute") || (addrmode = "near-data") in
  let is_writable = String.contains accmode 'W'
  and is_executable = String.contains accmode 'X' in
  let sec_type =
    match is_writable, is_executable with
    | true, true -> 'm'                 (* text+data *)
    | true, false -> 'd'                (* data *)
    | false, true -> 'c'                (* text *)
    | false, false -> 'r'               (* const *)
    in
  let info =
    { sec_name_init = sprintf "%s,,%c" istring sec_type;
      sec_name_uninit = sprintf "%s,,%c" ustring sec_type;
      sec_near_access = is_near } in
  Hashtbl.add section_table classname info

let process_use_section_pragma classname id =
  try
    let info = Hashtbl.find section_table classname in
    Hashtbl.add use_section_table (intern_string id) info
  with Not_found ->
    Cil2Csyntax.error (sprintf "unknown section name `%s'" classname)

(* CIL does not parse the "section" and "use_section" pragmas, which
   have irregular syntax, so we parse them using regexps *)

let re_start_pragma_section = Str.regexp "section\\b"

let re_pragma_section = Str.regexp
  "section[ \t]+\
   \\([A-Za-z_][A-Za-z_0-9]*\\)[ \t]+\
   \"\\([^\"]*\\)\"[ \t]+\
   \"\\([^\"]*\\)\"[ \t]+\
   \\([a-z-]+\\)[ \t]+\
   \\([A-Z]+\\)"

let re_start_pragma_use_section = Str.regexp "use_section\\b"

let re_pragma_use_section = Str.regexp
  "use_section[ \t]+\
   \\([A-Za-z_][A-Za-z_0-9]*\\)[ \t]+\
   \\(.*\\)$"

let re_split_idents = Str.regexp "[ \t,]+"

let process_pragma (Attr(name, _)) =
  if Str.string_match re_pragma_section name 0 then begin
    process_section_pragma
      (Str.matched_group 1 name) (* classname *)
      (Str.matched_group 2 name) (* istring *)
      (Str.matched_group 3 name) (* ustring *)
      (Str.matched_group 4 name) (* addrmode *)
      (Str.matched_group 5 name); (* accmode *)
    true
  end else if Str.string_match re_start_pragma_section name 0 then
    Cil2Csyntax.error "ill-formed `section' pragma"
 else if Str.string_match re_pragma_use_section name 0 then begin
    let classname = Str.matched_group 1 name
    and idents = Str.matched_group 2 name in
    let identlist = Str.split re_split_idents idents in
    if identlist = [] then Cil2Csyntax.warning "vacuous `use_section' pragma";
    List.iter (process_use_section_pragma classname) identlist;
    true
  end else if Str.string_match re_start_pragma_use_section name 0 then
    Cil2Csyntax.error "ill-formed `use_section' pragma"
  else
    false

let initialize () =
  Cil2Csyntax.process_pragma := process_pragma

(* PowerPC-specific: say if an atom is in a small data area *)

let atom_is_small_data a ofs =
  match Configuration.system with
  | "diab" ->
      begin try
        let v = Hashtbl.find Cil2Csyntax.varinfo_atom a in
        let sz = Cil.bitsSizeOf v.vtype / 8 in
        let ofs = camlint_of_coqint ofs in
        if ofs >= 0l && ofs < Int32.of_int sz then begin
          try (Hashtbl.find use_section_table a).sec_near_access
          with Not_found -> sz <= 8
        end else
          false
      with Not_found ->
        false
      end
  | _ ->
      false

(* PowerPC-specific: determine section to use for a particular symbol *)

let section_for_atom a init =
  try
    let sinfo = Hashtbl.find use_section_table a in
    Some(if init then sinfo.sec_name_init else sinfo.sec_name_uninit)
  with Not_found ->
    None
  

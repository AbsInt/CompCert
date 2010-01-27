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
  sec_acc_mode: string;
  sec_near_access: bool
}

let default_section_info = {
  sec_name_init = ".data";
  sec_name_uninit = ".data"; (* COMM? *)
  sec_acc_mode = "RW";
  sec_near_access = false
}

let section_table : (string, section_info) Hashtbl.t =
  Hashtbl.create 17

(* Built-in sections *)

let _ =
  let rodata =
    if Configuration.system = "linux" then ".rodata" else ".text" in
  List.iter (fun (n, si) -> Hashtbl.add section_table n si) [
     "CODE",  {sec_name_init = ".text";
               sec_name_uninit = ".text";
               sec_acc_mode = "RX";
               sec_near_access = false};
     "DATA",  {sec_name_init = ".data";
               sec_name_uninit = ".data"; (* COMM? *)
               sec_acc_mode = "RW";
               sec_near_access = false};
     "SDATA", {sec_name_init = ".sdata";
               sec_name_uninit = ".sbss";
               sec_acc_mode = "RW";
               sec_near_access = true};
     "CONST", {sec_name_init = rodata;
               sec_name_uninit = rodata;
               sec_acc_mode = "R";
               sec_near_access = false};
     "SCONST",{sec_name_init = ".sdata2";
               sec_name_uninit = ".sdata2";
               sec_acc_mode = "R";
               sec_near_access = true};
     "STRING",{sec_name_init = rodata;
               sec_name_uninit = rodata;
               sec_acc_mode = "R";
               sec_near_access = false}
  ]

let process_section_pragma classname istring ustring addrmode accmode =
  let old_si =
    try Hashtbl.find section_table classname
    with Not_found -> default_section_info in
  let si =
    { sec_name_init =
        if istring = "" then old_si.sec_name_init else istring;
      sec_name_uninit =
        if ustring = "" then old_si.sec_name_uninit else ustring;
      sec_acc_mode =
        if accmode = "" then old_si.sec_acc_mode else accmode;
      sec_near_access =
        if addrmode = ""
        then old_si.sec_near_access
        else (addrmode = "near-code") || (addrmode = "near-data") } in
  Hashtbl.add section_table classname si


let use_section_table : (AST.ident, section_info) Hashtbl.t =
  Hashtbl.create 51

let process_use_section_pragma classname id =
  try
    let info = Hashtbl.find section_table classname in
    Hashtbl.add use_section_table (intern_string id) info
  with Not_found ->
    Cil2Csyntax.error (sprintf "unknown section name `%s'" classname)

let default_use_section id classname =
  if not (Hashtbl.mem use_section_table id) then begin
    let info =
      try Hashtbl.find section_table classname
      with Not_found -> assert false in
    Hashtbl.add use_section_table id info
  end

let define_function id v =
  default_use_section id "CODE"

let define_stringlit id v =
  default_use_section id "STRING"

let define_variable id v =
  let sz = Cil.bitsSizeOf v.vtype / 8 in
  let sect =
    if Cil2Csyntax.var_is_readonly v then
      if sz <= !Clflags.option_small_const then "SCONST" else "CONST"
    else
      if sz <= !Clflags.option_small_data then "SDATA" else "DATA" in
  default_use_section id sect

(* CIL does not parse the "section" and "use_section" pragmas, which
   have irregular syntax, so we parse them using regexps *)

let re_start_pragma_section = Str.regexp "section\\b"

let re_pragma_section = Str.regexp(
  "section[ \t]+"
^ "\\([A-Za-z_][A-Za-z_0-9]*\\)[ \t]+"  (* class_name *)
^ "\\(\"[^\"]*\"\\)?[ \t]*"             (* istring *)
^ "\\(\"[^\"]*\"\\)?[ \t]*"             (* ustring *)
^ "\\(standard\\|near-absolute\\|far-absolute\\|near-data\\|far-data\\|near-code\\|far-code\\)?[ \t]*"                  (* addressing mode *)
^ "\\([RWXON]*\\)"                      (* access mode *)
)

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
  Cil2Csyntax.process_pragma_hook := process_pragma;
  Cil2Csyntax.define_variable_hook := define_variable;
  Cil2Csyntax.define_function_hook := define_function;
  Cil2Csyntax.define_stringlit_hook := define_stringlit

(* PowerPC-specific: say if an atom is in a small data area *)

let atom_is_small_data a ofs =
  begin try
    let v = Hashtbl.find Cil2Csyntax.varinfo_atom a in
    let sz = Cil.bitsSizeOf v.vtype / 8 in
    let ofs = camlint_of_coqint ofs in
    if ofs >= 0l && ofs < Int32.of_int sz then begin
      try
        (Hashtbl.find use_section_table a).sec_near_access
      with Not_found ->
        if Cil2Csyntax.var_is_readonly v
        then sz <= !Clflags.option_small_const
        else sz <= !Clflags.option_small_data
    end else
      false
  with Not_found ->
    false
  end

(* PowerPC-specific: determine section to use for a particular symbol *)

let section_for_atom a init =
  try
    let sinfo = Hashtbl.find use_section_table a in
    let sname =
      if init then sinfo.sec_name_init else sinfo.sec_name_uninit in
    if not (String.contains sname '\"') then
      Some sname
    else begin
      (* The following is Diab-specific... *)
      let accmode = sinfo.sec_acc_mode in
      let is_writable = String.contains accmode 'W'
      and is_executable = String.contains accmode 'X' in
      let stype =
        match is_writable, is_executable with
        | true, true -> 'm'                 (* text+data *)
        | true, false -> 'd'                (* data *)
        | false, true -> 'c'                (* text *)
        | false, false -> 'r'               (* const *)
      in Some(sprintf ".section\t%s,,%c" sname stype)
    end
  with Not_found -> None

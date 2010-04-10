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
open Camlcoq
open Cparser

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

(* #pragma section *)

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

(* #pragma use_section *)

let use_section_table : (AST.ident, section_info) Hashtbl.t =
  Hashtbl.create 51

let process_use_section_pragma classname id =
  try
    let info = Hashtbl.find section_table classname in
    Hashtbl.add use_section_table (intern_string id) info
  with Not_found ->
    C2Clight.error (sprintf "unknown section name `%s'" classname)

let default_use_section id classname =
  if not (Hashtbl.mem use_section_table id) then begin
    let info =
      try Hashtbl.find section_table classname
      with Not_found -> assert false in
    Hashtbl.add use_section_table id info
  end

let define_function id d =
  default_use_section id "CODE"

let define_stringlit id =
  default_use_section id "STRING"

let define_variable id d =
  let is_small limit =
    match C2Clight.atom_sizeof id with
    | None -> false
    | Some sz -> sz <= limit in
  let sect =
    if C2Clight.atom_is_readonly id then
      if is_small !Clflags.option_small_const then "SCONST" else "CONST"
    else
      if is_small !Clflags.option_small_data then "SDATA" else "DATA" in
  default_use_section id sect

(* #pragma reserve_register *)

let process_reserve_register_pragma name =
  match Machregsaux.register_by_name name with
  | None ->
      C2Clight.error "unknown register in `reserve_register' pragma"
  | Some r ->
      if Machregsaux.can_reserve_register r then
        Coloringaux.reserved_registers :=
          r :: !Coloringaux.reserved_registers
      else
        C2Clight.error "cannot reserve this register (not a callee-save)"

(* Parsing of pragmas using regexps *)

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

let re_start_pragma_reserve_register = Str.regexp "reserve_register\\b"

let re_pragma_reserve_register = Str.regexp
  "reserve_register[ \t]+\\([A-Za-z0-9]+\\)"

let process_pragma name =
  if Str.string_match re_pragma_section name 0 then begin
    process_section_pragma
      (Str.matched_group 1 name) (* classname *)
      (Str.matched_group 2 name) (* istring *)
      (Str.matched_group 3 name) (* ustring *)
      (Str.matched_group 4 name) (* addrmode *)
      (Str.matched_group 5 name); (* accmode *)
    true
  end else if Str.string_match re_start_pragma_section name 0 then
    (C2Clight.error "ill-formed `section' pragma"; true)
 else if Str.string_match re_pragma_use_section name 0 then begin
    let classname = Str.matched_group 1 name
    and idents = Str.matched_group 2 name in
    let identlist = Str.split re_split_idents idents in
    if identlist = [] then C2Clight.warning "vacuous `use_section' pragma";
    List.iter (process_use_section_pragma classname) identlist;
    true
  end else if Str.string_match re_start_pragma_use_section name 0 then begin
    C2Clight.error "ill-formed `use_section' pragma"; true
  end else if Str.string_match re_pragma_reserve_register name 0 then begin
    process_reserve_register_pragma (Str.matched_group 1 name); true
  end else if Str.string_match re_start_pragma_reserve_register name 0 then begin
    C2Clight.error "ill-formed `reserve_register' pragma"; true
  end else
    false

let initialize () =
  C2Clight.process_pragma_hook := process_pragma;
  C2Clight.define_variable_hook := define_variable;
  C2Clight.define_function_hook := define_function;
  C2Clight.define_stringlit_hook := define_stringlit

(* PowerPC-specific: say if an atom is in a small data area *)

let atom_is_small_data a ofs =
  match C2Clight.atom_sizeof a with
  | None -> false
  | Some sz ->
      let ofs = camlint_of_coqint ofs in
      if ofs >= 0l && ofs < Int32.of_int sz then begin
        try
          (Hashtbl.find use_section_table a).sec_near_access
        with Not_found ->
          if C2Clight.atom_is_readonly a
          then sz <= !Clflags.option_small_const
          else sz <= !Clflags.option_small_data
      end else
        false

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

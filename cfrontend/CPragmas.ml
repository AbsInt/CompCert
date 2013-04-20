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

(* Handling of pragmas *)

open Printf
open Camlcoq

(* #pragma section *)

let sda_supported =
  match Configuration.arch, Configuration.system with
  | "powerpc", "linux" -> true
  | "powerpc", "diab"  -> true
  | _, _ -> false

let process_section_pragma classname istring ustring addrmode accmode =
  Sections.define_section classname
    ?iname: (if istring = "" then None else Some istring)
    ?uname: (if ustring = "" then None else Some ustring)
    ?writable: (if accmode = "" then None else Some(String.contains accmode 'W'))
    ?executable: (if accmode = "" then None else Some(String.contains accmode 'X'))
    ?near: (if addrmode = "" then None else Some(sda_supported && addrmode = "near-data"))
    ()

(* #pragma use_section *)

let process_use_section_pragma classname id =
  if not (Sections.use_section_for (intern_string id) classname)
  then C2C.error (sprintf "unknown section name `%s'" classname)

(* #pragma reserve_register *)

let process_reserve_register_pragma name =
  match Machregsaux.register_by_name name with
  | None ->
      C2C.error "unknown register in `reserve_register' pragma"
  | Some r ->
      if Machregsaux.can_reserve_register r then
        IRC.reserved_registers := r :: !IRC.reserved_registers
      else
        C2C.error "cannot reserve this register (not a callee-save)"

(* Parsing of pragmas using regexps *)

let re_start_pragma_section = Str.regexp "section\\b"

let re_pragma_section = Str.regexp(
  "section[ \t]+"
^ "\\([A-Za-z_][A-Za-z_0-9]*\\)[ \t]+"  (* class_name *)
^ "\"\\([^\"]*\\)\"?[ \t]*"             (* istring *)
^ "\"\\([^\"]*\\)\"?[ \t]*"             (* ustring *)
^ "\\([a-zA-Z-]+\\)?[ \t]*"             (* addressing mode *)
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
    (C2C.error "ill-formed `section' pragma"; true)
 else if Str.string_match re_pragma_use_section name 0 then begin
    let classname = Str.matched_group 1 name
    and idents = Str.matched_group 2 name in
    let identlist = Str.split re_split_idents idents in
    if identlist = [] then C2C.warning "vacuous `use_section' pragma";
    List.iter (process_use_section_pragma classname) identlist;
    true
  end else if Str.string_match re_start_pragma_use_section name 0 then begin
    C2C.error "ill-formed `use_section' pragma"; true
  end else if Str.string_match re_pragma_reserve_register name 0 then begin
    process_reserve_register_pragma (Str.matched_group 1 name); true
  end else if Str.string_match re_start_pragma_reserve_register name 0 then begin
    C2C.error "ill-formed `reserve_register' pragma"; true
  end else
    false

let initialize () =
  C2C.process_pragma_hook := process_pragma

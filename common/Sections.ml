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

open Camlcoq
open Cparser

module StringMap = Map.Make(String)

(* Handling of linker sections *)

type section_name =
  | Section_text
  | Section_data of bool          (* true = init data, false = uninit data *)
  | Section_small_data of bool
  | Section_const
  | Section_small_const
  | Section_string
  | Section_literal
  | Section_jumptable
  | Section_user of string * bool (*writable*) * bool (*executable*)

type section_info = {
  sec_name_init: section_name;
  sec_name_uninit: section_name;
  sec_writable: bool;
  sec_executable: bool;
  sec_near_access: bool
}

let default_section_info = {
  sec_name_init = Section_data true;
  sec_name_uninit = Section_data false;
  sec_writable = true;
  sec_executable = false;
  sec_near_access = false
}

(* Built-in sections *)

let builtin_sections = [
  "CODE",
     {sec_name_init = Section_text; 
      sec_name_uninit = Section_text;
      sec_writable = false; sec_executable = true;
      sec_near_access = false};
  "DATA",
     {sec_name_init = Section_data true;
      sec_name_uninit = Section_data false;
      sec_writable = true; sec_executable = false;
      sec_near_access = false};
  "SDATA",
     {sec_name_init = Section_small_data true;
      sec_name_uninit = Section_small_data false;
      sec_writable = true; sec_executable = false;
      sec_near_access = true};
  "CONST",
     {sec_name_init = Section_const;
      sec_name_uninit = Section_const;
      sec_writable = false; sec_executable = false;
      sec_near_access = false};
  "SCONST",
     {sec_name_init = Section_small_const;
      sec_name_uninit = Section_small_const;
      sec_writable = false; sec_executable = false;
      sec_near_access = true};
  "STRING",
     {sec_name_init = Section_string;
      sec_name_uninit = Section_string;
      sec_writable = false; sec_executable = false;
      sec_near_access = false};
  "LITERAL",
     {sec_name_init = Section_literal;
      sec_name_uninit = Section_literal;
      sec_writable = false; sec_executable = false;
      sec_near_access = false};
  "JUMPTABLE",
     {sec_name_init = Section_jumptable;
      sec_name_uninit = Section_jumptable;
      sec_writable = false; sec_executable = false;
      sec_near_access = false}
]

let default_section_table =
  List.fold_right
    (fun (s, i) t -> StringMap.add s i t)
    builtin_sections StringMap.empty


(* The current mapping from section names to section info *)

let current_section_table : (section_info StringMap.t) ref = 
  ref StringMap.empty

(* The section to use for each global symbol: either explicitly
   assigned using a "use_section" pragma, or inferred at definition
   time. *)

let use_section_table : (AST.ident, section_info) Hashtbl.t =
  Hashtbl.create 51

(* For each global symbol, the mapping sect name -> sect info
   current at the time it was defined *)

let section_table_at_def : (AST.ident, section_info StringMap.t) Hashtbl.t =
  Hashtbl.create 51

let initialize () =
  current_section_table := default_section_table;
  Hashtbl.clear use_section_table;
  Hashtbl.clear section_table_at_def

(* Define or update a given section. *)

let define_section name ?iname ?uname ?writable ?executable ?near () =
  let si = 
    try StringMap.find name !current_section_table
    with Not_found -> default_section_info in
  let writable =
    match writable with Some b -> b | None -> si.sec_writable
  and executable =
    match executable with Some b -> b | None -> si.sec_executable
  and near =
    match near with Some b -> b | None -> si.sec_near_access in
  let iname =
    match iname with Some s -> Section_user(s, writable, executable)
                   | None -> si.sec_name_init in
  let uname =
    match uname with Some s -> Section_user(s, writable, executable)
                   | None -> si.sec_name_uninit in
  let new_si =
    { sec_name_init = iname;
      sec_name_uninit = uname;
      sec_writable = writable;
      sec_executable = executable;
      sec_near_access = near } in
  current_section_table := StringMap.add name new_si !current_section_table

(* Explicitly associate a section to a global symbol *)

let use_section_for id name =
  try
    let si = StringMap.find name !current_section_table in
    Hashtbl.add use_section_table id si;
    true
  with Not_found ->
    false

(* Default association of a section to a global symbol *)

let default_use_section id name =
  Hashtbl.add section_table_at_def id !current_section_table;
  if not (Hashtbl.mem use_section_table id) then begin
    let ok = use_section_for id name in
    assert ok
  end

(* Associate an undeclared section to a global symbol, GCC-style *)

let use_gcc_section id name readonly exec =
  Hashtbl.add section_table_at_def id !current_section_table;
  let sn = Section_user(name, not readonly, exec) in
  let si = { sec_name_init = sn; sec_name_uninit = sn;
             sec_writable = not readonly; sec_executable = exec;
             sec_near_access = false } in
  Hashtbl.add use_section_table id si

(* Record sections for a variable definition *)

let define_variable env id ty =
  let attr = Cutil.attributes_of_type env ty in
  let readonly = List.mem C.AConst attr && not(List.mem C.AVolatile attr) in
  (* Check for a GCC-style "section" attribute *)
  match Cutil.find_custom_attributes ["section"; "__section__"] attr with
  | [[C.AString name]] ->
    (* Use gcc-style section *)
    use_gcc_section id name readonly false
  | _ ->
    (* Use default section appropriate for size and const-ness *)
    let size = match Cutil.sizeof env ty with Some sz -> sz | None -> max_int in
    default_use_section id
      (if readonly
       then if size <= !Clflags.option_small_const then "SCONST" else "CONST"
       else if size <= !Clflags.option_small_data then "SDATA" else "DATA")

(* Record sections for a function definition *)

let define_function env id ty_res =
  let attr = Cutil.attributes_of_type env ty_res in
  match Cutil.find_custom_attributes ["section"; "__section__"] attr with
  | [[C.AString name]] ->
      use_gcc_section id name true true
  | _ ->
      default_use_section id "CODE"

(* Record sections for a string literal *)

let define_stringlit id =
  default_use_section id "STRING"

(* Determine section to use for a variable *)

let section_for_variable a initialized =
  try
    let si = Hashtbl.find use_section_table a in
    if initialized then si.sec_name_init else si.sec_name_uninit
  with Not_found ->
    Section_data initialized

(* Determine (text, literal, jumptable) sections to use for a function *)

let sections_for_function a =
  let s_text =
    try (Hashtbl.find use_section_table a).sec_name_init
    with Not_found -> Section_text in
  let s_table =
    try Hashtbl.find section_table_at_def a
    with Not_found -> default_section_table in
  let s_literal =
    try (StringMap.find "LITERAL" s_table).sec_name_init
    with Not_found -> Section_literal in
  let s_jumptable =
    try (StringMap.find "JUMPTABLE" s_table).sec_name_init
    with Not_found -> Section_jumptable in
  (s_text, s_literal, s_jumptable)

(* Say if an atom is in a small data area *)

let atom_is_small_data a ofs =
  try (Hashtbl.find use_section_table a).sec_near_access
  with Not_found -> false

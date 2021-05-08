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

(* Handling of linker sections *)

type initialized =
  | Uninit       (* uninitialized data area *)
  | Init         (* initialized with fixed, non-relocatable data *)
  | Init_reloc   (* initialized with relocatable data (symbol addresses) *)

type section_name =
  | Section_text
  | Section_data of initialized
  | Section_small_data of initialized
  | Section_const of initialized
  | Section_small_const of initialized
  | Section_string
  | Section_literal
  | Section_jumptable
  | Section_user of string * bool (*writable*) * bool (*executable*)
  | Section_debug_abbrev
  | Section_debug_info of string option
  | Section_debug_loc
  | Section_debug_line of string option
  | Section_debug_ranges
  | Section_debug_str
  | Section_ais_annotation

type access_mode =
  | Access_default
  | Access_near
  | Access_far

type section_info = {
  sec_name_init: section_name;
  sec_name_init_reloc: section_name;
  sec_name_uninit: section_name;
  sec_writable: bool;
  sec_executable: bool;
  sec_access: access_mode
}

let default_section_info = {
  sec_name_init = Section_data Init;
  sec_name_init_reloc = Section_data Init_reloc;
  sec_name_uninit = Section_data Uninit;
  sec_writable = true;
  sec_executable = false;
  sec_access = Access_default
}

(* Built-in sections *)

let builtin_sections = [
  "CODE",
     {sec_name_init = Section_text;
      sec_name_init_reloc = Section_text;
      sec_name_uninit = Section_text;
      sec_writable = false; sec_executable = true;
      sec_access = Access_default};
  "DATA",
     {sec_name_init = Section_data Init;
      sec_name_init_reloc = Section_data Init_reloc;
      sec_name_uninit = Section_data Uninit;
      sec_writable = true; sec_executable = false;
      sec_access = Access_default};
  "SDATA",
     {sec_name_init = Section_small_data Init;
      sec_name_init_reloc = Section_small_data Init_reloc;
      sec_name_uninit = Section_small_data Uninit;
      sec_writable = true; sec_executable = false;
      sec_access = Access_near};
  "CONST",
     {sec_name_init = Section_const Init;
      sec_name_init_reloc = Section_const Init_reloc;
      sec_name_uninit = Section_const Uninit;
      sec_writable = false; sec_executable = false;
      sec_access = Access_default};
  "SCONST",
     {sec_name_init = Section_small_const Init;
      sec_name_init_reloc = Section_small_const Init_reloc;
      sec_name_uninit = Section_small_const Uninit;
      sec_writable = false; sec_executable = false;
      sec_access = Access_near};
  "STRING",
     {sec_name_init = Section_string;
      sec_name_init_reloc = Section_string;
      sec_name_uninit = Section_string;
      sec_writable = false; sec_executable = false;
      sec_access = Access_default};
  "LITERAL",
     {sec_name_init = Section_literal;
      sec_name_init_reloc = Section_literal;
      sec_name_uninit = Section_literal;
      sec_writable = false; sec_executable = false;
      sec_access = Access_default};
  "JUMPTABLE",
     {sec_name_init = Section_jumptable;
      sec_name_init_reloc = Section_jumptable;
      sec_name_uninit = Section_jumptable;
      sec_writable = false; sec_executable = false;
      sec_access = Access_default}
]

(* The current mapping from section names to section info *)

let current_section_table : (string, section_info) Hashtbl.t =
  Hashtbl.create 17

(* The section assigned to a global symbol using a "use_section" pragma *)

let use_section_table : (AST.ident, section_info) Hashtbl.t =
  Hashtbl.create 51

let initialize () =
  Hashtbl.clear current_section_table;
  List.iter
    (fun (s, i) -> Hashtbl.add current_section_table s i)
    builtin_sections;
  Hashtbl.clear use_section_table

(* Define or update a given section. *)

let define_section name ?iname ?uname ?writable ?executable ?access () =
  let si =
    try Hashtbl.find current_section_table name
    with Not_found -> default_section_info in
  let writable =
    match writable with Some b -> b | None -> si.sec_writable
  and executable =
    match executable with Some b -> b | None -> si.sec_executable
  and access =
    match access with Some b -> b | None -> si.sec_access in
  let i =
    match iname with Some s -> Section_user(s, writable, executable)
                   | None -> si.sec_name_init in
  let ir =
    match iname with Some s -> Section_user(s, writable, executable)
                   | None -> si.sec_name_init_reloc in
  let u =
    match uname with Some s -> Section_user(s, writable, executable)
                   | None -> si.sec_name_uninit in
  let new_si =
    { sec_name_init = i;
      sec_name_init_reloc = ir;
      sec_name_uninit = u;
      sec_writable = writable;
      sec_executable = executable;
      sec_access = access } in
  Hashtbl.replace current_section_table name new_si

(* Explicitly associate a section to a global symbol *)

let use_section_for id name =
  try
    let si = Hashtbl.find current_section_table name in
    Hashtbl.add use_section_table id si;
    true
  with Not_found ->
    false

(* Undeclared section attached to a global variable, GCC-style *)

let gcc_section name readonly exec =
  let sn = Section_user(name, not readonly, exec) in
  { sec_name_init = sn; sec_name_init_reloc = sn; sec_name_uninit = sn;
    sec_writable = not readonly; sec_executable = exec;
    sec_access = Access_default }

(* Check and extract whether a section was given as attribute *)

let get_attr_section loc attr =
  match Cutil.find_custom_attributes ["section"; "__section__"] attr with
  | [] -> None
  | [[C.AString name]] -> Some name
  | [[_]] ->
    Diagnostics.error loc "'section' attribute requires a string";
    None
  | _ ->
    Diagnostics.error loc "ambiguous 'section' attribute";
    None

(* Determine section for a variable definition *)

let for_variable env loc id ty init =
  let attr = Cutil.attributes_of_type env ty in
  let readonly = List.mem C.AConst attr && not(List.mem C.AVolatile attr) in
  let si =
    try
      (* 1- Section explicitly associated with #use_section *)
      Hashtbl.find use_section_table id
    with Not_found ->
      match get_attr_section loc attr with
      | Some name ->
        (* 2- Section given as an attribute, gcc-style *)
        gcc_section name readonly false
      | None ->
        (* 3- Default section appropriate for size and const-ness *)
        let size =
          match Cutil.sizeof env ty with Some sz -> sz | None -> max_int in
        let name =
          if readonly
          then if size <= !Clflags.option_small_const then "SCONST" else "CONST"
          else if size <= !Clflags.option_small_data then "SDATA" else "DATA" in
        try
          Hashtbl.find current_section_table name
        with Not_found ->
          assert false in
  let secname =
    match init with
    | Uninit -> si.sec_name_uninit
    | Init -> si.sec_name_init
    | Init_reloc -> si.sec_name_init_reloc in
  (secname, si.sec_access)

(* Determine sections for a function definition *)

let for_function env loc id attr =
  let si_code =
    try
      (* 1- Section explicitly associated with #use_section *)
      Hashtbl.find use_section_table id
    with Not_found ->
      match get_attr_section loc attr with
      | Some name ->
          (* 2- Section given as an attribute, gcc-style *)
          gcc_section name true true
      | None ->
          (* 3- Default section *)
          try
            Hashtbl.find current_section_table "CODE"
          with Not_found ->
            assert false in
  let si_literal =
    try
      Hashtbl.find current_section_table "LITERAL"
    with Not_found ->
      assert false in
  let si_jumptbl =
    try
      Hashtbl.find current_section_table "JUMPTABLE"
    with Not_found ->
      assert false in
  [si_code.sec_name_init; si_literal.sec_name_init; si_jumptbl.sec_name_init]

(* Determine section for a string literal *)

let for_stringlit() =
  let si =
    try
      Hashtbl.find current_section_table "STRING"
    with Not_found ->
      assert false in
  si.sec_name_init

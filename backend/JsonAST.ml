(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*          Michael Schmidt, AbsInt Angewandte Informatik GmbH         *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

open Asm
open AST
open C2C
open Json
open Format
open Sections


let pp_storage pp static =
  pp_jstring pp (if static then "Static" else "Extern")

let pp_section pp sec =
  let pp_simple name =
    pp_jsingle_object pp "Section Name" pp_jstring name
  and pp_complex name init =
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Section Name" pp_jstring name;
    pp_jmember pp "Init" pp_jbool init;
    pp_jobject_end pp in
  match sec with
  | Section_text -> pp_simple "Text"
  | Section_data init -> pp_complex "Data" init
  | Section_small_data init -> pp_complex "Small Data" init
  | Section_const init -> pp_complex "Const" init
  | Section_small_const init -> pp_complex "Small Const" init
  | Section_string -> pp_simple "String"
  | Section_literal -> pp_simple "Literal"
  | Section_jumptable -> pp_simple "Jumptable"
  | Section_user (s,w,e) ->
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Section Name" pp_jstring s;
    pp_jmember pp "Writable" pp_jbool w;
    pp_jmember pp "Executable" pp_jbool e;
    pp_jobject_end pp
  | Section_debug_info _
  | Section_debug_abbrev
  | Section_debug_line _
  | Section_debug_loc
  | Section_debug_ranges
  | Section_debug_str
  | Section_ais_annotation -> () (* There should be no info in the debug sections *)

let pp_int_opt pp = function
  | None -> fprintf pp "0"
  | Some i -> fprintf pp "%d" i

let pp_fundef pp_inst pp (name,fn) =
  let alignment = atom_alignof name
  and inline = atom_inline name = Inline
  and static = atom_is_static name
  and c_section,l_section,j_section = match (atom_sections name) with [a;b;c] -> a,b,c | _ -> assert false in
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Fun Name" pp_atom name;
  pp_jmember pp "Fun Storage Class" pp_storage static;
  pp_jmember pp "Fun Alignment" pp_int_opt alignment;
  pp_jmember pp "Fun Section Code" pp_section c_section;
  pp_jmember pp "Fun Section Literals" pp_section l_section;
  pp_jmember pp "Fun Section Jumptable" pp_section j_section;
  pp_jmember pp "Fun Inline" pp_jbool inline;
  pp_jmember pp "Fun Code" pp_inst fn.fn_code;
  pp_jobject_end pp

let pp_init_data pp = function
  | Init_int8 ic -> pp_jsingle_object pp "Init_int8" pp_int ic
  | Init_int16 ic -> pp_jsingle_object pp "Init_int16" pp_int ic
  | Init_int32 ic -> pp_jsingle_object pp "Init_int32" pp_int ic
  | Init_int64 lc -> pp_jsingle_object pp "Init_int64" pp_int64 lc
  | Init_float32 f -> pp_jsingle_object pp "Init_float32" pp_float32 f
  | Init_float64 f -> pp_jsingle_object pp "Init_float64" pp_float64 f
  | Init_space z -> pp_jsingle_object pp "Init_space" pp_z z
  | Init_addrof (p,i) ->
    let pp_addr_of pp (p,i) =
      pp_jobject_start pp;
      pp_jmember ~first:true pp "Addr" pp_atom p;
      pp_jmember  pp "Offset" pp_int i;
      pp_jobject_end pp  in
    pp_jsingle_object pp "Init_addrof" pp_addr_of (p,i)

let pp_vardef pp (name,v) =
  let alignment = atom_alignof name
  and static = atom_is_static name
  and section = match  (atom_sections name) with [s] -> s | _ -> assert false in(* Should only have one section *)
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Var Name" pp_atom name;
  pp_jmember pp "Var Readonly" pp_jbool v.gvar_readonly;
  pp_jmember pp "Var Volatile" pp_jbool v.gvar_volatile;
  pp_jmember pp "Var Storage Class" pp_storage static;
  pp_jmember pp "Var Alignment" pp_int_opt alignment;
  pp_jmember pp "Var Section" pp_section section;
  pp_jmember pp "Var Init" (pp_jarray pp_init_data) v.gvar_init;
  pp_jobject_end pp

let pp_program pp pp_inst prog =
  let prog_vars,prog_funs = List.fold_left (fun (vars,funs) (ident,def) ->
      match def with
      | Gfun (Internal f) ->
        if not (atom_is_iso_inline_definition ident) then
          vars,(ident,f)::funs
        else
          vars,funs
      | Gvar v -> (ident,v)::vars,funs
      | _ -> vars,funs) ([],[]) prog.prog_defs in
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Global Variables" (pp_jarray pp_vardef) prog_vars;
  pp_jmember pp "Functions" (pp_jarray (pp_fundef pp_inst)) prog_funs;
  pp_jobject_end pp

let pp_mnemonics pp mnemonic_names =
  let mnemonic_names = List.sort (String.compare) mnemonic_names in
  let new_line pp () = pp_print_string pp "\n" in
  pp_print_list ~pp_sep:new_line pp_print_string pp mnemonic_names

let jdump_magic_number = "CompCertJDUMP" ^ Version.version

let pp_ast pp pp_inst ast sourcename =
   let get_args () =
    let buf = Buffer.create 100 in
    Buffer.add_string buf Sys.executable_name;
    for i = 1 to (Array.length  !Commandline.argv - 1) do
      Buffer.add_string buf " ";
      Buffer.add_string buf (Responsefile.gnu_quote !Commandline.argv.(i));
    done;
    Buffer.contents buf in
    let dump_compile_info pp () =
      pp_jobject_start pp;
      pp_jmember ~first:true pp "directory" pp_jstring (Sys.getcwd ());
      pp_jmember pp "command" pp_jstring (get_args ());
      pp_jmember pp "file" pp_jstring sourcename;
      pp_jobject_end pp in
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Version" pp_jstring jdump_magic_number;
    let json_arch =
      match Configuration.arch, !Clflags.option_mthumb with
      | "arm", false -> "arm-arm"
      | "arm", true  -> "arm-thumb"
      | a, _ -> a in
    pp_jmember pp "Architecture" pp_jstring json_arch;
    pp_jmember pp "System" pp_jstring Configuration.system;
    pp_jmember pp "Compile Info" dump_compile_info ();
    pp_jmember pp "Compilation Unit" pp_jstring sourcename;
    pp_jmember pp "Asm Ast" (fun pp prog -> pp_program pp pp_inst prog) ast;
    pp_jobject_end pp;
    Format.pp_print_flush pp ()

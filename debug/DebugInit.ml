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

open AST
open BinNums
open C
open Camlcoq
open Dwarfgen
open DwarfTypes
open Debug

let default_debug =
  {
   init = DebugInformation.init;
   atom_global = DebugInformation.atom_global;
   set_composite_size = DebugInformation.set_composite_size;
   set_member_offset = DebugInformation.set_member_offset;
   set_bitfield_offset = DebugInformation.set_bitfield_offset;
   insert_global_declaration = DebugInformation.insert_global_declaration;
   add_fun_addr = (fun _ _ _ -> ());
   generate_debug_info = (fun _ _  -> None);
   all_files_iter = (fun f -> DebugInformation.StringSet.iter f !DebugInformation.all_files);
   insert_local_declaration = DebugInformation.insert_local_declaration;
   atom_local_variable = DebugInformation.atom_local_variable;
   enter_scope = DebugInformation.enter_scope;
   enter_function_scope = DebugInformation.enter_function_scope;
   add_lvar_scope = DebugInformation.add_lvar_scope;
   open_scope = DebugInformation.open_scope;
   close_scope = DebugInformation.close_scope;
   start_live_range = DebugInformation.start_live_range;
   end_live_range = DebugInformation.end_live_range;
   stack_variable = DebugInformation.stack_variable;
   add_label = DebugInformation.add_label;
   atom_parameter = DebugInformation.atom_parameter;
   compute_diab_file_enum = DebugInformation.compute_diab_file_enum;
   compute_gnu_file_enum = DebugInformation.compute_gnu_file_enum;
   exists_section = DebugInformation.exists_section;
   remove_unused = DebugInformation.remove_unused;
   variable_printed = DebugInformation.variable_printed;
   add_diab_info = (fun _ _ _ _ -> ());
 }

let init_debug () =
  implem :=
  if ArchConfig.diab_system () then
    let gen = (fun a b -> Some (Dwarfgen.gen_diab_debug_info a b)) in
    Clflags.option_gdwarf := 2; (* Dwarf 2 is the only supported target *)
    {default_debug with generate_debug_info = gen;
     add_diab_info = DebugInformation.add_diab_info;
     add_fun_addr = DebugInformation.diab_add_fun_addr;}
  else
    {default_debug with generate_debug_info = (fun a b -> Some (Dwarfgen.gen_gnu_debug_info a b));
     add_fun_addr = DebugInformation.gnu_add_fun_addr}

let init_none () =
  implem := default_implem

let init () =
  if !Clflags.option_g && Configuration.advanced_debug then
    init_debug ()
  else
    init_none ()

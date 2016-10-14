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

open Clflags
open Commandline
open Debug
open Driveraux

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
   all_files_iter = DebugInformation.all_files_iter;
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
   remove_unused_function = DebugInformation.remove_unused_function;
   variable_printed = DebugInformation.variable_printed;
   add_diab_info = (fun _ _ _ _ -> ());
 }

let init_debug () =
  implem :=
  if Configuration.system = "diab" then
    let gen = (fun a b -> Some (Dwarfgen.gen_diab_debug_info a b)) in
    {default_debug with generate_debug_info = gen;
     add_diab_info = DebugInformation.add_diab_info;
     add_fun_addr = DebugInformation.diab_add_fun_addr;}
  else
    {default_debug with generate_debug_info = (fun a b -> Some (Dwarfgen.gen_gnu_debug_info a b));
     add_fun_addr = DebugInformation.gnu_add_fun_addr}

let init_none () =
  implem := default_implem

let init () =
  if !option_g then
    init_debug ()
  else
    init_none ()

let gnu_debugging_help =
"  -gdwarf-       Generate debug information in DWARF v2 or DWARF v3\n"

let debugging_help =
"Debugging options:\n\
\  -g             Generate debugging information\n\
\  -g<n>          Control generation of debugging information\n\
\                 (<n>=0: none, <n>=1: only-globals, <n>=2: globals + locals \n\
\                 without locations, <n>=3: full;)\n"
^ (if gnu_system then gnu_debugging_help else "")

let gnu_debugging_actions =
  let version version () =
    option_g:=true;
    option_gdwarf:=version
  in
  [Exact "-gdwarf-2", Unit (version 2);
   Exact "-gdwarf-3", Unit (version 3);]

let debugging_actions =
  let depth depth () =
    option_g:=true;
    option_gdepth := depth
  in
  [Exact "-g", Unit (depth 3);
   Exact "-g0", Unset option_g;
   Exact "-g1", Unit (depth 1);
   Exact "-g2", Unit (depth 2);
   Exact "-g3", Unit (depth 3);]
  @
  (if gnu_system then gnu_debugging_actions else [])

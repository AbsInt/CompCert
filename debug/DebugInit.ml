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

let init_debug () =
  implem.init <- DebugInformation.init;
  implem.atom_function <- DebugInformation.atom_function;
  implem.atom_global_variable <- DebugInformation.atom_global_variable;
  implem.set_composite_size <- DebugInformation.set_composite_size;
  implem.set_member_offset <- DebugInformation.set_member_offset;
  implem.set_bitfield_offset <- DebugInformation.set_bitfield_offset;
  implem.insert_global_declaration <- DebugInformation.insert_global_declaration;
  implem.add_fun_addr <- DebugInformation.add_fun_addr;
  implem.generate_debug_info <- 
    if Configuration.system = "diab" then
      (fun a b -> Some (Dwarfgen.gen_diab_debug_info a b))
    else
      (fun a b -> Some (Dwarfgen.gen_gnu_debug_info a b));
  implem.all_files_iter <- (fun f -> DebugInformation.StringSet.iter f !DebugInformation.all_files);
  implem.insert_local_declaration <- DebugInformation.insert_local_declaration;
  implem.atom_local_variable <- DebugInformation.atom_local_variable;
  implem.enter_scope <- DebugInformation.enter_scope;
  implem.enter_function_scope <- DebugInformation.enter_function_scope;
  implem.add_lvar_scope <- DebugInformation.add_lvar_scope;
  implem.open_scope <- DebugInformation.open_scope;
  implem.close_scope <- DebugInformation.close_scope;
  implem.start_live_range <- DebugInformation.start_live_range;
  implem.end_live_range <- DebugInformation.end_live_range;
  implem.stack_variable <- DebugInformation.stack_variable;
  implem.function_end <- DebugInformation.function_end;
  implem.add_label <- DebugInformation.add_label;
  implem.atom_parameter <- DebugInformation.atom_parameter;
  implem.add_compilation_section_start <- DebugInformation.add_compilation_section_start;
  implem.add_compilation_section_end <- DebugInformation.add_compilation_section_end;
  implem.compute_file_enum <- DebugInformation.compute_file_enum;
  implem.exists_section <- DebugInformation.exists_section;
  implem.remove_unused <- DebugInformation.remove_unused;
  implem.variable_printed <- DebugInformation.variable_printed;
  implem.add_diab_info <- DebugInformation.add_diab_info

let init_none () =
  implem.init <- (fun _ -> ());
  implem.atom_function <- (fun _ _ -> ());
  implem.atom_global_variable <- (fun _ _ -> ());
  implem.set_composite_size <- (fun _ _ _ -> ());
  implem.set_member_offset <- (fun _ _ _ -> ());
  implem.set_bitfield_offset <- (fun _ _ _ _ _ -> ());
  implem.insert_global_declaration <- (fun _ _ -> ());
  implem.add_fun_addr <- (fun _ _ -> ());
  implem.generate_debug_info <- (fun _ _ -> None);
  implem.all_files_iter <- (fun _ -> ());
  implem.insert_local_declaration <- (fun  _ _ _ _ -> ());
  implem.atom_local_variable <- (fun _ _ -> ());
  implem.enter_scope <- (fun _ _  _ -> ());
  implem.enter_function_scope <- (fun _ _ -> ());
  implem.add_lvar_scope <- (fun _ _ _ -> ());
  implem.open_scope <- (fun _ _ _ -> ());
  implem.close_scope <- (fun _ _ _ -> ());
  implem.start_live_range <- (fun _ _ _ -> ());
  implem.end_live_range <- (fun _ _ -> ());
  implem.stack_variable <- (fun _ _ -> ());
  implem.function_end <- (fun _ _ -> ());
  implem.add_label <- (fun _ _ _ -> ());
  implem.atom_parameter <- (fun _ _ _ -> ());
  implem.add_compilation_section_start <- (fun _ _ -> ());
  implem.add_compilation_section_end <- (fun _ _ -> ());
  implem.exists_section <- (fun _ -> true);
  implem.remove_unused <- (fun _ -> ());
  implem.variable_printed <- (fun _ -> ());
  implem.add_diab_info <- (fun _ _ -> ())

let init () =
  if !Clflags.option_g && Configuration.advanced_debug then
    init_debug ()
  else
    init_none ()

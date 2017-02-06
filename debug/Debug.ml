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

open BinNums
open C
open Camlcoq
open DwarfTypes
open Sections

(* Interface for generating and printing debug information *)

(* Record used for storing references to the actual implementation functions *)
type implem =
    {
      init: string -> unit;
      atom_global: ident -> atom -> unit;
      set_composite_size: ident -> struct_or_union -> int option -> unit;
      set_member_offset: ident -> string -> int -> unit;
      set_bitfield_offset: ident -> string -> int -> string -> int -> unit;
      insert_global_declaration: Env.t -> globdecl -> unit;
      add_fun_addr: atom -> section_name -> (int * int) -> unit;
      generate_debug_info: (atom -> string) -> string -> debug_entries option;
      all_files_iter: (string -> unit) -> unit;
      insert_local_declaration:  storage -> ident -> C.typ -> location -> unit;
      atom_local_variable: ident -> atom -> unit;
      enter_scope: int -> int -> int -> unit;
      enter_function_scope: int -> int -> unit;
      add_lvar_scope: int -> ident -> int -> unit;
      open_scope: atom -> int -> positive -> unit;
      close_scope: atom -> int -> positive -> unit;
      start_live_range: (atom * atom) -> positive -> int * int AST.builtin_arg -> unit;
      end_live_range: (atom * atom) -> positive -> unit;
      stack_variable: (atom * atom) -> int * int AST.builtin_arg -> unit;
      add_label: atom -> positive -> int -> unit;
      atom_parameter: ident -> ident -> atom -> unit;
      compute_diab_file_enum: (section_name -> int) -> (string-> int) -> (unit -> unit) -> unit;
      compute_gnu_file_enum: (string -> unit) -> unit;
      exists_section: section_name -> bool;
      remove_unused: ident -> unit;
      remove_unused_function: ident -> unit;
      variable_printed: string -> unit;
      add_diab_info: section_name -> int -> int -> int -> unit;
   }

let default_implem =
  {
   init = (fun _ -> ());
   atom_global = (fun _ _ -> ());
   set_composite_size = (fun _ _ _ -> ());
   set_member_offset = (fun _ _  _ -> ());
   set_bitfield_offset = (fun _ _ _ _ _ -> ());
   insert_global_declaration = (fun _ _ -> ());
   add_fun_addr = (fun _ _ _ -> ());
   generate_debug_info = (fun _  _ -> None);
   all_files_iter = (fun _ -> ());
   insert_local_declaration = (fun  _ _ _ _ -> ());
   atom_local_variable = (fun _ _ -> ());
   enter_scope = (fun _ _ _  -> ());
   enter_function_scope = (fun _ _ -> ());
   add_lvar_scope = (fun _ _ _ -> ());
   open_scope = (fun _ _ _ -> ());
   close_scope = (fun _ _ _ -> ());
   start_live_range = (fun _ _ _ -> ());
   end_live_range = (fun _ _ -> ());
   stack_variable = (fun _ _ -> ());
   add_label = (fun _ _ _ -> ());
   atom_parameter = (fun _ _ _ -> ());
   compute_diab_file_enum = (fun _ _ _ -> ());
   compute_gnu_file_enum = (fun _ -> ());
   exists_section = (fun _ -> true);
   remove_unused = (fun _ -> ());
   remove_unused_function = (fun _ -> ());
   variable_printed = (fun _ -> ());
   add_diab_info = (fun _ _ _ _ -> ());
}

let implem = ref default_implem

let init_compile_unit name = !implem.init name
let atom_global id atom = !implem.atom_global id atom
let set_composite_size id sou size = !implem.set_composite_size id sou size
let set_member_offset id field off = !implem.set_member_offset id field off
let set_bitfield_offset id field off underlying size = !implem.set_bitfield_offset id field off underlying size
let insert_global_declaration env dec = !implem.insert_global_declaration env dec
let add_fun_addr atom addr = !implem.add_fun_addr atom addr
let generate_debug_info fun_s var_s = !implem.generate_debug_info fun_s var_s
let all_files_iter f = !implem.all_files_iter f
let insert_local_declaration sto id ty loc = !implem.insert_local_declaration sto id ty loc
let atom_local_variable id atom = !implem.atom_local_variable id atom
let enter_scope p_id id = !implem.enter_scope p_id id
let enter_function_scope fun_id sc_id = !implem.enter_function_scope fun_id sc_id
let add_lvar_scope fun_id var_id s_id = !implem.add_lvar_scope fun_id var_id s_id
let open_scope atom id lbl = !implem.open_scope atom id lbl
let close_scope atom id lbl = !implem.close_scope atom id lbl
let start_live_range atom lbl loc = !implem.start_live_range atom lbl loc
let end_live_range atom lbl = !implem.end_live_range atom lbl
let stack_variable atom loc = !implem.stack_variable atom loc
let add_label atom p lbl = !implem.add_label atom p lbl
let atom_parameter fid pid atom = !implem.atom_parameter fid pid atom
let exists_section sec = !implem.exists_section sec
let compute_diab_file_enum end_l entry_l line_e = !implem.compute_diab_file_enum end_l entry_l line_e
let compute_gnu_file_enum f = !implem.compute_gnu_file_enum f
let remove_unused ident = !implem.remove_unused ident
let remove_unused_function ident = !implem.remove_unused_function ident
let variable_printed ident = !implem.variable_printed ident
let add_diab_info sec line_start debug_info low_pc = !implem.add_diab_info sec line_start debug_info low_pc

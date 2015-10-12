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

(* Interface for generating and printing debug information *)

(* Record used for stroring references to the actual implementation functions *)
type implem = 
    {
     mutable init: string -> unit;
     mutable atom_global: ident -> atom -> unit;
     mutable set_composite_size: ident -> struct_or_union -> int option -> unit;
     mutable set_member_offset: ident -> string -> int -> unit;
     mutable set_bitfield_offset: ident -> string -> int -> string -> int -> unit;
     mutable insert_global_declaration: Env.t -> globdecl -> unit;
     mutable add_fun_addr: atom -> (int * int) -> unit;
     mutable generate_debug_info: (atom -> string) -> string -> debug_entries option;
     mutable all_files_iter: (string -> unit) -> unit;
     mutable insert_local_declaration:  storage -> ident -> typ -> location -> unit;
     mutable atom_local_variable: ident -> atom -> unit;
     mutable enter_scope: int -> int -> int -> unit;
     mutable enter_function_scope: int -> int -> unit;
     mutable add_lvar_scope: int -> ident -> int -> unit;
     mutable open_scope: atom -> int -> positive -> unit;
     mutable close_scope: atom -> int -> positive -> unit;
     mutable start_live_range: (atom * atom) -> positive -> int * int builtin_arg -> unit;
     mutable end_live_range: (atom * atom) -> positive -> unit;
     mutable stack_variable: (atom * atom) -> int * int builtin_arg -> unit;
     mutable function_end: atom -> positive -> unit;
     mutable add_label: atom -> positive -> int -> unit;
     mutable atom_parameter: ident -> ident -> atom -> unit;
     mutable add_compilation_section_start: string -> int -> unit;
     mutable add_compilation_section_end: string -> int -> unit;
     mutable compute_diab_file_enum: (string -> int) -> (string-> int) -> (unit -> unit) -> unit;
     mutable compute_gnu_file_enum: (string -> unit) -> unit;
     mutable exists_section: string -> bool;
     mutable remove_unused: ident -> unit;
     mutable variable_printed: string -> unit;
     mutable add_diab_info: string -> (int * int * string) -> unit;
   }

let implem =
  {
   init = (fun _ -> ());
   atom_global = (fun _ _ -> ());
   set_composite_size = (fun _ _ _ -> ());
   set_member_offset = (fun _ _  _ -> ());
   set_bitfield_offset = (fun _ _ _ _ _ -> ());
   insert_global_declaration = (fun _ _ -> ());
   add_fun_addr = (fun _ _ -> ());
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
   function_end = (fun _ _ -> ());
   add_label = (fun _ _ _ -> ());
   atom_parameter = (fun _ _ _ -> ());
   add_compilation_section_start = (fun _ _ -> ());
   add_compilation_section_end = (fun _ _ -> ());
   compute_diab_file_enum = (fun _ _ _ -> ());
   compute_gnu_file_enum = (fun _ -> ());
   exists_section = (fun _ -> true);
   remove_unused = (fun _ -> ());
   variable_printed = (fun _ -> ());
   add_diab_info = (fun _ _ -> ());
}

let init_compile_unit name = implem.init name
let atom_global id atom = implem.atom_global id atom
let set_composite_size id sou size = implem.set_composite_size id sou size
let set_member_offset id field off = implem.set_member_offset id field off
let set_bitfield_offset id field off underlying size = implem.set_bitfield_offset id field off underlying size
let insert_global_declaration env dec = implem.insert_global_declaration env dec
let add_fun_addr atom addr = implem.add_fun_addr atom addr
let generate_debug_info fun_s var_s = implem.generate_debug_info fun_s var_s
let all_files_iter f = implem.all_files_iter f
let insert_local_declaration sto id ty loc = implem.insert_local_declaration sto id ty loc
let atom_local_variable id atom = implem.atom_local_variable id atom
let enter_scope p_id id = implem.enter_scope p_id id
let enter_function_scope fun_id sc_id = implem.enter_function_scope fun_id sc_id
let add_lvar_scope fun_id var_id s_id = implem.add_lvar_scope fun_id var_id s_id
let open_scope atom id lbl = implem.open_scope atom id lbl
let close_scope atom id lbl = implem.close_scope atom id lbl
let start_live_range atom lbl loc = implem.start_live_range atom lbl loc
let end_live_range atom lbl = implem.end_live_range atom lbl
let stack_variable atom loc = implem.stack_variable atom loc
let function_end atom loc = implem.function_end atom loc
let add_label atom p lbl = implem.add_label atom p lbl
let atom_parameter fid pid atom = implem.atom_parameter fid pid atom
let add_compilation_section_start sec addr = implem.add_compilation_section_start sec addr
let add_compilation_section_end sec addr = implem.add_compilation_section_end sec addr
let exists_section sec = implem.exists_section sec
let compute_diab_file_enum end_l entry_l line_e = implem.compute_diab_file_enum end_l entry_l line_e
let compute_gnu_file_enum f = implem.compute_gnu_file_enum f
let remove_unused ident = implem.remove_unused ident
let variable_printed ident = implem.variable_printed ident
let add_diab_info sec addr = implem.add_diab_info sec addr

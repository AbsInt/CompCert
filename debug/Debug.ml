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
     mutable atom_function: ident -> atom -> unit;
     mutable atom_global_variable: ident -> atom -> unit;
     mutable set_composite_size: ident -> struct_or_union -> int option -> unit;
     mutable set_member_offset: ident -> string -> int -> unit;
     mutable set_bitfield_offset: ident -> string -> int -> string -> int -> unit;
     mutable insert_global_declaration: Env.t -> globdecl -> unit;
     mutable add_fun_addr: atom -> (int * int) -> unit;
     mutable generate_debug_info: unit -> (dw_entry * dw_locations) option;
     mutable all_files_iter: (string -> unit) -> unit;
     mutable insert_local_declaration:  storage -> ident -> typ -> location -> unit;
     mutable atom_local_variable: ident -> atom -> unit;
     mutable enter_scope: int -> int -> int -> unit;
     mutable enter_function_scope: int -> int -> unit;
     mutable add_lvar_scope: int -> ident -> int -> unit;
     mutable open_scope: atom -> int -> positive -> unit;
     mutable close_scope: atom -> int -> positive -> unit;
     mutable start_live_range: atom -> positive -> int * int builtin_arg -> unit;
     mutable end_live_range: atom -> positive -> unit;
     mutable stack_variable: atom -> int * int builtin_arg -> unit;
     mutable function_end: atom -> positive -> unit;
     mutable add_label: atom -> positive -> int -> unit;
   }

let implem =
  {
   init = (fun _ -> ());
   atom_function = (fun _ _ -> ());
   atom_global_variable = (fun _ _ -> ());
   set_composite_size = (fun _ _ _ -> ());
   set_member_offset = (fun _ _  _ -> ());
   set_bitfield_offset = (fun _ _ _ _ _ -> ());
   insert_global_declaration = (fun _ _ -> ());
   add_fun_addr = (fun _ _ -> ());
   generate_debug_info = (fun _ -> None);
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
}

let init () =
  if !Clflags.option_g then begin
    implem.init <- DebugInformation.init;
    implem.atom_function <- DebugInformation.atom_function;
    implem.atom_global_variable <- DebugInformation.atom_global_variable;
    implem.set_composite_size <- DebugInformation.set_composite_size;
    implem.set_member_offset <- DebugInformation.set_member_offset;
    implem.set_bitfield_offset <- DebugInformation.set_bitfield_offset;
    implem.insert_global_declaration <- DebugInformation.insert_global_declaration;
    implem.add_fun_addr <- DebugInformation.add_fun_addr;
    implem.generate_debug_info <- (fun () -> Some (Dwarfgen.gen_debug_info ()));
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
  end else begin
    implem.init <- (fun _ -> ());
    implem.atom_function <- (fun _ _ -> ());
    implem.atom_global_variable <- (fun _ _ -> ());
    implem.set_composite_size <- (fun _ _ _ -> ());
    implem.set_member_offset <- (fun _ _ _ -> ());
    implem.set_bitfield_offset <- (fun _ _ _ _ _ -> ());
    implem.insert_global_declaration <- (fun _ _ -> ());
    implem.add_fun_addr <- (fun _ _ -> ());
    implem.generate_debug_info <- (fun _ -> None);
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
  end

let init_compile_unit name = implem.init name
let atom_function id atom = implem.atom_function id atom
let atom_global_variable id atom = implem.atom_global_variable id atom
let set_composite_size id sou size = implem.set_composite_size id sou size
let set_member_offset id field off = implem.set_member_offset id field off
let set_bitfield_offset id field off underlying size = implem.set_bitfield_offset id field off underlying size
let insert_global_declaration env dec = implem.insert_global_declaration env dec
let add_fun_addr atom addr = implem.add_fun_addr atom addr
let generate_debug_info () = implem.generate_debug_info ()
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

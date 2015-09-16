(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST
open Asm
open Camlcoq
open Datatypes
open DwarfPrinter
open PrintAsmaux
open Printf
open Sections
open TargetPrinter

module Printer(Target:TARGET) =
  struct

    let addr_mapping: (string, (int * int)) Hashtbl.t = Hashtbl.create 7

    let get_fun_addr name =
      let s = new_label ()
      and e = new_label () in
      Debug.add_fun_addr name (s,e);
      s,e

    let print_debug_label oc l =
      if !Clflags.option_g && Configuration.advanced_debug then
        fprintf oc "%a:\n" Target.label l
      else
        ()


    let print_location oc loc =
      if loc <> Cutil.no_loc then Target.print_file_line oc (fst loc) (snd loc)
          
    let print_function oc name fn =
      Hashtbl.clear current_function_labels;
      Target.reset_constants ();
      let (text, lit, jmptbl) = Target.get_section_names name in
      Target.section oc text;
      let alignment =
        match !Clflags.option_falignfunctions with Some n -> n | None -> Target.default_falignment in
      Target.print_align oc alignment;
      if not (C2C.atom_is_static name) then
        fprintf oc "	.globl %a\n" Target.symbol name;
      Target.print_optional_fun_info oc;
      let s,e = if !Clflags.option_g && Configuration.advanced_debug then
        get_fun_addr name
      else
        -1,-1 in
      print_debug_label oc s;
      fprintf oc "%a:\n" Target.symbol name;
      print_location oc (C2C.atom_location name);
      Target.cfi_startproc oc;
      Target.print_instructions oc fn;
      Target.cfi_endproc oc;
      print_debug_label oc e;
      Target.print_fun_info oc name;
      Target.emit_constants oc lit;
      Target.print_jumptable oc jmptbl
    
    let print_init_data oc name id =
      if Str.string_match PrintCsyntax.re_string_literal (extern_atom name) 0
          && List.for_all (function Init_int8 _ -> true | _ -> false) id
      then
        fprintf oc "	.ascii	\"%s\"\n" (PrintCsyntax.string_of_init id)
      else
        List.iter (Target.print_init oc) id
 
    let print_var oc name v =
      if !Clflags.option_g && Configuration.advanced_debug then Target.add_var_location name;
      match v.gvar_init with
      | [] -> ()
      | _  ->
          let sec =
            match C2C.atom_sections name with
            | [s] -> s
        |  _  -> Section_data true
          and align =
            match C2C.atom_alignof name with
            | Some a -> a
            | None -> 8 in (* 8-alignment is a safe default *)
          let name_sec = Target.name_of_section sec in
          if name_sec <> "COMM" then begin
            fprintf oc "	%s\n" name_sec;
            Target.print_align oc align;
            if not (C2C.atom_is_static name) then
              fprintf oc "	.globl	%a\n" Target.symbol name;
            fprintf oc "%a:\n" Target.symbol name;
            print_init_data oc name v.gvar_init;
            Target.print_var_info oc name;
          end else
            let sz =
              match v.gvar_init with [Init_space sz] -> sz | _ -> assert false in
            Target.print_comm_symb oc sz name align
                            
    let print_globdef oc (name,gdef) =
      match gdef with
      | Gfun (Internal code) -> print_function oc name code
      | Gfun (External ef) ->   ()
      | Gvar v -> print_var oc name v

    module DwarfTarget: DwarfTypes.DWARF_TARGET =
      struct
        let label = Target.label
        let name_of_section = Target.name_of_section
        let print_file_loc = Target.print_file_loc
        let get_start_addr = Target.get_start_addr   
        let get_end_addr = Target.get_end_addr
        let get_stmt_list_addr = Target.get_stmt_list_addr
        let name_of_section = Target.name_of_section
        let get_fun_addr s = try Some (Hashtbl.find addr_mapping s) with Not_found -> None
        let get_location a =  None
        let get_frame_base a = None
        let symbol = Target.symbol
      end

    module DebugPrinter = DwarfPrinter (DwarfTarget) (Target.DwarfAbbrevs)
      
     
  end

let print_program oc p db =
  let module Target = (val (sel_target ()):TARGET) in
  let module Printer = Printer(Target) in
  reset_filenames ();
  print_version_and_options oc Target.comment;
  Target.print_prologue oc;
  List.iter (Printer.print_globdef oc) p.prog_defs;
  Target.print_epilogue oc;
  close_filenames ();
  if !Clflags.option_g && Configuration.advanced_debug then
    begin
      match db with
      | None -> ()
      | Some db ->
          Printer.DebugPrinter.print_debug oc db
    end

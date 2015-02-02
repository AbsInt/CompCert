(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* The Diab specific printing functions *)

open Printf
open Datatypes
open DwarfTypes
open DwarfUtil
open DwarfPrinter
open Camlcoq
open Sections
open Asm
open PrintUtil
    
module Diab_System =
  (struct
    let comment =  ";"
        
    let constant oc cst =
      match cst with
      | Cint n ->
          fprintf oc "%ld" (camlint_of_coqint n)
      | Csymbol_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_high(s, n) ->
          symbol_fragment oc s n "@ha"
      | Csymbol_sda(s, n) ->
          symbol_fragment oc s n "@sdarx"
      | Csymbol_rel_low(s, n) ->
          symbol_fragment oc s n "@sdax@l"
      | Csymbol_rel_high(s, n) ->
          symbol_fragment oc s n "@sdarx@ha"
            
    let ireg oc r =
      output_char oc 'r';
      output_string oc (int_reg_name r)

    let freg oc r =
      output_char oc 'f';
      output_string oc (float_reg_name r)
        
    let creg oc r =
      fprintf oc "cr%d" r
        
    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i -> if i then ".data" else "COMM"
      | Section_small_data i -> if i then ".sdata" else ".sbss"
      | Section_const _ -> ".text"
      | Section_small_const _ -> ".sdata2"
      | Section_string -> ".text"
      | Section_literal -> ".text"
      | Section_jumptable -> ".text"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",,%c"
               s
            (match wr, ex with
            | true, true -> 'm'                 (* text+data *)
            | true, false -> 'd'                (* data *)
            | false, true -> 'c'                (* text *)
            | false, false -> 'r')              (* const *)

    let filenum : (string, int) Hashtbl.t = Hashtbl.create 7

    let print_file_line oc file line =
      PrintAnnot.print_file_line_d2 oc comment file line;
      if !Clflags.option_g && file <> "" && not (Hashtbl.mem filenum file) then
          Hashtbl.add filenum file (new_label ())

    (* Emit .cfi directives *)
    let cfi_startproc oc = ()

    let cfi_endproc oc = ()

    let cfi_adjust oc delta = ()

    let cfi_rel_offset oc reg ofs = ()
        
    let debug_line_start = ref (-1)

    let compilation_unit_start_addr = ref (-1)

    let compilation_unit_end_addr = ref (-1)
      
    (* Mapping from debug addresses to labels *)
    let addr_label_map: (int,int) Hashtbl.t = Hashtbl.create 7

    let set_compilation_unit_addrs cu_start cu_end =
      compilation_unit_start_addr := cu_start;
      compilation_unit_end_addr := cu_end

    let debug_info_start = ref (-1)

    let print_addr_label oc addr =
      let lbl = try
        Hashtbl.find addr_label_map addr
      with Not_found ->
        let lbl = new_label () in
        Hashtbl.add addr_label_map addr lbl;
        lbl in
      fprintf oc "%a:\n" label lbl

    let register_addr_label = Hashtbl.add addr_label_map

    let print_prologue oc =
      fprintf oc "	.xopt	align-fill-text=0x60000000\n";
      if !Clflags.option_g then
      begin
        fprintf oc "	.text\n";
        fprintf oc "	.section	.debug_line,,n\n";
        let label_debug_line = new_label () in
        debug_line_start := label_debug_line;
        fprintf oc "%a:\n" label label_debug_line;
        fprintf oc "	.text\n";
        print_addr_label oc !compilation_unit_start_addr;
        let label_debug_info = new_label () in
        debug_info_start := label_debug_info;
        fprintf oc "	.0byte	%a\n" label label_debug_info;
        fprintf oc "	.d2_line_start	.debug_line\n";
        fprintf oc "	.text\n";
        fprintf oc "	.align	2\n"
      end
          
    let print_epilogue oc =
      if !Clflags.option_g then
        begin
          (* Everthink available for printing of the compilation unit *)
          fprintf oc "	.text\n";
          (* End Address of the compilation unit *)
          print_addr_label oc !compilation_unit_end_addr;
          (* Print the filenum which is used for the location expressions *)
          Hashtbl.iter (fun name lbl ->
            fprintf oc "%a:	.d2filenum \"%s\"\n" label lbl name) filenum;
          (* The end of the debug line info *)
          fprintf oc "	.d2_line_end\n";
        end



  end:SYSTEM)

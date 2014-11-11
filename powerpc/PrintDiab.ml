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
      | Section_data i -> if i then ".data" else ".bss"
      | Section_small_data i -> if i then ".sdata" else ".sbss"
      | Section_const -> ".text"
      | Section_small_const -> ".sdata2"
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

    let last_file = ref ""
    let reset_file_line () = last_file := ""
    let print_file_line oc file line =
      if !Clflags.option_g && file <> "" then begin
        if file <> !last_file then begin
          fprintf oc "	.d1file	%S\n" file;
          last_file := file
        end;
        fprintf oc "	.d1line	%s\n" line
      end

          (* Emit .cfi directives *)
    let cfi_startproc oc = ()

    let cfi_endproc oc = ()

    let cfi_adjust oc delta = ()

    let cfi_rel_offset oc reg ofs = ()

    let print_prologue oc =
      fprintf oc "	.xopt	align-fill-text=0x60000000\n";
      if !Clflags.option_g then
        fprintf oc "	.xopt	asm-debug-on\n"
          

    module DiabAbbrvs =
      (struct
        let string_of_byte value =
          if value then
            "	.byte	0x1\n"
          else
            
            "	.byte	0x0\n"
            
        let string_of_uleb v =
          Printf.sprintf "	.uleb128	%d\n" v

        let sibling_type_abbr = 0x13
        let decl_file_type_abbr = 0x6
        let decl_line_type_abbr = 0xf
        let type_abbr = 0x10
        let name_type_abbr = 0x8
        let encoding_type_abbr = 0xb
        let byte_size_type_abbr = 0xb
        let high_pc_type_abbr = 0x1
        let low_pc_type_abbr = 0x1
        let stmt_list_type_abbr = 0x6
        let declaration_type_abbr = 0xc
        let external_type_abbr = 0xc
        let prototyped_type_abbr = 0xc
        let bit_offset_type_abbr = 0xb
        let comp_dir_type_abbr = 0x8
        let language_type_abbr = 0xf
        let producer_type_abbr = 0x8
        let value_type_abbr = 0xd
        let artificial_type_abbr = 0xc
        let variable_parameter_type_abbr = 0xc
        let bit_size_type_abbr = 0xb
        let location_const_type_abbr = 0x6
        let location_block_type_abbr = 0x9
        let data_location_block_type_abbr = 0x9
        let data_location_ref_type_abbr = 0x13
        let bound_const_type_abbr = 0xf
        let bound_ref_type_abbr=0x13
      end:ABBRV_DEFS)

  end:SYSTEM)

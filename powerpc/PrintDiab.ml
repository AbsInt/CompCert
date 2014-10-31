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
          
    let curr_abbrv = ref 0

    let next_abbrv =
      let abbrv = !curr_abbrv in
      incr curr_abbrv;abbrv

    let abbrvs: string list ref = ref []

    let abbrv_mapping: (string,int) Hashtbl.t = Hashtbl.create 7

    let add_byte buf value =
      let s = 
        if value then
          "	.byte	0x1\n"
        else
          
          "	.byte	0x0\n"
      in
      Buffer.add_string buf s

    let add_abbr_uleb v buf =
      Buffer.add_string buf "	.uleb128	";
      Buffer.add_string buf (string_of_int v);
      Buffer.add_string buf "\n"
   

    let add_abbr_entry (v1,v2) buf =
      add_abbr_uleb v1 buf;
      add_abbr_uleb v2 buf
 
   let add_sibling = add_abbr_entry (1,19)

    let add_decl_file = add_abbr_entry (58,6)
 
    let add_decl_line = add_abbr_entry (59,15)
        
    let add_type = add_abbr_entry (73,16)
   
    let add_name = add_abbr_entry (3,8)
        
    let add_encoding = add_abbr_entry (62,11)

    let add_byte_size = add_abbr_entry (11,11)

    let add_high_pc = add_abbr_entry (18,1)

    let add_low_pc = add_abbr_entry (17,1)

    let add_stmt_list = add_abbr_entry (16,6)
        
    let add_declaration = add_abbr_entry (60,12)

    let abbrv_string_of_entity entity has_sibling =
      let buf = Buffer.create 12 in
      let add_attr_some v f =
        match v with
        | None -> ()
        | Some _ -> f buf in
      let prologue id =
        let has_child = match entity.children with
        | [] -> false
        | _ -> true in
        add_abbr_uleb id buf;
        add_byte buf has_child;
        if has_sibling then add_sibling buf; 
      in     
      (match entity.tag with
      | DW_TAG_array_type e -> 
          prologue 1;
          add_attr_some e.array_type_decl_file add_decl_file;
          add_attr_some e.array_type_decl_line add_decl_line;
          add_type buf
      | DW_TAG_base_type _ ->
          prologue 36;
          add_encoding buf;
          add_byte_size buf;
          add_name buf
      | DW_TAG_compile_unit e ->
          prologue 17;
          add_abbr_entry (27,8) buf;
          add_high_pc buf;
          add_low_pc buf;
          add_abbr_entry (19,15) buf;
          add_name buf;
          add_abbr_entry (37,8) buf;
          add_attr_some e.compile_unit_stmt_list add_stmt_list
      | DW_TAG_const_type _ ->
          prologue 40;
          add_type buf
      | DW_TAG_enumeration_type e ->
          prologue 4;
          add_attr_some e.enumeration_decl_file add_decl_file;
          add_attr_some e.enumeration_decl_line add_decl_line;
          add_byte_size buf;
          add_name buf;
          add_attr_some e.enumeration_declaration add_declaration
      | DW_TAG_enumerator e ->
          prologue 40;
          add_attr_some e.enumerator_decl_file add_decl_file;
          add_attr_some e.enumerator_decl_line add_decl_line;
          add_abbr_entry (28,13) buf;
          add_name buf
      | DW_TAG_label _ ->
          prologue 10;
          add_low_pc buf;
          add_name buf;
      | DW_TAG_lexical_block _ ->
          prologue 0xb;
          add_high_pc buf;
          add_low_pc buf
      | DW_TAG_member e ->
          prologue 0xd;
          add_attr_some e.member_decl_file add_decl_file;
          add_attr_some e.member_decl_line add_decl_line;
          add_attr_some e.member_byte_size add_byte_size;
          add_attr_some e.member_bit_offset (add_abbr_entry (13,11));
          add_attr_some e.member_bit_size (add_abbr_entry (12,11));
          add_attr_some e.member_data_member_location (add_abbr_entry (56,9));
          add_attr_some e.member_declaration add_declaration;
          add_name buf;
          add_type buf
      | DW_TAG_pointer_type _ ->
          prologue 0xf;
          add_type buf
      | DW_TAG_structure_type e ->
          prologue 0x13;
          add_attr_some e.structure_decl_file add_decl_file;
          add_attr_some e.structure_decl_line add_decl_line;
          add_byte_size buf;
          add_attr_some e.structure_declaration add_declaration;
          add_name buf
      | _ -> ());
      Buffer.contents buf

    let get_abbrv entity  has_sibling =
      let abbrv_string = abbrv_string_of_entity entity has_sibling in
      (try
        Hashtbl.find abbrv_mapping abbrv_string
      with Not_found ->
        abbrvs:=abbrv_string::!abbrvs;
        let id = next_abbrv in
        Hashtbl.add abbrv_mapping abbrv_string id;
        id)

  end:SYSTEM)

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
 
    let add_sibling = add_abbr_entry (0x1,0x13)
       
    let add_decl_file = add_abbr_entry (0x3a,0x6)
 
    let add_decl_line = add_abbr_entry (0x3b,0xf)
        
    let add_type = add_abbr_entry (0x49,0x10)
   
    let add_name = add_abbr_entry (0x3,0x8)
        
    let add_encoding = add_abbr_entry (0x3e,0xb)

    let add_byte_size = add_abbr_entry (0xb,0xb)

    let add_high_pc = add_abbr_entry (0x12,0x1)

    let add_low_pc = add_abbr_entry (0x11,0x1)

    let add_stmt_list = add_abbr_entry (0x10,0x6)
        
    let add_declaration = add_abbr_entry (0x3c,0xc)

    let add_external = add_abbr_entry (0x3f,0xc)

    let add_prototyped = add_abbr_entry (0x27,0xc)

    let add_bit_offset = add_abbr_entry (0xd,0xb)

    let add_location loc buf = 
      match loc with
      | None -> ()
      | Some (LocConst _) -> add_abbr_entry (0x2,0x6) buf
      | Some (LocBlock _) -> add_abbr_entry (0x2,0x9) buf

    let add_data_location loc buf = 
      match loc with
      | None -> ()
      | Some (DataLocBlock __) -> add_abbr_entry (0x38,0x9) buf
      | Some (DataLocRef _) -> add_abbr_entry (0x38,0x13) buf

    let add_bound_value bound =
      match bound with
      | BoundConst _ -> add_abbr_entry (0x2f,0xf)
      | BoundRef _ -> add_abbr_entry (0x2f,0x13)

    let add_comp_dir = add_abbr_entry (0x1b,0x8)

    let add_language = add_abbr_entry (0x13,0xf)

    let add_producer = add_abbr_entry (0x25,0x8)

    let add_value = add_abbr_entry (0x1c,0xd)

    let add_artificial = add_abbr_entry (0x34,0xc)

    let add_variable_parameter = add_abbr_entry (0x4b,0xc)

    let add_bit_size = add_abbr_entry (0xc,0xb)

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
          prologue 0x1;
          add_attr_some e.array_type_decl_file add_decl_file;
          add_attr_some e.array_type_decl_line add_decl_line;
          add_type buf
      | DW_TAG_base_type _ ->
          prologue 0x24;
          add_encoding buf;
          add_byte_size buf;
          add_name buf
      | DW_TAG_compile_unit e ->
          prologue 0x11;
          add_comp_dir buf;
          add_high_pc buf;
          add_low_pc buf;
          add_language buf;
          add_name buf;
          add_producer buf;
          add_attr_some e.compile_unit_stmt_list add_stmt_list
      | DW_TAG_const_type _ ->
          prologue 0x26;
          add_type buf
      | DW_TAG_enumeration_type e ->
          prologue 0x4;
          add_attr_some e.enumeration_decl_file add_decl_file;
          add_attr_some e.enumeration_decl_line add_decl_line;
          add_byte_size buf;
          add_name buf;
          add_attr_some e.enumeration_declaration add_declaration
      | DW_TAG_enumerator e ->
          prologue 0x28;
          add_attr_some e.enumerator_decl_file add_decl_file;
          add_attr_some e.enumerator_decl_line add_decl_line;
          add_value buf;
          add_name buf
      | DW_TAG_formal_parameter e ->
          prologue 0x34;
          add_attr_some e.formal_parameter_decl_file add_decl_file;
          add_attr_some e.formal_parameter_decl_line add_decl_line;
          add_attr_some e.formal_parameter_artificial add_artificial;
          add_location  e.formal_parameter_location buf;
          add_name buf;
          add_location e.formal_parameter_segment buf;
          add_type buf;
          add_attr_some e.formal_parameter_variable_parameter add_variable_parameter
      | DW_TAG_label _ ->
          prologue 0xa;
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
          add_attr_some e.member_bit_offset add_bit_offset;
          add_attr_some e.member_bit_size add_bit_size;
          add_data_location e.member_data_member_location buf;
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
      | DW_TAG_subprogram e ->
          prologue 0x2e;
          add_attr_some e.subprogram_decl_file add_decl_file;
          add_attr_some e.subprogram_decl_line add_decl_line;
          add_attr_some e.subprogram_external add_external;
          add_high_pc buf;
          add_low_pc buf;
          add_name buf;
          add_prototyped buf;
          add_type buf
      | DW_TAG_subrange_type e ->
          prologue 0x21;
          add_attr_some e.subrange_type add_type;
          add_bound_value e.subrange_upper_bound buf
      | DW_TAG_subroutine_type _ ->
          prologue 0x15;
          add_prototyped buf
      | DW_TAG_typedef e ->
          prologue 0x16;
          add_attr_some e.typedef_decl_file add_decl_file;
          add_attr_some e.typedef_decl_line add_decl_line;
          add_name buf;
          add_type buf
      | DW_TAG_union_type e ->
          prologue 0x17;
          add_attr_some e.union_decl_file add_decl_file;
          add_attr_some e.union_decl_line add_decl_line;
          add_byte_size buf;
          add_name buf
      | DW_TAG_unspecified_parameter e ->
          prologue 0x18;
          add_attr_some e.unspecified_parameter_decl_file add_decl_file;
          add_attr_some e.unspecified_parameter_decl_line add_decl_line;
          add_attr_some e.unspecified_parameter_artificial add_artificial
      | DW_TAG_variable e ->
          prologue 0x34;
          add_attr_some e.variable_decl_file add_decl_file;
          add_attr_some e.variable_decl_line add_decl_line;
          add_attr_some e.variable_declaration add_declaration;
          add_attr_some e.variable_external add_external;
          add_location  e.variable_location buf;
          add_name buf;
          add_location e.variable_segment buf;
          add_type buf
      | DW_TAG_volatile_type _ ->
          prologue 0x35;
          add_type buf);
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

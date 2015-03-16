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


open DwarfTypes
open DwarfUtil
open Printf
open PrintAsmaux
open Sections

module DwarfPrinter(Target: TARGET) :
    sig
      val print_debug: out_channel -> dw_entry -> unit
    end =
  struct
    
    open Target

    let string_of_byte value =
      sprintf "	.byte		%s\n" (if value then "0x1" else "0x0")

    let print_label oc lbl =
      fprintf oc "%a:\n" label lbl
      
    let curr_abbrev = ref 1

    let next_abbrev =
      let abbrev = !curr_abbrev in
      incr curr_abbrev;abbrev

    let abbrevs: (string * int) list ref = ref []

    let abbrev_mapping: (string,int) Hashtbl.t = Hashtbl.create 7

    let add_byte buf value =
      Buffer.add_string buf (string_of_byte value)

    let add_abbr_uleb v buf =
      Buffer.add_string buf (Printf.sprintf "	.uleb128	%d\n" v)

    let add_abbr_entry (v1,v2) buf =
      add_abbr_uleb v1 buf;
      add_abbr_uleb v2 buf

    let add_sibling = add_abbr_entry (0x1,DwarfAbbrevs.sibling_type_abbr)

    let add_file_loc buf =
      let file,line = DwarfAbbrevs.file_loc_type_abbr in
      add_abbr_entry (0x3a,file) buf; 
      add_abbr_entry (0x3b,line) buf

    let add_type = add_abbr_entry (0x49,DwarfAbbrevs.type_abbr)

    let add_name = add_abbr_entry (0x3,DwarfAbbrevs.name_type_abbr)

    let add_encoding = add_abbr_entry (0x3e,DwarfAbbrevs.encoding_type_abbr)

    let add_byte_size = add_abbr_entry (0xb,DwarfAbbrevs.byte_size_type_abbr)

    let add_high_pc = add_abbr_entry (0x12,DwarfAbbrevs.high_pc_type_abbr)

    let add_low_pc = add_abbr_entry (0x11,DwarfAbbrevs.low_pc_type_abbr)

    let add_stmt_list = add_abbr_entry (0x10,DwarfAbbrevs.stmt_list_type_abbr)

    let add_declaration = add_abbr_entry (0x3c,DwarfAbbrevs.declaration_type_abbr)

    let add_external = add_abbr_entry (0x3f,DwarfAbbrevs.external_type_abbr)

    let add_prototyped = add_abbr_entry (0x27,DwarfAbbrevs.prototyped_type_abbr)

    let add_bit_offset = add_abbr_entry (0xd,DwarfAbbrevs.bit_offset_type_abbr)

    let add_comp_dir = add_abbr_entry (0x1b,DwarfAbbrevs.comp_dir_type_abbr)

    let add_language = add_abbr_entry (0x13,DwarfAbbrevs.language_type_abbr)

    let add_producer = add_abbr_entry (0x25,DwarfAbbrevs.producer_type_abbr)

    let add_value = add_abbr_entry (0x1c,DwarfAbbrevs.value_type_abbr)

    let add_artificial = add_abbr_entry (0x34,DwarfAbbrevs.artificial_type_abbr)

    let add_variable_parameter = add_abbr_entry (0x4b,DwarfAbbrevs.variable_parameter_type_abbr)

    let add_bit_size = add_abbr_entry (0xc,DwarfAbbrevs.bit_size_type_abbr)

    let add_location loc buf =
      match loc with
      | None -> ()
      | Some (LocConst _) -> add_abbr_entry (0x2,DwarfAbbrevs.location_const_type_abbr) buf
      | Some (LocBlock _) -> add_abbr_entry (0x2,DwarfAbbrevs.location_block_type_abbr) buf

    let add_data_location loc buf =
      match loc with
      | None -> ()
      | Some (DataLocBlock __) -> add_abbr_entry (0x38,DwarfAbbrevs.data_location_block_type_abbr) buf
      | Some (DataLocRef _) -> add_abbr_entry (0x38,DwarfAbbrevs.data_location_ref_type_abbr) buf

    let add_bound_value bound =
      match bound with
      | BoundConst _ -> add_abbr_entry (0x2f,DwarfAbbrevs.bound_const_type_abbr)
      | BoundRef _ -> add_abbr_entry (0x2f,DwarfAbbrevs.bound_ref_type_abbr)

    let abbrev_string_of_entity entity has_sibling =
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
          add_attr_some e.array_type_file_loc add_file_loc;
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
          add_stmt_list buf;
      | DW_TAG_const_type _ ->
          prologue 0x26;
          add_type buf
      | DW_TAG_enumeration_type e ->
          prologue 0x4;
          add_attr_some e.enumeration_file_loc add_file_loc;
          add_byte_size buf;
          add_name buf;
          add_attr_some e.enumeration_declaration add_declaration
      | DW_TAG_enumerator e ->
          prologue 0x28;
          add_attr_some e.enumerator_file_loc add_file_loc;
          add_value buf;
          add_name buf
      | DW_TAG_formal_parameter e ->
          prologue 0x34;
          add_attr_some e.formal_parameter_file_loc add_file_loc;
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
          add_attr_some e.member_file_loc add_file_loc;
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
          add_attr_some e.structure_file_loc add_file_loc;
          add_byte_size buf;
          add_attr_some e.structure_declaration add_declaration;
          add_name buf
      | DW_TAG_subprogram e ->
          prologue 0x2e;
          add_attr_some e.subprogram_file_loc add_file_loc;
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
          add_attr_some e.typedef_file_loc add_file_loc;
          add_name buf;
          add_type buf
      | DW_TAG_union_type e ->
          prologue 0x17;
          add_attr_some e.union_file_loc add_file_loc;
          add_byte_size buf;
          add_name buf
      | DW_TAG_unspecified_parameter e ->
          prologue 0x18;
          add_attr_some e.unspecified_parameter_file_loc add_file_loc;
          add_attr_some e.unspecified_parameter_artificial add_artificial
      | DW_TAG_variable e ->
          prologue 0x34;
          add_attr_some e.variable_file_loc add_file_loc;
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

    let get_abbrev entity has_sibling =
      let abbrev_string = abbrev_string_of_entity entity has_sibling in
      (try
        Hashtbl.find abbrev_mapping abbrev_string
      with Not_found ->
        let id = next_abbrev in
        abbrevs:=(abbrev_string,id)::!abbrevs;
        Hashtbl.add abbrev_mapping abbrev_string id;
        id)

    let compute_abbrev entry =
      entry_iter_sib (fun sib entry ->
        let has_sib = match sib with
        | None -> false
        | Some _ -> true in
        ignore (get_abbrev entry has_sib)) entry

    let abbrev_start_addr = ref (-1)
        
    let abbrev_section_start oc =
      fprintf oc "	.section	%s\n" (name_of_section Section_debug_abbrev);
      let lbl = new_label () in
      abbrev_start_addr := lbl;
      print_label oc lbl

    let abbrev_section_end oc =
      fprintf oc "	.sleb128	0\n"

    let abbrev_prologue oc id =
      fprintf oc "	.uleb128	%d\n" id

    let abbrev_epilogue oc =
      fprintf oc "	.uleb128	0\n";
      fprintf oc "	.uleb128	0\n"


    let print_abbrev oc =
      let abbrevs = List.sort (fun (_,a) (_,b) -> Pervasives.compare a b) !abbrevs in
      abbrev_section_start oc;
      List.iter (fun (s,id) ->
        abbrev_prologue oc id;
        output_string oc s;
        abbrev_epilogue oc) abbrevs;
      abbrev_section_end oc

    let debug_start_addr = ref (-1)

    let entry_labels: (int,int) Hashtbl.t = Hashtbl.create 7

    let entry_to_label id =
      try
        Hashtbl.find entry_labels id
      with Not_found ->
        let label = new_label () in
        Hashtbl.add entry_labels id label;
        label

    let print_opt_value oc o f =
      match o with
      | None -> ()
      | Some o -> f oc o

    let print_file_loc oc f =
      print_opt_value oc f print_file_loc

    let print_flag oc b =
      output_string oc (string_of_byte b)

    let print_string oc s =
      fprintf oc "	.asciz		\"%s\"\n" s

    let print_uleb128 oc d =
      fprintf oc "	.uleb128	%d\n" d

    let print_sleb128 oc d =
      fprintf oc "	.sleb128	%d\n" d

    let print_byte oc b =
      fprintf oc "	.byte		0x%X\n" b

    let print_loc oc loc =
      ()

    let print_data_location oc dl =
      ()

    let print_ref oc r =
      print_label oc (entry_to_label r)

    let print_array_type oc at =
      print_file_loc oc at.array_type_file_loc;
      print_label oc (entry_to_label at.array_type)

    let print_base_type oc bt =
      print_byte oc bt.base_type_byte_size;
      let encoding = match bt.base_type_encoding with
      | DW_ATE_address -> 0x1
      | DW_ATE_boolean -> 0x2
      | DW_ATE_complex_float -> 0x3
      | DW_ATE_float -> 0x4
      | DW_ATE_signed -> 0x5
      | DW_ATE_signed_char -> 0x6
      | DW_ATE_unsigned -> 0x7
      | DW_ATE_unsigned_char -> 0x8
      in
      print_byte oc encoding;
      print_string oc bt.base_type_name

    let print_compilation_unit oc tag =
      print_string oc (Sys.getcwd ());
      print_label oc (get_start_addr ());
      print_label oc (get_end_addr ());
      print_uleb128 oc 1;
      print_string oc tag.compile_unit_name;
      print_string oc ("CompCert "^Configuration.version); 
      print_label oc (get_stmt_list_addr ())

    let print_const_type oc ct =
      print_ref oc ct.const_type

    let print_enumeration_type oc et =
      print_file_loc oc et.enumeration_file_loc;
      print_uleb128 oc et.enumeration_byte_size;
      print_opt_value oc et.enumeration_declaration print_flag;
      print_string oc et.enumeration_name

    let print_enumerator oc en =
      print_file_loc oc en.enumerator_file_loc;
      print_sleb128 oc en.enumerator_value;
      print_string oc en.enumerator_name
      
    let print_formal_parameter oc fp =
      print_file_loc oc fp.formal_parameter_file_loc;
      print_opt_value oc fp.formal_parameter_artificial print_flag;
      print_opt_value oc fp.formal_parameter_location print_loc;
      print_string oc fp.formal_parameter_name;
      print_opt_value oc fp.formal_parameter_segment print_loc;
      print_ref oc fp.formal_parameter_type;
      print_opt_value oc fp.formal_parameter_variable_parameter print_flag
      
    let print_tag_label oc tl =
      print_ref oc tl.label_low_pc;
      print_string oc tl.label_name

    let print_lexical_block oc lb =
      print_ref oc lb.lexical_block_high_pc;
      print_ref oc lb.lexical_block_low_pc

    let print_member oc mb =
      print_file_loc oc mb.member_file_loc;
      print_opt_value oc mb.member_byte_size print_byte;
      print_opt_value oc mb.member_bit_offset print_byte;
      print_opt_value oc mb.member_bit_size print_byte;
      print_opt_value oc mb.member_data_member_location print_data_location;
      print_opt_value oc mb.member_declaration print_flag;
      print_string oc mb.member_name;
      print_ref oc mb.member_type

    let print_pointer oc pt =
      print_ref oc pt.pointer_type

    let print_structure oc st =
      print_file_loc oc st.structure_file_loc;
      print_uleb128 oc st.structure_byte_size;
      print_opt_value oc st.structure_declaration print_flag;
      print_string oc st.structure_name

    let  print_entry oc entry =
      entry_iter_sib (fun sib entry ->
        print_ref oc entry.id;
        let has_sib = match sib with
        | None -> false
        | Some _ -> true in
        let id = get_abbrev entry has_sib in
        print_sleb128 oc id;
        (match sib with
        | None -> ()
        | Some s -> let lbl = entry_to_label s in
          fprintf oc "	.4byte		%a-%a\n" label lbl label !debug_start_addr);
        begin
          match entry.tag with
          | DW_TAG_array_type arr_type -> print_array_type oc arr_type
          | DW_TAG_compile_unit comp -> print_compilation_unit oc comp
          | DW_TAG_base_type bt -> print_base_type oc bt
          | DW_TAG_const_type ct -> print_const_type oc ct
          | _ -> ()
        end;
        if entry.children = [] then
          print_sleb128 oc 0) entry
            
    let print_debug_abbrev oc entry =
      compute_abbrev entry;
      print_abbrev oc

    let print_debug oc entry =
      print_debug_abbrev oc entry;
      let debug_start = new_label () in
      debug_start_addr:= debug_start;
      fprintf oc"	.section	%s\n" (name_of_section Section_debug_info);
      print_label oc debug_start; 
      let debug_length_start = new_label ()  (* Address used for length calculation *)
      and debug_end = new_label () in
      fprintf oc "	.4byte		%a-%a\n" label debug_end label debug_length_start;
      print_label oc debug_length_start; 
      fprintf oc "	.2byte		0x2\n"; (* Dwarf version *)
      fprintf oc "	.4byte		%a\n" label !abbrev_start_addr; (* Offset into the abbreviation *)
      print_byte oc !Machine.config.Machine.sizeof_ptr; (* Sizeof pointer type *) 
      print_entry oc entry;
      print_sleb128 oc 0;
      print_label oc debug_end (* End of the debug section *)

  end

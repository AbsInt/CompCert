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

(* Printer for the Dwarf 2 debug information in ASM *)

open DwarfTypes
open DwarfUtil
open Printf
open PrintAsmaux
open Sections

(* The printer is parameterized over target specific functions and a set of dwarf type constants *)
module DwarfPrinter(Target: DWARF_TARGET):
    sig
      val print_debug: out_channel -> debug_entries -> unit
    end =
  struct

    open Target

    (* Do we need verbose debug information? *)
    let include_comment = !Clflags.option_S || !Clflags.option_dasm

    (* Print comments needed for verbose debug mode *)
    let print_comment =
      if include_comment then
        (fun  oc s ->
           if s <> "" then
             fprintf oc "	%s %s" comment s)
      else
        (fun _ _ -> ())

    let string_of_comment =
      if include_comment then
        (fun s -> String.concat " " ["";comment;s])
      else
        (fun _ -> "")

    (* Byte value to string *)
    let string_of_byte value ct =
      sprintf "	.byte		%s%s\n" (if value then "0x1" else "0x0") (string_of_comment ct)

    (* Print a label *)
    let print_label oc lbl =
      fprintf oc "%a:\n" label lbl

    (* Helper functions for abbreviation printing *)
    let add_byte buf value ct =
      Buffer.add_string buf (string_of_byte value ct)

    let add_abbr_uleb v ct buf =
      Buffer.add_string buf (sprintf "	.uleb128	%d%s\n" v (string_of_comment ct))

     let add_abbr_entry (v1,c1,v2) buf =
       add_abbr_uleb v1 c1 buf;
       let v2,c2 = code_of_dw_form v2 in
       Buffer.add_string buf (sprintf "	.uleb128	%d%s\n" v2 (string_of_comment c2))


    let add_file_loc buf =
      add_abbr_entry (0x3a,"DW_AT_decl_file",DW_FORM_data4) buf;
      add_abbr_entry (0x3b,"DW_AT_decl_line",DW_FORM_udata) buf

    let add_type = add_abbr_entry (0x49,"DW_AT_type",DW_FORM_ref_addr)

    let add_byte_size = add_abbr_entry (0x0b,"DW_AT_byte_size",DW_FORM_data1)

    let add_member_size = add_abbr_entry (0x0b,"DW_AT_byte_size",DW_FORM_udata)

    let add_low_pc = add_abbr_entry (0x11,"DW_AT_low_pc",DW_FORM_addr)

    let add_declaration = add_abbr_entry (0x3c,"DW_AT_declaration",DW_FORM_flag)

    let add_string buf id c = function
      | Simple_string _ -> add_abbr_entry (id,c,DW_FORM_string) buf
      | Offset_string _ -> add_abbr_entry (id,c,DW_FORM_strp) buf

    let add_name buf = add_string buf 0x3 "DW_AT_name"

    let add_name_opt buf = function
      | None -> ()
      | Some s -> add_name buf s

    let add_location loc buf =
      match loc with
      | None -> ()
      | Some (LocRef _) -> add_abbr_entry (0x2,"DW_AT_location",DW_FORM_data4) buf
      | Some (LocList _ )
      | Some (LocSymbol _)
      | Some (LocSimple _) -> add_abbr_entry (0x2,"DW_AT_location",DW_FORM_block) buf

    let add_range buf = function
      | Pc_pair _ ->
          add_abbr_entry (0x11,"DW_AT_low_pc",DW_FORM_addr) buf;
          add_abbr_entry (0x12,"DW_AT_high_pc",DW_FORM_addr) buf
      | Offset _ ->
          add_abbr_entry (0x55,"DW_AT_ranges",DW_FORM_data4) buf
      | Empty -> ()

    (* Dwarf entity to string function *)
    let abbrev_string_of_entity entity has_sibling =
      let buf = Buffer.create 12 in
      let add_attr_some v f =
        match v with
        | None -> ()
        | Some _ -> f buf in
      let prologue id c =
        let has_child = match entity.children with
        | [] -> false
        | _ -> true in
        add_abbr_uleb id c buf;
        add_byte buf has_child (if has_child then "DW_CHILDREN_yes" else "DW_CHILDREN_no");
        if has_sibling then add_abbr_entry (0x1,"DW_AT_sibling",DW_FORM_ref4) buf;
      in
      (match entity.tag with
      | DW_TAG_array_type _ ->
          prologue 0x1 "DW_TAG_array_type";
          add_type buf
      | DW_TAG_base_type b ->
          prologue 0x24 "DW_TAG_base_type";
          add_byte_size buf;
          add_attr_some b.base_type_encoding (add_abbr_entry (0x3e,"DW_AT_encoding",DW_FORM_data1));
          add_name buf b.base_type_name;
      | DW_TAG_compile_unit e ->
          prologue 0x11 "DW_TAG_compile_unit";
          add_string buf 0x1b "DW_AT_comp_dir" e.compile_unit_dir;
          add_range buf e.compile_unit_range;
          add_abbr_entry (0x13,"DW_AT_language",DW_FORM_udata) buf;
          add_name buf e.compile_unit_name;
          add_string buf 0x25 "DW_AT_producer" e.compile_unit_prod_name;
          add_abbr_entry (0x10,"DW_AT_stmt_list",DW_FORM_data4) buf;
      | DW_TAG_const_type _ ->
          prologue 0x26 "DW_TAG_const_type";
          add_type buf
      | DW_TAG_enumeration_type e ->
          prologue 0x4 "DW_TAG_enumeration_type";
          add_attr_some e.enumeration_file_loc add_file_loc;
          add_byte_size buf;
          add_attr_some e.enumeration_declaration add_declaration;
          add_name buf e.enumeration_name
      | DW_TAG_enumerator e ->
          prologue 0x28 "DW_TAG_enumerator";
          add_abbr_entry (0x1c,"DW_AT_const_value",DW_FORM_sdata) buf;
          add_name buf e.enumerator_name
      | DW_TAG_formal_parameter e ->
          prologue 0x5 "DW_TAG_formal_parameter";
          add_attr_some e.formal_parameter_artificial (add_abbr_entry (0x34,"DW_AT_artificial",DW_FORM_flag));
          add_name_opt buf e.formal_parameter_name;
          add_type buf;
          add_attr_some e.formal_parameter_variable_parameter (add_abbr_entry (0x4b,"DW_AT_variable_parameter",DW_FORM_flag));
          add_location  e.formal_parameter_location buf
      | DW_TAG_label e ->
          prologue 0xa "DW_TAG_label";
          add_low_pc buf;
          add_name buf e.label_name;
      | DW_TAG_lexical_block a ->
          prologue 0xb "DW_TAG_lexical_block";
          add_range buf a.lexical_block_range;
      | DW_TAG_member e ->
          prologue 0xd "DW_TAG_member";
          add_attr_some e.member_byte_size add_byte_size;
          add_attr_some e.member_bit_offset (add_abbr_entry (0xc,"DW_AT_bit_offset",DW_FORM_data1));
          add_attr_some e.member_bit_size (add_abbr_entry (0xd,"DW_AT_bit_size",DW_FORM_data1));
          add_attr_some e.member_declaration add_declaration;
          add_name_opt buf e.member_name;
          add_type buf;
          (match e.member_data_member_location with
          | None -> ()
          | Some (DataLocBlock __) -> add_abbr_entry (0x38,"DW_AT_data_member_location",DW_FORM_block) buf
          | Some (DataLocRef _) -> add_abbr_entry (0x38,"DW_AT_data_member_location",DW_FORM_ref4) buf)
      | DW_TAG_pointer_type _ ->
          prologue 0xf "DW_TAG_pointer_type";
          add_type buf
      | DW_TAG_structure_type e ->
          prologue 0x13 "DW_TAG_structure_type";
          add_attr_some e.structure_file_loc add_file_loc;
          add_attr_some e.structure_byte_size add_member_size;
          add_attr_some e.structure_declaration add_declaration;
          add_name_opt buf e.structure_name
      | DW_TAG_subprogram e ->
          prologue 0x2e "DW_TAG_subprogram";
          add_file_loc buf;
          add_attr_some e.subprogram_external (add_abbr_entry (0x3f,"DW_AT_external",DW_FORM_flag));
          add_range buf e.subprogram_range;
          add_name buf e.subprogram_name;
          add_abbr_entry (0x27,"DW_AT_prototyped",DW_FORM_flag) buf;
          add_attr_some e.subprogram_type add_type;
      | DW_TAG_subrange_type e ->
          prologue 0x21 "DW_TAG_subrange_type";
          add_type buf;
          (match e.subrange_upper_bound with
          | None -> ()
          | Some (BoundConst _) -> add_abbr_entry (0x2f,"DW_AT_upper_bound",DW_FORM_udata) buf
          | Some (BoundRef _) -> add_abbr_entry (0x2f,"DW_AT_upper_bound",DW_FORM_ref4) buf)
      | DW_TAG_subroutine_type e ->
          prologue 0x15 "DW_TAG_subroutine_type";
          add_attr_some e.subroutine_type add_type;
          add_abbr_entry (0x27,"DW_AT_prototyped",DW_FORM_flag) buf
      | DW_TAG_typedef e ->
          prologue 0x16 "DW_TAG_typedef";
          add_attr_some e.typedef_file_loc add_file_loc;
          add_name buf e.typedef_name;
          add_type buf
      | DW_TAG_union_type e ->
          prologue 0x17 "DW_TAG_union_type";
          add_attr_some e.union_file_loc add_file_loc;
          add_attr_some e.union_byte_size add_member_size;
          add_attr_some e.union_declaration add_declaration;
          add_name_opt buf e.union_name
      | DW_TAG_unspecified_parameter e ->
          prologue 0x18 "DW_TAG_unspecified_parameter";
          add_attr_some e.unspecified_parameter_artificial (add_abbr_entry (0x34,"DW_AT_artificial",DW_FORM_flag))
      | DW_TAG_variable e ->
          prologue 0x34 "DW_TAG_variable";
          add_file_loc buf;
          add_attr_some e.variable_declaration add_declaration;
          add_attr_some e.variable_external (add_abbr_entry (0x3f,"DW_AT_external",DW_FORM_flag));
          add_location e.variable_location buf;
          add_name buf e.variable_name;
          add_type buf
      | DW_TAG_volatile_type _ ->
          prologue 0x35 "DW_TAG_volatile_type";
          add_type buf);
      Buffer.contents buf

    let abbrev_start_addr = ref (-1)

    let curr_abbrev = ref 1

    (* Function to get unique abbreviation ids *)
    let next_abbrev () =
      let abbrev = !curr_abbrev in
      incr curr_abbrev;abbrev

    (* Mapping from abbreviation string to abbreviaton id *)
    let abbrev_mapping: (string,int) Hashtbl.t = Hashtbl.create 7

    (* Look up the id of the abbreviation and add it if it is missing *)
    let get_abbrev entity has_sibling =
      let abbrev_string = abbrev_string_of_entity entity has_sibling in
      (try
        Hashtbl.find abbrev_mapping abbrev_string
      with Not_found ->
        let id = next_abbrev () in
        Hashtbl.add abbrev_mapping abbrev_string id;
        id)

    (* Compute the abbreviations of an entry and its children *)
    let compute_abbrev entry =
      entry_iter_sib (fun sib entry ->
        let has_sib = match sib with
        | None -> false
        | Some _ -> true in
        ignore (get_abbrev entry has_sib)) (fun _ -> ()) entry

    (* Print the debug_abbrev section using the previous computed abbreviations*)
    let print_abbrev oc =
      let abbrevs = Hashtbl.fold (fun s i acc -> (s,i)::acc) abbrev_mapping [] in
      let abbrevs = List.sort (fun (_,a) (_,b) -> Pervasives.compare a b) abbrevs in
      section oc Section_debug_abbrev;
      print_label oc !abbrev_start_addr;
      List.iter (fun (s,id) ->
        fprintf oc "	.uleb128	%d%a\n" id print_comment "Abbreviation Code";
        output_string oc s;
        fprintf oc "	.uleb128	0%a\n" print_comment "EOM(1)";
        fprintf oc "	.uleb128	0%a\n" print_comment "EOM(2)")  abbrevs;
      fprintf oc "	.sleb128	0%a\n" print_comment "EOM(3)"

    let debug_start_addr = ref (-1)

    let debug_stmt_list = ref (-1)

    let debug_ranges_addr = ref (-1)

    let entry_labels: (int,int) Hashtbl.t = Hashtbl.create 7

    (* Translate the ids to address labels *)
    let entry_to_label id =
      try
        Hashtbl.find entry_labels id
      with Not_found ->
        let label = new_label () in
        Hashtbl.add entry_labels id label;
        label

    let loc_labels: (int,int) Hashtbl.t = Hashtbl.create 7

    (* Translate the ids to address labels *)
    let loc_to_label id =
      try
        Hashtbl.find loc_labels id
      with Not_found ->
        let label = new_label () in
        Hashtbl.add loc_labels id label;
        label

    let print_loc_ref oc c r =
      let ref = loc_to_label r in
      fprintf oc "	.4byte		%a%a\n" label ref print_comment c


    (* Helper functions for debug printing *)
    let print_opt_value oc c o f =
      match o with
      | None -> ()
      | Some o -> f oc c o

    let print_flag oc c b =
      output_string oc (string_of_byte b c)

    let print_string oc c = function
      | Simple_string s ->
          fprintf oc "	.asciz		%S%a\n" s print_comment c
      | Offset_string (o,s) ->
        let c = sprintf "%s %s" c s in
        print_loc_ref oc c o

    let print_uleb128 oc c d =
      fprintf oc "	.uleb128	%d%a\n" d print_comment c

    let print_sleb128 oc c d =
      fprintf oc "	.sleb128	%d%a\n" d print_comment c

    let print_byte oc c b =
      fprintf oc "	.byte		0x%X%a\n" b print_comment c

    let print_2byte oc c b =
      fprintf oc "	.2byte		0x%X%a\n" b print_comment c

    let print_ref oc c r =
      let ref = entry_to_label r in
      fprintf oc "	.4byte		%a%a\n" label ref print_comment c

    let print_file_loc oc = function
      | Some (Diab_file_loc (file,col)) ->
          fprintf oc "	.4byte		%a%a\n" label file print_comment "DW_AT_decl_file";
          print_uleb128 oc "DW_AT_decl_line" col
      | Some (Gnu_file_loc (file,col)) ->
          fprintf oc "	.4byte		%l%a\n" file print_comment "DW_AT_decl_file";
          print_uleb128 oc "DW_AT_decl_line"  col
     | None -> ()

    let print_loc_expr oc = function
      | DW_OP_bregx (a,b) ->
          print_byte oc "DW_OP_bregx" dw_op_bregx;
          print_uleb128 oc "Register number" a;
          print_sleb128 oc "Offset" (Int32.to_int b);
      | DW_OP_plus_uconst i ->
          print_byte oc "DW_OP_plus_uconst" dw_op_plus_uconst;
          print_uleb128 oc "Constant" i
      | DW_OP_piece i ->
          print_byte oc "DW_op_piece" dw_op_piece;
          print_uleb128 oc "Piece" i
      | DW_OP_reg i ->
          if i < 32 then
            print_byte oc "DW_op_reg" (dw_op_reg0 + i)
          else begin
            print_byte oc "DW_op_regx" dw_op_regx;
            print_uleb128 oc "Register number" i
          end

    let print_loc oc c loc =
      match loc with
      | LocSymbol s ->
          print_sleb128 oc c (1 + !Machine.config.Machine.sizeof_ptr);
          print_byte oc "" dw_op_addr;
          fprintf oc "	%s		%a\n" address symbol s
      | LocSimple e ->
          print_sleb128 oc c (size_of_loc_expr e);
          print_loc_expr oc e
      | LocList e ->
          let size = List.fold_left (fun acc a -> acc + size_of_loc_expr a) 0 e in
          print_sleb128 oc "" size;
          List.iter (print_loc_expr oc) e
      | LocRef f ->  print_loc_ref oc c f

    let print_list_loc oc = function
      | LocSymbol s ->
          print_2byte oc "" (1 + !Machine.config.Machine.sizeof_ptr);
          print_byte oc "" dw_op_addr;
          fprintf oc "	%s		%a\n" address symbol s
      | LocSimple e ->
          print_2byte oc "" (size_of_loc_expr e);
          print_loc_expr oc e
      | LocList e ->
          let size = List.fold_left (fun acc a -> acc + size_of_loc_expr a) 0 e in
          print_2byte oc "" size;
          List.iter (print_loc_expr oc) e
      | LocRef f ->  print_loc_ref oc ""  f

    let print_data_location oc c dl =
      match dl with
      | DataLocBlock e ->
          print_sleb128 oc c  (size_of_loc_expr e);
          print_loc_expr oc e
      | _ -> ()

    let print_addr oc c a =
      fprintf oc "	%s		%a%a\n" address label a print_comment c

    let print_data4_addr oc c a =
      fprintf oc "	.4byte	%a%a\n" label a print_comment c

    let print_array_type oc at =
      print_ref oc "DW_AT_type" at.array_type

    let print_bound_value oc c = function
      | BoundConst bc -> print_uleb128 oc c bc
      | BoundRef br -> print_ref oc c br

    let print_base_type oc bt =
      print_byte oc "DW_AT_byte_size" bt.base_type_byte_size;
      (match bt.base_type_encoding with
      | Some e ->
          let encoding = match e with
          | DW_ATE_address -> 0x1
          | DW_ATE_boolean -> 0x2
          | DW_ATE_complex_float -> 0x3
          | DW_ATE_float -> 0x4
          | DW_ATE_signed -> 0x5
          | DW_ATE_signed_char -> 0x6
          | DW_ATE_unsigned -> 0x7
          | DW_ATE_unsigned_char -> 0x8
          in
          print_byte oc "DW_AT_encoding" encoding;
      | None -> ());
      print_string oc "DW_AT_name" bt.base_type_name

    let print_range oc = function
      | Pc_pair (l,h) ->
          print_addr oc "DW_AT_low_pc" l;
          print_addr oc "DW_AT_high_pc" h
      | Offset i -> fprintf oc "	.4byte		%a+0x%d%a\n"
            label !debug_ranges_addr i print_comment "DW_AT_ranges"
      | _ -> ()

    let print_compilation_unit oc tag =
      print_string oc "DW_AT_comp_dir" tag.compile_unit_dir;
      print_range oc tag.compile_unit_range;
      print_uleb128 oc "DW_AT_language" 1;
      print_string oc "DW_AT_name" tag.compile_unit_name;
      print_string oc "DW_AT_producer" tag.compile_unit_prod_name;
      print_data4_addr oc "DW_AT_stmt_list" !debug_stmt_list

    let print_const_type oc ct =
      print_ref oc "DW_AT_type" ct.const_type

    let print_enumeration_type oc et =
      print_file_loc oc et.enumeration_file_loc;
      print_uleb128 oc "DW_AT_byte_size" et.enumeration_byte_size;
      print_opt_value oc "DW_AT_declaration" et.enumeration_declaration print_flag;
      print_string oc "DW_AT_name" et.enumeration_name

    let print_enumerator oc en =
      print_sleb128 oc "DW_AT_const_value" en.enumerator_value;
      print_string oc "DW_AT_name" en.enumerator_name

    let print_formal_parameter oc fp =
      print_opt_value oc "DW_AT_artificial" fp.formal_parameter_artificial print_flag;
      print_opt_value oc "DW_AT_name" fp.formal_parameter_name print_string;
      print_ref oc "DW_AT_type" fp.formal_parameter_type;
      print_opt_value oc "DW_AT_variable_parameter" fp.formal_parameter_variable_parameter print_flag;
      print_opt_value oc "DW_AT_location" fp.formal_parameter_location print_loc

    let print_tag_label oc tl =
      print_ref oc "DW_AT_low_pc" tl.label_low_pc;
      print_string oc "DW_AT_name" tl.label_name


    let print_lexical_block oc lb =
      print_range oc lb.lexical_block_range

    let print_member oc mb =
      print_opt_value oc "DW_AT_byte_size" mb.member_byte_size print_byte;
      print_opt_value oc "DW_AT_bit_offset" mb.member_bit_offset print_byte;
      print_opt_value oc "DW_AT_bit_size" mb.member_bit_size print_byte;
      print_opt_value oc  "DW_AT_declaration" mb.member_declaration print_flag;
      print_opt_value oc "DW_AT_name" mb.member_name print_string;
      print_ref oc "DW_AT_type" mb.member_type;
      print_opt_value oc "DW_AT_data_member_location" mb.member_data_member_location print_data_location


    let print_pointer oc pt =
      print_ref oc "DW_AT_type" pt.pointer_type

    let print_structure oc st =
      print_file_loc oc st.structure_file_loc;
      print_opt_value oc "DW_AT_byte_size" st.structure_byte_size print_uleb128;
      print_opt_value oc "DW_AT_declaration" st.structure_declaration print_flag;
      print_opt_value oc "DW_AT_name" st.structure_name print_string


    let print_subprogram oc sp =
      print_file_loc oc (Some sp.subprogram_file_loc);
      print_opt_value oc "DW_AT_external" sp.subprogram_external print_flag;
      print_range oc sp.subprogram_range;
      print_string oc "DW_AT_name" sp.subprogram_name;
      print_flag oc "DW_AT_prototyped" sp.subprogram_prototyped;
      print_opt_value oc "DW_AT_type" sp.subprogram_type print_ref

    let print_subrange oc sr =
      print_ref oc "DW_AT_type" sr.subrange_type;
      print_opt_value oc  "DW_AT_upper_bound" sr.subrange_upper_bound print_bound_value

    let print_subroutine oc st =
      print_opt_value oc "DW_AT_type" st.subroutine_type print_ref;
      print_flag oc "DW_AT_prototyped" st.subroutine_prototyped

    let print_typedef oc td =
      print_file_loc oc td.typedef_file_loc;
      print_string oc "DW_AT_name" td.typedef_name;
      print_ref oc "DW_AT_type" td.typedef_type

    let print_union_type oc ut =
      print_file_loc oc ut.union_file_loc;
      print_opt_value oc "DW_AT_byte_size" ut.union_byte_size print_uleb128;
      print_opt_value oc "DW_AT_declaration" ut.union_declaration print_flag;
      print_opt_value oc "DW_AT_name" ut.union_name print_string

    let print_unspecified_parameter oc up =
      print_opt_value oc "DW_AT_artificial" up.unspecified_parameter_artificial print_flag

    let print_variable oc var =
      print_file_loc oc (Some var.variable_file_loc);
      print_opt_value oc "DW_AT_declaration" var.variable_declaration print_flag;
      print_opt_value oc "DW_AT_external" var.variable_external print_flag;
      print_opt_value oc "DW_AT_location" var.variable_location print_loc;
      print_string oc "DW_AT_name" var.variable_name;
      print_ref oc "DW_AT_type" var.variable_type

    let print_volatile_type oc vt =
      print_ref oc "DW_AT_type" vt.volatile_type

    (* Print an debug entry *)
    let  print_entry oc entry =
      entry_iter_sib (fun sib entry ->
        print_label oc (entry_to_label entry.id);
        let has_sib = match sib with
        | None -> false
        | Some _ -> true in
        let id = get_abbrev entry has_sib in
        print_sleb128 oc (sprintf "Abbrev [%d] %s" id (string_of_dw_tag entry.tag)) id;
        (match sib with
        | None -> ()
        | Some s -> let lbl = entry_to_label s in
          fprintf oc "	.4byte		%a-%a%a\n" label lbl label !debug_start_addr print_comment "DW_AT_sibling");
        begin
          match entry.tag with
          | DW_TAG_array_type arr_type -> print_array_type oc arr_type
          | DW_TAG_compile_unit comp -> print_compilation_unit oc comp
          | DW_TAG_base_type bt -> print_base_type oc bt
          | DW_TAG_const_type ct -> print_const_type oc ct
          | DW_TAG_enumeration_type et -> print_enumeration_type oc et
          | DW_TAG_enumerator et -> print_enumerator oc et
          | DW_TAG_formal_parameter fp -> print_formal_parameter oc fp
          | DW_TAG_label lb -> print_tag_label oc lb
          | DW_TAG_lexical_block lb -> print_lexical_block oc lb
          | DW_TAG_member mb -> print_member oc mb
          | DW_TAG_pointer_type pt -> print_pointer oc pt
          | DW_TAG_structure_type st -> print_structure oc st
          | DW_TAG_subprogram sb -> print_subprogram oc sb
          | DW_TAG_subrange_type sb -> print_subrange oc sb
          | DW_TAG_subroutine_type st -> print_subroutine oc st
          | DW_TAG_typedef tp -> print_typedef oc tp
          | DW_TAG_union_type ut -> print_union_type oc ut
          | DW_TAG_unspecified_parameter up -> print_unspecified_parameter oc up
          | DW_TAG_variable var -> print_variable oc var
          | DW_TAG_volatile_type vt -> print_volatile_type oc vt
        end) (fun e ->
          if e.children <> [] then
          print_sleb128 oc "End Of Children Mark" 0) entry

    (* Print the debug info section *)
    let print_debug_info oc start line_start entry  =
      Hashtbl.reset entry_labels;
      debug_start_addr:= start;
      debug_stmt_list:= line_start;
      print_label oc start;
      let debug_length_start = new_label ()  (* Address used for length calculation *)
      and debug_end = new_label () in
      fprintf oc "	.4byte		%a-%a%a\n" label debug_end label debug_length_start print_comment "Length of Unit";
      print_label oc debug_length_start;
      fprintf oc "	.2byte		0x%d%a\n" !Clflags.option_gdwarf print_comment "DWARF version number"; (* Dwarf version *)
      print_data4_addr oc "Offset Into Abbrev. Section" !abbrev_start_addr; (* Offset into the abbreviation *)
      print_byte oc "Address Size (in bytes)" !Machine.config.Machine.sizeof_ptr; (* Sizeof pointer type *)
      print_entry oc entry;
      print_sleb128 oc "" 0;
      print_label oc debug_end (* End of the debug section *)

    let print_location_entry oc c_low l =
      print_label oc (loc_to_label l.loc_id);
      List.iter (fun (b,e,loc) ->
        fprintf oc "	%s		%a-%a\n" address label b label c_low;
        fprintf oc "	%s		%a-%a\n" address label e label c_low;
        print_list_loc oc loc) l.loc;
      fprintf oc "	%s	0\n" address;
      fprintf oc "	%s	0\n" address

    let print_location_entry_abs oc l =
      print_label oc (loc_to_label l.loc_id);
      List.iter (fun (b,e,loc) ->
        fprintf oc "	%s		%a\n" address label b;
        fprintf oc "	%s		%a\n" address label e;
        print_list_loc oc loc) l.loc;
      fprintf oc "	%s	0\n" address;
      fprintf oc "	%s	0\n" address


    let print_location_list oc (c_low,l) =
      let f =  match c_low with
      | Some s -> print_location_entry oc s
      | None -> print_location_entry_abs oc in
     List.iter f l

    let list_opt l f =
      match l with
      | [] -> ()
      | _ -> f ()

    let print_diab_entries oc entries =
      let abbrev_start = new_label () in
      abbrev_start_addr := abbrev_start;
      List.iter (fun e -> compute_abbrev e.entry) entries;
      print_abbrev oc;
      List.iter (fun e ->
        let name = if e.section_name <> ".text" then Some e.section_name else None in
        section oc (Section_debug_info name);
        print_debug_info oc e.start_label e.line_label e.entry) entries;
      if List.exists (fun e -> match e.dlocs with _,[] -> false | _,_ -> true) entries then begin
        section oc Section_debug_loc;
        List.iter (fun e -> print_location_list oc e.dlocs) entries
      end

    let print_ranges oc r =
      section oc Section_debug_ranges;
      print_label oc !debug_ranges_addr;
      List.iter (fun l ->
        List.iter (fun (b,e) ->
          fprintf oc "	%s		%a\n" address label b;
          fprintf oc "	%s		%a\n" address label e) l;
        fprintf oc "	%s	0\n" address;
        fprintf oc "	%s	0\n" address) r

    let print_gnu_entries oc cp (lpc,loc) s r =
      compute_abbrev cp;
      let line_start = new_label ()
      and start = new_label ()
      and  abbrev_start = new_label ()
      and range_label = new_label () in
      debug_ranges_addr := range_label;
      abbrev_start_addr := abbrev_start;
      section oc (Section_debug_info None);
      print_debug_info oc start line_start cp;
      print_abbrev oc;
      list_opt loc (fun () ->
        section oc Section_debug_loc;
        print_location_list oc (lpc,loc));
      list_opt r (fun () ->
        print_ranges oc r);
      section oc (Section_debug_line None);
      print_label oc line_start;
      list_opt s (fun () ->
        section oc Section_debug_str;
        let s = List.sort (fun (a,_) (b,_) -> Pervasives.compare a b) s in
        List.iter (fun (id,s) ->
          print_label oc (loc_to_label id);
          fprintf oc "	.asciz		%S\n" s) s)


    (* Print the debug info and abbrev section *)
    let print_debug oc debug =
      Hashtbl.clear abbrev_mapping;
      Hashtbl.clear loc_labels;
      match debug with
      | Diab entries -> print_diab_entries oc entries
      | Gnu (cp,loc,s,r) -> print_gnu_entries oc cp loc s r

  end

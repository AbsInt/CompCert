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

(* Utility functions for the dwarf debuging type *)

open DwarfTypes

let id = ref 0

let next_id () = 
  let nid = !id in
  incr id; nid

let reset_id () =
  id := 0

(* Hashtable to from type name to entry id *)
let type_table: (string, int) Hashtbl.t = Hashtbl.create 7

(* Clear the type map *)
let reset_type_table () = 
  Hashtbl.clear type_table

(* Generate a new entry from a given tag *)
let new_entry tag =
  let id = next_id () in
  {
   tag = tag;
   children = [];
   id = id;
 }

(* Add an entry as child to  another entry *)
let add_children entry child =
  {entry with children = child::entry.children;}


(* Iter over the tree in prefix order *)
let rec entry_iter f entry =
  f entry.tag;
  List.iter (entry_iter f) entry.children

(* Iter over the tree in prefix order with passing additional reference to next sibling *)
let entry_iter_sibling f acc entry =
  f None entry.tag;
  let rec aux = (function
    | [] -> ()
    | [last] -> f None last.tag
    | a::b::rest ->  f  (Some b.id) a.tag; aux (b::rest)) in
  aux entry.children


(* Fold over the tree in prefix order *)
let rec entry_fold f acc entry =
  let acc = f acc entry.tag in
  List.fold_left (entry_fold f) acc entry.children

(* Fold over the tree in prefix order with passing additional reference to next sibling *)
let entry_fold_sibling f acc entry =
  let acc = f acc None entry.tag in
  let rec aux acc = (function
    | [] -> acc
    | [last] -> f acc None last.tag
    | a::b::rest -> aux (f acc (Some b.id) a.tag) (b::rest)) in
  aux acc entry.children

module type ABBRV_DEFS =
    sig
      val string_of_byte: bool -> string
      val string_of_uleb: int -> string
      val sibling_type_abbr: int
      val decl_file_type_abbr: int
      val decl_line_type_abbr: int
      val type_abbr: int
      val name_type_abbr: int
      val encoding_type_abbr: int
      val byte_size_type_abbr: int
      val high_pc_type_abbr: int
      val low_pc_type_abbr: int
      val stmt_list_type_abbr: int
      val declaration_type_abbr: int
      val external_type_abbr: int
      val prototyped_type_abbr: int
      val bit_offset_type_abbr: int
      val comp_dir_type_abbr: int
      val language_type_abbr: int
      val producer_type_abbr: int
      val value_type_abbr: int
      val artificial_type_abbr: int
      val variable_parameter_type_abbr: int
      val bit_size_type_abbr: int
      val location_const_type_abbr: int
      val location_block_type_abbr: int
      val data_location_block_type_abbr: int
      val data_location_ref_type_abbr: int
      val bound_const_type_abbr: int
      val bound_ref_type_abbr: int
    end

module AbbrvPrinter(Defs:ABBRV_DEFS) =
  (struct
    
    let curr_abbrv = ref 0

    let next_abbrv =
      let abbrv = !curr_abbrv in
      incr curr_abbrv;abbrv

    let abbrvs: string list ref = ref []

    let abbrv_mapping: (string,int) Hashtbl.t = Hashtbl.create 7

    let add_byte buf value =
      Buffer.add_string buf (Defs.string_of_byte value)

    let add_abbr_uleb v buf =
      Buffer.add_string buf (Defs.string_of_uleb v) 

    let add_abbr_entry (v1,v2) buf =
      add_abbr_uleb v1 buf;
      add_abbr_uleb v2 buf
 
    let add_sibling = add_abbr_entry (0x1,Defs.sibling_type_abbr)
       
    let add_decl_file = add_abbr_entry (0x3a,Defs.decl_file_type_abbr)
 
    let add_decl_line = add_abbr_entry (0x3b,Defs.decl_line_type_abbr)
        
    let add_type = add_abbr_entry (0x49,Defs.type_abbr)
   
    let add_name = add_abbr_entry (0x3,Defs.name_type_abbr)
        
    let add_encoding = add_abbr_entry (0x3e,Defs.encoding_type_abbr)

    let add_byte_size = add_abbr_entry (0xb,Defs.byte_size_type_abbr)

    let add_high_pc = add_abbr_entry (0x12,Defs.high_pc_type_abbr)

    let add_low_pc = add_abbr_entry (0x11,Defs.low_pc_type_abbr)

    let add_stmt_list = add_abbr_entry (0x10,Defs.stmt_list_type_abbr)
        
    let add_declaration = add_abbr_entry (0x3c,Defs.declaration_type_abbr)

    let add_external = add_abbr_entry (0x3f,Defs.external_type_abbr)

    let add_prototyped = add_abbr_entry (0x27,Defs.prototyped_type_abbr)

    let add_bit_offset = add_abbr_entry (0xd,Defs.bit_offset_type_abbr)

    let add_comp_dir = add_abbr_entry (0x1b,Defs.comp_dir_type_abbr)

    let add_language = add_abbr_entry (0x13,Defs.language_type_abbr)

    let add_producer = add_abbr_entry (0x25,Defs.producer_type_abbr)

    let add_value = add_abbr_entry (0x1c,Defs.value_type_abbr)

    let add_artificial = add_abbr_entry (0x34,Defs.artificial_type_abbr)

    let add_variable_parameter = add_abbr_entry (0x4b,Defs.variable_parameter_type_abbr)

    let add_bit_size = add_abbr_entry (0xc,Defs.bit_size_type_abbr)

    let add_location loc buf = 
      match loc with
      | None -> ()
      | Some (LocConst _) -> add_abbr_entry (0x2,Defs.location_const_type_abbr) buf
      | Some (LocBlock _) -> add_abbr_entry (0x2,Defs.location_block_type_abbr) buf

    let add_data_location loc buf = 
      match loc with
      | None -> ()
      | Some (DataLocBlock __) -> add_abbr_entry (0x38,Defs.data_location_block_type_abbr) buf
      | Some (DataLocRef _) -> add_abbr_entry (0x38,Defs.data_location_ref_type_abbr) buf

    let add_bound_value bound =
      match bound with
      | BoundConst _ -> add_abbr_entry (0x2f,Defs.bound_const_type_abbr)
      | BoundRef _ -> add_abbr_entry (0x2f,Defs.bound_ref_type_abbr)

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

    let get_abbrv entity has_sibling =
      let abbrv_string = abbrv_string_of_entity entity has_sibling in
      (try
        Hashtbl.find abbrv_mapping abbrv_string
      with Not_found ->
        abbrvs:=abbrv_string::!abbrvs;
        let id = next_abbrv in
        Hashtbl.add abbrv_mapping abbrv_string id;
        id)


  end)

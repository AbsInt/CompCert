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

(* Types used for writing dwarf debug information *)

(* Basic types for the value of attributes *)

type constant = int

type flag = bool

type reference = int

type encoding =
  | DW_ATE_address
  | DW_ATE_boolean
  | DW_ATE_complex_float
  | DW_ATE_float
  | DW_ATE_signed
  | DW_ATE_signed_char
  | DW_ATE_unsigned
  | DW_ATE_unsigned_char

type address = int

type language =
  | DW_LANG_C
  | DW_LANG_C89

type block = string

type location_value =
  | LocConst of constant
  | LocBlock of block

type data_location_value =
  | DataLocBlock of block
  | DataLocRef of reference

type bound_value =
  | BoundConst of constant
  | BoundRef of reference

(* Types representing the attribute information per tag value *)

type dw_tag_array_type =
    {
     array_type_decl_file: constant  option;
     array_type_decl_line: constant  option;
     array_type:           reference;
   }

type dw_tag_base_type =
    {
     base_type_byte_size: constant;
     base_type_encoding:  encoding;
     base_type_name:      string;
   }

type dw_tag_compile_unit =
    {
     compile_unit_comp_dir:        string;
     compile_unit_high_pc:         address;
     compile_unit_low_pc:          address;
     compile_unit_language:        language;
     compile_unit_name:            string;
     compile_unit_producer:        string;
     compile_unit_stmt_list:       constant option;
   }

type dw_tag_const_type =
    {
     const_type: reference;     
   }

type dw_tag_enumeration_type =
    {
     enumeration_decl_file:   constant  option;
     enumeration_decl_line:   constant  option;
     enumeration_byte_size:   constant;
     enumeration_declaration: flag      option;
     enumeration_name:        string;
   }

type dw_tag_enumerator =
    {
     enumerator_decl_file: constant  option;
     enumerator_decl_line: constant  option;
     enumerator_value:     constant;
     enumerator_name:      string;
   }

type dw_tag_formal_parameter =
    {
     formal_parameter_decl_file:          constant       option;
     formal_parameter_decl_line:          constant       option;
     formal_parameter_artificial:         flag           option;
     formal_parameter_location:           location_value option;
     formal_parameter_name:               string;
     formal_parameter_segment:            location_value option;
     formal_parameter_type:               reference;
     formal_parameter_variable_parameter: flag           option;
   }

type dw_tag_label =
    {
     label_low_pc: address;
     label_name:   string;
   }

type dw_tag_lexical_block =
    {
     lexical_block__high_pc: address;
     lexical_block_low_pc:   address;
   }

type dw_tag_member =
    {
     member_decl_file:            constant            option;
     member_decl_line:            constant            option;
     member_byte_size:            constant            option;
     member_bit_offset:           constant            option;
     member_bit_size:             constant            option;
     member_data_member_location: data_location_value option;
     member_declaration:          flag                option;
     member_name:                 string;
     member_type:                 reference;
   }

type dw_tag_pointer_type =
    {
     pointer_type: reference;
   }

type dw_tag_structure_type =
    {
     structure_decl_file:   constant  option;
     structure_decl_line:   constant  option;
     structure_byte_size:   constant;
     structure_declaration: flag      option;
     structure_name:        string;
   }

type dw_tag_subprogram =
    {
     subprogram_decl_file:  constant       option;
     subprogram_decl_line:  constant       option;
     subprogram_external:   flag           option;
     subprogram_frame_base: location_value option;
     subprogram_high_pc:    address;
     subprogram_low_pc:     address;
     subprogram_name:       string;
     subprogram_prototyped: flag;
     subprogram_type:       reference;
   }

type dw_tag_subrange_type =
    {
     subrange_type:        reference option;
     subrange_upper_bound: bound_value;
   }

type dw_tag_subroutine_type =
    {
     subroutine_prototyped: flag;
   }

type dw_tag_typedef =
    {
     typedef_decl_file: constant  option;
     typedef_decl_line: constant  option;
     typedef_name:      string;
     typedef_type:      reference;
   }

type dw_tag_union_type =
    {
     union_decl_file: constant  option;
     union_decl_line: constant  option;
     union_byte_size: constant;
     union_name:      string;
   }

type dw_tag_unspecified_parameter =
    {
     unspecified_parameter_decl_file:  constant option;
     unspecified_parameter_decl_line:  constant option;
     unspecified_parameter_artificial: flag     option;
   }

type dw_tag_variable =
    {
     variable_decl_file:   constant       option;
     variable_decl_line:   constant       option;
     variable_declaration: flag           option;
     variable_external:    flag           option;
     variable_location:    location_value option;
     variable_name:        string;
     variable_segment:     location_value option;
     variable_type:        reference;
   }

type dw_tag_volatile_type =
    {
     volatile_type: reference;
   }

type dw_tag =
  | DW_TAG_array_type of dw_tag_array_type
  | DW_TAG_base_type of dw_tag_base_type
  | DW_TAG_compile_unit of dw_tag_compile_unit
  | DW_TAG_const_type of dw_tag_const_type
  | DW_TAG_enumeration_type of dw_tag_enumeration_type
  | DW_TAG_enumerator of dw_tag_enumerator
  | DW_TAG_formal_parameter of dw_tag_formal_parameter
  | DW_TAG_label of dw_tag_label
  | DW_TAG_lexical_block of dw_tag_lexical_block
  | DW_TAG_member of dw_tag_member
  | DW_TAG_pointer_type of dw_tag_pointer_type
  | DW_TAG_structure_type of dw_tag_structure_type
  | DW_TAG_subprogram of dw_tag_subprogram
  | DW_TAG_subrange_type of dw_tag_subrange_type
  | DW_TAG_subroutine_type of dw_tag_subroutine_type
  | DW_TAG_typedef of dw_tag_typedef
  | DW_TAG_union_type of dw_tag_union_type
  | DW_TAG_unspecified_parameter of dw_tag_unspecified_parameter
  | DW_TAG_variable of dw_tag_variable
  | DW_TAG_volatile_type of dw_tag_volatile_type

(* The type of the entries. *)

type dw_entry = 
    {
     tag:      dw_tag;
     children: dw_entry list;
     id:       reference;
   }



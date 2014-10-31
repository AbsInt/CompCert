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

type identifier_case =
  | DW_ID_case_sensitive
  | DW_ID_up_case
  | DW_ID_down_case
  | DW_ID_case_insensitive

type address = int

type language =
  | DW_LANG_C
  | DW_LANG_C89

type block = string (* Used as bitvector *)

type calling_convention =
  | DW_CC_normal
  | DW_CC_program
  | DW_CC_nocall
  | DW_CC_lo_user
  | DW_CC_hi_user

type inline =
  | DW_INL_not_inlined
  | DW_INL_inlined
  | DW_INL_declared_not_inlined
  | DW_INL_declared_inlined

type const_value =
  | String of string
  | Const of constant
  | Block of block

type location_value =
  | Const of constant
  | Block of block

type data_location_value =
  | Block of block
  | Ref of reference

type bound_value =
  | Const of constant
  | Ref of reference

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
     dw_at_decl_file:          constant       option;
     dw_at_decl_line:          constant       option;
     dw_at_artificial:         flag           option;
     dw_at_location:           location_value option;
     dw_at_name:               string;
     dw_at_segment:            location_value option;
     dw_at_type:               reference;
     dw_at_variable_parameter: flag           option;
   }

type dw_tag_label =
    {
     label_low_pc: address;
     label_name:   string;
   }

type dw_tag_lexical_block =
    {
     lexical_block__high_pc: address;
     lexical_block_low_pc:  address;
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
     dw_at_decl_file:  constant       option;
     dw_at_decl_line:  constant       option;
     dw_at_external:   flag           option;
     dw_at_frame_base: location_value option;
     dw_at_high_pc:    address;
     dw_at_inline:     inline         option;
     dw_at_low_pc:     address;
     dw_at_name:       string;
     dw_at_prototyped: flag;
     dw_at_type:       reference;
   }

type dw_tag_subrange_type =
    {
     dw_at_type:        reference option;
     dw_at_upper_bound: bound_value;
   }

type dw_tag_subroutine_type =
    {
     dw_at_prototyped: flag;
   }

type dw_tag_typedef =
    {
     dw_at_decl_file: constant  option;
     dw_at_decl_line: constant  option;
     dw_at_name:      string;
     dw_at_type:      reference;
   }

type dw_tag_union_type =
    {
     dw_at_decl_file: constant  option;
     dw_at_decl_line: constant  option;
     dw_at_byte_size: constant;
     dw_at_name:      string;
   }

type dw_tag_unspecified_parameter =
    {
     dw_at_decl_file:  constant option;
     dw_at_decl_line:  constant option;
     dw_at_artificial: flag      option;
   }

type dw_tag_variable =
    {
     dw_at_decl_file:   constant       option;
     dw_at_decl_line:   constant       option;
     dw_at_declaration: flag           option;
     dw_at_external:    flag           option;
     dw_at_location:    location_value option;
     dw_at_name:        string;
     dw_at_segment:     location_value option;
     dw_at_type:        reference;
   }

type dw_tag_volatile_type =
    {
     dw_at_type: reference;
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
  | DW_TAG_tag_subprogram of dw_tag_subprogram
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



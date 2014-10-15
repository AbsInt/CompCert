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
     dw_at_byte_size:   constant  option;
     dw_at_declaration: flag      option;
     dw_at_name:        string    option;
     dw_at_sibling:     reference option;
     dw_at_start_scope: constant  option;
     dw_at_stride_size: constant  option;
     dw_at_type:        reference option;
   }

type dw_tag_base_type =
    {
     dw_at_bit_offset: constant  option;
     dw_at_bit_size:   constant  option;
     dw_at_byte_size:  constant  option;
     dw_at_encoding:   encoding  option;
     dw_at_name:       string    option;
     dw_at_sibling:    reference option;
   }

type dw_tag_compile_unit =
    {
     dw_at_base_types:      reference       option;
     dw_at_comp_dir:        string          option;
     dw_at_identifier_case: identifier_case option;
     dw_at_high_pc:         address         option;
     dw_at_language:        language        option;
     dw_at_low_pc:          address         option;
     dw_at_macro_info:      constant        option;
     dw_at_name:            string          option;
     dw_at_producer:        string          option;
     dw_at_sibling:         reference       option;
     dw_at_stmt_list:       constant        option;
   }

type dw_tag_const_type =
    {
     dw_at_sibling: reference option;
     dw_at_type:    reference option;     
   }

type dw_tag_constant =
    {
     dw_at_const_value: constant  option;
     dw_at_declaration: flag      option;
     dw_at_external:    flag      option;
     dw_at_name:        string    option;
     dw_at_sibling:     reference option;
     dw_at_start_scope: constant  option;
     dw_at_type:        reference option;
   }

type dw_tag_enumeration_type =
    {
     dw_at_byte_size:   constant option;
     dw_at_declaration: flag     option;
     dw_at_name:        string    option;
     dw_at_sibling:     reference option;
     dw_at_start_scope: constant  option;
   }

type dw_tag_enumerator =
    {
     dw_at_const_value: constant  option;
     dw_at_name:        string    option;
     dw_at_sibling:     reference option;
   }

type dw_tag_formal_parameter =
    {
     dw_at_artificial:         flag           option;
     dw_at_location:           location_value option;
     dw_at_name:               string         option;
     dw_at_segment:            location_value option;
     dw_at_sibling:            reference      option;
     dw_at_type:               reference      option;
     dw_at_variable_parameter: flag           option;
   }

type dw_tag_inlined_subroutine =
    {
     dw_at_high_pc:     address        option;
     dw_at_low_pc:      address        option;
     dw_at_segment:     location_value option;
     dw_at_sibling:     reference      option;
     dw_at_return_addr: location_value option;
     dw_at_start_scope: constant       option;
   }

type dw_tag_label =
    {
     dw_at_low_pc:      address        option;
     dw_at_name:        string         option;
     dw_at_segment:     location_value option;
     dw_at_start_scope: constant       option;
     dw_at_sibling:     reference      option;
   }

type dw_tag_lexical_block =
    {
     dw_at_high_pc: address        option;
     dw_at_low_pc:  address        option;
     dw_at_name:    string         option;
     dw_at_segment: location_value option;
     dw_at_sibling: reference      option;
   }

type dw_tag_member =
    {
     dw_at_byte_size:            constant            option;
     dw_at_bit_offset:           constant            option;
     dw_at_bit_size:             constant            option;
     dw_at_data_member_location: data_location_value option;
     dw_at_declaration:          flag                option;
     dw_at_name:                 string              option;
     dw_at_sibling:              reference           option;
     dw_at_type:                 reference           option;
   }

type dw_tag_pointer_type =
    {
     dw_at_address_class: constant  option;
     dw_at_sibling:       reference option;
     dw_at_type:          reference option;
   }

type dw_tag_structure_type =
    {
     dw_at_byte_size:   constant  option;
     dw_at_declaration: flag      option;
     dw_at_name:        string    option;
     dw_at_sibling:     reference option;
     dw_at_start_scope: constant  option;
   }

type dw_tag_subprogram =
    {
     dw_at_address_class:      constant           option;
     dw_at_artificial:         flag               option;
     dw_at_calling_convention: calling_convention option;
     dw_at_declaration:        flag               option;
     dw_at_external:           flag               option;
     dw_at_frame_base:         location_value     option;
     dw_at_high_pc:            address            option;
     dw_at_inline:             inline             option;
     dw_at_low_pc:             address            option;
     dw_at_name:               string             option;
     dw_at_prototyped:         flag               option;
     dw_at_return_addr:        location_value     option;
     dw_at_segment:            location_value     option;
     dw_at_sibling:            reference          option;
     dw_at_start_scope:        constant           option;
     dw_at_static_link:        location_value     option;
     dw_at_type:               reference          option;
   }

type dw_subrange_type =
    {
     dw_at_byte_size:   constant    option;
     dw_at_declaration: flag        option;
     dw_at_count:       bound_value option;
     dw_at_lower_bound: bound_value option;
     dw_at_name:        string      option;
     dw_at_sibling:     reference   option;
     dw_at_type:        reference   option;
     dw_at_upper_bound: bound_value option;
   }

type dw_tag_subroutine_type =
    {
     dw_at_address_class: constant  option;
     dw_at_declaration:   flag      option;
     dw_at_name:          string    option;
     dw_at_prototyped:    flag      option;
     dw_at_sibling:       reference option;
     dw_at_type:          reference option;
   }

type dw_tag_typedef =
    {
     dw_at_declaration: flag      option;
     dw_at_name:        string    option;
     dw_at_sibling:     reference option;
     dw_at_start_scope: constant  option;
     dw_at_type:        reference option;
   }

type dw_tag_union_type =
    {
     dw_at_byte_size:   constant    option;
     dw_at_declaration: flag      option;
     dw_at_name:        string    option;
     dw_at_sibling:     reference option;
     dw_at_start_scope: constant  option;
     dw_at_type:        reference option;
   }

type dw_tag_unspecified_parameter =
    {
     dw_at_artificial: flag      option;
     dw_at_sibling:    reference option;
   }

type dw_tag_variable =
    {
     dw_at_const_value: constant       option;
     dw_at_declaration: flag           option;
     dw_at_external:    flag           option;
     dw_at_location:    location_value option;
     dw_at_name:        string         option;
     dw_at_segment:     location_value option;
     dw_at_sibling:     reference      option;
     dw_at_start_scope: constant       option;
     dw_at_type:        reference      option;
   }

type dw_tag_volatile_type =
    {
     dw_at_sibling: reference option;
     dw_at_type:    reference option;

   }

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

type const_value =
  | String of string
  | Const of constant
  | Block of block

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

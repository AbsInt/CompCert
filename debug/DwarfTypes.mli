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

open Sections
open Camlcoq

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

type block = string

type location_expression =
  | DW_OP_plus_uconst of constant
  | DW_OP


type location_value =
  | LocSymbol of atom
  | LocConst of constant
  | LocBlock of block

type data_location_value =
  | DataLocBlock of location_expression list
  | DataLocRef of reference

type bound_value =
  | BoundConst of constant
  | BoundRef of reference

(* Types representing the attribute information per tag value *)

type file_loc = string * constant

type dw_tag_array_type =
    {
     array_type_file_loc: file_loc option;
     array_type:          reference;
   }

type dw_tag_base_type =
    {
     base_type_byte_size: constant;
     base_type_encoding:  encoding option;
     base_type_name:      string;
   }

type dw_tag_compile_unit =
    {
     compile_unit_name:            string;
   }

type dw_tag_const_type =
    {
     const_type: reference;
   }

type dw_tag_enumeration_type =
    {
     enumeration_file_loc:    file_loc  option;
     enumeration_byte_size:   constant;
     enumeration_declaration: flag      option;
     enumeration_name:        string    option;
   }

type dw_tag_enumerator =
    {
     enumerator_file_loc: file_loc option;
     enumerator_value:    constant;
     enumerator_name:     string;
   }

type dw_tag_formal_parameter =
    {
     formal_parameter_file_loc:           file_loc       option;
     formal_parameter_artificial:         flag           option;
     formal_parameter_name:               string         option;
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
     lexical_block_high_pc: address option;
     lexical_block_low_pc:  address option;
   }

type dw_tag_member =
    {
     member_file_loc:             file_loc            option;
     member_byte_size:            constant            option;
     member_bit_offset:           constant            option;
     member_bit_size:             constant            option;
     member_data_member_location: data_location_value option;
     member_declaration:          flag                option;
     member_name:                 string              option;
     member_type:                 reference;
   }

type dw_tag_pointer_type =
    {
     pointer_type: reference;
   }

type dw_tag_structure_type =
    {
     structure_file_loc:    file_loc option;
     structure_byte_size:   constant option;
     structure_declaration: flag     option;
     structure_name:        string   option;
   }

type dw_tag_subprogram =
    {
     subprogram_file_loc:   file_loc;
     subprogram_external:   flag      option;
     subprogram_name:       string;
     subprogram_prototyped: flag;
     subprogram_type:       reference option;
     subprogram_high_pc:    reference option;
     subprogram_low_pc:     reference option;
   }

type dw_tag_subrange_type =
    {
     subrange_type:        reference   option;
     subrange_upper_bound: bound_value option;
   }

type dw_tag_subroutine_type =
    {
     subroutine_type:       reference option;
     subroutine_prototyped: flag;
   }

type dw_tag_typedef =
    {
     typedef_file_loc: file_loc option;
     typedef_name:     string;
     typedef_type:     reference;
   }

type dw_tag_union_type =
    {
     union_file_loc:    file_loc option;
     union_byte_size:   constant option;
     union_declaration: flag     option;
     union_name:        string   option;
   }

type dw_tag_unspecified_parameter =
    {
     unspecified_parameter_file_loc:   file_loc option;
     unspecified_parameter_artificial: flag     option;
   }

type dw_tag_variable =
    {
     variable_file_loc:    file_loc;
     variable_declaration: flag           option;
     variable_external:    flag           option;
     variable_name:        string;
     variable_type:        reference;
     variable_location:    location_value option;
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

(* Module type for a matching from type to dwarf encoding *)
module type DWARF_ABBREVS =
  sig
    val sibling_type_abbr: int
    val file_loc_type_abbr: int * int
    val type_abbr: int
    val name_type_abbr: int
    val encoding_type_abbr: int
    val byte_size_type_abbr: int
    val member_size_abbr: int
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

(* The target specific functions for printing the debug information *)
module type DWARF_TARGET=
  sig
    val label: out_channel -> int -> unit
    val print_file_loc: out_channel -> file_loc -> unit
    val get_start_addr: unit -> int
    val get_end_addr: unit -> int
    val get_stmt_list_addr: unit -> int    
    val name_of_section: section_name -> string
    val get_location: int -> location_value option
    val get_frame_base: int -> location_value option
    val symbol: out_channel -> atom -> unit
  end

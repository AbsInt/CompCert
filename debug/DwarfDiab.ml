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

open Printf
open DwarfPrinter
open DwarfTypes
open DwarfUtil

module AbbrvPrinter = DwarfPrinter(struct
  let string_of_byte value =
    Printf.sprintf "	.byte	%s\n" (if value then "0x1" else "0x2")
      
  let string_of_abbrv_entry v =
    Printf.sprintf "	.uleb128	%d\n" v

  let sibling_type_abbr = dw_form_ref4
  let decl_file_type_abbr = dw_form_data4
  let decl_line_type_abbr = dw_form_udata
  let type_abbr = dw_form_ref_addr
  let name_type_abbr = dw_form_string
  let encoding_type_abbr = dw_form_data1
  let byte_size_type_abbr = dw_form_data1
  let high_pc_type_abbr = dw_form_addr
  let low_pc_type_abbr = dw_form_addr
  let stmt_list_type_abbr = dw_form_data4
  let declaration_type_abbr = dw_form_flag
  let external_type_abbr = dw_form_flag
  let prototyped_type_abbr = dw_form_flag
  let bit_offset_type_abbr = dw_form_data1
  let comp_dir_type_abbr = dw_form_string
  let language_type_abbr = dw_form_udata
  let producer_type_abbr = dw_form_string
  let value_type_abbr = dw_form_sdata
  let artificial_type_abbr = dw_form_flag
  let variable_parameter_type_abbr = dw_form_flag
  let bit_size_type_abbr = dw_form_data1
  let location_const_type_abbr = dw_form_data4
  let location_block_type_abbr = dw_form_block
  let data_location_block_type_abbr = dw_form_block
  let data_location_ref_type_abbr = dw_form_ref4
  let bound_const_type_abbr = dw_form_udata
  let bound_ref_type_abbr=dw_form_ref4
      

      
end)

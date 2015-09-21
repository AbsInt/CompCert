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

(* Generate a new entry from a given tag *)
let new_entry id tag =
  {
   tag = tag;
   children = [];
   id = id;
 }

(* Add an entry as child to  another entry *)
let add_child entry child =
  {entry with children = child::entry.children;}


(* Add entries as children to  another entry *)
let add_children entry children =
  {entry with children = entry.children@children;}


let list_iter_with_next f list =
  let rec aux = (function
    | [] -> ()
    | [a] -> f None a
    | a::b::rest -> f (Some b.id) a; aux (b::rest)) in
  aux list

(* Iter over the tree and pass the sibling id *)
let entry_iter_sib f g entry =
  let rec aux sib entry =
    f sib entry;
    list_iter_with_next aux entry.children;
    g entry in
  aux None entry


(* Fold over the tree in prefix order *)
let rec entry_fold f acc entry =
  let acc = f acc entry.tag in
  List.fold_left (entry_fold f) acc entry.children

(* Attribute form encoding *)
let dw_form_addr     = 0x01
let dw_form_block2   = 0x03
let dw_form_block4   = 0x04
let dw_form_data2    = 0x05
let dw_form_data4    = 0x06
let dw_form_data8    = 0x07
let dw_form_string   = 0x08
let dw_form_block    = 0x09
let dw_form_block1   = 0x0a
let dw_form_data1    = 0x0b
let dw_form_flag     = 0x0c
let dw_form_sdata    = 0x0d
let dw_form_strp     = 0x0e
let dw_form_udata    = 0x0f
let dw_form_ref_addr = 0x10
let dw_form_ref1     = 0x11
let dw_form_ref2     = 0x12
let dw_form_ref4     = 0x13
let dw_form_ref8     = 0x14
let dw_ref_udata     = 0x15
let dw_ref_indirect  = 0x16

(* Default corresponding encoding for the different abbreviations *)
module DefaultAbbrevs =
  struct
    let sibling_type_abbr = dw_form_ref4
    let file_loc_type_abbr = dw_form_data4,dw_form_udata
    let type_abbr = dw_form_ref_addr
    let name_type_abbr = dw_form_string
    let encoding_type_abbr = dw_form_data1
    let byte_size_type_abbr = dw_form_data1
    let member_size_abbr = dw_form_udata
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
  end

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* The Diab specific printing functions *)

open Printf
open Datatypes
open DwarfTypes
open Camlcoq
open Sections
open Asm
open PrintUtil
    
module Diab_System =
  (struct
    let comment =  ";"
        
    let constant oc cst =
      match cst with
      | Cint n ->
          fprintf oc "%ld" (camlint_of_coqint n)
      | Csymbol_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_high(s, n) ->
          symbol_fragment oc s n "@ha"
      | Csymbol_sda(s, n) ->
          symbol_fragment oc s n "@sdarx"
      | Csymbol_rel_low(s, n) ->
          symbol_fragment oc s n "@sdax@l"
      | Csymbol_rel_high(s, n) ->
          symbol_fragment oc s n "@sdarx@ha"
            
    let ireg oc r =
      output_char oc 'r';
      output_string oc (int_reg_name r)

    let freg oc r =
      output_char oc 'f';
      output_string oc (float_reg_name r)
        
    let creg oc r =
      fprintf oc "cr%d" r
        
    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i -> if i then ".data" else ".bss"
      | Section_small_data i -> if i then ".sdata" else ".sbss"
      | Section_const -> ".text"
      | Section_small_const -> ".sdata2"
      | Section_string -> ".text"
      | Section_literal -> ".text"
      | Section_jumptable -> ".text"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",,%c"
            s
            (match wr, ex with
            | true, true -> 'm'                 (* text+data *)
            | true, false -> 'd'                (* data *)
            | false, true -> 'c'                (* text *)
            | false, false -> 'r')              (* const *)

    let last_file = ref ""
    let reset_file_line () = last_file := ""
    let print_file_line oc file line =
      if !Clflags.option_g && file <> "" then begin
        if file <> !last_file then begin
          fprintf oc "	.d1file	%S\n" file;
          last_file := file
        end;
        fprintf oc "	.d1line	%s\n" line
      end

          (* Emit .cfi directives *)
    let cfi_startproc oc = ()

    let cfi_endproc oc = ()

    let cfi_adjust oc delta = ()

    let cfi_rel_offset oc reg ofs = ()

    let print_prologue oc =
      fprintf oc "	.xopt	align-fill-text=0x60000000\n";
      if !Clflags.option_g then
        fprintf oc "	.xopt	asm-debug-on\n"
          
    let curr_abbrv = ref 0

    let next_abbrv =
      let abbrv = !curr_abbrv in
      incr curr_abbrv;abbrv

    let abbrvs: string list ref = ref []

    let abbrv_mapping: (string,int) Hashtbl.t = Hashtbl.create 7

    let add_byte buf value =
      let s = 
        if value then
          "	.byte	0x1\n"
        else
          
          "	.byte	0x0\n"
      in
      Buffer.add_string buf s

    let add_abbr_uleb buf v =
      Buffer.add_string buf "	.uleb128	";
      Buffer.add_string buf v;
      Buffer.add_string buf "\n"
        
    let add_sibling buf =
      add_abbr_uleb buf "1";
      add_abbr_uleb buf "19"
        
    let add_decl_file buf =
      add_abbr_uleb buf "58";
      add_abbr_uleb buf "6"
 
    let add_decl_line buf =
      add_abbr_uleb buf "59";
      add_abbr_uleb buf "15"
        
    let add_type buf =
      add_abbr_uleb buf "73";
      add_abbr_uleb buf "16"
   
    let add_array_type buf a_typ =
      (match a_typ.array_type_file with
      | None -> ()
      | Some _ -> add_decl_file buf);
      (match a_typ.array_type_line with
      | None -> ()
      | Some _ -> add_decl_line buf);
      add_type buf

    let add_name buf =
      add_abbr_uleb buf "3";
      add_abbr_uleb buf "8"
        
    let abbrv_string_of_entity entity has_sibling =
      let buf = Buffer.create 12 in
      let has_child = (match entity.children with [] -> false | _ -> true) in
      (match entity.tag with
      | DW_TAG_array_type e -> 
          (add_abbr_uleb buf "1";
          add_byte buf has_child;
          if has_sibling then add_sibling buf;
          add_array_type buf e)
      | _ -> ());
      Buffer.contents buf

    let get_abbrv entity  has_sibling =
      let abbrv_string = abbrv_string_of_entity entity has_sibling in
      (try
        Hashtbl.find abbrv_mapping abbrv_string
      with Not_found ->
        abbrvs:=abbrv_string::!abbrvs;
        let id = next_abbrv in
        Hashtbl.add abbrv_mapping abbrv_string id;
        id)

  end:SYSTEM)

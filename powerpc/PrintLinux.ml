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

(* The Linux specific printing functions *)

open Printf
open Datatypes
open Camlcoq
open Sections
open Asm
open PrintUtil

module Linux_System =
  (struct
    let comment =  "#"

    let constant oc cst =
      match cst with
      | Cint n ->
          fprintf oc "%ld" (camlint_of_coqint n)
      | Csymbol_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_high(s, n) ->
          symbol_fragment oc s n "@ha"
      | Csymbol_sda(s, n) ->
          symbol_fragment oc s n "@sda21"
            (* 32-bit relative addressing is supported by the Diab tools but not by
               GNU binutils.  In the latter case, for testing purposes, we treat
               them as absolute addressings.  The default base register being GPR0,
               this produces correct code, albeit with absolute addresses. *)
      | Csymbol_rel_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_rel_high(s, n) ->
          symbol_fragment oc s n "@ha"

    let ireg oc r =
      output_string oc (int_reg_name r)

    let freg oc r =
      output_string oc (float_reg_name r)
        
    let creg oc r = 
      fprintf oc "%d" r
 
    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i -> if i then ".data" else "COMM"
      | Section_small_data i -> 
          if i
          then ".section	.sdata,\"aw\",@progbits"
          else ".section	.sbss,\"aw\",@progbits"
      | Section_const -> ".rodata"
      | Section_small_const -> ".section	.sdata2,\"a\",@progbits"
      | Section_string -> ".rodata"
      | Section_literal -> ".section	.rodata.cst8,\"aM\",@progbits,8"
      | Section_jumptable -> ".text"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",@progbits"
            s (if wr then "w" else "") (if ex then "x" else "")

    let filename_num : (string, int) Hashtbl.t = Hashtbl.create 7
    let reset_file_line () = Hashtbl.clear filename_num
    let print_file_line oc file line =
      if !Clflags.option_g && file <> "" then begin
        let filenum = 
          try
            Hashtbl.find filename_num file
          with Not_found ->
            let n = Hashtbl.length filename_num + 1 in
            Hashtbl.add filename_num file n;
            fprintf oc "	.file	%d %S\n" n file;
            n
        in fprintf oc "	.loc	%d %s\n" filenum line
      end
    
    (* Emit .cfi directives *)      
    let cfi_startproc =
      if Configuration.asm_supports_cfi then
        (fun oc -> fprintf oc "	.cfi_startproc\n")
      else
        (fun _ -> ())

    let cfi_endproc =
      if Configuration.asm_supports_cfi then
        (fun oc -> fprintf oc "	.cfi_endproc\n")
      else
        (fun _ -> ())

              
    let cfi_adjust =
      if Configuration.asm_supports_cfi then
       (fun oc delta -> fprintf oc "	.cfi_adjust_cfa_offset	%ld\n" delta)
      else
        (fun _ _ -> ())
              
    let cfi_rel_offset =
      if Configuration.asm_supports_cfi then
        (fun oc reg ofs -> fprintf oc "	.cfi_rel_offset	%s, %ld\n" reg ofs)
      else
        (fun _ _ _ -> ())


    let print_prologue oc = ()
  
  end:SYSTEM)

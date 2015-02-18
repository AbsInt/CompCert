(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST
open Asm
open Camlcoq
open Datatypes
open Printf
open Sections

(** Auxiliary functions for printing of asm *)

module type TARGET =
    sig
      val print_prologue: out_channel -> unit
      val print_epilogue: out_channel -> unit
      val print_align: out_channel -> int -> unit
      val print_comm_symb:  out_channel -> Z.t -> P.t -> int -> unit
      val print_var_info: out_channel -> P.t -> unit
      val print_fun_info: out_channel -> P.t -> unit
      val print_init: out_channel -> init_data -> unit
      val reset_constants: unit -> unit
      val get_section_names: P.t -> section_name * section_name * section_name
      val print_file_line: out_channel -> string -> int -> unit
      val print_optional_fun_info: out_channel -> unit
      val cfi_startproc: out_channel -> unit
      val print_instructions: out_channel -> coq_function -> unit
      val cfi_endproc: out_channel -> unit
      val emit_constants: out_channel -> section_name -> unit
      val print_jumptable: out_channel -> section_name -> unit
      val section: out_channel -> section_name -> unit
      val name_of_section: section_name -> string
      val comment: string
      val symbol: out_channel -> P.t -> unit
    end

(* On-the-fly label renaming *)

let next_label = ref 100

let new_label () =
  let lbl = !next_label in incr next_label; lbl

let current_function_labels = (Hashtbl.create 39 : (label, int) Hashtbl.t)

let transl_label lbl =
  try
    Hashtbl.find current_function_labels lbl
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add current_function_labels lbl lbl';
    lbl'

let elf_label oc lbl =
  fprintf oc ".L%d" lbl

(* List of literals and jumptables used in the code *)

let float64_literals : (int * int64) list ref = ref []
let float32_literals : (int * int32) list ref = ref []
let jumptables : (int * label list) list ref = ref []

let reset_constants () =
  float64_literals := [];
  float32_literals := [];
  jumptables := []

(* Variables used for the handling of varargs *)

let current_function_stacksize = ref 0l
let current_function_sig =
  ref { sig_args = []; sig_res = None; sig_cc = cc_default }

(* Functions for printing of symbol names *)
let elf_symbol oc symb =
  fprintf oc "%s" (extern_atom symb)

let elf_symbol_offset oc (symb, ofs) =
  elf_symbol oc symb;
  let ofs = camlint_of_coqint ofs in
  if ofs <> 0l then fprintf oc " + %ld" ofs

(* Functions for fun and var info *)
let elf_print_fun_info oc name =
  fprintf oc "	.type	%a, @function\n" elf_symbol name;
  fprintf oc "	.size	%a, . - %a\n" elf_symbol name elf_symbol name
   
let elf_print_var_info oc name =
  fprintf oc "	.type	%a, @object\n" elf_symbol name;
  fprintf oc "	.size	%a, . - %a\n" elf_symbol name elf_symbol name

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

(* For handling of annotations *)
let re_file_line = Str.regexp "#line:\\(.*\\):\\([1-9][0-9]*\\)$"

(* Basic printing functions *)
let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

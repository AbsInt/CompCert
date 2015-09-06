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
open DwarfTypes
open Datatypes
open Memdata
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
      val default_falignment: int
      val get_start_addr: unit -> int
      val get_end_addr: unit -> int
      val get_stmt_list_addr: unit -> int
      val new_label: unit -> int
      val label: out_channel -> int -> unit
      val print_file_loc: out_channel -> file_loc -> unit
      val get_location: P.t -> location_value option
      val get_segment_location: P.t -> location_value option
      val add_var_location: P.t -> unit
      module DwarfAbbrevs:  DWARF_ABBREVS
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

(* Basic printing functions *)
let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

(** Programmer-supplied annotations (__builtin_annot). *)

let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"

let rec print_annot print_preg sp_reg_name oc = function
  | BA x -> print_preg oc x
  | BA_int n -> fprintf oc "%ld" (camlint_of_coqint n)
  | BA_long n -> fprintf oc "%Ld" (camlint64_of_coqint n)
  | BA_float n -> fprintf oc "%.18g" (camlfloat_of_coqfloat n)
  | BA_single n -> fprintf oc "%.18g" (camlfloat_of_coqfloat32 n)
  | BA_loadstack(chunk, ofs) ->
      fprintf oc "mem(%s + %ld, %ld)"
         sp_reg_name
         (camlint_of_coqint ofs)
         (camlint_of_coqint (size_chunk chunk))
  | BA_addrstack ofs ->
      fprintf oc "(%s + %ld)"
         sp_reg_name
         (camlint_of_coqint ofs)
  | BA_loadglobal(chunk, id, ofs) ->
      fprintf oc "mem(\"%s\" + %ld, %ld)"
         (extern_atom id)
         (camlint_of_coqint ofs)
         (camlint_of_coqint (size_chunk chunk))
  | BA_addrglobal(id, ofs) ->
      fprintf oc "(\"%s\" + %ld)"
         (extern_atom id)
         (camlint_of_coqint ofs)
  | BA_splitlong(hi, lo) ->
      fprintf oc "(%a * 0x100000000 + %a)"
        (print_annot print_preg sp_reg_name) hi
        (print_annot print_preg sp_reg_name) lo

let print_annot_text print_preg sp_reg_name oc txt args =
  let print_fragment = function
  | Str.Text s ->
      output_string oc s
  | Str.Delim "%%" ->
      output_char oc '%'
  | Str.Delim s ->
      let n = int_of_string (String.sub s 1 (String.length s - 1)) in
      try
        print_annot print_preg sp_reg_name oc (List.nth args (n-1))
      with Failure _ ->
        fprintf oc "<bad parameter %s>" s in
  List.iter print_fragment (Str.full_split re_annot_param txt);
  fprintf oc "\n"

(* Printing of [EF_debug] info.  To be completed. *)

let re_file_line = Str.regexp "#line:\\(.*\\):\\([1-9][0-9]*\\)$"

let print_debug_info comment print_line print_preg sp_name oc kind txt args =
  let print_debug_args oc args =
    List.iter
      (fun a -> fprintf oc " %a" (print_annot print_preg sp_name) a)
      args in
  match kind with
  | 1 ->  (* line number *)
      if Str.string_match re_file_line txt 0 then
        print_line oc (Str.matched_group 1 txt)
                      (int_of_string (Str.matched_group 2 txt))
  | 2 ->  (* assignment to local variable, not useful *)
      ()
  | 3 ->  (* beginning of live range for local variable *)
      fprintf oc "%s debug: start live range %s =%a\n"
                 comment txt print_debug_args args
  | 4 ->  (* end of live range for local variable *)
      fprintf oc "%s debug: end live range %s\n"
                 comment txt
  | 5 ->  (* local variable preallocated in stack *)
      fprintf oc "%s debug: %s resides at%a\n"
                 comment txt print_debug_args args
  | _ ->
      ()
					    
(** Inline assembly *)

let print_asm_argument print_preg oc modifier = function
  | BA r -> print_preg oc r
  | BA_splitlong(BA hi, BA lo) ->
      begin match modifier with
      | "R" -> print_preg oc hi
      | "Q" -> print_preg oc lo
      |  _  -> fprintf oc "%a:%a" print_preg hi print_preg lo
                  (* Probably not what was intended *)
      end
  | _ -> failwith "bad asm argument"

let builtin_arg_of_res = function
  | BR r -> BA r
  | BR_splitlong(BR hi, BR lo) -> BA_splitlong(BA hi, BA lo)
  | _ -> assert false

let re_asm_param_1 = Str.regexp "%%\\|%[QR]?[0-9]+"
let re_asm_param_2 = Str.regexp "%\\([QR]?\\)\\([0-9]+\\)"

let print_inline_asm print_preg oc txt sg args res =
  let operands =
    if sg.sig_res = None then args else builtin_arg_of_res res :: args in
  let print_fragment = function
  | Str.Text s ->
      output_string oc s
  | Str.Delim "%%" ->
      output_char oc '%'
  | Str.Delim s ->
      assert (Str.string_match re_asm_param_2 s 0);
      let modifier = Str.matched_group 1 s
      and number = int_of_string (Str.matched_group 2 s) in
      try
        print_asm_argument print_preg oc modifier (List.nth operands number)
      with Failure _ ->
        fprintf oc "<bad parameter %s>" s in
  List.iter print_fragment (Str.full_split re_asm_param_1 txt);
  fprintf oc "\n"


(** Print CompCert version and command-line as asm comment *)

let print_version_and_options oc comment =
  fprintf oc "%s File generated by CompCert %s\n" comment Version.version;
  fprintf oc "%s Command line:" comment;
  for i = 1 to Array.length Sys.argv - 1 do
    fprintf oc " %s" Sys.argv.(i)
  done;
  fprintf oc "\n"

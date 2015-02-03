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
      val print_comm_symb:  out_channel -> P.t -> int -> unit
      val print_var_info: out_channel -> P.t -> unit
      val print_fun_info: out_channel -> P.t -> unit
      val print_init: out_channel -> init_data -> unit
      val reset_constants: unit -> unit
      val get_section_names: unit -> section_name * section_name * section_name
      val print_file_line: out_channel -> string -> int -> unit
      val print_optional_fun_info: out_channel -> unit
      val cfi_startproc: out_channel -> unit
      val print_instructions: out_channel -> code -> unit
      val cfi_endproc: out_channel -> unit
      val emit_constants: out_channel -> section_name -> unit
      val print_jumptable: out_channel -> section_name -> unit
      val section: out_channel -> section_name -> unit
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


(* List of literals and jumptables used in the code *)

let float64_literals : (int * int64) list ref = ref []
let float32_literals : (int * int32) list ref = ref []
let jumptables : (int * label list) list ref = ref []

(* Variables used for the handling of varargs *)

let current_function_stacksize = ref 0l
let current_function_sig =
  ref { sig_args = []; sig_res = None; sig_cc = cc_default }

(* Functions for printing of symbol names *)
let symbol oc symb =
  fprintf oc "%s" (extern_atom symb)

let symbol_offset oc (symb, ofs) =
  symbol oc symb;
  let ofs = camlint_of_coqint ofs in
  if ofs <> 0l then fprintf oc " + %ld" ofs

(* The comment deliminiter *)
let comment = "#"

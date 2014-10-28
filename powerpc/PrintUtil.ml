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

(* Common functions for the AsmPrinter *)

open Printf
open Maps
open Camlcoq
open Sections
open Asm

(* Recognition of target ABI and asm syntax *)

module type SYSTEM =
    sig
      val comment: string
      val constant: out_channel -> constant -> unit
      val ireg: out_channel -> ireg -> unit
      val freg: out_channel -> freg -> unit
      val creg: out_channel -> int -> unit
      val name_of_section: section_name -> string
      val print_file_line: out_channel -> string -> string -> unit
      val reset_file_line: unit -> unit
      val cfi_startproc: out_channel -> unit
      val cfi_endproc: out_channel -> unit
      val cfi_adjust: out_channel -> int32 -> unit
      val cfi_rel_offset: out_channel -> string -> int32 -> unit
      val print_prologue: out_channel -> unit
    end

let symbol oc symb =
  fprintf oc "%s" (extern_atom symb)

let symbol_offset oc (symb, ofs) =
  symbol oc symb;
  if ofs <> 0l then fprintf oc " + %ld" ofs

let symbol_fragment oc s n op =
      fprintf oc "(%a)%s" symbol_offset (s, camlint_of_coqint n) op


let int_reg_name = function
  | GPR0 -> "0"  | GPR1 -> "1"  | GPR2 -> "2"  | GPR3 -> "3"
  | GPR4 -> "4"  | GPR5 -> "5"  | GPR6 -> "6"  | GPR7 -> "7"
  | GPR8 -> "8"  | GPR9 -> "9"  | GPR10 -> "10" | GPR11 -> "11"
  | GPR12 -> "12" | GPR13 -> "13" | GPR14 -> "14" | GPR15 -> "15"
  | GPR16 -> "16" | GPR17 -> "17" | GPR18 -> "18" | GPR19 -> "19"
  | GPR20 -> "20" | GPR21 -> "21" | GPR22 -> "22" | GPR23 -> "23"
  | GPR24 -> "24" | GPR25 -> "25" | GPR26 -> "26" | GPR27 -> "27"
  | GPR28 -> "28" | GPR29 -> "29" | GPR30 -> "30" | GPR31 -> "31"

let float_reg_name = function
  | FPR0 -> "0"  | FPR1 -> "1"  | FPR2 -> "2"  | FPR3 -> "3"
  | FPR4 -> "4"  | FPR5 -> "5"  | FPR6 -> "6"  | FPR7 -> "7"
  | FPR8 -> "8"  | FPR9 -> "9"  | FPR10 -> "10" | FPR11 -> "11"
  | FPR12 -> "12" | FPR13 -> "13" | FPR14 -> "14" | FPR15 -> "15"
  | FPR16 -> "16" | FPR17 -> "17" | FPR18 -> "18" | FPR19 -> "19"
  | FPR20 -> "20" | FPR21 -> "21" | FPR22 -> "22" | FPR23 -> "23"
  | FPR24 -> "24" | FPR25 -> "25" | FPR26 -> "26" | FPR27 -> "27"
  | FPR28 -> "28" | FPR29 -> "29" | FPR30 -> "30" | FPR31 -> "31"

(* On-the-fly label renaming *)

let next_label = ref 100

let new_label() =
  let lbl = !next_label in incr next_label; lbl

let current_function_labels = (Hashtbl.create 39 : (label, int) Hashtbl.t)

let transl_label lbl =
  try
    Hashtbl.find current_function_labels lbl
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add current_function_labels lbl lbl';
    lbl'

(* Basic printing functions *)

let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

let raw_symbol oc s =
  fprintf oc "%s" s


let label oc lbl =
  fprintf oc ".L%d" lbl

let label_low oc lbl =
  fprintf oc ".L%d@l" lbl

let label_high oc lbl =
  fprintf oc ".L%d@ha" lbl

let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3
  | CRbit_6 -> 6

let crbit oc bit =
  fprintf oc "%d" (num_crbit bit)


(* Encoding masks for rlwinm instructions *)

let rolm_mask n =
  let mb = ref 0       (* location of last 0->1 transition *)
  and me = ref 32      (* location of last 1->0 transition *)
  and last = ref ((Int32.logand n 1l) <> 0l)  (* last bit seen *)
  and count = ref 0    (* number of transitions *)
  and mask = ref 0x8000_0000l in
  for mx = 0 to 31 do
    if Int32.logand n !mask <> 0l then
      if !last then () else (incr count; mb := mx; last := true)
    else
      if !last then (incr count; me := mx; last := false) else ();
    mask := Int32.shift_right_logical !mask 1
  done;
  if !me = 0 then me := 32;
  assert (!count = 2 || (!count = 0 && !last));
  (!mb, !me-1)

(* Handling of annotations *)

let re_file_line = Str.regexp "#line:\\(.*\\):\\([1-9][0-9]*\\)$"

(* Determine if the displacement of a conditional branch fits the short form *)

let short_cond_branch tbl pc lbl_dest =
  match PTree.get lbl_dest tbl with
  | None -> assert false
  | Some pc_dest -> 
      let disp = pc_dest - pc in -0x2000 <= disp && disp < 0x2000

(* Determine if an instruction falls through *)

let instr_fall_through = function
  | Pb _ -> false
  | Pbctr _ -> false
  | Pbs _ -> false
  | Pblr -> false
  | _ -> true

(* Estimate the size of an Asm instruction encoding, in number of actual
   PowerPC instructions.  We can over-approximate. *)

let instr_size = function
  | Pbf(bit, lbl) -> 2
  | Pbt(bit, lbl) -> 2
  | Pbtbl(r, tbl) -> 5
  | Plfi(r1, c) -> 2
  | Plfis(r1, c) -> 2
  | Plabel lbl -> 0
  | Pbuiltin(ef, args, res) -> 0
  | Pannot(ef, args) -> 0
  | Pcfi_adjust _ | Pcfi_rel_offset _ -> 0
  | _ -> 1

(* Build a table label -> estimated position in generated code.
   Used to predict if relative conditional branches can use the short form. *)

let rec label_positions tbl pc = function
  | [] -> tbl
  | Plabel lbl :: c -> label_positions (PTree.set lbl pc tbl) pc c
  | i :: c -> label_positions tbl (pc + instr_size i) c

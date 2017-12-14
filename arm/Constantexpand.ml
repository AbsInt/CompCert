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

open Asm
open Asmexpandaux
open AST
 open Camlcoq
(* open Integers *)

let _0 = Integers.Int.zero

(* Options controlling the output of the constants *)

let literals_in_code = ref true     (* to be turned into a proper option *)

let vfpv3 = Configuration.model >= "armv7"


(* Record current code position and latest position at which to
   emit float and symbol constants. *)

let currpos = ref 0
let size_constants = ref 0
let max_pos_constants = ref max_int

let distance_to_emit_constants () =
  if !literals_in_code
  then !max_pos_constants - (!currpos + !size_constants)
  else max_int


(* Associate labels to floating-point constants and to symbols *)

let float_labels = (Hashtbl.create 39 : (Floats.float, label) Hashtbl.t)
let float32_labels = (Hashtbl.create 39 : (Floats.float32, label) Hashtbl.t)
let symbol_labels =
  (Hashtbl.create 39 : (ident * Integers.Int.int, label) Hashtbl.t)

let get_label tbl sz pinc bf =
  try
    Hashtbl.find tbl bf
  with Not_found ->
    let lbl' = new_label () in
    Hashtbl.add tbl bf lbl';
    size_constants := !size_constants + sz;
    max_pos_constants := min !max_pos_constants (!currpos + pinc);
    lbl'

let label_float = get_label float_labels 8 1024
let label_float32 = get_label float32_labels 4 1024
let label_symbol id ofs = get_label symbol_labels 4 4096 (id,ofs)

let reset_constants () =
  Hashtbl.clear float_labels;
  Hashtbl.clear float32_labels;
  Hashtbl.clear symbol_labels;
  size_constants := 0;
  max_pos_constants := max_int


(* Recognition of float constants appropriate for VMOV.
   a normalized binary floating point encoding with 1 sign bit, 4
   bits of fraction and a 3-bit exponent *)

let is_immediate_float64 bits =
  let exp = (Int64.(to_int (shift_right_logical bits 52)) land 0x7FF) - 1023 in
  let mant = Int64.logand bits 0xF_FFFF_FFFF_FFFFL in
  exp >= -3 && exp <= 4 && Int64.logand mant 0xF_0000_0000_0000L = mant

let is_immediate_float32 bits =
  let exp = (Int32.(to_int (shift_right_logical bits 23)) land 0xFF) - 127 in
  let mant = Int32.logand bits 0x7F_FFFFl in
  exp >= -3 && exp <= 4 && Int32.logand mant 0x78_0000l = mant

let no_fallthrough = function
  | Pb _ -> true
  | Pbsymb _ -> true
  | Pbreg _ -> true
  | _ -> false

let estimate_size = function
  | Pflid _
  | Pflis _ -> 3
  | Pfcmpd _
  | Pfcmpzd _
  | Pfsitod _
  | Pfuitod _
  | Pftosizd _
  | Pftouizd _
  | Pfcmps _
  | Pfcmpzs _
  | Pfsitos _
  | Pfuitos _
  | Pftosizs _
  | Pftouizs _
  | Pmovite _ -> 2
  | Pbuiltin (ef,_,_) ->
    begin match ef with
    | EF_inline_asm _ -> 256
    | _ -> 0 end
  | Pcfi_adjust _
  | Pcfi_rel_offset _
  | Plabel _ -> 0
  | Pbtbl (r,tbl) ->  2 + List.length tbl
  | _ -> 1

let expand_constants () =
  let consts = Hashtbl.fold (fun bf lbl c ->
      Float64 (lbl, bf)::c)
      float_labels [] in
  let consts = Hashtbl.fold (fun bf lbl c ->
      Float32 (lbl, bf)::c)
      float32_labels consts in
  let consts = Hashtbl.fold (fun (id,ofs) lbl c ->
      Symbol (lbl,id,ofs)::c)
      symbol_labels consts in
  if consts <> [] then
    emit (Pconstants consts);
  reset_constants ()

let expand_instruction = function
  | Pflid (r1,f) ->
    let f' = camlint64_of_coqint(Floats.Float.to_bits f) in
    if vfpv3 && is_immediate_float64 f' then begin
      emit (Pflid_imm (r1,f));
      1
    end else if !literals_in_code then begin
      let lbl = label_float f in
      emit (Pflid_lbl (r1,lbl,f));
      1
    end else begin
      emit (Pflid (r1,f));
      3
    end
  | Pflis (r1,f) ->
    let f' = camlint_of_coqint(Floats.Float32.to_bits f) in
    if vfpv3 && is_immediate_float32 f' then begin
      emit (Pflis_imm (r1,f));
      1
    end else if !literals_in_code then begin
      let lbl = label_float32 f in
      emit (Pflis_lbl (r1,lbl,f));
      1
    end else begin
      let lo =  coqint_of_camlint (Int32.logand f' 0xFFFFl)
      and hi = coqint_of_camlint (Int32.shift_right_logical f' 16) in
      emit (Pmovw (IR14,lo));
      emit (Pmovt (IR14,hi));
      emit (Pfcpy_fi (r1,IR14));
      3
    end
  | Ploadsymbol(r1, id, ofs) ->
    let o = camlint_of_coqint ofs in
    if o >= -32768l && o <= 32767l && !Clflags.option_mthumb then begin
      emit (Ploadsymbol_imm (r1,id,ofs));
      2
    end else begin
      let lbl = label_symbol id ofs in
      emit (Ploadsymbol_lbl (r1,lbl,id,ofs));
      1
    end
  | inst ->
    emit inst;
    estimate_size inst

let rec expand_instructions no_fall = function
  | [] -> ()
  | i :: il ->
    let estimate = estimate_size i * 4 in
    let d = distance_to_emit_constants() - estimate in
    if d < 256 && no_fall then
      expand_constants ()
    else if d < 16 then begin
      let lbl = new_label () in
      emit (Pb lbl);
      expand_constants ();
      emit (Plabel lbl)
    end;
    let n = expand_instruction i in
    currpos := !currpos + n * 4;
    expand_instructions (no_fallthrough i) il

let expand_constants fn =
  reset_constants ();
  set_current_function fn;
  expand_instructions false fn.fn_code;
  expand_constants ();
  get_current_function ()

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

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the ARM assembly code.  *)

open Asm
open Asmexpandaux
open Asmgen
open AST
open Camlcoq
open Integers

exception Error of string

(* Useful constants and helper functions *)

let _0 = Integers.Int.zero
let _1 = Integers.Int.one
let _2 = coqint_of_camlint 2l
let _4 = coqint_of_camlint 4l
let _8 = coqint_of_camlint 8l
let _16 = coqint_of_camlint 16l

(* Emit instruction sequences that set or offset a register by a constant. *)
(* No S suffix because they are applied to SP most of the time. *)

let expand_movimm dst n =
  match Asmgen.decompose_int n with
  | [] -> assert false
  | hd::tl->
     emit (Pmov (dst,SOimm hd));
     List.iter
       (fun n -> emit (Porr (dst,dst, SOimm n))) tl

let expand_subimm dst src n =
  match Asmgen.decompose_int n with
  | [] -> assert false
  | hd::tl ->
     emit (Psub(dst,src,SOimm hd));
     List.iter (fun n -> emit (Psub (dst,dst,SOimm n))) tl

let expand_addimm dst src n =
  match Asmgen.decompose_int n with
  | [] -> assert false
  | hd::tl ->
     emit (Padd (dst,src,SOimm hd));
     List.iter (fun n -> emit (Padd (dst,dst,SOimm n))) tl

let expand_int64_arith conflict rl fn =
  if conflict then
    begin
      fn IR14;
      emit (Pmov (rl,SOreg IR14))
    end else
    fn rl


(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers.
*)

(* Handling of annotations *)

let expand_annot_val txt targ args res =
  emit (Pbuiltin (EF_annot(txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmov (dst,SOreg src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pfcpyd (dst,src))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_val")

(* Handling of memcpy *)

(* The ARM has strict alignment constraints for 2 and 4 byte accesses.
   8-byte accesses must be 4-aligned. *)

let offset_in_range ofs =
  let n = camlint_of_coqint ofs in n <= 128l && n >= -128l

let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (IR r) ->
      (r, _0)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Int.add ofs (Int.repr (Z.of_uint sz)))
      then (IR13, ofs)
      else begin expand_addimm tmp IR13 ofs; (tmp, _0) end
  | _ ->
      assert false

let expand_builtin_memcpy_small sz al src dst =
  let (tsrc, tdst) =
    if dst <> BA (IR IR2) then (IR2, IR3) else (IR3, IR2) in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  let rec copy osrc odst sz  =
    if sz >= 8 && al >= 4 && !Clflags.option_ffpu then begin
      emit (Pfldd (FR7,rsrc,osrc));
      emit (Pfstd (FR7,rdst,odst));
      copy (Int.add osrc _8) (Int.add odst _8) (sz - 8)
    end else if sz >= 4 && al >= 4 then begin
      emit (Pldr (IR14,rsrc,SOimm osrc));
      emit (Pstr (IR14,rdst,SOimm odst));
      copy (Int.add osrc _4) (Int.add odst _4) (sz - 4)
    end else if sz >= 2 && al >= 2 then begin
      emit (Pldrh (IR14,rsrc,SOimm osrc));
      emit (Pstrh (IR14,rdst,SOimm odst));
      copy (Int.add osrc _2) (Int.add odst _2) (sz - 2)
    end else if sz >= 1 then begin
      emit (Pldrb (IR14,rsrc,SOimm osrc));
      emit (Pstrb (IR14,rdst,SOimm odst));
      copy (Int.add osrc _1) (Int.add odst _1) (sz - 1)
    end in
  copy osrc odst sz

let memcpy_big_arg arg tmp =
  match arg with
  | BA (IR r) ->
      if r <> tmp then emit (Pmov(tmp, SOreg r))
  | BA_addrstack ofs ->
      expand_addimm tmp IR13 ofs
  | _ ->
      assert false

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= al);
  assert (sz mod al = 0);
  let (s, d) =
    if dst <> BA (IR IR2) then (IR2, IR3) else (IR3, IR2) in
  memcpy_big_arg src s;
  memcpy_big_arg dst d;
  let (load, store, chunksize) =
    if al >= 4 then
      (Pldr_p (IR12,s,SOimm _4), Pstr_p (IR12,d,SOimm _4) , 4)
    else if al = 2 then
       (Pldrh_p (IR12,s,SOimm _2), Pstrh_p (IR12,d,SOimm _2), 2)
    else
       (Pldrb_p (IR12,s,SOimm _1), Pstrb_p (IR12,d,SOimm _1), 1) in
  expand_movimm IR14 (coqint_of_camlint (Int32.of_int (sz / chunksize)));
  let lbl = new_label () in
  emit (Plabel lbl);
  emit load;
  emit (Psubs (IR14,IR14,SOimm _1));
  emit store;
  emit (Pbne lbl)

let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if sz <= 32
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | Mint8unsigned, BR(IR res) ->
     emit (Pldrb (res, base, SOimm ofs))
  | Mint8signed, BR(IR res) ->
     emit (Pldrsb (res, base, SOimm ofs))
  | Mint16unsigned, BR(IR res) ->
     emit (Pldrh (res, base, SOimm ofs))
  | Mint16signed, BR(IR res) ->
     emit (Pldrsh (res, base, SOimm ofs))
  | Mint32, BR(IR res) ->
     emit (Pldr (res, base, SOimm ofs))
  | Mint64, BR_splitlong(BR(IR res1), BR(IR res2)) ->
     let ofs' = Int.add ofs _4 in
     if base <> res2 then begin
	 emit (Pldr (res2, base, SOimm ofs));
	 emit (Pldr (res1, base, SOimm ofs'))
       end else begin
	 emit (Pldr (res1, base, SOimm ofs'));
	 emit (Pldr (res2, base, SOimm ofs))
       end
  | Mfloat32, BR(FR res) ->
     emit (Pflds (res, base, ofs))
  | Mfloat64, BR(FR res) ->
     emit (Pfldd (res, base, ofs))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [BA(IR addr)] ->
      expand_builtin_vload_common chunk addr _0 res
  | [BA_addrstack ofs] ->
      if offset_in_range (Int.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vload_common chunk IR13 ofs res
      else begin
        expand_addimm IR14 IR13 ofs;
        expand_builtin_vload_common chunk IR14 _0 res
      end
  | [BA_addrglobal(id, ofs)] ->
      emit (Ploadsymbol (IR14,id,ofs));
      expand_builtin_vload_common chunk IR14 _0 res
  | _ ->
      assert false

let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) ->
     emit (Pstrb (src, base, SOimm ofs))
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Pstrh (src, base, SOimm ofs))
  | Mint32, BA(IR src) ->
     emit (Pstr (src, base, SOimm ofs))
  | Mint64, BA_splitlong(BA(IR src1), BA(IR src2)) ->
     let ofs' = Int.add ofs _4 in
     emit (Pstr (src2, base, SOimm ofs));
     emit (Pstr (src1, base, SOimm ofs'))
  | Mfloat32, BA(FR src) ->
     emit (Pfsts (src, base, ofs))
  | Mfloat64, BA(FR src) ->
     emit (Pfstd (src, base, ofs))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA(IR addr); src] ->
      expand_builtin_vstore_common chunk addr _0 src
  | [BA_addrstack ofs; src] ->
      if offset_in_range (Int.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vstore_common chunk IR13 ofs src
      else begin
        expand_addimm IR14 IR13 ofs;
        expand_builtin_vstore_common chunk IR14 _0 src
      end
  | [BA_addrglobal(id, ofs); src] ->
      emit (Ploadsymbol (IR14,id,ofs));
      expand_builtin_vstore_common chunk IR14 _0 src
  | _ ->
      assert false

(* Handling of varargs *)

let align n a = (n + a - 1) land (-a)

let rec next_arg_location ir ofs = function
  | [] ->
     Int32.of_int (ir * 4 + ofs)
  | (Tint | Tsingle | Tany32) :: l ->
     if ir < 4
     then next_arg_location (ir + 1) ofs l
     else next_arg_location ir (ofs + 4) l
  | (Tfloat | Tlong | Tany64) :: l ->
     if ir < 3
     then next_arg_location (align ir 2 + 2) ofs l
     else next_arg_location ir (align ofs 8 + 8) l

let expand_builtin_va_start r =
  if not !current_function.fn_sig.sig_cc.cc_vararg then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let ofs =
    Int32.add
      (next_arg_location 0 0 !current_function.fn_sig.sig_args)
      !PrintAsmaux.current_function_stacksize in
  expand_addimm IR14 IR13 (coqint_of_camlint ofs);
  emit (Pstr (IR14,r,SOimm _0))


(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Integer arithmetic *)
  | ("__builtin_bswap" | "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     emit (Prev (res, a1))
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     emit (Prev16 (res, a1))
  | "__builtin_clz", [BA(IR a1)], BR(IR res) ->
     emit (Pclz (res, a1))
  (* Float arithmetic *)
  | "__builtin_fabs",  [BA(FR a1)], BR(FR res) ->
     emit (Pfabsd (res,a1))
  | "__builtin_fsqrt", [BA(FR a1)], BR(FR res) ->
     emit (Pfsqrt (res,a1))
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [BA_splitlong(BA(IR ah), BA(IR al))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
      expand_int64_arith (rl = ah ) rl (fun rl ->
        emit (Prsbs (rl,al,SOimm _0));
        (* No "rsc" instruction in Thumb2.  Emulate based on
           rsc a, b, #0 == a <- AddWithCarry(~b, 0, carry)
           == mvn a, b; adc a, a, #0 *)
        if !Clflags.option_mthumb then begin
	  emit (Pmvn (rh,SOreg ah));
	  emit (Padc (rh,rh,SOimm _0))
        end else begin
	  emit (Prsc (rh,ah,SOimm _0))
        end)
  | "__builtin_addl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = ah || rl = bh) rl
			(fun rl ->
			 emit (Padds (rl,al,SOreg bl));
			 emit (Padc (rh,ah,SOreg bh)))
  | "__builtin_subl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = ah || rl = bh) rl
		       (fun rl ->
			emit (Psubs (rl,al,SOreg bl));
			emit (Psbc (rh,ah,SOreg bh)))
  | "__builtin_mull", [BA(IR a); BA(IR b)],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     emit (Pumull (rl,rh,a,b))
  (* Memory accesses *)
  | "__builtin_read16_reversed", [BA(IR a1)], BR(IR res) ->
     emit (Pldrh (res,a1,SOimm _0));
     emit (Prev16 (res, res));
  | "__builtin_read32_reversed", [BA(IR a1)], BR(IR res) ->
     emit (Pldr (res,a1,SOimm _0));
     emit (Prev (res, res));
  | "__builtin_write16_reversed", [BA(IR a1); BA(IR a2)], _ ->
     emit (Prev16 (IR14, a2));
     emit (Pstrh (IR14, a1, SOimm _0))
  | "__builtin_write32_reversed", [BA(IR a1); BA(IR a2)], _ ->
     emit (Prev (IR14, a2));
     emit (Pstr (IR14, a1, SOimm _0))
  (* Synchronization *)
  | "__builtin_membar",[], _ ->
     ()
  | "__builtin_dmb", [], _ ->
     emit Pdmb
  | "__builtin_dsb", [], _ ->
     emit Pdsb
  | "__builtin_isb", [], _ ->
     emit Pisb
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     expand_builtin_va_start a
  (* Catch-all *)
  | _ ->
      raise (Error ("unrecognized builtin " ^ name))

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs) ->
     emit (Pmov (IR12,SOreg IR13));
     if (!current_function).fn_sig.sig_cc.cc_vararg then begin
	 emit (Ppush [IR0;IR1;IR2;IR3]);
	 emit (Pcfi_adjust _16);
       end;
     expand_subimm IR13 IR13 sz;
     emit (Pcfi_adjust sz);
     emit (Pstr (IR12,IR13,SOimm ofs));
     PrintAsmaux.current_function_stacksize := camlint_of_coqint sz
  | Pfreeframe (sz, ofs) ->
     let sz =
       if (!current_function).fn_sig.sig_cc.cc_vararg
       then coqint_of_camlint (Int32.add 16l (camlint_of_coqint sz))
       else sz in
     if Asmgen.is_immed_arith sz
     then emit (Padd (IR13,IR13,SOimm sz))
     else emit (Pldr (IR13,IR13,SOimm ofs))
  | Pbuiltin (ef,args,res) ->
     begin match ef with
	   | EF_builtin (name,sg) ->
	      expand_builtin_inline (camlstring_of_coqstring name) args res
	   | EF_vload chunk ->
	      expand_builtin_vload chunk args res
	   | EF_vstore chunk ->
	      expand_builtin_vstore chunk args
	   | EF_annot_val (txt,targ) ->
	      expand_annot_val txt targ args res
	   | EF_memcpy(sz, al) ->
	      expand_builtin_memcpy (Int32.to_int (camlint_of_coqint sz))
		(Int32.to_int (camlint_of_coqint al)) args
	   | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
              emit instr
	   | _ ->
              assert false
     end
  | _ ->
     emit instr

let int_reg_to_dwarf = function
   | IR0 -> 0  | IR1 -> 1  | IR2 -> 2  | IR3 -> 3
   | IR4 -> 4  | IR5 -> 5  | IR6 -> 6  | IR7 -> 7
   | IR8 -> 8  | IR9 -> 9  | IR10 -> 10 | IR11 -> 11
   | IR12 -> 12 | IR13 -> 13 | IR14 -> 14

let float_reg_to_dwarf = function
   | FR0 -> 64  | FR1 -> 65  | FR2 -> 66  | FR3 -> 67
   | FR4 -> 68  | FR5 -> 69  | FR6 -> 70  | FR7 -> 71
   | FR8 -> 72  | FR9 -> 73  | FR10 -> 74 | FR11 -> 75
   | FR12 -> 76 | FR13 -> 77 | FR14 -> 78 | FR15 -> 79

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | FR r -> float_reg_to_dwarf r
   | _ -> assert false


let expand_function id fn =
  try
    set_current_function fn;
    if !Clflags.option_g then
      expand_debug id 13 preg_to_dwarf expand_instruction fn.fn_code
    else
      List.iter expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with Error s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_ident_program expand_fundef p

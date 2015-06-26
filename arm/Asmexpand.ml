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

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the ARM assembly code.  Currently not everything done, this
   expansion is performed on the fly in PrintAsm. *)

open Asm
open Asmexpandaux
open Asmgen
open AST
open Camlcoq
open Integers

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
  emit (Pannot (EF_annot(txt,[targ]), List.map (fun r -> AA_base r) args));
  match args, res with
  | [IR src], [IR dst] ->
     if dst <> src then emit (Pmov (dst,SOreg src))
  | [FR src], [FR dst] ->
     if dst <> src then emit (Pfcpyd (dst,src))
  | _, _ -> assert false


(* Handling of memcpy *)

(* The ARM has strict alignment constraints for 2 and 4 byte accesses.
   8-byte accesses must be 4-aligned. *)

let expand_builtin_memcpy_small sz al src dst =
  let rec copy ofs sz  =
    if sz >= 8 && al >= 4 && !Clflags.option_ffpu then begin
	emit (Pfldd (FR7,src,ofs));
	emit (Pfstd (FR7,dst,ofs));
	copy (Int.add ofs _8) (sz - 8)
      end else if sz >= 4 && al >= 4 then begin
	emit (Pldr (IR14,src,SOimm ofs));
	emit (Pstr (IR14,dst,SOimm ofs));
	copy (Int.add ofs _4) (sz - 4)
      end else if sz >= 2 && al >= 2 then begin
	emit (Pldrh (IR14,src,SOimm ofs));
	emit (Pstrh (IR14,dst,SOimm ofs));
	copy (Int.add ofs _2) (sz - 2)
      end else if sz >= 1 then begin
	emit (Pldrb (IR14,src,SOimm ofs));
	emit (Pstrb (IR14,dst,SOimm ofs));
	copy (Int.add ofs _1) (sz - 1)
      end else
      () in
  copy _0 sz

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= al);
  assert (sz mod al = 0);
  assert (src = IR2);
  assert (dst = IR3);
  let (load, store, chunksize) =
    if al >= 4 then (Pldr (IR12,src,SOimm _4), Pstr (IR12,dst,SOimm _4) , 4)
    else if al = 2 then (Pldrh (IR12,src,SOimm _2), Pstrh (IR12,dst,SOimm _2), 2)
    else (Pldrb (IR12,src,SOimm _1), Pstrb (IR12,dst,SOimm _1), 1) in
  expand_movimm IR14 (coqint_of_camlint (Int32.of_int (sz / chunksize)));
  let lbl = new_label () in
  emit (Plabel lbl);
  emit load;
  emit (Psubs (IR14,IR14,SOimm _1));
  emit store;
  emit (Pbne lbl)

let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [IR d; IR s] -> (d, s) | _ -> assert false in
  if sz <= 32
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk args res =
  match chunk, args, res with
  | Mint8unsigned, [IR addr], [IR res] ->
     emit (Pldrb (res, addr,SOimm _0))
  | Mint8signed, [IR addr], [IR res] ->
     emit (Pldrsb (res, addr,SOimm _0))
  | Mint16unsigned, [IR addr], [IR res] ->
     emit (Pldrh (res, addr, SOimm _0))
  | Mint16signed, [IR addr], [IR res] ->
     emit (Pldrsh (res, addr, SOimm _0))
  | Mint32, [IR addr], [IR res] ->
     emit (Pldr (res,addr, SOimm _0))
  | Mint64, [IR addr], [IR res1; IR res2] ->
     if addr <> res2 then begin
	 emit (Pldr (res2, addr, SOimm _0));
	 emit (Pldr (res1, addr, SOimm _4))
       end else begin
	 emit (Pldr (res1,addr, SOimm _4));
	 emit (Pldr (res2,addr, SOimm _0))
       end
  | Mfloat32, [IR addr], [FR res] ->
     emit (Pflds (res, addr, _0))
  | Mfloat64, [IR addr], [FR res] ->
     emit (Pfldd (res,addr, _0))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  expand_builtin_vload_common chunk args res

let expand_builtin_vload_global chunk id ofs args res =
  emit (Ploadsymbol (IR14,id,ofs));
  expand_builtin_vload_common chunk args res

let expand_builtin_vstore_common chunk args =
  match chunk, args with
  | (Mint8signed | Mint8unsigned), [IR  addr; IR src] ->
     emit (Pstrb (src,addr, SOimm _0))
  | (Mint16signed | Mint16unsigned), [IR  addr; IR src] ->
     emit (Pstrh (src,addr, SOimm _0))
  | Mint32, [IR  addr; IR src] ->
     emit (Pstr (src,addr, SOimm _0))
  | Mint64, [IR  addr; IR src1; IR src2] ->
     emit (Pstr (src2,addr,SOimm _0));
     emit (Pstr (src1,addr,SOimm _0))
  | Mfloat32, [IR  addr; FR src] ->
     emit (Pfstd (src,addr,_0))
  | Mfloat64, [IR  addr; FR src] ->
     emit (Pfsts (src,addr,_0));
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  expand_builtin_vstore_common chunk args

let expand_builtin_vstore_global chunk id ofs args =
  emit (Ploadsymbol (IR14,id,ofs));
  expand_builtin_vstore_common chunk args

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
  | ("__builtin_bswap" | "__builtin_bswap32"), [IR a1], [IR res] ->
     emit (Prev (IR res,IR a1))
  | "__builtin_bswap16", [IR a1], [IR res] ->
     emit (Prev16 (IR res,IR a1))
  | "__builtin_clz", [IR a1], [IR res] ->
     emit (Pclz (IR res, IR a1))
  (* Float arithmetic *)
  | "__builtin_fabs",  [FR a1], [FR res] ->
     emit (Pfabsd (res,a1))
  | "__builtin_fsqrt", [FR a1], [FR res] ->
     emit (Pfsqrt (res,a1))
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [IR ah;IR al], [IR rh; IR rl] ->
     emit (Prsbs (rl,al,SOimm _0));
     if !Clflags.option_mthumb then begin
	 emit (Pmvn (rh,SOreg ah));
	 emit (Padc (rh,rh,SOimm _0))
       end else
       begin
	 emit (Prsc (rh,ah,SOimm _0))
       end
  | "__builtin_addl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
     expand_int64_arith (rl = ah || rl = bh) rl
			(fun rl ->
			 emit (Padds (rl,al,SOreg bl));
			 emit (Padc (rh,ah,SOreg bh)))
  | "__builtin_subl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
     expand_int64_arith (rl = ah || rl = bh) rl
		       (fun rl ->
			emit (Psubs (rl,al,SOreg bl));
			emit (Psbc (rh,ah,SOreg bh)))
  | "__builtin_mull", [IR a; IR b], [IR rh; IR rl] ->
     emit (Pumull (rl,rh,a,b))
  (* Memory accesses *)
  | "__builtin_read16_reversed", [IR a1], [IR res] ->
     emit (Pldrh (res,a1,SOimm _0));
     emit (Prev16 (IR res,IR res));
  | "__builtin_read32_reversed", [IR a1], [IR res] ->
     emit (Pldr (res,a1,SOimm _0));
     emit (Prev (IR res,IR res));
  | "__builtin_write16_reverse", [IR a1; IR a2], _ ->
     emit (Prev16 (IR IR14, IR a2));
     emit (Pstrh (IR14, a1, SOimm _0))
  | "__builtin_write32_reverse", [IR a1; IR a2], _ ->
     emit (Prev (IR IR14, IR a2));
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
  | "__builtin_va_start", [IR a], _ ->
     expand_builtin_va_start a
  (* Catch-all *)
  | _ ->
      invalid_arg ("unrecognized builtin " ^ name)

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
     emit (Pstr (IR12,IR13,SOimm ofs))
  | Pfreeframe (sz, ofs) ->
     let sz =
       if (!current_function).fn_sig.sig_cc.cc_vararg
       then coqint_of_camlint (Int32.add 16l (camlint_of_coqint sz))
       else sz in
     if Asmgen.is_immed_arith sz
     then emit (Padd (IR13,IR13,SOimm sz))
     else emit (Pldr (IR13,IR13,SOimm sz))
  | Pbuiltin (ef,args,res) ->
     begin match ef with
	   | EF_builtin (name,sg) ->
	      expand_builtin_inline (extern_atom name) args res
	   | EF_vload chunk ->
	      expand_builtin_vload chunk args res
	   | EF_vstore chunk ->
	      expand_builtin_vstore chunk args
	   | EF_vload_global(chunk, id, ofs) ->
	      expand_builtin_vload_global chunk id ofs args res
	   | EF_vstore_global(chunk, id, ofs) ->
	      expand_builtin_vstore_global chunk id ofs args
	   | EF_annot_val (txt,targ) ->
	      expand_annot_val txt targ args res
	   | EF_memcpy(sz, al) ->
	      expand_builtin_memcpy (Int32.to_int (camlint_of_coqint sz))
		(Int32.to_int (camlint_of_coqint al)) args
	   | EF_inline_asm(txt, sg, clob) ->
              emit instr
	   | _ -> assert false
     end
  | _ ->
     emit instr

let expand_function fn =
  set_current_function fn;
  List.iter expand_instruction fn.fn_code;
  get_current_function ()

let expand_fundef = function
  | Internal f -> Internal (expand_function f)
  | External ef -> External ef

let expand_program (p: Asm.program) : Asm.program =
  AST.transform_program expand_fundef p

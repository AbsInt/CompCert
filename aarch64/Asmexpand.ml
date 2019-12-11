(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the AArch64 assembly code. *)

open Asm
open Asmexpandaux
open AST
open Camlcoq
module Ptrofs = Integers.Ptrofs

exception Error of string

(* Useful constants *)

let _0  = Z.zero
let _1  = Z.one
let _2  = Z.of_sint 2
let _4  = Z.of_sint 4
let _8  = Z.of_sint 8
let _16  = Z.of_sint 16
let _m1 = Z.of_sint (-1)

(* Emit instruction sequences that set or offset a register by a constant. *)

let expand_loadimm32 (dst: ireg) n =
  List.iter emit (Asmgen.loadimm32 dst n [])

let expand_addimm64 (dst: iregsp) (src: iregsp) n =
  List.iter emit (Asmgen.addimm64 dst src n [])

let expand_storeptr (src: ireg) (base: iregsp) ofs =
  List.iter emit (Asmgen.storeptr src base ofs [])

(* Handling of varargs *)

(* Determine the number of int registers, FP registers, and stack locations
   used to pass the fixed parameters. *)

let rec next_arg_locations ir fr stk = function
  | [] ->
      (ir, fr, stk)
  | (Tint | Tlong | Tany32 | Tany64) :: l ->
      if ir < 8
      then next_arg_locations (ir + 1) fr stk l
      else next_arg_locations ir fr (stk + 8) l
  | (Tfloat | Tsingle) :: l ->
      if fr < 8
      then next_arg_locations ir (fr + 1) stk l
      else next_arg_locations ir fr (stk + 8) l

(* Allocate memory on the stack and use it to save the registers
   used for parameter passing.  As an optimization, do not save
   the registers used to pass the fixed parameters. *)

let int_param_regs = [| X0; X1; X2; X3; X4; X5; X6; X7 |]
let float_param_regs = [| D0; D1; D2; D3; D4; D5; D6; D7 |]
let size_save_register_area = 8*8 + 8*16

let save_parameter_registers ir fr =
  emit (Psubimm(X, XSP, XSP, Z.of_uint size_save_register_area));
  let i = ref ir in
  while !i < 8 do
    let pos = 8*16 + !i*8 in
    if !i land 1 = 0 then begin
      emit (Pstp(int_param_regs.(!i), int_param_regs.(!i + 1),
                 ADimm(XSP, Z.of_uint pos)));
      i := !i + 2
    end else begin
      emit (Pstrx(int_param_regs.(!i), ADimm(XSP, Z.of_uint pos)));
      i := !i + 1
    end
  done;
  for i = fr to 7 do
    let pos = i*16 in
    emit (Pstrd(float_param_regs.(i), ADimm(XSP, Z.of_uint pos)))
  done

(* Initialize a va_list as per va_start.
   Register r points to the following struct:

   typedef struct __va_list {
     void *__stack;             // next stack parameter
     void *__gr_top;            // top of the save area for int regs
     void *__vr_top;            // top of the save area for float regs
     int__gr_offs;              // offset from gr_top to next int reg
     int__vr_offs;              // offset from gr_top to next FP reg
   }
*)

let current_function_stacksize = ref 0L

let expand_builtin_va_start r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let (ir, fr, stk) =
    next_arg_locations 0 0 0 (get_current_function_args ()) in
  let stack_ofs = Int64.(add !current_function_stacksize (of_int stk))
  and gr_top_ofs = !current_function_stacksize
  and vr_top_ofs = Int64.(sub !current_function_stacksize 64L)
  and gr_offs = - ((8 - ir) * 8)
  and vr_offs = - ((8 - fr) * 16) in
  (* va->__stack = sp + stack_ofs *)
  expand_addimm64 (RR1 X16) XSP (coqint_of_camlint64 stack_ofs);
  emit (Pstrx(X16, ADimm(RR1 r, coqint_of_camlint64 0L)));
  (* va->__gr_top = sp + gr_top_ofs *)
  if gr_top_ofs <> stack_ofs then
    expand_addimm64 (RR1 X16) XSP (coqint_of_camlint64 gr_top_ofs);
  emit (Pstrx(X16, ADimm(RR1 r, coqint_of_camlint64 8L)));
  (* va->__vr_top = sp + vr_top_ofs *)
  expand_addimm64 (RR1 X16) XSP (coqint_of_camlint64 vr_top_ofs);
  emit (Pstrx(X16, ADimm(RR1 r, coqint_of_camlint64 16L)));
  (* va->__gr_offs = gr_offs *)
  expand_loadimm32 X16 (coqint_of_camlint (Int32.of_int gr_offs));
  emit (Pstrw(X16, ADimm(RR1 r, coqint_of_camlint64 24L)));
  (* va->__vr_offs = vr_offs *)
  expand_loadimm32 X16 (coqint_of_camlint (Int32.of_int vr_offs));
  emit (Pstrw(X16, ADimm(RR1 r, coqint_of_camlint64 28L)))

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmov (RR1 dst, RR1 src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pfmov (dst, src))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_val")

(* Handling of memcpy *)

(* We assume unaligned memory accesses are efficient.  Hence we use
   memory accesses as wide as we can, up to 16 bytes.
   Temporary registers used: x15 x16 x17 x29 x30. *)

let offset_in_range ofs =
  (* The 512 upper bound comes from ldp/stp.  Single-register load/store
     instructions support bigger offsets. *)
  let ofs = Z.to_int64 ofs in 0L <= ofs && ofs < 512L
  
let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (IR r) ->
      (RR1 r, _0)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Ptrofs.add ofs (Ptrofs.repr (Z.of_uint sz)))
      then (XSP, ofs)
      else begin expand_addimm64 (RR1 tmp) XSP ofs; (RR1 tmp, _0) end
  | _ ->
      assert false

let expand_builtin_memcpy_small sz al src dst =
  let (tsrc, tdst) =
    if dst <> BA (IR X17) then (X17, X29) else (X29, X17) in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  let rec copy osrc odst sz =
    if sz >= 16 then begin
      emit (Pldp(X16, X30, ADimm(rsrc, osrc)));
      emit (Pstp(X16, X30, ADimm(rdst, odst)));
      copy (Ptrofs.add osrc _16) (Ptrofs.add odst _16) (sz - 16)
    end
    else if sz >= 8 then begin
      emit (Pldrx(X16, ADimm(rsrc, osrc)));
      emit (Pstrx(X16, ADimm(rdst, odst)));
      copy (Ptrofs.add osrc _8) (Ptrofs.add odst _8) (sz - 8)
    end
    else if sz >= 4 then begin
      emit (Pldrw(X16, ADimm(rsrc, osrc)));
      emit (Pstrw(X16, ADimm(rdst, odst)));
      copy (Ptrofs.add osrc _4) (Ptrofs.add odst _4) (sz - 4)
    end
    else if sz >= 2 then begin
      emit (Pldrh(W, X16, ADimm(rsrc, osrc)));
      emit (Pstrh(X16, ADimm(rdst, odst)));
      copy (Ptrofs.add osrc _2) (Ptrofs.add odst _2) (sz - 2)
    end
    else if sz >= 1 then begin
      emit (Pldrb(W, X16, ADimm(rsrc, osrc)));
      emit (Pstrb(X16, ADimm(rdst, odst)));
      copy (Ptrofs.add osrc _1) (Ptrofs.add odst _1) (sz - 1)
    end
  in copy osrc odst sz

let memcpy_big_arg arg tmp =
  match arg with
  | BA (IR r) -> emit (Pmov(RR1 tmp, RR1 r))
  | BA_addrstack ofs -> expand_addimm64 (RR1 tmp) XSP ofs
  | _ -> assert false

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= 16);
  memcpy_big_arg src X30;
  memcpy_big_arg dst X29;
  let lbl = new_label () in
  expand_loadimm32 X15 (Z.of_uint (sz / 16));
  emit (Plabel lbl);
  emit (Pldp(X16, X17, ADpostincr(RR1 X30, _16)));
  emit (Pstp(X16, X17, ADpostincr(RR1 X29, _16)));
  emit (Psubimm(W, RR1 X15, RR1 X15, _1));
  emit (Pcbnz(W, X15, lbl));
  if sz mod 16 >= 8 then begin
    emit (Pldrx(X16, ADpostincr(RR1 X30, _8)));
    emit (Pstrx(X16, ADpostincr(RR1 X29, _8)))
  end;
  if sz mod 8 >= 4 then begin
    emit (Pldrw(X16, ADpostincr(RR1 X30, _4)));
    emit (Pstrw(X16, ADpostincr(RR1 X29, _4)))
  end;
  if sz mod 4 >= 2 then begin
    emit (Pldrh(W, X16, ADpostincr(RR1 X30, _2)));
    emit (Pstrh(X16, ADpostincr(RR1 X29, _2)))
  end;
  if sz mod 2 >= 1 then begin
    emit (Pldrb(W, X16, ADpostincr(RR1 X30, _1)));
    emit (Pstrb(X16, ADpostincr(RR1 X29, _1)))
  end

let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if sz < 64
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk base ofs res =
  let addr = ADimm(base, ofs) in
  match chunk, res with
  | Mint8unsigned, BR(IR res) ->
     emit (Pldrb(W, res, addr))
  | Mint8signed, BR(IR res) ->
     emit (Pldrsb(W, res, addr))
  | Mint16unsigned, BR(IR res) ->
     emit (Pldrh(W, res, addr))
  | Mint16signed, BR(IR res) ->
     emit (Pldrsh(W, res, addr))
  | Mint32, BR(IR res) ->
     emit (Pldrw(res, addr))
  | Mint64, BR(IR res) ->
     emit (Pldrx(res, addr))
  | Mfloat32, BR(FR res) ->
     emit (Pldrs(res, addr))
  | Mfloat64, BR(FR res) ->
     emit (Pldrd(res, addr))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [BA(IR addr)] ->
      expand_builtin_vload_common chunk (RR1 addr) _0 res
  | [BA_addrstack ofs] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vload_common chunk XSP ofs res
      else begin
        expand_addimm64 (RR1 X16) XSP ofs; (* X16 <- SP + ofs *)
        expand_builtin_vload_common chunk (RR1 X16) _0 res
      end
  | [BA_addptr(BA(IR addr), BA_long ofs)] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vload_common chunk (RR1 addr) ofs res
      else begin
        expand_addimm64 (RR1 X16) (RR1 addr) ofs; (* X16 <- addr + ofs *)
        expand_builtin_vload_common chunk (RR1 X16) _0 res
      end
  | _ ->
      assert false

let expand_builtin_vstore_common chunk base ofs src =
  let addr = ADimm(base, ofs) in
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) ->
     emit (Pstrb(src, addr))
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Pstrh(src, addr))
  | Mint32, BA(IR src) ->
     emit (Pstrw(src, addr))
  | Mint64, BA(IR src) ->
     emit (Pstrx(src, addr))
  | Mfloat32, BA(FR src) ->
     emit (Pstrs(src, addr))
  | Mfloat64, BA(FR src) ->
     emit (Pstrd(src, addr))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA(IR addr); src] ->
      expand_builtin_vstore_common chunk (RR1 addr) _0 src
  | [BA_addrstack ofs; src] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vstore_common chunk XSP ofs src
      else begin
        expand_addimm64 (RR1 X16) XSP ofs; (* X16 <- SP + ofs *)
        expand_builtin_vstore_common chunk (RR1 X16) _0 src
      end
  | [BA_addptr(BA(IR addr), BA_long ofs); src] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vstore_common chunk (RR1 addr) ofs src
      else begin
        expand_addimm64 (RR1 X16) (RR1 addr) ofs; (* X16 <- addr + ofs *)
        expand_builtin_vstore_common chunk (RR1 X16) _0 src
      end
  | _ ->
      assert false

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
     ()
  | "__builtin_nop", [], _ ->
     emit Pnop
  (* Byte swap *)
  | ("__builtin_bswap" | "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     emit (Prev(W, res, a1))
  | "__builtin_bswap64", [BA(IR a1)], BR(IR res) ->
     emit (Prev(X, res, a1))
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     emit (Prev16(W, res, a1));
     emit (Pandimm(W, res, RR0 res, Z.of_uint 0xFFFF))
  (* Count leading zeros and leading sign bits *)
  | "__builtin_clz",  [BA(IR a1)], BR(IR res) ->
     emit (Pclz(W, res, a1))
  | ("__builtin_clzl" | "__builtin_clzll"),  [BA(IR a1)], BR(IR res) ->
     emit (Pclz(X, res, a1)) 
  | "__builtin_cls",  [BA(IR a1)], BR(IR res) ->
     emit (Pcls(W, res, a1))
  | ("__builtin_clsl" | "__builtin_clsll"),  [BA(IR a1)], BR(IR res) ->
     emit (Pcls(X, res, a1))
 (* Float arithmetic *)
  | "__builtin_fabs",  [BA(FR a1)], BR(FR res) ->
     emit (Pfabs(D, res, a1))
  | "__builtin_fsqrt",  [BA(FR a1)], BR(FR res) ->
     emit (Pfsqrt(D, res, a1))
  | "__builtin_fmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmadd(D, res, a1, a2, a3))
  | "__builtin_fmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmsub(D, res, a1, a2, a3))
  | "__builtin_fnmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmadd(D, res, a1, a2, a3))
  | "__builtin_fnmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmsub(D, res, a1, a2, a3))
  (* Vararg *)
  | "__builtin_va_start", [BA(IR a)], _ ->
      expand_builtin_va_start a
  (* Catch-all *)
  | _ ->
     raise (Error ("unrecognized builtin " ^ name))

(* Expansion of instructions *)

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs) ->
      emit (Pmov (RR1 X29, XSP));
      if is_current_function_variadic() then begin
        let (ir, fr, _) =
          next_arg_locations 0 0 0 (get_current_function_args ()) in
        save_parameter_registers ir fr;
        current_function_stacksize :=
          Int64.(add (Z.to_int64 sz) (of_int size_save_register_area))
      end else begin
        current_function_stacksize := Z.to_int64 sz
      end;
      expand_addimm64 XSP XSP (Ptrofs.repr (Z.neg sz));
      expand_storeptr X29 XSP ofs
  | Pfreeframe (sz, ofs) ->
      expand_addimm64 XSP XSP (coqint_of_camlint64 !current_function_stacksize)
  | Pcvtx2w rd ->
      (* no code generated, the upper 32 bits of rd will be ignored *)
      ()
  | Pbuiltin (ef,args,res) ->
     begin match ef with
     | EF_builtin (name,sg) ->
        expand_builtin_inline (camlstring_of_coqstring name) args res
     | EF_vload chunk ->
        expand_builtin_vload chunk args res
     | EF_vstore chunk ->
        expand_builtin_vstore chunk args
     | EF_annot_val (kind,txt,targ) ->
        expand_annot_val kind txt targ args res
     | EF_memcpy(sz, al) ->
        expand_builtin_memcpy (Z.to_int sz) (Z.to_int al) args
     | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit instr
     | _ ->
        assert false
     end
  | _ ->
     emit instr

let int_reg_to_dwarf = function
  | X0 -> 0 | X1 -> 1 | X2 -> 2 | X3 -> 3 | X4 -> 4
  | X5 -> 5 | X6 -> 6 | X7 -> 7 | X8 -> 8 | X9 -> 9
  | X10 -> 10 | X11 -> 11 | X12 -> 12 | X13 -> 13 | X14 -> 14
  | X15 -> 15 | X16 -> 16 | X17 -> 17 | X18 -> 18 | X19 -> 19
  | X20 -> 20 | X21 -> 21 | X22 -> 22 | X23 -> 23 | X24 -> 24
  | X25 -> 25 | X26 -> 26 | X27 -> 27 | X28 -> 28 | X29 -> 29
  | X30 -> 30

let float_reg_to_dwarf = function
  | D0 -> 64 | D1 -> 65 | D2 -> 66 | D3 -> 67 | D4 -> 68
  | D5 -> 69 | D6 -> 70 | D7 -> 71 | D8 -> 72 | D9 -> 73
  | D10 -> 74 | D11 -> 75 | D12 -> 76 | D13 -> 77 | D14 -> 78
  | D15 -> 79 | D16 -> 80 | D17 -> 81 | D18 -> 82 | D19 -> 83
  | D20 -> 84 | D21 -> 85 | D22 -> 86 | D23 -> 87 | D24 -> 88
  | D25 -> 89 | D26 -> 90 | D27 -> 91 | D28 -> 92 | D29 -> 93
  | D30 -> 94 | D31 -> 95

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | FR r -> float_reg_to_dwarf r
   | SP -> 31
   | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    expand id (* sp= *) 31 preg_to_dwarf expand_instruction fn.fn_code;
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
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p

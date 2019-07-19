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
   of the IA32 assembly code.  *)

open Asm
open Asmexpandaux
open AST
open Camlcoq
open Datatypes

exception Error of string

(* Useful constants and helper functions *)

let _0 = Integers.Int.zero
let _1 = Integers.Int.one
let _2 = coqint_of_camlint 2l
let _4 = coqint_of_camlint 4l
let _8 = coqint_of_camlint 8l

let _0z = Z.zero
let _1z = Z.one
let _2z = Z.of_sint 2
let _4z = Z.of_sint 4
let _8z = Z.of_sint 8
let _16z = Z.of_sint 16

let stack_alignment () = 16

(* Pseudo instructions for 32/64 bit compatibility *)

let _Plea (r, addr) =
  if Archi.ptr64 then Pleaq (r, addr) else Pleal (r, addr)

(* SP adjustment to allocate or free a stack frame *)

let align n a =
  if n >= 0 then (n + a - 1) land (-a) else n land (-a)

let sp_adjustment_32 sz =
  let sz = Z.to_int sz in
  (* Preserve proper alignment of the stack *)
  let sz = align sz (stack_alignment ()) in
  (* The top 4 bytes have already been allocated by the "call" instruction. *)
  sz - 4

let sp_adjustment_64 sz =
  let sz = Z.to_int sz in
  if is_current_function_variadic() then begin
    (* If variadic, add room for register save area, which must be 16-aligned *)
    let ofs = align (sz - 8) 16 in
    let sz = ofs + 176 (* save area *) + 8 (* return address *) in
    (* Preserve proper alignment of the stack *)
    let sz = align sz 16 in
    (* The top 8 bytes have already been allocated by the "call" instruction. *)
    (sz - 8, ofs)
  end else begin
    (* Preserve proper alignment of the stack *)
    let sz = align sz 16 in
    (* The top 8 bytes have already been allocated by the "call" instruction. *)
    (sz - 8, -1)
  end

(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
   locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
   registers; preserve all registers except ECX, EDX, XMM6 and XMM7. *)

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmov_rr (dst,src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pmovsd_ff (dst,src))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_intval")

(* Operations on addressing modes *)

let offset_addressing (Addrmode(base, ofs, cst)) delta =
  Addrmode(base, ofs,
           match cst with
           | Coq_inl n -> Coq_inl(Z.add n delta)
           | Coq_inr(id, n) -> Coq_inr(id, Integers.Ptrofs.add n delta))

let linear_addr reg ofs = Addrmode(Some reg, None, Coq_inl ofs)
let global_addr id ofs = Addrmode(None, None, Coq_inr(id, ofs))

(* Translate a builtin argument into an addressing mode *)

let addressing_of_builtin_arg = function
  | BA (IR r) -> linear_addr r Z.zero
  | BA_addrstack ofs -> linear_addr RSP (Integers.Ptrofs.unsigned ofs)
  | BA_addrglobal(id, ofs) -> global_addr id ofs
  | BA_addptr(BA (IR r), BA_int n) -> linear_addr r (Integers.Int.signed n)
  | BA_addptr(BA (IR r), BA_long n) -> linear_addr r (Integers.Int64.signed n)
  | _ -> assert false

(* Handling of memcpy *)

(* Unaligned memory accesses are quite fast on IA32, so use large
   memory accesses regardless of alignment. *)

let expand_builtin_memcpy_small sz al src dst =
  let rec copy src dst sz =
    if sz >= 8 && Archi.ptr64 then begin
	emit (Pmovq_rm (RCX, src));
	emit (Pmovq_mr (dst, RCX));
        copy (offset_addressing src _8z) (offset_addressing dst _8z) (sz - 8)
    end else if sz >= 8 && !Clflags.option_ffpu then begin
	emit (Pmovsq_rm (XMM7, src));
	emit (Pmovsq_mr (dst, XMM7));
        copy (offset_addressing src _8z) (offset_addressing dst _8z) (sz - 8)
      end else if sz >= 4 then begin
	emit (Pmovl_rm (RCX, src));
	emit (Pmovl_mr (dst, RCX));
        copy (offset_addressing src _4z) (offset_addressing dst _4z) (sz - 4)
      end else if sz >= 2 then begin
	emit (Pmovw_rm (RCX, src));
	emit (Pmovw_mr (dst, RCX));
        copy (offset_addressing src _2z) (offset_addressing dst _2z) (sz - 2)
      end else if sz >= 1 then begin
	emit (Pmovb_rm (RCX, src));
	emit (Pmovb_mr (dst, RCX));
        copy (offset_addressing src _1z) (offset_addressing dst _1z) (sz - 1)
      end in
  copy (addressing_of_builtin_arg src) (addressing_of_builtin_arg dst) sz

let expand_builtin_memcpy_big sz al src dst =
  if src <> BA (IR RSI) then emit (_Plea (RSI, addressing_of_builtin_arg src));
  if dst <> BA (IR RDI) then emit (_Plea (RDI, addressing_of_builtin_arg dst));
  (* TODO: movsq? *)
  emit (Pmovl_ri (RCX,coqint_of_camlint (Int32.of_int (sz / 4))));
  emit Prep_movsl;
  if sz mod 4 >= 2 then emit Pmovsw;
  if sz mod 2 >= 1 then emit Pmovsb

let expand_builtin_memcpy sz al args =
  let (dst, src) = match args with [d; s] -> (d, s) | _ -> assert false in
  if sz <= 32
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk addr res =
  match chunk, res with
  | Mint8unsigned, BR(IR res) ->
     emit (Pmovzb_rm (res,addr))
  | Mint8signed, BR(IR res) ->
     emit (Pmovsb_rm (res,addr))
  | Mint16unsigned, BR(IR res) ->
     emit (Pmovzw_rm (res,addr))
  | Mint16signed, BR(IR res) ->
     emit (Pmovsw_rm (res,addr))
  | Mint32, BR(IR res) ->
     emit (Pmovl_rm (res,addr))
  | Mint64, BR(IR res) ->
     emit (Pmovq_rm (res,addr))
  | Mint64, BR_splitlong(BR(IR res1), BR(IR res2)) ->
     let addr' = offset_addressing addr _4z in
     if not (Asmgen.addressing_mentions addr res2) then begin
	 emit (Pmovl_rm (res2,addr));
	 emit (Pmovl_rm (res1,addr'))
       end else begin
	 emit (Pmovl_rm (res1,addr'));
	 emit (Pmovl_rm (res2,addr))
       end
  | Mfloat32, BR(FR res) ->
     emit (Pmovss_fm (res,addr))
  | Mfloat64, BR(FR res) ->
     emit (Pmovsd_fm (res,addr))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [addr] ->
     expand_builtin_vload_common chunk (addressing_of_builtin_arg addr) res
  | _ ->
     assert false

let expand_builtin_vstore_common chunk addr src tmp =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) ->
     if Archi.ptr64 || Asmgen.low_ireg src then
       emit (Pmovb_mr (addr,src))
     else begin
       emit (Pmov_rr (tmp,src));
       emit (Pmovb_mr (addr,tmp))
     end
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Pmovw_mr (addr,src))
  | Mint32, BA(IR src) ->
     emit (Pmovl_mr (addr,src))
  | Mint64, BA(IR src) ->
     emit (Pmovq_mr (addr,src))
  | Mint64, BA_splitlong(BA(IR src1), BA(IR src2)) ->
     let addr' = offset_addressing addr _4z in
     emit (Pmovl_mr (addr,src2));
     emit (Pmovl_mr (addr',src1))
  | Mfloat32, BA(FR src) ->
     emit (Pmovss_mf (addr,src))
  | Mfloat64, BA(FR src) ->
     emit (Pmovsd_mf (addr,src))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [addr; src] ->
     let addr = addressing_of_builtin_arg addr in
     expand_builtin_vstore_common chunk addr src
       (if Asmgen.addressing_mentions addr RAX then RCX else RAX)
  | _ -> assert false

(* Handling of varargs *)

let rec next_arg_locations ir fr ofs = function
  | [] ->
      (ir, fr, ofs)
  | (Tint | Tlong | Tany32 | Tany64) :: l ->
      if ir < 6
      then next_arg_locations (ir + 1) fr ofs l
      else next_arg_locations ir fr (ofs + 8) l
  | (Tfloat | Tsingle) :: l ->
      if fr < 8
      then next_arg_locations ir (fr + 1) ofs l
      else next_arg_locations ir fr (ofs + 8) l

let current_function_stacksize = ref 0L

let expand_builtin_va_start_32 r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let ofs =
    Int32.(add (add !PrintAsmaux.current_function_stacksize 4l)
               (mul 4l (Z.to_int32 (Conventions1.size_arguments
                                      (get_current_function_sig ()))))) in
  emit (Pleal (RAX, linear_addr RSP (Z.of_uint32 ofs)));
  emit (Pmovl_mr (linear_addr r _0z, RAX))

let expand_builtin_va_start_64 r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let (ir, fr, ofs) =
    next_arg_locations 0 0 0 (get_current_function_args ()) in
  (* [r] points to the following struct:
       struct {
         unsigned int gp_offset;
         unsigned int fp_offset;
         void *overflow_arg_area;
         void *reg_save_area;
       }
     gp_offset is initialized to ir * 8
     fp_offset is initialized to  6 * 8 + fr * 16
     overflow_arg_area is initialized to sp + current stacksize + ofs
     reg_save_area is initialized to
         sp + current stacksize - 16 - save area size (6 * 8 + 8 * 16) *)
  let gp_offset = Int32.of_int (ir * 8)
  and fp_offset = Int32.of_int (6 * 8 + fr * 16)
  and overflow_arg_area = Int64.(add !current_function_stacksize (of_int ofs))
  and reg_save_area = Int64.(sub !current_function_stacksize 192L) in
  assert (r <> RAX);
  emit (Pmovl_ri (RAX, coqint_of_camlint gp_offset));
  emit (Pmovl_mr (linear_addr r _0z, RAX));
  emit (Pmovl_ri (RAX, coqint_of_camlint fp_offset));
  emit (Pmovl_mr (linear_addr r _4z, RAX));
  emit (Pleaq (RAX, linear_addr RSP (Z.of_uint64 overflow_arg_area)));
  emit (Pmovq_mr (linear_addr r _8z, RAX));
  emit (Pleaq (RAX, linear_addr RSP (Z.of_uint64 reg_save_area)));
  emit (Pmovq_mr (linear_addr r _16z, RAX))

(* FMA operations *)

(*   vfmadd<i><j><k> r1, r2, r3   performs r1 := ri * rj + rk
   hence
     vfmadd132 r1, r2, r3    performs  r1 := r1 * r3 + r2
     vfmadd213 r1, r2, r3    performs  r1 := r2 * r1 + r3
     vfmadd231 r1, r2, r3    performs  r1 := r2 * r3 + r1
*)

let expand_fma args res i132 i213 i231 =
  match args, res with
  | [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      if res = a1 then emit (i132 a1 a3 a2)       (* a1 * a2 + a3 *)
      else if res = a2 then emit (i213 a2 a1 a3)  (* a1 * a2 + a3 *)
      else if res = a3 then emit (i231 a3 a1 a2)  (* a1 * a2 + a3 *)
      else begin
        emit (Pmovsd_ff(res, a3));
        emit (i231 res a1 a2)                     (* a1 * a2 + res *)
      end
  | _ ->
     invalid_arg ("ill-formed fma builtin")

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Integer arithmetic *)
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Pbswap32 res)
  | "__builtin_bswap64", [BA(IR a1)], BR(IR res) ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Pbswap64 res)
  | "__builtin_bswap64", [BA_splitlong(BA(IR ah), BA(IR al))],
                         BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (ah = RAX && al = RDX && rh = RDX && rl = RAX);
     emit (Pbswap32 RAX);
     emit (Pbswap32 RDX)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Pbswap16 res)
  | "__builtin_clz", [BA(IR a1)], BR(IR res) ->
     emit (Pbsrl (res,a1));
     emit (Pxorl_ri(res,coqint_of_camlint 31l))
  | "__builtin_clzl", [BA(IR a1)], BR(IR res) ->
     if not(Archi.ptr64) then begin
       emit (Pbsrl (res,a1));
       emit (Pxorl_ri(res,coqint_of_camlint 31l))
     end else begin
       emit (Pbsrq (res,a1));
       emit (Pxorl_ri(res,coqint_of_camlint 63l))
     end
  | "__builtin_clzll", [BA(IR a1)], BR(IR res) ->
     emit (Pbsrq (res,a1));
     emit (Pxorl_ri(res,coqint_of_camlint 63l))
  | "__builtin_clzll", [BA_splitlong(BA (IR ah), BA (IR al))], BR(IR res) ->
     let lbl1 = new_label() in
     let lbl2 = new_label() in
     emit (Ptestl_rr(ah, ah));
     emit (Pjcc(Cond_e, lbl1));
     emit (Pbsrl(res, ah));
     emit (Pxorl_ri(res, coqint_of_camlint 31l));
     emit (Pjmp_l lbl2);
     emit (Plabel lbl1);
     emit (Pbsrl(res, al));
     emit (Pxorl_ri(res, coqint_of_camlint 63l));
     emit (Plabel lbl2)
  | "__builtin_ctz", [BA(IR a1)], BR(IR res) ->
     emit (Pbsfl (res,a1))
  | "__builtin_ctzl", [BA(IR a1)], BR(IR res) ->
     if not(Archi.ptr64) then
       emit (Pbsfl (res,a1))
     else
       emit (Pbsfq (res,a1))
  | "__builtin_ctzll", [BA(IR a1)], BR(IR res) ->
     emit (Pbsfq (res,a1))
  | "__builtin_ctzll", [BA_splitlong(BA (IR ah), BA (IR al))], BR(IR res) ->
     let lbl1 = new_label() in
     let lbl2 = new_label() in
     emit (Ptestl_rr(al, al));
     emit (Pjcc(Cond_e, lbl1));
     emit (Pbsfl(res, al));
     emit (Pjmp_l lbl2);
     emit (Plabel lbl1);
     emit (Pbsfl(res, ah));
     emit (Paddl_ri(res, coqint_of_camlint 32l));
     emit (Plabel lbl2)
  (* Float arithmetic *)
  | "__builtin_fabs", [BA(FR a1)], BR(FR res) ->
     if a1 <> res then
       emit (Pmovsd_ff (res,a1));
     emit (Pabsd res) (* This ensures that need_masks is set to true *)
  | "__builtin_fsqrt", [BA(FR a1)], BR(FR res) ->
     emit (Psqrtsd (res,a1))
  | "__builtin_fmax", [BA(FR a1); BA(FR a2)], BR(FR res) ->
     if res = a1 then
       emit (Pmaxsd (res,a2))
     else if res = a2 then
       emit (Pmaxsd (res,a1))
     else begin
	 emit (Pmovsd_ff (res,a1));
	 emit (Pmaxsd (res,a2))
       end
  | "__builtin_fmin", [BA(FR a1); BA(FR a2)], BR(FR res) ->
     if res = a1 then
       emit (Pminsd (res,a2))
     else if res = a2 then
       emit (Pminsd (res,a1))
     else begin
	 emit (Pmovsd_ff (res,a1));
	 emit (Pminsd (res,a2))
       end
  | "__builtin_fmadd",  _, _ ->
      expand_fma args res
        (fun r1 r2 r3 -> Pfmadd132(r1, r2, r3))
        (fun r1 r2 r3 -> Pfmadd213(r1, r2, r3))
        (fun r1 r2 r3 -> Pfmadd231(r1, r2, r3))
  | "__builtin_fmsub",  _, _ ->
      expand_fma args res
        (fun r1 r2 r3 -> Pfmsub132(r1, r2, r3))
        (fun r1 r2 r3 -> Pfmsub213(r1, r2, r3))
        (fun r1 r2 r3 -> Pfmsub231(r1, r2, r3))
  | "__builtin_fnmadd",  _, _ ->
      expand_fma args res
        (fun r1 r2 r3 -> Pfnmadd132(r1, r2, r3))
        (fun r1 r2 r3 -> Pfnmadd213(r1, r2, r3))
        (fun r1 r2 r3 -> Pfnmadd231(r1, r2, r3))
  | "__builtin_fnmsub",  _, _ ->
      expand_fma args res
        (fun r1 r2 r3 -> Pfnmsub132(r1, r2, r3))
        (fun r1 r2 r3 -> Pfnmsub213(r1, r2, r3))
        (fun r1 r2 r3 -> Pfnmsub231(r1, r2, r3))
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [BA_splitlong(BA(IR ah), BA(IR al))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (ah = RDX && al = RAX && rh = RDX && rl = RAX);
     emit (Pnegl RAX);
     emit (Padcl_ri (RDX,_0));
     emit (Pnegl RDX)
  | "__builtin_addl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                       BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (ah = RDX && al = RAX && bh = RCX && bl = RBX && rh = RDX && rl = RAX);
     emit (Paddl_rr (RAX,RBX));
     emit (Padcl_rr (RDX,RCX))
  | "__builtin_subl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                       BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (ah = RDX && al = RAX && bh = RCX && bl = RBX && rh = RDX && rl = RAX);
     emit (Psubl_rr (RAX,RBX));
     emit (Psbbl_rr (RDX,RCX))
  | "__builtin_mull", [BA(IR a); BA(IR b)],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (a = RAX && b = RDX && rh = RDX && rl = RAX);
     emit (Pmull_r RDX)
  (* Memory accesses *)
  | "__builtin_read16_reversed", [BA(IR a1)], BR(IR res) ->
     emit (Pmovzw_rm (res, linear_addr a1 _0));
     emit (Pbswap16 res)
  | "__builtin_read32_reversed", [BA(IR a1)], BR(IR res) ->
     emit (Pmovl_rm (res, linear_addr a1 _0));
     emit (Pbswap32 res)
  | "__builtin_write16_reversed", [BA(IR a1); BA(IR a2)], _ ->
     let tmp = if a1 = RCX then RDX else RCX in
     if a2 <> tmp then
       emit (Pmov_rr (tmp,a2));
     emit (Pbswap16 tmp);
     emit (Pmovw_mr (linear_addr a1 _0z, tmp))
  | "__builtin_write32_reversed", [BA(IR a1); BA(IR a2)], _ ->
     let tmp = if a1 = RCX then RDX else RCX in
     if a2 <> tmp then
       emit (Pmov_rr (tmp,a2));
     emit (Pbswap32 tmp);
     emit (Pmovl_mr (linear_addr a1 _0z, tmp))
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     assert (a = RDX);
     if Archi.ptr64
     then expand_builtin_va_start_64 a
     else expand_builtin_va_start_32 a
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
     ()
  (* no operation *)
  | "__builtin_nop", [], _ ->
     emit Pnop
  (* Catch-all *)
  | _ ->
     raise (Error ("unrecognized builtin " ^ name))

(* Calls to variadic functions for x86-64: register AL must contain
   the number of XMM registers used for parameter passing.  To be on
   the safe side.  do the same if the called function is
   unprototyped. *)

let set_al sg =
  if Archi.ptr64 && (sg.sig_cc.cc_vararg || sg.sig_cc.cc_unproto) then begin
    let (ir, fr, ofs) = next_arg_locations 0 0 0 sg.sig_args in
    emit (Pmovl_ri (RAX, coqint_of_camlint (Int32.of_int fr)))
  end

(* Expansion of instructions *)

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs_ra, ofs_link) ->
     if Archi.ptr64 then begin
       let (sz, save_regs) = sp_adjustment_64 sz in
       (* Allocate frame *)
       let sz' = Z.of_uint sz in
       emit (Psubq_ri (RSP, sz'));
       emit (Pcfi_adjust sz');
       if save_regs >= 0 then begin
         (* Save the registers *)
         emit (Pleaq (R10, linear_addr RSP (Z.of_uint save_regs)));
         emit (Pcall_s (intern_string "__compcert_va_saveregs",
                        {sig_args = []; sig_res = None; sig_cc = cc_default}))
       end;
       (* Stack chaining *)
       let fullsz = sz + 8 in
       let addr1 = linear_addr RSP (Z.of_uint fullsz) in
       let addr2 = linear_addr RSP ofs_link in
       emit (Pleaq (RAX, addr1));
       emit (Pmovq_mr (addr2, RAX));
       current_function_stacksize := Int64.of_int fullsz
     end else begin
       let sz = sp_adjustment_32 sz in
       (* Allocate frame *)
       let sz' = Z.of_uint sz in
       emit (Psubl_ri (RSP, sz'));
       emit (Pcfi_adjust sz');
       (* Stack chaining *)
       let addr1 = linear_addr RSP (Z.of_uint (sz + 4)) in
       let addr2 = linear_addr RSP ofs_link in
       emit (Pleal (RAX,addr1));
       emit (Pmovl_mr (addr2,RAX));
       PrintAsmaux.current_function_stacksize := Int32.of_int sz
     end
  | Pfreeframe(sz, ofs_ra, ofs_link) ->
     if Archi.ptr64 then begin
       let (sz, _) = sp_adjustment_64 sz in
       emit (Paddq_ri (RSP, Z.of_uint sz))
     end else begin
       let sz = sp_adjustment_32 sz in
       emit (Paddl_ri (RSP, Z.of_uint sz))
     end
  | Pjmp_s(_, sg) | Pjmp_r(_, sg) | Pcall_s(_, sg) | Pcall_r(_, sg) ->
     set_al sg;
     emit instr
  | Pbuiltin (ef,args, res) ->
     begin
       match ef with
       | EF_builtin(name, sg) ->
	  expand_builtin_inline (camlstring_of_coqstring name) args res
       | EF_vload chunk ->
          expand_builtin_vload chunk args res
       | EF_vstore chunk ->
          expand_builtin_vstore chunk args
       | EF_memcpy(sz, al) ->
          expand_builtin_memcpy (Z.to_int sz) (Z.to_int al) args
       | EF_annot_val(kind,txt, targ) ->
          expand_annot_val kind txt targ args res
       | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
          emit instr
       | _ ->
          assert false
     end
  | _ -> emit instr

let int_reg_to_dwarf_32 = function
  | RAX -> 0
  | RBX -> 3
  | RCX -> 1
  | RDX -> 2
  | RSI -> 6
  | RDI -> 7
  | RBP -> 5
  | RSP -> 4
  | _ -> assert false

let int_reg_to_dwarf_64 = function
  | RAX -> 0
  | RDX -> 1
  | RCX -> 2
  | RBX -> 3
  | RSI -> 4
  | RDI -> 5
  | RBP -> 6
  | RSP -> 7
  | R8 -> 8
  | R9 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15

let int_reg_to_dwarf =
  if Archi.ptr64 then int_reg_to_dwarf_64 else int_reg_to_dwarf_32

let float_reg_to_dwarf_32 = function
  | XMM0 -> 21
  | XMM1 -> 22
  | XMM2 -> 23
  | XMM3 -> 24
  | XMM4 -> 25
  | XMM5 -> 26
  | XMM6 -> 27
  | XMM7 -> 28
  | _ -> assert false

let float_reg_to_dwarf_64 = function
  | XMM0 -> 17
  | XMM1 -> 18
  | XMM2 -> 19
  | XMM3 -> 20
  | XMM4 -> 21
  | XMM5 -> 22
  | XMM6 -> 23
  | XMM7 -> 24
  | XMM8 -> 25
  | XMM9 -> 26
  | XMM10 -> 27
  | XMM11 -> 28
  | XMM12 -> 29
  | XMM13 -> 30
  | XMM14 -> 31
  | XMM15 -> 32

let float_reg_to_dwarf =
  if Archi.ptr64 then float_reg_to_dwarf_64 else float_reg_to_dwarf_32

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | FR r -> float_reg_to_dwarf r
   | _ -> assert false


let expand_function id fn =
  try
    set_current_function fn;
    expand id (int_reg_to_dwarf RSP) preg_to_dwarf expand_instruction fn.fn_code;
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

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
   of the IA32 assembly code.  Currently not done, this expansion
   is performed on the fly in PrintAsm. *)

open Asm
open Asmexpandaux
open Asmgen
open AST
open Camlcoq
open Datatypes
open Integers
       
(* Useful constants and helper functions *)

let _0 = Int.zero
let _1 = Int.one
let _2 = coqint_of_camlint 2l
let _4 = coqint_of_camlint 4l
let _8 = coqint_of_camlint 8l

let stack_alignment () =
  if Configuration.system = "macoxs" then 16
  else 8
	 
(* SP adjustment to allocate or free a stack frame *)
			   
let int32_align n a =
  if n >= 0l
  then Int32.logand (Int32.add n (Int32.of_int (a-1))) (Int32.of_int (-a))
  else Int32.logand n (Int32.of_int (-a))
		    
let sp_adjustment sz =
  let sz = camlint_of_coqint sz in
  (* Preserve proper alignment of the stack *)
  let sz = int32_align sz (stack_alignment ()) in
  (* The top 4 bytes have already been allocated by the "call" instruction. *)
  let sz = Int32.sub sz 4l in
  sz
			   
			   
(* Built-ins.  They come in two flavors: 
   - annotation statements: take their arguments in registers or stack
   locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
   registers; preserve all registers except ECX, EDX, XMM6 and XMM7. *)

(* Handling of annotations *)

let expand_annot_val txt targ args res =
  emit (Pbuiltin (EF_annot(txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmov_rr (dst,src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pmovsd_ff (dst,src))
  | _, _ -> assert false

(* Translate a builtin argument into an addressing mode *)

let addressing_of_builtin_arg = function
  | BA (IR r) -> Addrmode(Some r, None, Coq_inl Integers.Int.zero)
  | BA_addrstack ofs -> Addrmode(Some ESP, None, Coq_inl ofs)
  | BA_addrglobal(id, ofs) -> Addrmode(None, None, Coq_inr(id, ofs))
  | _ -> assert false

let offset_addressing (Addrmode(base, ofs, cst)) delta =
  Addrmode(base, ofs,
           match cst with
           | Coq_inl n -> Coq_inl(Integers.Int.add n delta)
           | Coq_inr(id, n) -> Coq_inr(id, Integers.Int.add n delta))

(* Handling of memcpy *)

(* Unaligned memory accesses are quite fast on IA32, so use large
   memory accesses regardless of alignment. *)

let expand_builtin_memcpy_small sz al src dst =
  let rec copy src dst sz =
    if sz >= 8 && !Clflags.option_ffpu then begin
	emit (Pmovq_rm (XMM7, src));
	emit (Pmovq_mr (dst, XMM7));
        copy (offset_addressing src _8) (offset_addressing dst _8) (sz - 8)
      end else if sz >= 4 then begin
	emit (Pmov_rm (ECX, src));
	emit (Pmov_mr (dst, ECX));
        copy (offset_addressing src _4) (offset_addressing dst _4) (sz - 4)
      end else if sz >= 2 then begin
	emit (Pmovw_rm (ECX, src));
	emit (Pmovw_mr (dst, ECX));
        copy (offset_addressing src _2) (offset_addressing dst _2) (sz - 2)
      end else if sz >= 1 then begin
	emit (Pmovb_rm (ECX, src));
	emit (Pmovb_mr (dst, ECX));
        copy (offset_addressing src _1) (offset_addressing dst _1) (sz - 1)
      end in
  copy (addressing_of_builtin_arg src) (addressing_of_builtin_arg dst) sz

let expand_builtin_memcpy_big sz al src dst =
  if src <> BA (IR ESI) then emit (Plea (ESI, addressing_of_builtin_arg src));
  if dst <> BA (IR EDI) then emit (Plea (EDI, addressing_of_builtin_arg dst));
  emit (Pmov_ri (ECX,coqint_of_camlint (Int32.of_int (sz / 4))));
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
     emit (Pmov_rm (res,addr))
  | Mint64, BR_longofwords(BR(IR res1), BR(IR res2)) ->
     let addr' = offset_addressing addr (coqint_of_camlint 4l) in
     if not (Asmgen.addressing_mentions addr res2) then begin
	 emit (Pmov_rm (res2,addr));
	 emit (Pmov_rm (res1,addr'))
       end else begin
	 emit (Pmov_rm (res1,addr'));
	 emit (Pmov_rm (res2,addr))
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
     if Asmgen.low_ireg src then
       emit (Pmovb_mr (addr,src))
     else begin
	 emit (Pmov_rr (tmp,src));
	 emit (Pmovb_mr (addr,tmp))
       end
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Pmovw_mr (addr,src))
  | Mint32, BA(IR src) ->
     emit (Pmov_mr (addr,src))
  | Mint64, BA_longofwords(BA(IR src1), BA(IR src2)) ->
     let addr' = offset_addressing addr (coqint_of_camlint 4l) in
     emit (Pmov_mr (addr,src2));
     emit (Pmov_mr (addr',src1))
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
       (if Asmgen.addressing_mentions addr EAX then ECX else EAX)
  | _ -> assert false
		 
(* Handling of varargs *)
		 
let expand_builtin_va_start r =
  if not !current_function.fn_sig.sig_cc.cc_vararg then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let ofs = coqint_of_camlint
    Int32.(add (add !PrintAsmaux.current_function_stacksize 4l)
               (mul 4l (Z.to_int32 (Conventions1.size_arguments
                                      !current_function.fn_sig)))) in
  emit (Pmov_mr (Addrmode (Some r, None, Coq_inl _0),ESP));
  emit (Paddl_mi (Addrmode (Some r,None,Coq_inl _0),ofs))
	   
(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Integer arithmetic *)
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Pbswap res)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Prolw_8 res)
  | "__builtin_clz", [BA(IR a1)], BR(IR res) ->
     emit (Pbslr (a1,res));
     emit (Pxor_ri(res,coqint_of_camlint 31l))
  | "__builtin_ctz", [BA(IR a1)], BR(IR res) ->
     emit (Pbsfl (a1,res))
  (* Float arithmetic *)
  | "__builtin_fabs", [BA(FR a1)], BR(FR res) ->
     if a1 <> res then
       emit (Pmovsd_ff (a1,res));
     emit (Pabsd res) (* This ensures that need_masks is set to true *)
  | "__builtin_fsqrt", [BA(FR a1)], BR(FR res) ->
     emit (Psqrtsd (a1,res))
  | "__builtin_fmax", [BA(FR a1); BA(FR a2)], BR(FR res) ->
     if res = a1 then
       emit (Pmaxsd (a2,res))
     else if res = a2 then
       emit (Pmaxsd (a1,res))
     else begin
	 emit (Pmovsd_ff (a1,res));
	 emit (Pmaxsd (a2,res))
       end
  | "__builtin_fmin", [BA(FR a1); BA(FR a2)], BR(FR res) ->
     if res = a1 then
       emit (Pminsd (a2,res))
     else if res = a2 then
       emit (Pminsd (a1,res))
     else begin
	 emit (Pmovsd_ff (a1,res));
	 emit (Pminsd (a2,res))
       end
  | "__builtin_fmadd",  [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
     if res = a1 then
       emit (Pfmadd132 (a2,a3,res))
     else if res = a2 then
       emit (Pfmadd213 (a2,a3,res))
     else if res = a3 then
       emit (Pfmadd231 (a2,a3,res))
     else begin
	 emit (Pmovsd_ff (a2,res));
	 emit (Pfmadd231 (a1,a2,res))
       end
  |"__builtin_fmsub",  [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
     if res = a1 then
       emit (Pfmsub132 (a2,a3,res))
     else if res = a2 then
       emit (Pfmsub213 (a2,a3,res))
     else if res = a3 then
       emit (Pfmsub231 (a2,a3,res))
     else begin
	 emit (Pmovsd_ff (a2,res));
	 emit (Pfmsub231 (a1,a2,res))
       end
  | "__builtin_fnmadd",  [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
     if res = a1 then
       emit (Pfnmadd132 (a2,a3,res))
     else if res = a2 then
       emit (Pfnmadd213 (a2,a3,res))
     else if res = a3 then
       emit (Pfnmadd231 (a2,a3,res))
     else begin
	 emit (Pmovsd_ff (a2,res));
	 emit (Pfnmadd231 (a1,a2,res))
       end
  |"__builtin_fnmsub",  [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
     if res = a1 then
       emit (Pfnmsub132 (a2,a3,res))
     else if res = a2 then
       emit (Pfnmsub213 (a2,a3,res))
     else if res = a3 then
       emit (Pfnmsub231 (a2,a3,res))
     else begin
	 emit (Pmovsd_ff (a2,res));
	 emit (Pfnmsub231 (a1,a2,res))
       end
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [BA_longofwords(BA(IR ah), BA(IR al))],
                      BR_longofwords(BR(IR rh), BR(IR rl)) ->
     assert (ah = EDX && al = EAX && rh = EDX && rl = EAX);
     emit (Pneg EAX);
     emit (Padcl_ir (_0,EDX));
     emit (Pneg EDX)
  | "__builtin_addl", [BA_longofwords(BA(IR ah), BA(IR al));
                       BA_longofwords(BA(IR bh), BA(IR bl))],
                       BR_longofwords(BR(IR rh), BR(IR rl)) ->
     assert (ah = EDX && al = EAX && bh = ECX && bl = EBX && rh = EDX && rl = EAX);
     emit (Paddl (EBX,EAX));
     emit (Padcl_rr (ECX,EDX))
  | "__builtin_subl", [BA_longofwords(BA(IR ah), BA(IR al));
                       BA_longofwords(BA(IR bh), BA(IR bl))],
                       BR_longofwords(BR(IR rh), BR(IR rl)) ->
     assert (ah = EDX && al = EAX && bh = ECX && bl = EBX && rh = EDX && rl = EAX);
     emit (Psub_rr (EBX,EAX));
     emit (Psbbl (ECX,EDX))
  | "__builtin_mull", [BA(IR a); BA(IR b)],
                      BR_longofwords(BR(IR rh), BR(IR rl)) ->
     assert (a = EAX && b = EDX && rh = EDX && rl = EAX);
     emit (Pmul_r EDX)
  (* Memory accesses *)
  | "__builtin_read16_reversed", [BA(IR a1)], BR(IR res) ->
     let addr = Addrmode(Some a1,None,Coq_inl _0) in
     emit (Pmovzw_rm (res,addr));
     emit (Prolw_8 res)
  | "__builtin_read32_reversed", [BA(IR a1)], BR(IR res) ->
     let addr = Addrmode(Some a1,None,Coq_inl _0) in
     emit (Pmov_rm (res,addr));
     emit (Pbswap res)
  | "__builtin_write16_reversed", [BA(IR a1); BA(IR a2)], _ ->
     let tmp = if a1 = ECX then EDX else ECX in
     let addr = Addrmode(Some a1,None,Coq_inl _0) in
     if a2 <> tmp then
       emit (Pmov_rr (a2,tmp));
     emit (Pxchg (tmp,tmp));
     emit (Pmovw_mr (addr,tmp))
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     expand_builtin_va_start a
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
     ()
  (* Catch-all *)
  | _ ->
     invalid_arg ("unrecognized builtin " ^ name)

(* Expansion of instructions *)
       
let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs_ra, ofs_link) ->
     let sz = sp_adjustment sz in
     let addr = Addrmode(Some ESP,None,Coq_inl (coqint_of_camlint (Int32.add sz 4l))) in
     let addr' = Addrmode (Some ESP, None, Coq_inl ofs_link) in
     let sz' = coqint_of_camlint sz in
     emit (Psubl_ri (ESP,sz'));
     emit (Pcfi_adjust sz');
     emit (Plea (EDX,addr));
     emit (Pmov_mr (addr',EDX));
     PrintAsmaux.current_function_stacksize := sz
  | Pfreeframe(sz, ofs_ra, ofs_link) ->
     let sz = sp_adjustment sz in
     emit (Paddl_ri (ESP,coqint_of_camlint sz))
  | Pbuiltin (ef,args, res) ->
     begin
       match ef with
       | EF_builtin(name, sg) ->
	  expand_builtin_inline (extern_atom name) args res
       | EF_vload chunk ->
          expand_builtin_vload chunk args res
       | EF_vstore chunk ->
          expand_builtin_vstore chunk args
       | EF_memcpy(sz, al) ->
          expand_builtin_memcpy (Int32.to_int (camlint_of_coqint sz))
	    (Int32.to_int (camlint_of_coqint al)) args
       | EF_annot_val(txt, targ) ->
          expand_annot_val txt targ args res      
       | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
          emit instr
       | _ ->
          assert false
     end
  | _ -> emit instr
       
let expand_program p = p

let expand_function fn =
  set_current_function fn;
  List.iter expand_instruction fn.fn_code;
  get_current_function ()

let expand_fundef = function
  | Internal f -> Internal (expand_function f)
  | External ef -> External ef

let expand_program (p: Asm.program) : Asm.program =
  AST.transform_program expand_fundef p

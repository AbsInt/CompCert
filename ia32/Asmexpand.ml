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
open AST
open Camlcoq

(* Useful constants and helper functions *)

let _0 = Integers.Int.zero

(* Handling of compiler-inlined builtins *)

let emit_builtin_inline oc name args res =
  match name, args, res with
  (* Integer arithmetic *)
  | ("__builtin_bswap"| "__builtin_bswap32"), [IR a1], [IR res] ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Pbswap res)
  | "__builtin_bswap16", [IR a1], [IR res] ->
     if a1 <> res then
       emit (Pmov_rr (res,a1));
     emit (Prolw_8 res)
  | "__builtin_clz", [IR a1], [IR res] ->
     emit (Pbslr (a1,res));
     emit (Pxor_ri(res,coqint_of_camlint 31l))
  | "__builtin_ctz", [IR a1], [IR res] ->
     emit (Pbsfl (a1,res))
  (* Float arithmetic *)
  | "__builtin_fabs", [FR a1], [FR res] ->
     if a1 <> res then
       emit (Pmovsd_ff (a1,res));
     emit (Pabsd res) (* This ensures that need_masks is set to true *)
  | "__builtin_fsqrt", [FR a1], [FR res] ->
     emit (Psqrtsd (a1,res))
  | "__builtin_fmax", [FR a1; FR a2], [FR res] ->
     if res = a1 then
       emit (Pmaxsd (a2,res))
     else if res = a2 then
       emit (Pmaxsd (a1,res))
     else begin
	 emit (Pmovsd_ff (a1,res));
	 emit (Pmaxsd (a2,res))
       end
  | "__builtin_fmin", [FR a1; FR a2], [FR res] ->
     if res = a1 then
       emit (Pminsd (a2,res))
     else if res = a2 then
       emit (Pminsd (a1,res))
     else begin
	 emit (Pmovsd_ff (a1,res));
	 emit (Pminsd (a2,res))
       end
  | "__builtin_fmadd",  [FR a1; FR a2; FR a3], [FR res] ->
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
  |"__builtin_fmsub",  [FR a1; FR a2; FR a3], [FR res] ->
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
  | "__builtin_fnmadd",  [FR a1; FR a2; FR a3], [FR res] ->
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
  |"__builtin_fnmsub",  [FR a1; FR a2; FR a3], [FR res] ->
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
  | "__builtin_negl", [IR ah; IR al], [IR rh; IR rl] ->
     assert (ah = EDX && al = EAX && rh = EDX && rl = EAX);
     emit (Pneg EAX);
     emit (Padcl_ir (_0,EDX));
     emit (Pneg EDX)
  | "__builtin_addl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
     assert (ah = EDX && al = EAX && bh = ECX && bl = EBX && rh = EDX && rl = EAX);
     emit (Paddl (EBX,EAX));
     emit (Padcl_rr (ECX,EDX))
  | "__builtin_subl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
     assert (ah = EDX && al = EAX && bh = ECX && bl = EBX && rh = EDX && rl = EAX);
     emit (Psub_rr (EBX,EAX));
     emit (Psbbl (ECX,EDX))
  | "__builtin_mull", [IR a; IR b], [IR rh; IR rl] ->
     assert (a = EAX && b = EDX && rh = EDX && rl = EAX);
     emit (Pmul_r EDX)
  (* Memory accesses *)
 (* | "__builtin_read16_reversed", [IR a1], [IR res] ->
     fprintf oc "	movzwl	0(%a), %a\n" ireg a1 ireg res;
     fprintf oc "	rolw	$8, %a\n" ireg16 res
  | "__builtin_read32_reversed", [IR a1], [IR res] ->
     fprintf oc "	movl	0(%a), %a\n" ireg a1 ireg res;
     fprintf oc "	bswap	%a\n" ireg res
  | "__builtin_write16_reversed", [IR a1; IR a2], _ ->
     let tmp = if a1 = ECX then EDX else ECX in
     if a2 <> tmp then
       emit (Pmov_rr (a2,tmp));
     fprintf oc "	xchg	%a, %a\n" ireg8 tmp high_ireg8 tmp;
     fprintf oc "	movw	%a, 0(%a)\n" ireg16 tmp ireg a1
  | "__builtin_write32_reversed", [IR a1; IR a2], _ ->
     let tmp = if a1 = ECX then EDX else ECX in
     if a2 <> tmp then
       emit (Pmov_rr (a2,tmp));
     emit (Pbswap res);
     fprintf oc "	movl	%a, 0(%a)\n" ireg tmp ireg a1
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
     ()
  (* Vararg stuff *)
  | "__builtin_va_start", [IR a], _ ->
     print_builtin_va_start oc a
		       (* Catch-all *)  *)
  | _ ->
     invalid_arg ("unrecognized builtin " ^ name)
       
let expand_instruction instr =
  match instr with
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

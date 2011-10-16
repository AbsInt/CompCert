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

(* Printing IA32 assembly code in asm syntax *)

open Printf
open Datatypes
open Camlcoq
open Sections
open AST
open Memdata
open Asm

(* Recognition of target ABI and asm syntax *)

type target = ELF | MacOS | Cygwin

let target = 
  match Configuration.system with
  | "macosx" -> MacOS
  | "linux"  -> ELF
  | "bsd"    -> ELF
  | "cygwin" -> Cygwin
  | _        -> invalid_arg ("System " ^ Configuration.system ^ " not supported")

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
  match target with
  | ELF -> fprintf oc "%s" s
  | MacOS | Cygwin -> fprintf oc "_%s" s

let re_variadic_stub = Str.regexp "\\(.*\\)\\$[if]*$"

let symbol oc symb =
  let s = extern_atom symb in
  if Str.string_match re_variadic_stub s 0
  then raw_symbol oc (Str.matched_group 1 s)
  else raw_symbol oc s

let symbol_offset oc (symb, ofs) =
  symbol oc symb;
  if ofs <> 0l then fprintf oc " + %ld" ofs

let label oc lbl =
  match target with
  | ELF -> fprintf oc ".L%d" lbl
  | MacOS | Cygwin -> fprintf oc "L%d" lbl

let comment = "#"

let int_reg_name = function
  | EAX -> "%eax"  | EBX -> "%ebx"  | ECX -> "%ecx"  | EDX -> "%edx"
  | ESI -> "%esi"  | EDI -> "%edi"  | EBP -> "%ebp"  | ESP -> "%esp"

let int8_reg_name = function
  | EAX -> "%al"  | EBX -> "%bl"  | ECX -> "%cl"  | EDX -> "%dl"
  | _ -> assert false

let high_int8_reg_name = function
  | EAX -> "%ah"  | EBX -> "%bh"  | ECX -> "%ch"  | EDX -> "%dh"
  | _ -> assert false

let int16_reg_name = function
  | EAX -> "%ax"  | EBX -> "%bx"  | ECX -> "%cx"  | EDX -> "%dx"
  | ESI -> "%si"  | EDI -> "%di"  | EBP -> "%bp"  | ESP -> "%sp"

let float_reg_name = function
  | XMM0 -> "%xmm0"  | XMM1 -> "%xmm1"  | XMM2 -> "%xmm2"  | XMM3 -> "%xmm3"
  | XMM4 -> "%xmm4"  | XMM5 -> "%xmm5"  | XMM6 -> "%xmm6"  | XMM7 -> "%xmm7"

let ireg oc r = output_string oc (int_reg_name r)
let ireg8 oc r = output_string oc (int8_reg_name r)
let high_ireg8 oc r = output_string oc (high_int8_reg_name r)
let ireg16 oc r = output_string oc (int16_reg_name r)
let freg oc r = output_string oc (float_reg_name r)

let preg oc = function
  | IR r -> ireg oc r
  | FR r -> freg oc r
  | _    -> assert false

let addressing oc (Addrmode(base, shift, cst)) =
  begin match cst with
  | Coq_inl n ->
      let n = camlint_of_coqint n in
      fprintf oc "%ld" n
  | Coq_inr(Coq_pair(id, ofs)) -> 
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then symbol oc id
      else fprintf oc "(%a + %ld)" symbol id ofs
  end;
  begin match base, shift with
  | None, None -> ()
  | Some r1, None -> fprintf oc "(%a)" ireg r1
  | None, Some(Coq_pair(r2,sc)) -> fprintf oc "(,%a,%a)" ireg r2 coqint sc
  | Some r1, Some(Coq_pair(r2,sc)) -> fprintf oc "(%a,%a,%a)" ireg r1 ireg r2 coqint sc
  end

let name_of_condition = function
  | Cond_e -> "e" | Cond_ne -> "ne"
  | Cond_b -> "b" | Cond_be -> "be" | Cond_ae -> "ae" | Cond_a -> "a"
  | Cond_l -> "l" | Cond_le -> "le" | Cond_ge -> "ge" | Cond_g -> "g"
  | Cond_p -> "p" | Cond_np -> "np" 

let name_of_neg_condition = function
  | Cond_e -> "ne" | Cond_ne -> "e"
  | Cond_b -> "ae" | Cond_be -> "a" | Cond_ae -> "b" | Cond_a -> "be"
  | Cond_l -> "ge" | Cond_le -> "g" | Cond_ge -> "l" | Cond_g -> "le"
  | Cond_p -> "np" | Cond_np -> "p" 

let section oc name =
  fprintf oc "	%s\n" name

(* Names of sections *)

let name_of_section_ELF = function
  | Section_text -> ".text"
  | Section_data i | Section_small_data i -> if i then ".data" else ".bss"
  | Section_const | Section_small_const -> ".section	.rodata"
  | Section_string -> ".section	.rodata"
  | Section_literal -> ".section	.rodata.cst8,\"aM\",@progbits,8"
  | Section_jumptable -> ".text"
  | Section_user(s, wr, ex) ->
       sprintf ".section	%s,\"a%s%s\",@progbits"
               s (if wr then "w" else "") (if ex then "x" else "")

let name_of_section_MacOS = function
  | Section_text -> ".text"
  | Section_data _ | Section_small_data _ -> ".data"
  | Section_const  | Section_small_const -> ".const"
  | Section_string -> ".const"
  | Section_literal -> ".literal8"
  | Section_jumptable -> ".const"
  | Section_user(s, wr, ex) ->
       sprintf ".section	%s, %s, %s"
               (if wr then "__DATA" else "__TEXT") s
               (if ex then "regular, pure_instructions" else "regular")

let name_of_section_Cygwin = function
  | Section_text -> ".text"
  | Section_data _ | Section_small_data _ -> ".data"
  | Section_const  | Section_small_const -> ".section	.rdata,\"dr\""
  | Section_string -> ".section	.rdata,\"dr\""
  | Section_literal -> ".section	.rdata,\"dr\""
  | Section_jumptable -> ".text"
  | Section_user _ -> assert false

let name_of_section =
  match target with
  | ELF    -> name_of_section_ELF
  | MacOS  -> name_of_section_MacOS
  | Cygwin -> name_of_section_Cygwin

let section oc sec =
  fprintf oc "	%s\n" (name_of_section sec)

(* SP adjustment to allocate or free a stack frame *)

let stack_alignment =
  match target with
  | ELF | Cygwin -> 8               (* minimum is 4, 8 is better for perfs *)
  | MacOS -> 16                     (* mandatory *)

let int32_align n a =
  if n >= 0l
  then Int32.logand (Int32.add n (Int32.of_int (a-1))) (Int32.of_int (-a))
  else Int32.logand n (Int32.of_int (-a))

let sp_adjustment sz =
  let sz = camlint_of_coqint sz in
  (* Preserve proper alignment of the stack *)
  let sz = int32_align sz stack_alignment in
  (* The top 4 bytes have already been allocated by the "call" instruction. *)
  let sz = Int32.sub sz 4l in
  assert (sz >= 0l);
  sz

(* Base-2 log of a Caml integer *)

let rec log2 n =
  assert (n > 0);
  if n = 1 then 0 else 1 + log2 (n lsr 1)

(* Emit a align directive *)

let print_align oc n =
  match target with
  | ELF | Cygwin -> fprintf oc "	.align	%d\n" n
  | MacOS        -> fprintf oc "	.align	%d\n" (log2 n)

let need_masks = ref false

(* Built-in functions *)

(* Built-ins.  They come in two flavors: 
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers; preserve all registers except ECX, EDX, XMM6 and XMM7. *)

(* Handling of annotations *)

let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"

let print_annot_text print_arg oc txt args =
  fprintf oc "%s annotation: " comment;
  let print_fragment = function
  | Str.Text s ->
      output_string oc s
  | Str.Delim "%%" ->
      output_char oc '%'
  | Str.Delim s ->
      let n = int_of_string (String.sub s 1 (String.length s - 1)) in
      try
        print_arg oc (List.nth args (n-1))
      with Failure _ ->
        fprintf oc "<bad parameter %s>" s in
  List.iter print_fragment (Str.full_split re_annot_param txt);
  fprintf oc "\n"

let print_annot_stmt oc txt args =
  let print_annot_param oc = function
  | APreg r -> preg oc r
  | APstack(chunk, ofs) ->
      fprintf oc "mem(ESP + %a, %a)" coqint ofs coqint (size_chunk chunk) in
  print_annot_text print_annot_param oc txt args

let print_annot_val oc txt args res =
  print_annot_text preg oc txt args;
  match args, res with
  | IR src :: _, IR dst ->
      if dst <> src then fprintf oc "	movl	%a, %a\n" ireg src ireg dst
  | FR src :: _, FR dst ->
      if dst <> src then fprintf oc "	movsd	%a, %a\n" freg src freg dst
  | _, _ -> assert false

(* Handling of memcpy *)

(* Unaligned memory accesses are quite fast on IA32, so use large
   memory accesses regardless of alignment. *)

let print_builtin_memcpy_small oc sz al src dst =
  let tmp =
    if src <> ECX && dst <> ECX then ECX
    else if src <> EDX && dst <> EDX then EDX
    else EAX in
  let need_tmp =
    sz mod 4 <> 0 || not !Clflags.option_fsse in
  let rec copy ofs sz =
    if sz >= 8 && !Clflags.option_fsse then begin
      fprintf oc "	movq	%d(%a), %a\n" ofs ireg src freg XMM6;
      fprintf oc "	movq	%a, %d(%a)\n" freg XMM6 ofs ireg dst;
      copy (ofs + 8) (sz - 8)
    end else if sz >= 4 then begin
      if !Clflags.option_fsse then begin
        fprintf oc "	movd	%d(%a), %a\n" ofs ireg src freg XMM6;
        fprintf oc "	movd	%a, %d(%a)\n" freg XMM6 ofs ireg dst
      end else begin
        fprintf oc "	movl	%d(%a), %a\n" ofs ireg src ireg tmp;
        fprintf oc "	movl	%a, %d(%a)\n" ireg tmp ofs ireg dst
      end;
      copy (ofs + 4) (sz - 4)
    end else if sz >= 2 then begin
      fprintf oc "	movw	%d(%a), %a\n" ofs ireg src ireg16 tmp;
      fprintf oc "	movw	%a, %d(%a)\n" ireg16 tmp ofs ireg dst;
      copy (ofs + 2) (sz - 2)
    end else if sz >= 1 then begin
      fprintf oc "	movb	%d(%a), %a\n" ofs ireg src ireg8 tmp;
      fprintf oc "	movb	%a, %d(%a)\n" ireg8 tmp ofs ireg dst;
      copy (ofs + 1) (sz - 1)
    end in
  if need_tmp && tmp = EAX then
    fprintf oc "	pushl	%a\n" ireg EAX;
  copy 0 sz;
  if need_tmp && tmp = EAX then
    fprintf oc "	popl	%a\n" ireg EAX

let print_mov2 oc src1 dst1 src2 dst2 =
  if src1 = dst1 then
    if src2 = dst2
    then ()
    else fprintf oc "	movl	%a, %a\n" ireg src2 ireg dst2
  else if src2 = dst2 then
    fprintf oc "	movl	%a, %a\n" ireg src1 ireg dst1
  else if src2 = dst1 then
    if src1 = dst2 then
      fprintf oc "	xchgl	%a, %a\n" ireg src1 ireg src2
    else begin
      fprintf oc "	movl	%a, %a\n" ireg src2 ireg dst2;
      fprintf oc "	movl	%a, %a\n" ireg src1 ireg dst1
    end
  else begin
    fprintf oc "	movl	%a, %a\n" ireg src1 ireg dst1;
    fprintf oc "	movl	%a, %a\n" ireg src2 ireg dst2
  end

let print_builtin_memcpy_big oc sz al src dst =
  fprintf oc "	pushl	%a\n" ireg ESI;
  fprintf oc "	pushl	%a\n" ireg EDI;
  print_mov2 oc src ESI dst EDI;
  fprintf oc "	movl	$%d, %a\n" (sz / 4) ireg ECX;
  fprintf oc "	rep	movsl\n";
  if sz mod 4 >= 2 then fprintf oc "	movsw\n";
  if sz mod 2 >= 1 then fprintf oc "	movsb\n";
  fprintf oc "	popl	%a\n" ireg EDI;
  fprintf oc "	popl	%a\n" ireg ESI

let print_builtin_memcpy oc sz al args =
  let (dst, src) =
    match args with [IR d; IR s] -> (d, s) | _ -> assert false in
  fprintf oc "%s begin builtin __builtin_memcpy_aligned, size = %d, alignment = %d\n"
          comment sz al;
  if sz <= 64
  then print_builtin_memcpy_small oc sz al src dst
  else print_builtin_memcpy_big oc sz al src dst;
  fprintf oc "%s end builtin __builtin_memcpy_aligned\n" comment

(* Handling of volatile reads and writes *)

let print_builtin_vload oc chunk args res =
  fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
  begin match chunk, args, res with
  | Mint8unsigned, [IR addr], IR res ->
      fprintf oc "	movzbl	0(%a), %a\n" ireg addr ireg res
  | Mint8signed, [IR addr], IR res ->
      fprintf oc "	movsbl	0(%a), %a\n" ireg addr ireg res
  | Mint16unsigned, [IR addr], IR res ->
      fprintf oc "	movzwl	0(%a), %a\n" ireg addr ireg res
  | Mint16signed, [IR addr], IR res ->
      fprintf oc "	movswl	0(%a), %a\n" ireg addr ireg res
  | Mint32, [IR addr], IR res ->
      fprintf oc "	movl	0(%a), %a\n" ireg addr ireg res
  | Mfloat32, [IR addr], FR res ->
      fprintf oc "	cvtss2sd 0(%a), %a\n" ireg addr freg res
  | Mfloat64, [IR addr], FR res ->
      fprintf oc "	movsd	0(%a), %a\n" ireg addr freg res
  | _ ->
      assert false
  end;
  fprintf oc "%s end builtin __builtin_volatile_read\n" comment

let print_builtin_vstore oc chunk args =
  fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
  begin match chunk, args with
  | (Mint8signed | Mint8unsigned), [IR addr; IR src] ->
      if Asmgen.low_ireg src then
        fprintf oc "	movb	%a, 0(%a)\n" ireg8 src ireg addr
      else begin
        fprintf oc "	movl	%a, %%ecx\n" ireg src;
        fprintf oc "	movb	%%cl, 0(%a)\n" ireg addr
      end
  | (Mint16signed | Mint16unsigned), [IR addr; IR src] ->
      if Asmgen.low_ireg src then
        fprintf oc "	movw	%a, 0(%a)\n" ireg16 src ireg addr
      else begin
        fprintf oc "	movl	%a, %%ecx\n" ireg src;
        fprintf oc "	movw	%%cx, 0(%a)\n" ireg addr
      end
  | Mint32, [IR addr; IR src] ->
      fprintf oc "	movl	%a, 0(%a)\n" ireg src ireg addr
  | Mfloat32, [IR addr; FR src] ->
      fprintf oc "	cvtsd2ss %a, %%xmm7\n" freg src;
      fprintf oc "	movss	%%xmm7, 0(%a)\n" ireg addr
  | Mfloat64, [IR addr; FR src] ->
      fprintf oc "	movsd	%a, 0(%a)\n" freg src ireg addr
  | _ ->
      assert false
  end;
  fprintf oc "%s end builtin __builtin_volatile_write\n" comment

(* Handling of compiler-inlined builtins *)

let print_builtin_inline oc name args res =
  fprintf oc "%s begin builtin %s\n" comment name;
  begin match name, args, res with
  (* Memory accesses *)
  | "__builtin_read16_reversed", [IR a1], IR res ->
      let tmp = if Asmgen.low_ireg res then res else ECX in
      fprintf oc "	movzwl	0(%a), %a\n" ireg a1 ireg tmp;
      fprintf oc "	xchg	%a, %a\n" ireg8 tmp high_ireg8 tmp;
      if tmp <> res then
        fprintf oc "	movl	%a, %a\n" ireg tmp ireg res
  | "__builtin_read32_reversed", [IR a1], IR res ->
      fprintf oc "	movl	0(%a), %a\n" ireg a1 ireg res;
      fprintf oc "	bswap	%a\n" ireg res
  | "__builtin_write16_reversed", [IR a1; IR a2], _ ->
      let tmp = if a1 = ECX then EDX else ECX in
      if a2 <> tmp then
        fprintf oc "	movl	%a, %a\n" ireg a2 ireg tmp;
      fprintf oc "	xchg	%a, %a\n" ireg8 tmp high_ireg8 tmp;
      fprintf oc "	movw	%a, 0(%a)\n" ireg16 tmp ireg a1
  | "__builtin_write32_reversed", [IR a1; IR a2], _ ->
      let tmp = if a1 = ECX then EDX else ECX in
      if a2 <> tmp then
        fprintf oc "	movl	%a, %a\n" ireg a2 ireg tmp;
      fprintf oc "	bswap	%a\n" ireg tmp;
      fprintf oc "	movl	%a, 0(%a)\n" ireg tmp ireg a1
  (* Integer arithmetic *)
  | "__builtin_bswap", [IR a1], IR res ->
      if a1 <> res then
        fprintf oc "	movl	%a, %a\n" ireg a1 ireg res;
      fprintf oc "	bswap	%a\n" ireg res
  (* Float arithmetic *)
  | "__builtin_fabs", [FR a1], FR res ->
      need_masks := true;
      if a1 <> res then
        fprintf oc "	movsd	%a, %a\n" freg a1 freg res;
      fprintf oc "	andpd	%a, %a\n" raw_symbol "__absd_mask" freg res
  | "__builtin_fsqrt", [FR a1], FR res ->
      fprintf oc "	sqrtsd	%a, %a\n" freg a1 freg res
  | "__builtin_fmax", [FR a1; FR a2], FR res ->
      if res = a1 then
        fprintf oc "	maxsd	%a, %a\n" freg a2 freg res
      else if res = a2 then
        fprintf oc "	maxsd	%a, %a\n" freg a1 freg res
      else begin
        fprintf oc "	movsd	%a, %a\n" freg a1 freg res;
        fprintf oc "	maxsd	%a, %a\n" freg a2 freg res
      end
  | "__builtin_fmin", [FR a1; FR a2], FR res ->
      if res = a1 then
        fprintf oc "	minsd	%a, %a\n" freg a2 freg res
      else if res = a2 then
        fprintf oc "	minsd	%a, %a\n" freg a1 freg res
      else begin
        fprintf oc "	movsd	%a, %a\n" freg a1 freg res;
        fprintf oc "	minsd	%a, %a\n" freg a2 freg res
      end
  (* Catch-all *)  
  | _ ->
      invalid_arg ("unrecognized builtin " ^ name)
  end;
  fprintf oc "%s end builtin %s\n" comment name

(* Printing of instructions *)

let float_literals : (int * int64) list ref = ref []
let jumptables : (int * label list) list ref = ref []

(* Reminder on AT&T syntax: op source, dest *)

let print_instruction oc = function
  (* Moves *)
  | Pmov_rr(rd, r1) ->
      fprintf oc "	movl	%a, %a\n" ireg r1 ireg rd
  | Pmov_ri(rd, n) ->
      fprintf oc "	movl	$%ld, %a\n" (camlint_of_coqint n) ireg rd
  | Pmov_rm(rd, a) ->
      fprintf oc "	movl	%a, %a\n" addressing a ireg rd
  | Pmov_mr(a, r1) ->
      fprintf oc "	movl	%a, %a\n" ireg r1 addressing a
  | Pmovd_fr(rd, r1) ->
      fprintf oc "	movd	%a, %a\n" ireg r1 freg rd
  | Pmovd_rf(rd, r1) ->
      fprintf oc "	movd	%a, %a\n" freg r1 ireg rd
  | Pmovsd_ff(rd, r1) ->
      fprintf oc "	movapd	%a, %a\n" freg r1 freg rd
  | Pmovsd_fi(rd, n) ->
      let b = Int64.bits_of_float n in
      let lbl = new_label() in
      fprintf oc "	movsd	%a, %a %s %.18g\n" label lbl freg rd comment n;
      float_literals := (lbl, b) :: !float_literals
  | Pmovsd_fm(rd, a) ->
      fprintf oc "	movsd	%a, %a\n" addressing a freg rd
  | Pmovsd_mf(a, r1) ->
      fprintf oc "	movsd	%a, %a\n" freg r1 addressing a
  | Pfld_f(r1) ->
      fprintf oc "	subl	$8, %%esp\n";
      fprintf oc "	movsd	%a, 0(%%esp)\n" freg r1;
      fprintf oc "	fldl	0(%%esp)\n";
      fprintf oc "	addl	$8, %%esp\n"
  | Pfld_m(a) ->
      fprintf oc "	fldl	%a\n" addressing a
  | Pfstp_f(rd) ->
      fprintf oc "	subl	$8, %%esp\n";
      fprintf oc "	fstpl	0(%%esp)\n";
      fprintf oc "	movsd	0(%%esp), %a\n" freg rd;
      fprintf oc "	addl	$8, %%esp\n"
  | Pfstp_m(a) ->
      fprintf oc "	fstpl	%a\n" addressing a
  | Pxchg_rr(r1, r2) ->
      fprintf oc "	xchgl	%a, %a\n" ireg r1 ireg r2
  (** Moves with conversion *)
  | Pmovb_mr(a, r1) ->
      fprintf oc "	movb	%a, %a\n" ireg8 r1 addressing a
  | Pmovw_mr(a, r1) ->
      fprintf oc "	movw	%a, %a\n" ireg16 r1 addressing a
  | Pmovzb_rr(rd, r1) ->
      fprintf oc "	movzbl	%a, %a\n" ireg8 r1 ireg rd
  | Pmovzb_rm(rd, a) ->
      fprintf oc "	movzbl	%a, %a\n" addressing a ireg rd
  | Pmovsb_rr(rd, r1) ->
      fprintf oc "	movsbl	%a, %a\n" ireg8 r1 ireg rd
  | Pmovsb_rm(rd, a) ->
      fprintf oc "	movsbl	%a, %a\n" addressing a ireg rd
  | Pmovzw_rr(rd, r1) ->
      fprintf oc "	movzwl	%a, %a\n" ireg16 r1 ireg rd
  | Pmovzw_rm(rd, a) ->
      fprintf oc "	movzwl	%a, %a\n" addressing a ireg rd
  | Pmovsw_rr(rd, r1) ->
      fprintf oc "	movswl	%a, %a\n" ireg16 r1 ireg rd
  | Pmovsw_rm(rd, a) ->
      fprintf oc "	movswl	%a, %a\n" addressing a ireg rd
  | Pcvtss2sd_fm(rd, a) ->
      fprintf oc "	cvtss2sd %a, %a\n" addressing a freg rd
  | Pcvtsd2ss_ff(rd, r1) ->
      fprintf oc "	cvtsd2ss %a, %a\n" freg r1 freg rd;
      fprintf oc "	cvtss2sd %a, %a\n" freg rd freg rd
  | Pcvtsd2ss_mf(a, r1) ->
      fprintf oc "	cvtsd2ss %a, %%xmm7\n" freg r1;
      fprintf oc "	movss	%%xmm7, %a\n" addressing a
  | Pcvttsd2si_rf(rd, r1) ->
      fprintf oc "	cvttsd2si %a, %a\n" freg r1 ireg rd
  | Pcvtsi2sd_fr(rd, r1) ->
      fprintf oc "	cvtsi2sd %a, %a\n" ireg r1 freg rd
  (** Arithmetic and logical operations over integers *)
  | Plea(rd, a) ->
      fprintf oc "	leal	%a, %a\n" addressing a ireg rd
  | Pneg(rd) ->
      fprintf oc "	negl	%a\n" ireg rd
  | Psub_rr(rd, r1) ->
      fprintf oc "	subl	%a, %a\n" ireg r1 ireg rd
  | Pimul_rr(rd, r1) ->
      fprintf oc "	imull	%a, %a\n" ireg r1 ireg rd
  | Pimul_ri(rd, n) ->
      fprintf oc "	imull	$%a, %a\n" coqint n ireg rd
  | Pdiv(r1) ->
      fprintf oc "	xorl	%%edx, %%edx\n";
      fprintf oc "	divl	%a\n" ireg r1
  | Pidiv(r1) ->
      let lbl1 = new_label() in
      let lbl2 = new_label() in
      fprintf oc "	cmpl	$-1, %a\n" ireg r1;
      fprintf oc "	je	%a\n" label lbl1;
      fprintf oc "	cltd\n";
      fprintf oc "	idivl	%a\n" ireg r1;
      fprintf oc "	jmp	%a\n" label lbl2;
      (* Division by -1 can cause an overflow trap if dividend = min_int.
         Force x div (-1) = -x and x mod (-1) = 0. *)
      fprintf oc "%a:	negl	%a\n" label lbl1 ireg EAX;
      fprintf oc "	xorl	%a, %a\n" ireg EDX ireg EDX;
      fprintf oc "%a:\n" label lbl2
  | Pand_rr(rd, r1) ->
      fprintf oc "	andl	%a, %a\n" ireg r1 ireg rd
  | Pand_ri(rd, n) ->
      fprintf oc "	andl	$%a, %a\n" coqint n ireg rd
  | Por_rr(rd, r1) ->
      fprintf oc "	orl	%a, %a\n" ireg r1 ireg rd
  | Por_ri(rd, n) ->
      fprintf oc "	orl	$%a, %a\n" coqint n ireg rd
  | Pxor_r(rd) ->
      fprintf oc "	xorl	%a, %a\n" ireg rd ireg rd
  | Pxor_rr(rd, r1) ->
      fprintf oc "	xorl	%a, %a\n" ireg r1 ireg rd
  | Pxor_ri(rd, n) ->
      fprintf oc "	xorl	$%a, %a\n" coqint n ireg rd
  | Psal_rcl(rd) ->
      fprintf oc "	sall	%%cl, %a\n" ireg rd
  | Psal_ri(rd, n) ->
      fprintf oc "	sall	$%a, %a\n" coqint n ireg rd
  | Pshr_rcl(rd) ->
      fprintf oc "	shrl	%%cl, %a\n" ireg rd
  | Pshr_ri(rd, n) ->
      fprintf oc "	shrl	$%a, %a\n" coqint n ireg rd
  | Psar_rcl(rd) ->
      fprintf oc "	sarl	%%cl, %a\n" ireg rd
  | Psar_ri(rd, n) ->
      fprintf oc "	sarl	$%a, %a\n" coqint n ireg rd
  | Pror_ri(rd, n) ->
      fprintf oc "	rorl	$%a, %a\n" coqint n ireg rd
  | Pcmp_rr(r1, r2) ->
      fprintf oc "	cmpl	%a, %a\n" ireg r2 ireg r1
  | Pcmp_ri(r1, n) ->
      fprintf oc "	cmpl	$%a, %a\n" coqint n ireg r1
  | Ptest_rr(r1, r2) ->
      fprintf oc "	testl	%a, %a\n" ireg r2 ireg r1
  | Ptest_ri(r1, n) ->
      fprintf oc "	testl	$%a, %a\n" coqint n ireg r1
  | Pcmov(c, rd, r1) ->
      fprintf oc "	cmov%s	%a, %a\n" (name_of_condition c) ireg r1 ireg rd
  | Psetcc(c, rd) ->
      fprintf oc "	set%s	%%cl\n" (name_of_condition c);
      fprintf oc "	movzbl	%%cl, %a\n" ireg rd
  (** Arithmetic operations over floats *)
  | Paddd_ff(rd, r1) ->
      fprintf oc "	addsd	%a, %a\n" freg r1 freg rd
  | Psubd_ff(rd, r1) ->
      fprintf oc "	subsd	%a, %a\n" freg r1 freg rd
  | Pmuld_ff(rd, r1) ->
      fprintf oc "	mulsd	%a, %a\n" freg r1 freg rd
  | Pdivd_ff(rd, r1) ->
      fprintf oc "	divsd	%a, %a\n" freg r1 freg rd
  | Pnegd (rd) ->
      need_masks := true;
      fprintf oc "	xorpd	%a, %a\n" raw_symbol "__negd_mask" freg rd
  | Pabsd (rd) ->
      need_masks := true;
      fprintf oc "	andpd	%a, %a\n" raw_symbol "__absd_mask" freg rd
  | Pcomisd_ff(r1, r2) ->
      fprintf oc "	comisd	%a, %a\n" freg r2 freg r1
  | Pxorpd_f (rd) ->
      fprintf oc "	xorpd	%a, %a\n" freg rd freg rd
  (** Branches and calls *)
  | Pjmp_l(l) ->
      fprintf oc "	jmp	%a\n" label (transl_label l)
  | Pjmp_s(f) ->
      fprintf oc "	jmp	%a\n" symbol f
  | Pjmp_r(r) ->
      fprintf oc "	jmp	*%a\n" ireg r
  | Pjcc(c, l) ->
      let l = transl_label l in
      fprintf oc "	j%s	%a\n" (name_of_condition c) label l
  | Pjcc2(c1, c2, l) ->
      let l = transl_label l in
      let l' = new_label() in
      fprintf oc "	j%s	%a\n" (name_of_neg_condition c1) label l';
      fprintf oc "	j%s	%a\n" (name_of_condition c2) label l;
      fprintf oc "%a:\n" label l'
  | Pjmptbl(r, tbl) ->
      let l = new_label() in
      fprintf oc "	jmp	*%a(, %a, 4)\n" label l ireg r;
      jumptables := (l, tbl) :: !jumptables
  | Pcall_s(f) ->
      fprintf oc "	call	%a\n" symbol f
  | Pcall_r(r) ->
      fprintf oc "	call	*%a\n" ireg r
  | Pret ->
      fprintf oc "	ret\n"
  (** Pseudo-instructions *)
  | Plabel(l) ->
      fprintf oc "%a:\n" label (transl_label l)
  | Pallocframe(sz, ofs_ra, ofs_link) ->
      let sz = sp_adjustment sz in
      let ofs_link = camlint_of_coqint ofs_link in
      fprintf oc "	subl	$%ld, %%esp\n" sz;
      fprintf oc "	leal	%ld(%%esp), %%edx\n" (Int32.add sz 4l);
      fprintf oc "	movl	%%edx, %ld(%%esp)\n" ofs_link
  | Pfreeframe(sz, ofs_ra, ofs_link) ->
      let sz = sp_adjustment sz in
      fprintf oc "	addl	$%ld, %%esp\n" sz
  | Pbuiltin(ef, args, res) ->
      begin match ef with
      | EF_builtin(name, sg) ->
          print_builtin_inline oc (extern_atom name) args res
      | EF_vload chunk ->
          print_builtin_vload oc chunk args res
      | EF_vstore chunk ->
          print_builtin_vstore oc chunk args
      | EF_memcpy(sz, al) ->
          print_builtin_memcpy oc (Int32.to_int (camlint_of_coqint sz))
                                  (Int32.to_int (camlint_of_coqint al)) args
      | EF_annot_val(txt, targ) ->
          print_annot_val oc (extern_atom txt) args res
      | _ ->
          assert false
      end
  | Pannot(ef, args) ->
      begin match ef with
      | EF_annot(txt, targs) ->
          print_annot_stmt oc (extern_atom txt) args
      | _ ->
          assert false
      end

let print_literal oc (lbl, n) =
  fprintf oc "%a:	.quad	0x%Lx\n" label lbl n

let print_jumptable oc (lbl, tbl) =
  fprintf oc "%a:" label lbl;
  List.iter
    (fun l -> fprintf oc "	.long	%a\n" label (transl_label l))
    tbl

let print_function oc name code =
  Hashtbl.clear current_function_labels;
  float_literals := [];
  jumptables := [];
  let (text, lit, jmptbl) = sections_for_function name in
  section oc text;
  print_align oc 16;
  if not (C2C.atom_is_static name) then
    fprintf oc "	.globl %a\n" symbol name;
  fprintf oc "%a:\n" symbol name;
  List.iter (print_instruction oc) code;
  if target = ELF then begin
    fprintf oc "	.type	%a, @function\n" symbol name;
    fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
  end;
  if !float_literals <> [] then begin
    section oc lit;
    print_align oc 8;
    List.iter (print_literal oc) !float_literals;
    float_literals := []
  end;
  if !jumptables <> [] then begin
    section oc jmptbl;
    print_align oc 4;
    List.iter (print_jumptable oc) !jumptables;
    jumptables := []
  end

let print_fundef oc (Coq_pair(name, defn)) =
  match defn with
  | Internal code -> print_function oc name code
  | External ef -> ()

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
  | Init_float32 n ->
      fprintf oc "	.long	%ld %s %.18g\n" (Int32.bits_of_float n) comment n
  | Init_float64 n ->
      fprintf oc "	.quad	%Ld %s %.18g\n" (Int64.bits_of_float n) comment n
  | Init_space n ->
      let n = camlint_of_z n in
      if n > 0l then fprintf oc "	.space	%ld\n" n
  | Init_addrof(symb, ofs) ->
      fprintf oc "	.long	%a\n" 
                 symbol_offset (symb, camlint_of_coqint ofs)

let print_init_data oc name id =
  if Str.string_match PrintCsyntax.re_string_literal (extern_atom name) 0
  && List.for_all (function Init_int8 _ -> true | _ -> false) id
  then
    fprintf oc "	.ascii	\"%s\"\n" (PrintCsyntax.string_of_init id)
  else
    List.iter (print_init oc) id

let print_var oc (Coq_pair(name, v)) =
  match v.gvar_init with
  | [] -> ()
  | _  ->
      let init =
        match v.gvar_init with [Init_space _] -> false | _ -> true in
      let sec =
        Sections.section_for_variable name init
      and align =
        match C2C.atom_alignof name with
        | Some a -> a
        | None -> 8 (* 8-alignment is a safe default *)
      in
      section oc sec;
      print_align oc align;
      if not (C2C.atom_is_static name) then
        fprintf oc "	.globl	%a\n" symbol name;
      fprintf oc "%a:\n" symbol name;
      print_init_data oc name v.gvar_init;
      if target = ELF then begin
        fprintf oc "	.type	%a, @object\n" symbol name;
        fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
      end

let print_program oc p =
  need_masks := false;
  List.iter (print_var oc) p.prog_vars;
  List.iter (print_fundef oc) p.prog_funct;
  if !need_masks then begin
    section oc Section_const;  (* not Section_literal because not 8-bytes *)
    print_align oc 16;
    fprintf oc "%a:	.quad   0x8000000000000000, 0\n"
               raw_symbol "__negd_mask";
    fprintf oc "%a:	.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF\n"
               raw_symbol "__absd_mask"
  end

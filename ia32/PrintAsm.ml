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

module StringSet = Set.Make(String)

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

let re_variadic_stub = Str.regexp "\\(.*\\)\\$[ifl]*$"

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
  | Coq_inr(id, ofs) -> 
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then symbol oc id
      else fprintf oc "(%a + %ld)" symbol id ofs
  end;
  begin match base, shift with
  | None, None -> ()
  | Some r1, None -> fprintf oc "(%a)" ireg r1
  | None, Some(r2,sc) -> fprintf oc "(,%a,%a)" ireg r2 coqint sc
  | Some r1, Some(r2,sc) -> fprintf oc "(%a,%a,%a)" ireg r1 ireg r2 coqint sc
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

(* Names of sections *)

let name_of_section_ELF = function
  | Section_text -> ".text"
  | Section_data i | Section_small_data i -> if i then ".data" else ".bss"
  | Section_const | Section_small_const -> ".section	.rodata"
  | Section_string -> ".section	.rodata"
  | Section_literal -> ".section	.rodata.cst8,\"aM\",@progbits,8"
  | Section_jumptable -> ".text"
  | Section_user(s, wr, ex) ->
       sprintf ".section	\"%s\",\"a%s%s\",@progbits"
               s (if wr then "w" else "") (if ex then "x" else "")

let name_of_section_MacOS = function
  | Section_text -> ".text"
  | Section_data _ | Section_small_data _ -> ".data"
  | Section_const  | Section_small_const -> ".const"
  | Section_string -> ".const"
  | Section_literal -> ".literal8"
  | Section_jumptable -> ".const"
  | Section_user(s, wr, ex) ->
       sprintf ".section	\"%s\", %s, %s"
               (if wr then "__DATA" else "__TEXT") s
               (if ex then "regular, pure_instructions" else "regular")

let name_of_section_Cygwin = function
  | Section_text -> ".text"
  | Section_data _ | Section_small_data _ -> ".data"
  | Section_const  | Section_small_const -> ".section	.rdata,\"dr\""
  | Section_string -> ".section	.rdata,\"dr\""
  | Section_literal -> ".section	.rdata,\"dr\""
  | Section_jumptable -> ".text"
  | Section_user(s, wr, ex) ->
       sprintf ".section	\"%s\", \"%s\"\n"
             s (if ex then "xr" else if wr then "d" else "dr")

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

(* Emit .file / .loc debugging directives *)

let filename_num : (string, int) Hashtbl.t = Hashtbl.create 7

let print_file_line oc file line =
  if !Clflags.option_g && file <> "" then begin
    let filenum = 
      try
        Hashtbl.find filename_num file
      with Not_found ->
        let n = Hashtbl.length filename_num + 1 in
        Hashtbl.add filename_num file n;
        fprintf oc "	.file	%d %S\n" n file;
        n
    in fprintf oc "	.loc	%d %s\n" filenum line
  end

let print_location oc loc =
  if loc <> Cutil.no_loc then
    print_file_line oc (fst loc) (string_of_int (snd loc))

(* Emit .cfi directives *)

let cfi_startproc oc =
  if Configuration.asm_supports_cfi then fprintf oc "	.cfi_startproc\n"

let cfi_endproc oc =
  if Configuration.asm_supports_cfi then fprintf oc "	.cfi_endproc\n"

let cfi_adjust oc delta =
  if Configuration.asm_supports_cfi then
    fprintf oc "	.cfi_adjust_cfa_offset	%ld\n" delta

(* Built-in functions *)

(* Built-ins.  They come in two flavors: 
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers; preserve all registers except ECX, EDX, XMM6 and XMM7. *)

(* Handling of annotations *)

let re_file_line = Str.regexp "#line:\\(.*\\):\\([1-9][0-9]*\\)$"

let print_annot_stmt oc txt targs args =
  if Str.string_match re_file_line txt 0 then begin
    print_file_line oc (Str.matched_group 1 txt) (Str.matched_group 2 txt)
  end else begin
    fprintf oc "%s annotation: " comment;
    PrintAnnot.print_annot_stmt preg "ESP" oc txt targs args
  end

let print_annot_val oc txt args res =
  fprintf oc "%s annotation: " comment;
  PrintAnnot.print_annot_val preg oc txt args;
  match args, res with
  | [IR src], [IR dst] ->
      if dst <> src then fprintf oc "	movl	%a, %a\n" ireg src ireg dst
  | [FR src], [FR dst] ->
      if dst <> src then fprintf oc "	movapd	%a, %a\n" freg src freg dst
  | _, _ -> assert false

(* Handling of memcpy *)

(* Unaligned memory accesses are quite fast on IA32, so use large
   memory accesses regardless of alignment. *)

let print_builtin_memcpy_small oc sz al src dst =
  assert (src = EDX && dst = EAX);
  let rec copy ofs sz =
    if sz >= 8 && !Clflags.option_fsse then begin
      fprintf oc "	movq	%d(%a), %a\n" ofs ireg src freg XMM7;
      fprintf oc "	movq	%a, %d(%a)\n" freg XMM7 ofs ireg dst;
      copy (ofs + 8) (sz - 8)
    end else if sz >= 4 then begin
      fprintf oc "	movl	%d(%a), %a\n" ofs ireg src ireg ECX;
      fprintf oc "	movl	%a, %d(%a)\n" ireg ECX ofs ireg dst;
      copy (ofs + 4) (sz - 4)
    end else if sz >= 2 then begin
      fprintf oc "	movw	%d(%a), %a\n" ofs ireg src ireg16 ECX;
      fprintf oc "	movw	%a, %d(%a)\n" ireg16 ECX ofs ireg dst;
      copy (ofs + 2) (sz - 2)
    end else if sz >= 1 then begin
      fprintf oc "	movb	%d(%a), %a\n" ofs ireg src ireg8 ECX;
      fprintf oc "	movb	%a, %d(%a)\n" ireg8 ECX ofs ireg dst;
      copy (ofs + 1) (sz - 1)
    end in
  copy 0 sz

let print_builtin_memcpy_big oc sz al src dst =
  assert (src = ESI && dst = EDI);
  fprintf oc "	movl	$%d, %a\n" (sz / 4) ireg ECX;
  fprintf oc "	rep	movsl\n";
  if sz mod 4 >= 2 then fprintf oc "	movsw\n";
  if sz mod 2 >= 1 then fprintf oc "	movsb\n"

let print_builtin_memcpy oc sz al args =
  let (dst, src) =
    match args with [IR d; IR s] -> (d, s) | _ -> assert false in
  fprintf oc "%s begin builtin __builtin_memcpy_aligned, size = %d, alignment = %d\n"
          comment sz al;
  if sz <= 32
  then print_builtin_memcpy_small oc sz al src dst
  else print_builtin_memcpy_big oc sz al src dst;
  fprintf oc "%s end builtin __builtin_memcpy_aligned\n" comment

(* Handling of volatile reads and writes *)

let offset_addressing (Addrmode(base, ofs, cst)) delta =
  Addrmode(base, ofs,
           match cst with
           | Coq_inl n -> Coq_inl(Integers.Int.add n delta)
           | Coq_inr(id, n) -> Coq_inr(id, Integers.Int.add n delta))

let print_builtin_vload_common oc chunk addr res =
  match chunk, res with
  | Mint8unsigned, [IR res] ->
      fprintf oc "	movzbl	%a, %a\n" addressing addr ireg res
  | Mint8signed, [IR res] ->
      fprintf oc "	movsbl	%a, %a\n" addressing addr ireg res
  | Mint16unsigned, [IR res] ->
      fprintf oc "	movzwl	%a, %a\n" addressing addr ireg res
  | Mint16signed, [IR res] ->
      fprintf oc "	movswl	%a, %a\n" addressing addr ireg res
  | Mint32, [IR res] ->
      fprintf oc "	movl	%a, %a\n" addressing addr ireg res
  | Mint64, [IR res1; IR res2] ->
      let addr' = offset_addressing addr (coqint_of_camlint 4l) in
      if not (Asmgen.addressing_mentions addr res2) then begin
        fprintf oc "	movl	%a, %a\n" addressing addr ireg res2;
        fprintf oc "	movl	%a, %a\n" addressing addr' ireg res1
      end else begin
        fprintf oc "	movl	%a, %a\n" addressing addr' ireg res1;
        fprintf oc "	movl	%a, %a\n" addressing addr ireg res2
      end
  | Mfloat32, [FR res] ->
      fprintf oc "	cvtss2sd %a, %a\n" addressing addr freg res
  | (Mfloat64 | Mfloat64al32), [FR res] ->
      fprintf oc "	movsd	%a, %a\n" addressing addr freg res
  | _ ->
      assert false

let print_builtin_vload oc chunk args res =
  fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
  begin match args with
  | [IR addr] ->
      print_builtin_vload_common oc chunk
                 (Addrmode(Some addr, None, Coq_inl Integers.Int.zero)) res
  | _ ->
      assert false
  end;
  fprintf oc "%s end builtin __builtin_volatile_read\n" comment

let print_builtin_vload_global oc chunk id ofs args res =
  fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
  print_builtin_vload_common oc chunk
                 (Addrmode(None, None, Coq_inr(id,ofs))) res;
  fprintf oc "%s end builtin __builtin_volatile_read\n" comment

let print_builtin_vstore_common oc chunk addr src tmp =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), [IR src] ->
      if Asmgen.low_ireg src then
        fprintf oc "	movb	%a, %a\n" ireg8 src addressing addr
      else begin
        fprintf oc "	movl	%a, %a\n" ireg src ireg tmp;
        fprintf oc "	movb	%a, %a\n" ireg8 tmp addressing addr
      end
  | (Mint16signed | Mint16unsigned), [IR src] ->
      fprintf oc "	movw	%a, %a\n" ireg16 src addressing addr
  | Mint32, [IR src] ->
      fprintf oc "	movl	%a, %a\n" ireg src addressing addr
  | Mint64, [IR src1; IR src2] ->
      let addr' = offset_addressing addr (coqint_of_camlint 4l) in
      fprintf oc "	movl	%a, %a\n" ireg src2 addressing addr;
      fprintf oc "	movl	%a, %a\n" ireg src1 addressing addr'
  | Mfloat32, [FR src] ->
      fprintf oc "	cvtsd2ss %a, %%xmm7\n" freg src;
      fprintf oc "	movss	%%xmm7, %a\n" addressing addr
  | (Mfloat64 | Mfloat64al32), [FR src] ->
      fprintf oc "	movsd	%a, %a\n" freg src addressing addr
  | _ ->
      assert false

let print_builtin_vstore oc chunk args =
  fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
  begin match args with
  | IR addr :: src ->
      print_builtin_vstore_common oc chunk
                 (Addrmode(Some addr, None, Coq_inl Integers.Int.zero)) src
                 (if addr = EAX then ECX else EAX)
  | _ ->
      assert false
  end;
  fprintf oc "%s end builtin __builtin_volatile_write\n" comment

let print_builtin_vstore_global oc chunk id ofs args =
  fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
  print_builtin_vstore_common oc chunk
                 (Addrmode(None, None, Coq_inr(id,ofs))) args EAX;
  fprintf oc "%s end builtin __builtin_volatile_write\n" comment

(* Handling of compiler-inlined builtins *)

let print_builtin_inline oc name args res =
  fprintf oc "%s begin builtin %s\n" comment name;
  begin match name, args, res with
  (* Integer arithmetic *)
  | ("__builtin_bswap"| "__builtin_bswap32"), [IR a1], [IR res] ->
      if a1 <> res then
        fprintf oc "	movl	%a, %a\n" ireg a1 ireg res;
      fprintf oc "	bswap	%a\n" ireg res
  | "__builtin_bswap16", [IR a1], [IR res] ->
      if a1 <> res then
        fprintf oc "	movl	%a, %a\n" ireg a1 ireg res;
      fprintf oc "	rolw	$8, %a\n" ireg16 res
  (* Float arithmetic *)
  | "__builtin_fabs", [FR a1], [FR res] ->
      need_masks := true;
      if a1 <> res then
        fprintf oc "	movapd	%a, %a\n" freg a1 freg res;
      fprintf oc "	andpd	%a, %a\n" raw_symbol "__absd_mask" freg res
  | "__builtin_fsqrt", [FR a1], [FR res] ->
      fprintf oc "	sqrtsd	%a, %a\n" freg a1 freg res
  | "__builtin_fmax", [FR a1; FR a2], [FR res] ->
      if res = a1 then
        fprintf oc "	maxsd	%a, %a\n" freg a2 freg res
      else if res = a2 then
        fprintf oc "	maxsd	%a, %a\n" freg a1 freg res
      else begin
        fprintf oc "	movapd	%a, %a\n" freg a1 freg res;
        fprintf oc "	maxsd	%a, %a\n" freg a2 freg res
      end
  | "__builtin_fmin", [FR a1; FR a2], [FR res] ->
      if res = a1 then
        fprintf oc "	minsd	%a, %a\n" freg a2 freg res
      else if res = a2 then
        fprintf oc "	minsd	%a, %a\n" freg a1 freg res
      else begin
        fprintf oc "	movapd	%a, %a\n" freg a1 freg res;
        fprintf oc "	minsd	%a, %a\n" freg a2 freg res
      end
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [IR ah; IR al], [IR rh; IR rl] ->
      assert (ah = EDX && al = EAX && rh = EDX && rl = EAX);
      fprintf oc "	negl	%a\n" ireg EAX;
      fprintf oc "	adcl	$0, %a\n" ireg EDX;
      fprintf oc "	negl	%a\n" ireg EDX
  | "__builtin_addl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
      assert (ah = EDX && al = EAX && bh = ECX && bl = EBX && rh = EDX && rl = EAX);
      fprintf oc "	addl	%a, %a\n" ireg EBX ireg EAX;
      fprintf oc "	adcl	%a, %a\n" ireg ECX ireg EDX
  | "__builtin_subl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
      assert (ah = EDX && al = EAX && bh = ECX && bl = EBX && rh = EDX && rl = EAX);
      fprintf oc "	subl	%a, %a\n" ireg EBX ireg EAX;
      fprintf oc "	sbbl	%a, %a\n" ireg ECX ireg EDX
  | "__builtin_mull", [IR a; IR b], [IR rh; IR rl] ->
      assert (a = EAX && b = EDX && rh = EDX && rl = EAX);
      fprintf oc "	mull    %a\n" ireg EDX
  (* Memory accesses *)
  | "__builtin_read16_reversed", [IR a1], [IR res] ->
      fprintf oc "	movzwl	0(%a), %a\n" ireg a1 ireg res;
      fprintf oc "	rolw	$8, %a\n" ireg16 res
  | "__builtin_read32_reversed", [IR a1], [IR res] ->
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
  (* Catch-all *)  
  | _ ->
      invalid_arg ("unrecognized builtin " ^ name)
  end;
  fprintf oc "%s end builtin %s\n" comment name

(* Printing of instructions *)

let float_literals : (int * int64) list ref = ref []
let jumptables : (int * label list) list ref = ref []
let indirect_symbols : StringSet.t ref = ref StringSet.empty

(* Reminder on AT&T syntax: op source, dest *)

let print_instruction oc = function
  (* Moves *)
  | Pmov_rr(rd, r1) ->
      fprintf oc "	movl	%a, %a\n" ireg r1 ireg rd
  | Pmov_ri(rd, n) ->
      fprintf oc "	movl	$%ld, %a\n" (camlint_of_coqint n) ireg rd
  | Pmov_ra(rd, id) ->
      if target = MacOS then begin
        let id = extern_atom id in
        indirect_symbols := StringSet.add id !indirect_symbols;
        fprintf oc "	movl	L%a$non_lazy_ptr, %a\n" raw_symbol id ireg rd
      end else
        fprintf oc "	movl	$%a, %a\n" symbol id ireg rd
  | Pmov_rm(rd, a) ->
      fprintf oc "	movl	%a, %a\n" addressing a ireg rd
  | Pmov_mr(a, r1) ->
      fprintf oc "	movl	%a, %a\n" ireg r1 addressing a
  | Pmovsd_ff(rd, r1) ->
      fprintf oc "	movapd	%a, %a\n" freg r1 freg rd
  | Pmovsd_fi(rd, n) ->
      let b = camlint64_of_coqint (Floats.Float.bits_of_double n) in
      let lbl = new_label() in
      fprintf oc "	movsd	%a, %a %s %.18g\n" label lbl freg rd comment (camlfloat_of_coqfloat n);
      float_literals := (lbl, b) :: !float_literals
  | Pmovsd_fm(rd, a) ->
      fprintf oc "	movsd	%a, %a\n" addressing a freg rd
  | Pmovsd_mf(a, r1) ->
      fprintf oc "	movsd	%a, %a\n" freg r1 addressing a
  | Pfld_f(r1) ->
      fprintf oc "	subl	$8, %%esp\n";
      cfi_adjust oc 8l;
      fprintf oc "	movsd	%a, 0(%%esp)\n" freg r1;
      fprintf oc "	fldl	0(%%esp)\n";
      fprintf oc "	addl	$8, %%esp\n";
      cfi_adjust oc (-8l)
  | Pfld_m(a) ->
      fprintf oc "	fldl	%a\n" addressing a
  | Pfstp_f(rd) ->
      fprintf oc "	subl	$8, %%esp\n";
      cfi_adjust oc 8l;
      fprintf oc "	fstpl	0(%%esp)\n";
      fprintf oc "	movsd	0(%%esp), %a\n" freg rd;
      fprintf oc "	addl	$8, %%esp\n";
      cfi_adjust oc (-8l)
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
      fprintf oc "	cltd\n";
      fprintf oc "	idivl	%a\n" ireg r1
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
  | Pshld_ri(rd, r1, n) ->
      fprintf oc "	shldl	$%a, %a, %a\n" coqint n ireg r1 ireg rd
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
      fprintf oc "	set%s	%a\n" (name_of_condition c) ireg8 rd;
      fprintf oc "	movzbl	%a, %a\n" ireg8 rd ireg rd
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
      cfi_adjust oc sz;
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
      | EF_vload_global(chunk, id, ofs) ->
          print_builtin_vload_global oc chunk id ofs args res
      | EF_vstore_global(chunk, id, ofs) ->
          print_builtin_vstore_global oc chunk id ofs args
      | EF_memcpy(sz, al) ->
          print_builtin_memcpy oc (Int32.to_int (camlint_of_coqint sz))
                                  (Int32.to_int (camlint_of_coqint al)) args
      | EF_annot_val(txt, targ) ->
          print_annot_val oc (extern_atom txt) args res
      | EF_inline_asm txt ->
          fprintf oc "%s begin inline assembly\n" comment;
          fprintf oc "	%s\n" (extern_atom txt);
          fprintf oc "%s end inline assembly\n" comment
      | _ ->
          assert false
      end
  | Pannot(ef, args) ->
      begin match ef with
      | EF_annot(txt, targs) ->
          print_annot_stmt oc (extern_atom txt) targs args
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
  let (text, lit, jmptbl) =
    match C2C.atom_sections name with
    | [t;l;j] -> (t, l, j)
    |    _    -> (Section_text, Section_literal, Section_jumptable) in
  section oc text;
  let alignment =
    match !Clflags.option_falignfunctions with Some n -> n | None -> 16 in
  print_align oc alignment;
  if not (C2C.atom_is_static name) then
    fprintf oc "	.globl %a\n" symbol name;
  fprintf oc "%a:\n" symbol name;
  print_location oc (C2C.atom_location name);
  cfi_startproc oc;
  List.iter (print_instruction oc) code;
  cfi_endproc oc;
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

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
  | Init_int64 n ->
      fprintf oc "	.quad	%Ld\n" (camlint64_of_coqint n)
  | Init_float32 n ->
      fprintf oc "	.long	%ld %s %.18g\n"
	(camlint_of_coqint (Floats.Float.bits_of_single n))
	comment (camlfloat_of_coqfloat n)
  | Init_float64 n ->
      fprintf oc "	.quad	%Ld %s %.18g\n"
	(camlint64_of_coqint (Floats.Float.bits_of_double n))
	comment (camlfloat_of_coqfloat n)
  | Init_space n ->
      if Z.gt n Z.zero then
        fprintf oc "	.space	%s\n" (Z.to_string n)
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

let print_var oc name v =
  match v.gvar_init with
  | [] -> ()
  | _  ->
      let sec =
        match C2C.atom_sections name with
        | [s] -> s
        |  _  -> Section_data true
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

let print_globdef oc (name, gdef) =
  match gdef with
  | Gfun(Internal code) -> print_function oc name code
  | Gfun(External ef) -> ()
  | Gvar v -> print_var oc name v

let print_program oc p =
  need_masks := false;
  indirect_symbols := StringSet.empty;
  Hashtbl.clear filename_num;
  List.iter (print_globdef oc) p.prog_defs;
  if !need_masks then begin
    section oc Section_const;  (* not Section_literal because not 8-bytes *)
    print_align oc 16;
    fprintf oc "%a:	.quad   0x8000000000000000, 0\n"
               raw_symbol "__negd_mask";
    fprintf oc "%a:	.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF\n"
               raw_symbol "__absd_mask"
  end;
  if target = MacOS then begin
    fprintf oc "	.section __IMPORT,__pointers,non_lazy_symbol_pointers\n";
    StringSet.iter
      (fun s ->
        fprintf oc "L%a$non_lazy_ptr:\n" raw_symbol s;
        fprintf oc "	.indirect_symbol %a\n" raw_symbol s;
        fprintf oc "	.long	0\n")
      !indirect_symbols
  end

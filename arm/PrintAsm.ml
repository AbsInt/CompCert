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

(* Printing ARM assembly code in asm syntax *)

open Printf
open Datatypes
open Camlcoq
open Sections
open AST
open Memdata
open Asm

(* On-the-fly label renaming *)

let next_label = ref 100

let new_label() =
  let lbl = !next_label in incr next_label; lbl

let current_function_labels = (Hashtbl.create 39 : (label, int) Hashtbl.t)

let label_for_label lbl =
  try
    Hashtbl.find current_function_labels lbl
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add current_function_labels lbl lbl';
    lbl'

(* Basic printing functions *)

let strip_variadic_suffix name =
  try String.sub name 0 (String.index name '$')
  with Not_found -> name

let print_symb oc symb =
  fprintf oc "%s" (strip_variadic_suffix (extern_atom symb))

let print_label oc lbl =
  fprintf oc ".L%d" (label_for_label lbl)

let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

let comment = "@"

let print_symb_ofs oc (symb, ofs) =
  print_symb oc symb;
  let ofs = camlint_of_coqint ofs in
  if ofs <> 0l then fprintf oc " + %ld" ofs

let int_reg_name = function
  | IR0 -> "r0" | IR1 -> "r1" | IR2 -> "r2" | IR3 -> "r3"
  | IR4 -> "r4" | IR5 -> "r5" | IR6 -> "r6" | IR7 -> "r7"
  | IR8 -> "r8" | IR9 -> "r9" | IR10 -> "r10" | IR11 -> "r11"
  | IR12 -> "r12" | IR13 -> "sp" | IR14 -> "lr"

let float_reg_name = function
  | FR0 -> "d0"  | FR1 -> "d1"  | FR2 -> "d2"  | FR3 -> "d3"
  | FR4 -> "d4"  | FR5 -> "d5"  | FR6 -> "d6"  | FR7 -> "d7"
  | FR8 -> "d8"  | FR9 -> "d9"  | FR10 -> "d10"  | FR11 -> "d11"
  | FR12 -> "d12"  | FR13 -> "d13"  | FR14 -> "d14"  | FR15 -> "d15"

let single_float_reg_index = function
  | FR0 -> 0  | FR1 -> 2  | FR2 -> 4  | FR3 -> 6
  | FR4 -> 8  | FR5 -> 10  | FR6 -> 12  | FR7 -> 14
  | FR8 -> 16  | FR9 -> 18  | FR10 -> 20  | FR11 -> 22
  | FR12 -> 24  | FR13 -> 26  | FR14 -> 28  | FR15 -> 30

let single_float_reg_name = function
  | FR0 -> "s0"  | FR1 -> "s2"  | FR2 -> "s4"  | FR3 -> "s6"
  | FR4 -> "s8"  | FR5 -> "s10"  | FR6 -> "s12"  | FR7 -> "s14"
  | FR8 -> "s16"  | FR9 -> "s18"  | FR10 -> "s20"  | FR11 -> "s22"
  | FR12 -> "s24"  | FR13 -> "s26"  | FR14 -> "s28"  | FR15 -> "s30"

let ireg oc r = output_string oc (int_reg_name r)
let freg oc r = output_string oc (float_reg_name r)
let freg_single oc r = output_string oc (single_float_reg_name r)

let preg oc = function
  | IR r -> ireg oc r
  | FR r -> freg oc r
  | _    -> assert false

let condition_name = function
  | CReq -> "eq"
  | CRne -> "ne"
  | CRhs -> "hs"
  | CRlo -> "lo"
  | CRmi -> "mi"
  | CRpl -> "pl"
  | CRhi -> "hi"
  | CRls -> "ls"
  | CRge -> "ge"
  | CRlt -> "lt"
  | CRgt -> "gt"
  | CRle -> "le"

(* Names of sections *)

let name_of_section_ELF = function
  | Section_text -> ".text"
  | Section_data i | Section_small_data i -> if i then ".data" else ".bss"
  | Section_const | Section_small_const -> ".section	.rodata"
  | Section_string -> ".section	.rodata"
  | Section_literal -> ".text"
  | Section_jumptable -> ".text"
  | Section_user(s, wr, ex) ->
       sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
               s (if wr then "w" else "") (if ex then "x" else "")

let section oc sec =
  fprintf oc "	%s\n" (name_of_section_ELF sec)

(* Record current code position and latest position at which to
   emit float and symbol constants. *)

let currpos = ref 0
let size_constants = ref 0
let max_pos_constants = ref max_int

let distance_to_emit_constants () =
  !max_pos_constants - (!currpos + !size_constants)

(* Associate labels to floating-point constants and to symbols *)

let float_labels = (Hashtbl.create 39 : (int64, int) Hashtbl.t)

let label_float f =
  let bf = camlint64_of_coqint(Floats.Float.bits_of_double f) in
  try
    Hashtbl.find float_labels bf
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add float_labels bf lbl';
    size_constants := !size_constants + 8;
    max_pos_constants := min !max_pos_constants (!currpos + 1024);
    lbl'

let symbol_labels =
  (Hashtbl.create 39 : (ident * Integers.Int.int, int) Hashtbl.t)

let label_symbol id ofs =
  try
    Hashtbl.find symbol_labels (id, ofs)
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add symbol_labels (id, ofs) lbl';
    size_constants := !size_constants + 4;
    max_pos_constants := min !max_pos_constants (!currpos + 4096);
    lbl'

let reset_constants () =
  Hashtbl.clear float_labels;
  Hashtbl.clear symbol_labels;
  size_constants := 0;
  max_pos_constants := max_int

let emit_constants oc =
  Hashtbl.iter
    (fun bf lbl ->
      (* Little-endian floats *)
      let bfhi = Int64.shift_right_logical bf 32
      and bflo = Int64.logand bf 0xFFFF_FFFFL in
      fprintf oc ".L%d:	.word	0x%Lx, 0x%Lx\n" lbl bflo bfhi)
    float_labels;
  Hashtbl.iter
    (fun (id, ofs) lbl ->
      fprintf oc ".L%d:	.word	%a\n"
          lbl print_symb_ofs (id, ofs))
    symbol_labels;
  reset_constants ()

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
  if Configuration.asm_supports_cfi then
    fprintf oc "	.cfi_startproc\n"

let cfi_endproc oc =
  if Configuration.asm_supports_cfi then
    fprintf oc "	.cfi_endproc\n"

let cfi_adjust oc delta =
  if Configuration.asm_supports_cfi then
    fprintf oc "	.cfi_adjust_cfa_offset	%ld\n" delta

let cfi_rel_offset oc reg ofs =
  if Configuration.asm_supports_cfi then
    fprintf oc "	.cfi_rel_offset	%s, %ld\n" reg ofs

(* Built-ins.  They come in two flavors: 
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers; preserve all registers except IR2, IR3, IR12 and FP6.
*)

(* Handling of annotations *)

let re_file_line = Str.regexp "#line:\\(.*\\):\\([1-9][0-9]*\\)$"

let print_annot_stmt oc txt targs args =
  if Str.string_match re_file_line txt 0 then begin
    print_file_line oc (Str.matched_group 1 txt) (Str.matched_group 2 txt)
  end else begin
    fprintf oc "%s annotation: " comment;
    PrintAnnot.print_annot_stmt preg "sp" oc txt targs args
  end

let print_annot_val oc txt args res =
  fprintf oc "%s annotation: " comment;
  PrintAnnot.print_annot_val preg oc txt args;
  match args, res with
  | [IR src], [IR dst] ->
      if dst = src then 0 else (fprintf oc "	mov	%a, %a\n" ireg dst ireg src; 1)
  | [FR src], [FR dst] ->
      if dst = src then 0 else (fprintf oc "	fcpy	%a, %a\n" freg dst freg src; 1)
  | _, _ -> assert false

(* Handling of memcpy *)

(* The ARM has strict alignment constraints. *)

let print_builtin_memcpy_small oc sz al src dst =
  let rec copy ofs sz ninstr =
    if sz >= 4 && al >= 4 then begin
      fprintf oc "	ldr	%a, [%a, #%d]\n" ireg IR14 ireg src ofs;
      fprintf oc "	str	%a, [%a, #%d]\n" ireg IR14 ireg dst ofs;
      copy (ofs + 4) (sz - 4) (ninstr + 2)
    end else if sz >= 2 && al >= 2 then begin
      fprintf oc "	ldrh	%a, [%a, #%d]\n" ireg IR14 ireg src ofs;
      fprintf oc "	strh	%a, [%a, #%d]\n" ireg IR14 ireg dst ofs;
      copy (ofs + 2) (sz - 2) (ninstr + 2)
    end else if sz >= 1 then begin
      fprintf oc "	ldrb	%a, [%a, #%d]\n" ireg IR14 ireg src ofs;
      fprintf oc "	strb	%a, [%a, #%d]\n" ireg IR14 ireg dst ofs;
      copy (ofs + 1) (sz - 1) (ninstr + 2)
    end else
      ninstr in
  copy 0 sz 0

let print_builtin_memcpy_big oc sz al src dst =
  assert (sz >= al);
  assert (sz mod al = 0);
  assert (src = IR2);
  assert (dst = IR3);
  let (load, store, chunksize) =
    if al >= 4 then ("ldr", "str", 4)
    else if al = 2 then ("ldrh", "strh", 2)
    else ("ldrb", "strb", 1) in
  begin match Asmgen.decompose_int
                 (coqint_of_camlint (Int32.of_int (sz / chunksize))) with
  | [] -> assert false
  | hd::tl ->
      fprintf oc "	mov	%a, #%a\n" ireg IR14 coqint hd;
      List.iter
        (fun n ->
           fprintf oc "	orr	%a, %a, #%a\n" ireg IR14 ireg IR14 coqint n)
        tl
  end;
  let lbl = new_label() in
  fprintf oc ".L%d:	%s	%a, [%a], #%d\n" lbl load ireg IR12 ireg src chunksize;
  fprintf oc "	subs	%a, %a, #1\n" ireg IR14 ireg IR14;
  fprintf oc "	%s	%a, [%a], #%d\n" store ireg IR12 ireg dst chunksize;
  fprintf oc "	bne	.L%d\n" lbl;
  8

let print_builtin_memcpy oc sz al args =
  let (dst, src) =
    match args with [IR d; IR s] -> (d, s) | _ -> assert false in
  fprintf oc "%s begin builtin __builtin_memcpy_aligned, size = %d, alignment = %d\n"
          comment sz al;
  let n =
    if sz <= 32
    then print_builtin_memcpy_small oc sz al src dst
    else print_builtin_memcpy_big oc sz al src dst in
  fprintf oc "%s end builtin __builtin_memcpy_aligned\n" comment; n

(* Handling of volatile reads and writes *)

let print_builtin_vload_common oc chunk args res =
  match chunk, args, res with
  | Mint8unsigned, [IR addr], [IR res] ->
      fprintf oc "	ldrb	%a, [%a, #0]\n" ireg res ireg addr; 1
  | Mint8signed, [IR addr], [IR res] ->
      fprintf oc "	ldrsb	%a, [%a, #0]\n" ireg res ireg addr; 1
  | Mint16unsigned, [IR addr], [IR res] ->
      fprintf oc "	ldrh	%a, [%a, #0]\n" ireg res ireg addr; 1
  | Mint16signed, [IR addr], [IR res] ->
      fprintf oc "	ldrsh	%a, [%a, #0]\n" ireg res ireg addr; 1
  | Mint32, [IR addr], [IR res] ->
      fprintf oc "	ldr	%a, [%a, #0]\n" ireg res ireg addr; 1
  | Mint64, [IR addr], [IR res1; IR res2] ->
      if addr <> res2 then begin
        fprintf oc "	ldr	%a, [%a, #0]\n" ireg res2 ireg addr;
        fprintf oc "	ldr	%a, [%a, #4]\n" ireg res1 ireg addr
      end else begin
        fprintf oc "	ldr	%a, [%a, #4]\n" ireg res1 ireg addr;
        fprintf oc "	ldr	%a, [%a, #0]\n" ireg res2 ireg addr
      end; 2
  | Mfloat32, [IR addr], [FR res] ->
      fprintf oc "	flds	%a, [%a, #0]\n" freg_single res ireg addr;
      fprintf oc "	fcvtds	%a, %a\n" freg res freg_single res; 2
  | (Mfloat64 | Mfloat64al32), [IR addr], [FR res] ->
      fprintf oc "	fldd	%a, [%a, #0]\n" freg res ireg addr; 1
  | _ ->
      assert false

let print_builtin_vload oc chunk args res =
  fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
  let n = print_builtin_vload_common oc chunk args res in
  fprintf oc "%s end builtin __builtin_volatile_read\n" comment; n

let print_builtin_vload_global oc chunk id ofs args res =
  fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
  let lbl = label_symbol id ofs in
  fprintf oc "	ldr	%a, .L%d @ %a\n" ireg IR14 lbl print_symb_ofs (id, ofs);
  let n = print_builtin_vload_common oc chunk [IR IR14] res in
  fprintf oc "%s end builtin __builtin_volatile_read\n" comment; n + 1

let print_builtin_vstore_common oc chunk args =
  match chunk, args with
  | (Mint8signed | Mint8unsigned), [IR  addr; IR src] ->
      fprintf oc "	strb	%a, [%a, #0]\n" ireg src ireg addr; 1
  | (Mint16signed | Mint16unsigned), [IR  addr; IR src] ->
      fprintf oc "	strh	%a, [%a, #0]\n" ireg src ireg addr; 1
  | Mint32, [IR  addr; IR src] ->
      fprintf oc "	str	%a, [%a, #0]\n" ireg src ireg addr; 1
  | Mint64, [IR  addr; IR src1; IR src2] ->
      fprintf oc "	str	%a, [%a, #0]\n" ireg src2 ireg addr;
      fprintf oc "	str	%a, [%a, #4]\n" ireg src1 ireg addr; 2
  | Mfloat32, [IR  addr; FR src] ->
      fprintf oc "	fcvtsd	%a, %a\n" freg_single FR6 freg src;
      fprintf oc "	fsts	%a, [%a, #0]\n" freg_single FR6 ireg addr; 2
  | (Mfloat64 | Mfloat64al32), [IR  addr; FR src] ->
      fprintf oc "	fstd	%a, [%a, #0]\n" freg src ireg addr; 1
  | _ ->
      assert false

let print_builtin_vstore oc chunk args =
  fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
  let n = print_builtin_vstore_common oc chunk args in
  fprintf oc "%s end builtin __builtin_volatile_write\n" comment; n

let print_builtin_vstore_global oc chunk id ofs args =
  fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
  let lbl = label_symbol id ofs in
  fprintf oc "	ldr	%a, .L%d @ %a\n" ireg IR14 lbl print_symb_ofs (id, ofs);
  let n = print_builtin_vstore_common oc chunk (IR IR14 :: args) in
  fprintf oc "%s end builtin __builtin_volatile_write\n" comment; n + 1

(* Handling of compiler-inlined builtins *)

let print_builtin_inline oc name args res =
  fprintf oc "%s begin %s\n" comment name;
  let n = match name, args, res with
  (* Integer arithmetic *)
  | ("__builtin_bswap" | "__builtin_bswap32"), [IR a1], [IR res] ->
      fprintf oc "	rev	%a, %a\n" ireg res ireg a1; 1
  | "__builtin_bswap16", [IR a1], [IR res] ->
      fprintf oc "	rev16	%a, %a\n" ireg res ireg a1; 1
  | "__builtin_cntlz", [IR a1], [IR res] ->
      fprintf oc "	clz	%a, %a\n" ireg res ireg a1; 1
  (* Float arithmetic *)
  | "__builtin_fabs", [FR a1], [FR res] ->
      fprintf oc "	fabsd	%a, %a\n" freg res freg a1; 1
  | "__builtin_fsqrt", [FR a1], [FR res] ->
      fprintf oc "	fsqrtd	%a, %a\n" freg res freg a1; 1
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [IR ah; IR al], [IR rh; IR rl] ->
      if rl = ah then begin
        fprintf oc "	rsbs	%a, %a, #0\n" ireg IR14 ireg al;
        fprintf oc "	rsc	%a, %a, #0\n" ireg rh ireg ah;
        fprintf oc "	mov	%a, %a\n" ireg rl ireg IR14; 3
      end else begin
        fprintf oc "	rsbs	%a, %a, #0\n" ireg rl ireg al;
        fprintf oc "	rsc	%a, %a, #0\n" ireg rh ireg ah; 2
      end
  | "__builtin_addl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
      if rl = ah || rl = bh then begin
        fprintf oc "	adds	%a, %a, %a\n" ireg IR14 ireg al ireg bl;
        fprintf oc "	adc	%a, %a, %a\n" ireg rh ireg ah ireg bh;
        fprintf oc "	mov	%a, %a\n" ireg rl ireg IR14; 3
      end else begin
        fprintf oc "	adds	%a, %a, %a\n" ireg rl ireg al ireg bl;
        fprintf oc "	adc	%a, %a, %a\n" ireg rh ireg ah ireg bh; 2
      end
  | "__builtin_subl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
      if rl = ah || rl = bh then begin
        fprintf oc "	subs	%a, %a, %a\n" ireg IR14 ireg al ireg bl;
        fprintf oc "	sbc	%a, %a, %a\n" ireg rh ireg ah ireg bh;
        fprintf oc "	mov	%a, %a\n" ireg rl ireg IR14; 3
      end else begin
        fprintf oc "	subs	%a, %a, %a\n" ireg rl ireg al ireg bl;
        fprintf oc "	sbc	%a, %a, %a\n" ireg rh ireg ah ireg bh; 2
      end
  | "__builtin_mull", [IR a; IR b], [IR rh; IR rl] ->
      if rl = a || rh = a then begin
        fprintf oc "	mov	%a, %a\n" ireg IR14 ireg a;
        fprintf oc "	umull   %a, %a, %a, %a\n" ireg rl ireg rh ireg IR14 ireg b; 2
      end else begin
        fprintf oc "	umull   %a, %a, %a, %a\n" ireg rl ireg rh ireg a ireg b; 1
      end
  (* Memory accesses *)
  | "__builtin_read16_reversed", [IR a1], [IR res] ->
      fprintf oc "	ldrh	%a, [%a, #0]\n" ireg res ireg a1;
      fprintf oc "	rev16	%a, %a\n" ireg res ireg res; 2
  | "__builtin_read32_reversed", [IR a1], [IR res] ->
      fprintf oc "	ldr	%a, [%a, #0]\n" ireg res ireg a1;
      fprintf oc "	rev	%a, %a\n" ireg res ireg res; 2
  | "__builtin_write16_reversed", [IR a1; IR a2], _ ->
      fprintf oc "	rev16	%a, %a\n" ireg IR14 ireg a2;
      fprintf oc "	strh	%a, [%a, #0]\n" ireg IR14 ireg a1; 2
  | "__builtin_write32_reversed", [IR a1; IR a2], _ ->
      fprintf oc "	rev	%a, %a\n" ireg IR14 ireg a2;
      fprintf oc "	str	%a, [%a, #0]\n" ireg IR14 ireg a1; 2
  (* Catch-all *)
  | _ ->
      invalid_arg ("unrecognized builtin " ^ name)
  in
  fprintf oc "%s end %s\n" comment name;
  n

(* Fixing up calling conventions *)

type direction = Incoming | Outgoing

let ireg_param = function
  | 0 -> IR0 | 1 -> IR1 | 2 -> IR2 | 3 -> IR3 | _ -> assert false

let freg_param = function
  | 0 -> FR0 | 1 -> FR1 | 2 -> FR2 | 3 -> FR3 | _ -> assert false

let fixup_double oc dir f i1 i2 =
  match dir with
  | Incoming ->     (* f <- (i1, i2)  *)
      fprintf oc "	fmdrr	%a, %a, %a\n" freg f ireg i1 ireg i2
  | Outgoing ->     (* (i1, i2) <- f *)
      fprintf oc "	fmrrd	%a, %a, %a\n" ireg i1 ireg i2 freg f

let fixup_single oc dir f i =
  match dir with
  | Incoming ->     (* f <- i; f <- double_of_single f *)
      fprintf oc "	fmsr	%a, %a\n" freg_single f ireg i;
      fprintf oc "	fcvtds	%a, %a\n" freg f freg_single f
  | Outgoing ->     (* f <- single_of_double f; i <- f *)
      fprintf oc "	fcvtsd	%a, %a\n" freg_single f freg f;
      fprintf oc "	fmrs	%a, %a\n" ireg i freg_single f

let fixup_conventions oc dir tyl =
  let rec fixup i tyl =
    if i >= 4 then 0 else
      match tyl with
      | [] -> 0
      | Tint :: tyl' ->
          fixup (i+1) tyl'
      | Tlong :: tyl' ->
          fixup (((i + 1) land (-2)) + 2) tyl'
      | Tfloat :: tyl' ->
          let i = (i + 1) land (-2) in
          if i >= 4 then 0 else begin
            fixup_double oc dir (freg_param i) (ireg_param i) (ireg_param (i+1));
            1 + fixup (i+2) tyl'
          end
      | Tsingle :: tyl' ->
          fixup_single oc dir (freg_param i) (ireg_param i);
          2 + fixup (i+1) tyl'
  in fixup 0 tyl

let fixup_arguments oc dir sg =
  fixup_conventions oc dir sg.sig_args

let fixup_result oc dir sg =
  fixup_conventions oc dir (proj_sig_res sg :: [])

(* Printing of instructions *)

let shift_op oc = function
  | SOimm n -> fprintf oc "#%a" coqint n
  | SOreg r -> ireg oc r
  | SOlslimm(r, n) -> fprintf oc "%a, lsl #%a" ireg r coqint n
  | SOlslreg(r, r') -> fprintf oc "%a, lsl %a" ireg r ireg r'
  | SOlsrimm(r, n) -> fprintf oc "%a, lsr #%a" ireg r coqint n
  | SOlsrreg(r, r') -> fprintf oc "%a, lsr %a" ireg r ireg r'
  | SOasrimm(r, n) -> fprintf oc "%a, asr #%a" ireg r coqint n
  | SOasrreg(r, r') -> fprintf oc "%a, asr %a" ireg r ireg r'
  | SOrorimm(r, n) -> fprintf oc "%a, ror #%a" ireg r coqint n
  | SOrorreg(r, r') -> fprintf oc "%a, ror %a" ireg r ireg r'

let shift_addr oc = function
  | SAimm n -> fprintf oc "#%a" coqint n
  | SAreg r -> ireg oc r
  | SAlsl(r, n) -> fprintf oc "%a, lsl #%a" ireg r coqint n
  | SAlsr(r, n) -> fprintf oc "%a, lsr #%a" ireg r coqint n
  | SAasr(r, n) -> fprintf oc "%a, asr #%a" ireg r coqint n
  | SAror(r, n) -> fprintf oc "%a, ror #%a" ireg r coqint n

let print_instruction oc = function
  (* Core instructions *)
  | Padd(r1, r2, so) ->
      fprintf oc "	add	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pand(r1, r2, so) ->
      fprintf oc "	and	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pb lbl ->
      fprintf oc "	b	%a\n" print_label lbl; 1
  | Pbc(bit, lbl) ->
      fprintf oc "	b%s	%a\n" (condition_name bit) print_label lbl; 1
  | Pbsymb(id, sg) ->
      let n = fixup_arguments oc Outgoing sg in
      fprintf oc "	b	%a\n" print_symb id;
      n + 1
  | Pbreg(r, sg) ->
      let n = 
        if r = IR14
        then fixup_result oc Outgoing sg
        else fixup_arguments oc Outgoing sg in
      fprintf oc "	bx	%a\n" ireg r;
      n + 1
  | Pblsymb(id, sg) ->
      let n1 = fixup_arguments oc Outgoing sg in
      fprintf oc "	bl	%a\n" print_symb id;
      let n2 = fixup_result oc Incoming sg in
      n1 + 1 + n2
  | Pblreg(r, sg) ->
      let n1 = fixup_arguments oc Outgoing sg in
      fprintf oc "	blx	%a\n" ireg r;
      let n2 = fixup_result oc Incoming sg in
      n1 + 1 + n2
  | Pbic(r1, r2, so) ->
      fprintf oc "	bic	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pcmp(r1, so) ->
      fprintf oc "	cmp	%a, %a\n" ireg r1 shift_op so; 1
  | Peor(r1, r2, so) ->
      fprintf oc "	eor	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pldr(r1, r2, sa) ->
      fprintf oc "	ldr	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pldrb(r1, r2, sa) ->
      fprintf oc "	ldrb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pldrh(r1, r2, sa) ->
      fprintf oc "	ldrh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pldrsb(r1, r2, sa) ->
      fprintf oc "	ldrsb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pldrsh(r1, r2, sa) ->
      fprintf oc "	ldrsh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pmla(r1, r2, r3, r4) ->
      fprintf oc "	mla	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4; 1
  | Pmov(r1, so) ->
      fprintf oc "	mov	%a, %a\n" ireg r1 shift_op so; 1
  | Pmovc(bit, r1, so) ->
      fprintf oc "	mov%s	%a, %a\n" (condition_name bit) ireg r1 shift_op so; 1
  | Pmul(r1, r2, r3) ->
      fprintf oc "	mul	%a, %a, %a\n" ireg r1 ireg r2 ireg r3; 1
  | Pmvn(r1, so) ->
      fprintf oc "	mvn	%a, %a\n" ireg r1 shift_op so; 1
  | Porr(r1, r2, so) ->
      fprintf oc "	orr	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Prsb(r1, r2, so) ->
      fprintf oc "	rsb	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pstr(r1, r2, sa) ->
      fprintf oc "	str	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa;
      begin match r1, r2, sa with
      | IR14, IR13, SAimm n -> cfi_rel_offset oc "lr" (camlint_of_coqint n)
      | _ -> ()
      end;
      1
  | Pstrb(r1, r2, sa) ->
      fprintf oc "	strb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pstrh(r1, r2, sa) ->
      fprintf oc "	strh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Psdiv(r1, r2, r3) ->
      assert (r1 = IR0 && r2 = IR0 && r3 = IR1);
      fprintf oc "	bl	__aeabi_idiv\n"; 1
  | Psub(r1, r2, so) ->
      fprintf oc "	sub	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pudiv(r1, r2, r3) ->
      assert (r1 = IR0 && r2 = IR0 && r3 = IR1);
      fprintf oc "	bl	__aeabi_uidiv\n"; 1
  (* Floating-point coprocessor instructions *)
  | Pfcpyd(r1, r2) ->
      fprintf oc "	fcpyd	%a, %a\n" freg r1 freg r2; 1
  | Pfabsd(r1, r2) ->
      fprintf oc "	fabsd	%a, %a\n" freg r1 freg r2; 1
  | Pfnegd(r1, r2) ->
      fprintf oc "	fnegd	%a, %a\n" freg r1 freg r2; 1
  | Pfaddd(r1, r2, r3) ->
      fprintf oc "	faddd	%a, %a, %a\n" freg r1 freg r2 freg r3; 1
  | Pfdivd(r1, r2, r3) ->
      fprintf oc "	fdivd	%a, %a, %a\n" freg r1 freg r2 freg r3; 1
  | Pfmuld(r1, r2, r3) ->
      fprintf oc "	fmuld	%a, %a, %a\n" freg r1 freg r2 freg r3; 1
  | Pfsubd(r1, r2, r3) ->
      fprintf oc "	fsubd	%a, %a, %a\n" freg r1 freg r2 freg r3; 1
  | Pflid(r1, f) ->
      (* We could make good use of the fconstd instruction, but it's available
         in VFD v3 and up, not in v1 nor v2 *)
      let lbl = label_float f in
      fprintf oc "	fldd	%a, .L%d @ %.12g\n" freg r1 lbl (camlfloat_of_coqfloat f); 1
  | Pfcmpd(r1, r2) ->
      fprintf oc "	fcmpd	%a, %a\n" freg r1 freg r2;
      fprintf oc "	fmstat\n"; 2
  | Pfcmpzd(r1) ->
      fprintf oc "	fcmpzd	%a\n" freg r1;
      fprintf oc "	fmstat\n"; 2
  | Pfsitod(r1, r2) ->
      fprintf oc "	fmsr	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	fsitod	%a, %a\n" freg r1 freg_single r1; 2
  | Pfuitod(r1, r2) ->
      fprintf oc "	fmsr	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	fuitod	%a, %a\n" freg r1 freg_single r1; 2
  | Pftosizd(r1, r2) ->
      fprintf oc "	ftosizd	%a, %a\n" freg_single FR6 freg r2;
      fprintf oc "	fmrs	%a, %a\n" ireg r1 freg_single FR6; 2
  | Pftouizd(r1, r2) ->
      fprintf oc "	ftouizd	%a, %a\n" freg_single FR6 freg r2;
      fprintf oc "	fmrs	%a, %a\n" ireg r1 freg_single FR6; 2
  | Pfcvtsd(r1, r2) ->
      fprintf oc "	fcvtsd	%a, %a\n" freg_single r1 freg r2;
      fprintf oc "	fcvtds	%a, %a\n" freg r1 freg_single r1; 2
  | Pfldd(r1, r2, n) ->
      fprintf oc "	fldd	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n; 1
  | Pflds(r1, r2, n) ->
      fprintf oc "	flds	%a, [%a, #%a]\n" freg_single r1 ireg r2 coqint n;
      fprintf oc "	fcvtds	%a, %a\n" freg r1 freg_single r1; 2
  | Pfstd(r1, r2, n) ->
      fprintf oc "	fstd	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n; 1
  | Pfsts(r1, r2, n) ->
      fprintf oc "	fcvtsd	%a, %a\n" freg_single FR6 freg r1;
      fprintf oc "	fsts	%a, [%a, #%a]\n" freg_single FR6 ireg r2 coqint n; 2
  (* Pseudo-instructions *)
  | Pallocframe(sz, ofs) ->
      fprintf oc "	mov	r12, sp\n";
      let ninstr = ref 0 in
      List.iter
        (fun n ->
           fprintf oc "	sub	sp, sp, #%a\n" coqint n;
           incr ninstr)
        (Asmgen.decompose_int sz);
      cfi_adjust oc (camlint_of_coqint sz);
      fprintf oc "	str	r12, [sp, #%a]\n" coqint ofs;
      2 + !ninstr
  | Pfreeframe(sz, ofs) ->
      if Asmgen.is_immed_arith sz
      then fprintf oc "	add	sp, sp, #%a\n" coqint sz
      else fprintf oc "	ldr	sp, [sp, #%a]\n" coqint ofs; 1
  | Plabel lbl ->
      fprintf oc "%a:\n" print_label lbl; 0
  | Ploadsymbol(r1, id, ofs) ->
      let lbl = label_symbol id ofs in
      fprintf oc "	ldr	%a, .L%d @ %a\n" 
         ireg r1 lbl print_symb_ofs (id, ofs); 1
  | Pbtbl(r, tbl) ->
      fprintf oc "	mov	r14, %a, lsl #2\n" ireg r;
      fprintf oc "	ldr	pc, [pc, r14]\n";
      fprintf oc "	mov	r0, r0\n"; (* no-op *)
      List.iter
        (fun l -> fprintf oc "	.word	%a\n" print_label l)
        tbl;
      3 + List.length tbl
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
          fprintf oc "%s end inline assembly\n" comment;
          5 (* hoping this is an upper bound...  *)
      | _ ->
          assert false
      end
  | Pannot(ef, args) ->
      begin match ef with
      | EF_annot(txt, targs) ->
          print_annot_stmt oc (extern_atom txt) targs args; 0
      | _ ->
          assert false
      end

let no_fallthrough = function
  | Pb _ -> true
  | Pbsymb _ -> true
  | Pbreg _ -> true
  | _ -> false

let rec print_instructions oc instrs =
  match instrs with
  | [] -> ()
  | i :: il ->
      let n = print_instruction oc i in
      currpos := !currpos + n * 4;
      let d = distance_to_emit_constants() in
      if d < 256 && no_fallthrough i then
        emit_constants oc
      else if d < 16 then begin
        let lbl = new_label() in
        fprintf oc "	b	.L%d\n" lbl;
        emit_constants oc;
        fprintf oc ".L%d:\n" lbl
      end;
      print_instructions oc il

(* Base-2 log of a Caml integer *)

let rec log2 n =
  assert (n > 0);
  if n = 1 then 0 else 1 + log2 (n lsr 1)

let print_function oc name fn =
  Hashtbl.clear current_function_labels;
  reset_constants();
  currpos := 0;
  let text =
    match C2C.atom_sections name with
    | t :: _ -> t
    |   _    -> Section_text in
  section oc text;
  let alignment =
    match !Clflags.option_falignfunctions with Some n -> log2 n | None -> 2 in
  fprintf oc "	.align %d\n" alignment;
  if not (C2C.atom_is_static name) then
    fprintf oc "	.global	%a\n" print_symb name;
  fprintf oc "%a:\n" print_symb name;
  print_location oc (C2C.atom_location name);
  cfi_startproc oc;
  ignore (fixup_arguments oc Incoming fn.fn_sig);
  print_instructions oc fn.fn_code;
  emit_constants oc;
  cfi_endproc oc;
  fprintf oc "	.type	%a, %%function\n" print_symb name;
  fprintf oc "	.size	%a, . - %a\n" print_symb name print_symb name

(* Data *)

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.word	%ld\n" (camlint_of_coqint n)
  | Init_int64 n ->
      fprintf oc "	.quad	%Ld\n" (camlint64_of_coqint n)
  | Init_float32 n ->
      fprintf oc "	.word	0x%lx %s %.15g \n" (camlint_of_coqint (Floats.Float.bits_of_single n))
	comment (camlfloat_of_coqfloat n)
  | Init_float64 n ->
      fprintf oc "	.quad	%Ld %s %.18g\n" (camlint64_of_coqint (Floats.Float.bits_of_double n))
	comment (camlfloat_of_coqfloat n)
  | Init_space n ->
      if Z.gt n Z.zero then
        fprintf oc "	.space	%s\n" (Z.to_string n)
  | Init_addrof(symb, ofs) ->
      fprintf oc "	.word	%a\n" print_symb_ofs (symb, ofs)

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
        | Some a -> log2 a
        | None -> 3 (* 8-alignment is a safe default *)
      in
      section oc sec;
      fprintf oc "	.align	%d\n" align;
      if not (C2C.atom_is_static name) then
        fprintf oc "	.global	%a\n" print_symb name;
      fprintf oc "%a:\n" print_symb name;
      print_init_data oc name v.gvar_init;
      fprintf oc "	.type	%a, %%object\n" print_symb name;
      fprintf oc "	.size	%a, . - %a\n" print_symb name print_symb name

let print_globdef oc (name, gdef) =
  match gdef with
  | Gfun(Internal f) -> print_function oc name f
  | Gfun(External ef) -> ()
  | Gvar v -> print_var oc name v

let print_program oc p =
(*  fprintf oc "	.fpu	vfp\n"; *)
  Hashtbl.clear filename_num;
  List.iter (print_globdef oc) p.prog_defs



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
open Camlcoq
open Sections
open AST
open Asm
open PrintAsmaux
open Fileinfo

(* Module type for the options *)
module type PRINTER_OPTIONS =
sig
  val vfpv3: bool
  val hardware_idiv: bool
end

(* Basic printing functions *)

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

let single_float_reg_name = function
  | FR0 -> "s0"  | FR1 -> "s2"  | FR2 -> "s4"  | FR3 -> "s6"
  | FR4 -> "s8"  | FR5 -> "s10"  | FR6 -> "s12"  | FR7 -> "s14"
  | FR8 -> "s16"  | FR9 -> "s18"  | FR10 -> "s20"  | FR11 -> "s22"
  | FR12 -> "s24"  | FR13 -> "s26"  | FR14 -> "s28"  | FR15 -> "s30"

let single_param_reg_name = function
    | SR0 -> "s0" | SR1 -> "s1" | SR2 -> "s2" | SR3 -> "s3"
    | SR4 -> "s4" | SR5 -> "s5" | SR6 -> "s6" | SR7 -> "s7"
    | SR8 -> "s8" | SR9 -> "s9" | SR10 -> "s10" | SR11 -> "s11"
    | SR12 -> "s12" | SR13 -> "s13" | SR14 -> "s14" | SR15 -> "s15"
    | SR16 -> "s16" | SR17 -> "s1"  | SR18 -> "s18" | SR19 -> "s19"
    | SR20 -> "s20" | SR21 -> "s21" | SR22 -> "s22" | SR23 -> "s23"
    | SR24 -> "s24" | SR25 -> "s25" | SR26 -> "s26" | SR27 -> "s27"
    | SR28 -> "s28" | SR29 -> "s29" | SR30 -> "s30" | SR31 -> "s31"

let preg_annot = function
  | IR r -> int_reg_name r
  | FR r -> float_reg_name r
  | _ -> assert false

let condition_name = function
  | TCeq -> "eq"
  | TCne -> "ne"
  | TChs -> "hs"
  | TClo -> "lo"
  | TCmi -> "mi"
  | TCpl -> "pl"
  | TChi -> "hi"
  | TCls -> "ls"
  | TCge -> "ge"
  | TClt -> "lt"
  | TCgt -> "gt"
  | TCle -> "le"

let neg_condition_name = function
  | TCeq -> "ne"
  | TCne -> "eq"
  | TChs -> "lo"
  | TClo -> "hs"
  | TCmi -> "pl"
  | TCpl -> "mi"
  | TChi -> "ls"
  | TCls -> "hi"
  | TCge -> "lt"
  | TClt -> "ge"
  | TCgt -> "le"
  | TCle -> "gt"


(* Module containing the printing functions *)

module Target (Opt: PRINTER_OPTIONS) : TARGET =
struct
  (* Code generation options. *)

  let literals_in_code = ref true     (* to be turned into a proper option *)

  (* Basic printing functions *)

  let label = elf_label

  let print_label oc lbl = elf_label oc (transl_label lbl)

  let comment = "@"

  let symbol = elf_symbol

  let symbol_offset = elf_symbol_offset

  let ireg oc r = output_string oc (int_reg_name r)
  let freg oc r = output_string oc (float_reg_name r)
  let freg_single oc r = output_string oc (single_float_reg_name r)
  let freg_param_single oc r = output_string oc (single_param_reg_name r)

  let preg oc = function
    | IR r -> ireg oc r
    | FR r -> freg oc r
    | _    -> assert false

  (* In Thumb2 mode, some arithmetic instructions have shorter encodings
     if they carry the "S" flag (update condition flags):
         add   (but not sp + imm)
         and
         asr
         bic
         eor
         lsl
         lsr
         mvn
         orr
         rsb
         sub    (but not sp - imm)
     On the other hand, "mov rd, rs" and "mov rd, #imm" have shorter
     encodings if they do not have the "S" flag.  Moreover, the "S"
     flag is not supported if rd or rs is sp.

     The proof of Asmgen shows that CompCert-generated code behaves the
     same whether flags are updated or not by those instructions.  The
     following printing function adds a "S" suffix if we are in Thumb2
     mode. *)

  let thumbS oc =
    if !Clflags.option_mthumb then output_char oc 's'

  (* Names of sections *)

  let name_of_section = function
    | Section_text -> ".text"
    | Section_data i | Section_small_data i ->
      if i then ".data" else "COMM"
    | Section_const i | Section_small_const i ->
      if i then ".section	.rodata" else "COMM"
    | Section_string -> ".section	.rodata"
    | Section_literal -> ".text"
    | Section_jumptable -> ".text"
    | Section_user(s, wr, ex) ->
      sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
        s (if wr then "w" else "") (if ex then "x" else "")
    | Section_debug_info _ -> ".section	.debug_info,\"\",%progbits"
    | Section_debug_loc -> ".section	.debug_loc,\"\",%progbits"
    | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",%progbits"
    | Section_debug_line _ -> ".section	.debug_line,\"\",%progbits"
    | Section_debug_ranges -> ".section	.debug_ranges,\"\",%progbits"
    | Section_debug_str -> ".section	.debug_str,\"MS\",%progbits,1"
    | Section_ais_annotation ->  sprintf ".section	\"__compcert_ais_annotations\",\"\",%%note"

  let section oc sec =
    fprintf oc "	%s\n" (name_of_section sec)

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

  let float_labels = (Hashtbl.create 39 : (int64, int) Hashtbl.t)
  let float32_labels = (Hashtbl.create 39 : (int32, int) Hashtbl.t)

  let label_float bf =
    try
      Hashtbl.find float_labels bf
    with Not_found ->
      let lbl' = new_label() in
      Hashtbl.add float_labels bf lbl';
      size_constants := !size_constants + 8;
      max_pos_constants := min !max_pos_constants (!currpos + 1024);
      lbl'

  let label_float32 bf =
    try
      Hashtbl.find float32_labels bf
    with Not_found ->
      let lbl' = new_label() in
      Hashtbl.add float32_labels bf lbl';
      size_constants := !size_constants + 4;
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
    Hashtbl.clear float32_labels;
    Hashtbl.clear symbol_labels;
    size_constants := 0;
    max_pos_constants := max_int

  let emit_constants oc =
    fprintf oc "	.balign	4\n";
    Hashtbl.iter
      (fun bf lbl ->
         (* Big or little-endian floats *)
         let bfhi = Int64.shift_right_logical bf 32
         and bflo = Int64.logand bf 0xFFFF_FFFFL in
         if Archi.big_endian
         then fprintf oc ".L%d:	.word	0x%Lx, 0x%Lx\n" lbl bfhi bflo
         else fprintf oc ".L%d:	.word	0x%Lx, 0x%Lx\n" lbl bflo bfhi)
      float_labels;
    Hashtbl.iter
      (fun bf lbl ->
         fprintf oc ".L%d:	.word	0x%lx\n" lbl bf)
      float32_labels;
    Hashtbl.iter
      (fun (id, ofs) lbl ->
         fprintf oc ".L%d:	.word	%a\n"
           lbl symbol_offset (id, ofs))
      symbol_labels;
    reset_constants ()

  (* Generate code to load the address of id + ofs in register r *)

  let loadsymbol oc r id ofs =
    let o = camlint_of_coqint ofs in
    if o >= -32768l && o <= 32767l && !Clflags.option_mthumb then begin
      fprintf oc "	movw	%a, #:lower16:%a\n"
        ireg r symbol_offset (id, ofs);
      fprintf oc "	movt	%a, #:upper16:%a\n"
        ireg r symbol_offset (id, ofs); 2
    end else begin
      let lbl = label_symbol id ofs in
      fprintf oc "	ldr	%a, .L%d @ %a\n"
        ireg r lbl symbol_offset (id, ofs); 1
    end

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


  (* Emit .file / .loc debugging directives *)

  let print_file_line oc file line =
    print_file_line oc comment file line


  (* Printing of instructions *)

  let shift_op oc = function
    | SOimm n -> fprintf oc "#%a" coqint n
    | SOreg r -> ireg oc r
    | SOlsl(r, n) -> fprintf oc "%a, lsl #%a" ireg r coqint n
    | SOlsr(r, n) -> fprintf oc "%a, lsr #%a" ireg r coqint n
    | SOasr(r, n) -> fprintf oc "%a, asr #%a" ireg r coqint n
    | SOror(r, n) -> fprintf oc "%a, ror #%a" ireg r coqint n

  let print_instruction oc = function
    (* Core instructions *)
    | Padc (r1,r2,so) ->
      fprintf oc "	adc	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
    | Padd(r1, r2, so) ->
      fprintf oc "	add%s	%a, %a, %a\n"
        (if !Clflags.option_mthumb && r2 <> IR14 then "s" else "")
        ireg r1 ireg r2 shift_op so; 1
    | Padds (r1,r2,so) ->
      fprintf oc "	adds	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
    | Pand(r1, r2, so) ->
      fprintf oc "	and%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so; 1
    | Pasr(r1, r2, r3) ->
      fprintf oc "	asr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 ireg r3; 1
    | Pb lbl ->
      fprintf oc "	b	%a\n" print_label lbl; 1
    | Pbc(bit, lbl) ->
      fprintf oc "	b%s	%a\n" (condition_name bit) print_label lbl; 1
    | Pbne lbl ->
      fprintf oc "	bne	%a\n" print_label lbl; 1
    | Pbsymb(id, sg) ->
      fprintf oc "	b	%a\n" symbol id; 1
    | Pbreg(r, sg) ->
      fprintf oc "	bx	%a\n" ireg r; 1
    | Pblsymb(id, sg) ->
      fprintf oc "	bl	%a\n" symbol id; 1
    | Pblreg(r, sg) ->
      fprintf oc "	blx	%a\n" ireg r; 1
    | Pbic(r1, r2, so) ->
      fprintf oc "	bic%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so; 1
    | Pclz (r1,r2) ->
      fprintf oc "	clz	%a, %a\n" ireg r1 ireg r2; 1
    | Pcmp(r1, so) ->
      fprintf oc "	cmp	%a, %a\n" ireg r1 shift_op so; 1
    | Pdmb ->
      fprintf oc "	dmb\n"; 1
    | Pdsb ->
      fprintf oc "	dsb\n"; 1
    |  Peor(r1, r2, so) ->
      fprintf oc "	eor%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so; 1
    | Pisb ->
      fprintf oc "	isb\n"; 1
    | Pldr(r1, r2, sa) | Pldr_a(r1, r2, sa) ->
      fprintf oc "	ldr	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa; 1
    | Pldrb(r1, r2, sa) ->
      fprintf oc "	ldrb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa; 1
    | Pldrh(r1, r2, sa) ->
      fprintf oc "	ldrh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa; 1
    | Pldr_p(r1, r2, sa)  ->
      fprintf oc "	ldr	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa; 1
    | Pldrb_p(r1, r2, sa) ->
      fprintf oc "	ldrb	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa; 1
    | Pldrh_p(r1, r2, sa) ->
      fprintf oc "	ldrh	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa; 1
    | Pldrsb(r1, r2, sa) ->
      fprintf oc "	ldrsb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa; 1
    | Pldrsh(r1, r2, sa) ->
      fprintf oc "	ldrsh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa; 1
    | Plsl(r1, r2, r3) ->
      fprintf oc "	lsl%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 ireg r3; 1
    | Plsr(r1, r2, r3) ->
      fprintf oc "	lsr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 ireg r3; 1
    | Pmla(r1, r2, r3, r4) ->
      fprintf oc "	mla	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4; 1
    | Pmov(r1, (SOimm _ | SOreg _ as so)) ->
      (* No S flag even in Thumb2 mode *)
      fprintf oc "	mov	%a, %a\n" ireg r1 shift_op so; 1
    | Pmov(r1, so) ->
      fprintf oc "	mov%t	%a, %a\n" thumbS ireg r1 shift_op so; 1
    | Pmovw(r1, n) ->
      fprintf oc "	movw	%a, #%a\n" ireg r1 coqint n; 1
    | Pmovt(r1, n) ->
      fprintf oc "	movt	%a, #%a\n" ireg r1 coqint n; 1
    | Pmul(r1, r2, r3) ->
      fprintf oc "	mul	%a, %a, %a\n" ireg r1 ireg r2 ireg r3; 1
    | Pmvn(r1, so) ->
      fprintf oc "	mvn%t	%a, %a\n" thumbS ireg r1 shift_op so; 1
    | Porr(r1, r2, so) ->
      fprintf oc "	orr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so; 1
    | Prev (r1,r2) ->
      fprintf oc "	rev	%a, %a\n" ireg r1 ireg r2; 1
    | Prev16 (r1,r2) ->
      fprintf oc "	rev16	%a, %a\n" ireg r1 ireg r2; 1
    | Prsb(r1, r2, so) ->
      fprintf oc "	rsb%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so; 1
    | Prsbs(r1, r2, so) ->
      fprintf oc "	rsbs	%a, %a, %a\n"
        ireg r1 ireg r2 shift_op so; 1
    | Prsc (r1,r2,so) ->
      fprintf oc "	rsc	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
    | Pfsqrt (f1,f2) ->
      fprintf oc "	vsqrt.f64 %a, %a\n" freg f1 freg f2; 1
    | Psbc (r1,r2,sa) ->
      fprintf oc "	sbc	%a, %a, %a\n" ireg r1 ireg r2 shift_op sa; 1
    | Pstr(r1, r2, sa) | Pstr_a(r1, r2, sa) ->
      fprintf oc "	str	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa; 1
    | Pstrb(r1, r2, sa) ->
      fprintf oc "	strb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa; 1
    | Pstrh(r1, r2, sa) ->
      fprintf oc "	strh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa; 1
    | Pstr_p(r1, r2, sa) ->
      fprintf oc "	str	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa; 1
    | Pstrb_p(r1, r2, sa) ->
      fprintf oc "	strb	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa; 1
    | Pstrh_p(r1, r2, sa) ->
      fprintf oc "	strh	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa; 1
    | Psdiv ->
      if Opt.hardware_idiv then begin
        fprintf oc "	sdiv	r0, r0, r1\n"; 1
      end else begin
        fprintf oc "	bl	__aeabi_idiv\n"; 1
      end
    | Psbfx(r1, r2, lsb, sz) ->
      fprintf oc "	sbfx	%a, %a, #%a, #%a\n" ireg r1 ireg r2 coqint lsb coqint sz; 1
    | Psmull(r1, r2, r3, r4) ->
      fprintf oc "	smull	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4; 1
    | Psub(r1, r2, so) ->
      fprintf oc "	sub%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so; 1
    | Psubs(r1, r2, so) ->
      fprintf oc "	subs	%a, %a, %a\n"
        ireg r1 ireg r2 shift_op so; 1
    | Pudiv ->
      if Opt.hardware_idiv then begin
        fprintf oc "	udiv	r0, r0, r1\n"; 1
      end else begin
        fprintf oc "	bl	__aeabi_uidiv\n"; 1
      end
    | Pumull(r1, r2, r3, r4) ->
      fprintf oc "	umull	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4; 1
    (* Floating-point VFD instructions *)
    | Pfcpyd(r1, r2) ->
      fprintf oc "	vmov.f64 %a, %a\n" freg r1 freg r2; 1
    | Pfabsd(r1, r2) ->
      fprintf oc "	vabs.f64 %a, %a\n" freg r1 freg r2; 1
    | Pfnegd(r1, r2) ->
      fprintf oc "	vneg.f64 %a, %a\n" freg r1 freg r2; 1
    | Pfaddd(r1, r2, r3) ->
      fprintf oc "	vadd.f64 %a, %a, %a\n" freg r1 freg r2 freg r3; 1
    | Pfdivd(r1, r2, r3) ->
      fprintf oc "	vdiv.f64 %a, %a, %a\n" freg r1 freg r2 freg r3; 1
    | Pfmuld(r1, r2, r3) ->
      fprintf oc "	vmul.f64 %a, %a, %a\n" freg r1 freg r2 freg r3; 1
    | Pfsubd(r1, r2, r3) ->
      fprintf oc "	vsub.f64 %a, %a, %a\n" freg r1 freg r2 freg r3; 1
    | Pflid(r1, f) ->
      let f = camlint64_of_coqint(Floats.Float.to_bits f) in
      if Opt.vfpv3 && is_immediate_float64 f then begin
        fprintf oc "	vmov.f64 %a, #%.15F\n"
          freg r1 (Int64.float_of_bits f); 1
          (* immediate floats have at most 4 bits of fraction, so they
             should print exactly with OCaml's F decimal format. *)
      end else if !literals_in_code then begin
        let lbl = label_float f in
        fprintf oc "	vldr	%a, .L%d @ %.12g\n"
          freg r1 lbl (Int64.float_of_bits f); 1
      end else begin
        let lbl = label_float f in
        fprintf oc "	movw	r14, #:lower16:.L%d\n" lbl;
        fprintf oc "	movt	r14, #:upper16:.L%d\n" lbl;
        fprintf oc "	vldr	%a, [r14, #0] @ %.12g\n"
          freg r1 (Int64.float_of_bits f); 3
      end
    | Pfcmpd(r1, r2) ->
      fprintf oc "	vcmp.f64 %a, %a\n" freg r1 freg r2;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"; 2
    | Pfcmpzd(r1) ->
      fprintf oc "	vcmp.f64 %a, #0\n" freg r1;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"; 2
    | Pfsitod(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	vcvt.f64.s32 %a, %a\n" freg r1 freg_single r1; 2
    | Pfuitod(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	vcvt.f64.u32 %a, %a\n" freg r1 freg_single r1; 2
    | Pftosizd(r1, r2) ->
      fprintf oc "	vcvt.s32.f64 %a, %a\n" freg_single FR6 freg r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single FR6; 2
    | Pftouizd(r1, r2) ->
      fprintf oc "	vcvt.u32.f64 %a, %a\n" freg_single FR6 freg r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single FR6; 2
    | Pfabss(r1, r2) ->
      fprintf oc "	vabs.f32 %a, %a\n" freg_single r1 freg_single r2; 1
    | Pfnegs(r1, r2) ->
      fprintf oc "	vneg.f32 %a, %a\n" freg_single r1 freg_single r2; 1
    | Pfadds(r1, r2, r3) ->
      fprintf oc "	vadd.f32 %a, %a, %a\n" freg_single r1 freg_single r2 freg_single r3; 1
    | Pfdivs(r1, r2, r3) ->
      fprintf oc "	vdiv.f32 %a, %a, %a\n" freg_single r1 freg_single r2 freg_single r3; 1
    | Pfmuls(r1, r2, r3) ->
      fprintf oc "	vmul.f32 %a, %a, %a\n" freg_single r1 freg_single r2 freg_single r3; 1
    | Ppush rl ->
      let first = ref true in
      let sep () = if !first then first := false else output_string oc ", " in
      fprintf oc "	push	{%a}\n"  (fun oc rl -> List.iter (fun ir -> sep (); ireg oc ir) rl) rl; ;1
    | Pfsubs(r1, r2, r3) ->
      fprintf oc "	vsub.f32 %a, %a, %a\n" freg_single r1 freg_single r2 freg_single r3; 1
    | Pflis(r1, f) ->
      let f = camlint_of_coqint(Floats.Float32.to_bits f) in
      if Opt.vfpv3 && is_immediate_float32 f then begin
        fprintf oc "	vmov.f32 %a, #%.15F\n"
          freg_single r1 (Int32.float_of_bits f); 1
          (* immediate floats have at most 4 bits of fraction, so they
             should print exactly with OCaml's F decimal format. *)
      end else if !literals_in_code then begin
        let lbl = label_float32 f in
        fprintf oc "	vldr	%a, .L%d @ %.12g\n"
          freg_single r1 lbl (Int32.float_of_bits f); 1
      end else begin
        fprintf oc "	movw	r14, #%ld\n" (Int32.logand f 0xFFFFl);
        fprintf oc "	movt	r14, #%ld\n" (Int32.shift_right_logical f 16);
        fprintf oc "	vmov	%a, r14 @ %.12g\n"
          freg_single r1 (Int32.float_of_bits f); 3
      end
    | Pfcmps(r1, r2) ->
      fprintf oc "	vcmp.f32 %a, %a\n" freg_single r1 freg_single r2;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"; 2
    | Pfcmpzs(r1) ->
      fprintf oc "	vcmp.f32 %a, #0\n" freg_single r1;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"; 2
    | Pfsitos(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	vcvt.f32.s32 %a, %a\n" freg_single r1 freg_single r1; 2
    | Pfuitos(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	vcvt.f32.u32 %a, %a\n" freg_single r1 freg_single r1; 2
    | Pftosizs(r1, r2) ->
      fprintf oc "	vcvt.s32.f32 %a, %a\n" freg_single FR6 freg_single r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single FR6; 2
    | Pftouizs(r1, r2) ->
      fprintf oc "	vcvt.u32.f32 %a, %a\n" freg_single FR6 freg_single r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single FR6; 2
    | Pfcvtsd(r1, r2) ->
      fprintf oc "	vcvt.f32.f64 %a, %a\n" freg_single r1 freg r2; 1
    | Pfcvtds(r1, r2) ->
      fprintf oc "	vcvt.f64.f32 %a, %a\n" freg r1 freg_single r2; 1
    | Pfldd(r1, r2, n) | Pfldd_a(r1, r2, n) ->
      fprintf oc "	vldr	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n; 1
    | Pflds(r1, r2, n) ->
      fprintf oc "	vldr	%a, [%a, #%a]\n" freg_single r1 ireg r2 coqint n; 1
    | Pfstd(r1, r2, n) | Pfstd_a(r1, r2, n) ->
      fprintf oc "	vstr	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n; 1
    | Pfsts(r1, r2, n) ->
      fprintf oc "	vstr	%a, [%a, #%a]\n" freg_single r1 ireg r2 coqint n; 1
    (* Pseudo-instructions *)
    | Pallocframe(sz, ofs) ->
      assert false
    | Pfreeframe(sz, ofs) ->
      assert false
    | Plabel lbl ->
      fprintf oc "%a:\n" print_label lbl; 0
    | Ploadsymbol(r1, id, ofs) ->
      loadsymbol oc r1 id ofs
    | Pmovite(cond, r1, ifso, ifnot) ->
      fprintf oc "	ite	%s\n" (condition_name cond);
      fprintf oc "	mov%s	%a, %a\n"
        (condition_name cond) ireg r1 shift_op ifso;
      fprintf oc "	mov%s	%a, %a\n"
        (neg_condition_name cond) ireg r1 shift_op ifnot; 2
    | Pbtbl(r, tbl) ->
      if !Clflags.option_mthumb then begin
        fprintf oc "	lsl	r14, %a, #2\n" ireg r;
        fprintf oc "	add	pc, r14\n";   (* 16-bit encoding *)
        fprintf oc "	nop\n";               (* 16-bit encoding *)
        List.iter
          (fun l -> fprintf oc "	b.w	%a\n" print_label l)
          tbl;
        2 + List.length tbl
      end else begin
        fprintf oc "	add	pc, pc, %a, lsl #2\n" ireg r;
        fprintf oc "	nop\n";
        List.iter
          (fun l -> fprintf oc "	b	%a\n" print_label l)
          tbl;
        2 + List.length tbl
      end
    | Pbuiltin(ef, args, res) ->
      begin match ef with
        | EF_annot(kind,txt, targs) ->
          let annot =
            begin match (P.to_int kind) with
              | 1 -> annot_text preg_annot "sp" (camlstring_of_coqstring txt) args
              | 2 -> let lbl = new_label () in
                fprintf oc "%a: " label lbl;
                ais_annot_text lbl preg_annot "sp" (camlstring_of_coqstring txt) args
              | _ -> assert false
            end in
          fprintf oc "%s annotation: %S\n" comment annot;
          0
        | EF_debug(kind, txt, targs) ->
          print_debug_info comment print_file_line preg_annot "sp" oc
            (P.to_int kind) (extern_atom txt) args;
          0
        | EF_inline_asm(txt, sg, clob) ->
          fprintf oc "%s begin inline assembly\n\t" comment;
          print_inline_asm preg oc (camlstring_of_coqstring txt) sg args res;
          fprintf oc "%s end inline assembly\n" comment;
          256 (* Better be safe than sorry  *)
        | _ ->
          assert false
      end
    | Pcfi_adjust sz -> cfi_adjust oc (camlint_of_coqint sz); 0
    | Pcfi_rel_offset ofs -> cfi_rel_offset oc "lr" (camlint_of_coqint ofs); 0
    (* Fixup instructions for calling conventions *)
    | Pfcpy_fs(r1, r2) ->
      fprintf oc "	vmov.f32	%a, %a\n" freg_single r1 freg_param_single r2; 1
    | Pfcpy_sf(r1, r2) ->
      fprintf oc "	vmov.f32	%a, %a\n" freg_param_single r1 freg_single r2; 1
    | Pfcpy_fii (r1, r2, r3) ->
      fprintf oc "	vmov	%a, %a, %a\n" freg r1 ireg r2 ireg r3; 1
    | Pfcpy_fi (r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2; 1
    | Pfcpy_iif (r1, r2, r3) ->
      fprintf oc "	vmov	%a, %a, %a\n" ireg r1 ireg r2 freg r3; 1
    |  Pfcpy_if (r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single r2; 1


  let no_fallthrough = function
    | Pb _ -> true
    | Pbsymb _ -> true
    | Pbreg _ -> true
    | _ -> false

  let estimate_size = function
    | Pbtbl (_,tbl) ->
      let len = List.length tbl in
      let add =if !Clflags.option_mthumb then
        3
      else
        2 in
      (len + add) * 4
    | Pbuiltin (EF_inline_asm _,_,_) -> 1024 (* Better be safe than sorry *)
    | _ -> 12


  let rec print_instructions oc no_fall instrs =
    match instrs with
    | [] -> ()
    | i :: il ->
      let d = distance_to_emit_constants() - estimate_size i in
      if d < 256 && no_fall then
        emit_constants oc
      else if d < 16 then begin
        let lbl = new_label() in
        fprintf oc "	b	.L%d\n" lbl;
        emit_constants oc;
        fprintf oc ".L%d:\n" lbl
      end;
      let n = print_instruction oc i in
      currpos := !currpos + n * 4;
      print_instructions oc (no_fallthrough i) il

  let get_section_names name =
    let (text, lit) =
      match C2C.atom_sections name with
      | t :: l :: _ -> (t, l)
      | _    -> (Section_text, Section_literal) in
    text,lit,Section_jumptable

  let print_align oc alignment =
    fprintf oc "	.balign %d\n" alignment

  let print_jumptable _ _ = ()

  let cfi_startproc = cfi_startproc

  let cfi_endproc = cfi_endproc

  let print_optional_fun_info oc =
    if !Clflags.option_mthumb then
      fprintf oc "	.thumb_func\n"

  let print_fun_info oc name =
    fprintf oc "	.type	%a, %%function\n" symbol name;
    fprintf oc "	.size	%a, . - %a\n" symbol name symbol name

  let print_var_info oc name =
    fprintf oc "	.type	%a, %%object\n" symbol name;
    fprintf oc "	.size	%a, . - %a\n" symbol name symbol name

  let print_comm_symb oc sz name align =
    if C2C.atom_is_static name then
      fprintf oc "	.local	%a\n" symbol name;
    fprintf oc "	.comm	%a, %s, %d\n"
      symbol name
      (Z.to_string sz)
      align

  let print_instructions oc fn =
    current_function_sig := fn.fn_sig;
    print_instructions oc false fn.fn_code;
    if !literals_in_code then emit_constants oc

  let emit_constants oc lit =
    if not !literals_in_code && !size_constants > 0 then begin
      section oc lit;
      emit_constants oc
    end

  (* Data *)

  let print_prologue oc =
    fprintf oc "	.syntax	unified\n";
    fprintf oc "	.arch	%s\n"
      (match Configuration.model with
       | "armv6"   -> "armv6"
       | "armv6t2" -> "armv6t2"
       | "armv7a"  -> "armv7-a"
       | "armv7r"  -> "armv7-r"
       | "armv7m"  -> "armv7-m"
       | _ -> "armv7");
    fprintf oc "	.fpu	%s\n"
      (if Opt.vfpv3 then "vfpv3-d16" else "vfpv2");
    fprintf oc "	.%s\n" (if !Clflags.option_mthumb then "thumb" else "arm");
    if !Clflags.option_g then begin
      section oc Section_text;
      cfi_section oc
    end

  let print_epilogue oc =
    if !Clflags.option_g then begin
      Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
      section oc Section_text;
    end

  let default_falignment = 4

  let address = if Archi.ptr64 then ".quad" else ".4byte"
end

let sel_target () =
  let module S : PRINTER_OPTIONS = struct

    let vfpv3 = Configuration.model >= "armv7"

    let hardware_idiv  =
      match  Configuration.model with
      | "armv7r" | "armv7m" -> !Clflags.option_mthumb
      | _ -> false

  end in
  (module Target(S):TARGET)

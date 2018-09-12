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

  (* Emit .file / .loc debugging directives *)

  let print_file_line oc file line =
    print_file_line oc comment file line


  (* Printing of instructions *)

  let print_literal64 oc n lbl =
    let bfhi = Int64.shift_right_logical n 32
    and bflo = Int64.logand n 0xFFFF_FFFFL in
    if Archi.big_endian
    then fprintf oc ".L%d:	.word	0x%Lx, 0x%Lx\n" lbl bfhi bflo
    else fprintf oc ".L%d:	.word	0x%Lx, 0x%Lx\n" lbl bflo bfhi

  let print_constants oc = function
    | Float32 (lbl,c) ->
      let c = camlint_of_coqint (Floats.Float32.to_bits c) in
      fprintf oc "%a:	.word	0x%lx\n"  print_label lbl c
    | Float64 (lbl,bf) ->
      let bf = camlint64_of_coqint (Floats.Float.to_bits  bf)
      and lbl = transl_label lbl in
      print_literal64 oc bf lbl
    | Symbol (lbl,id,ofs) ->
      fprintf oc "%a:	.word	%a\n" print_label lbl symbol_offset (id, ofs)

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
      fprintf oc "	adc	%a, %a, %a\n" ireg r1 ireg r2 shift_op so
    | Padd(r1, r2, so) ->
      fprintf oc "	add%s	%a, %a, %a\n"
        (if !Clflags.option_mthumb && r2 <> IR14 then "s" else "")
        ireg r1 ireg r2 shift_op so
    | Padds (r1,r2,so) ->
      fprintf oc "	adds	%a, %a, %a\n" ireg r1 ireg r2 shift_op so
    | Pand(r1, r2, so) ->
      fprintf oc "	and%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Pasr(r1, r2, r3) ->
      fprintf oc "	asr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 ireg r3
    | Pb lbl ->
      fprintf oc "	b	%a\n" print_label lbl
    | Pbc(bit, lbl) ->
      fprintf oc "	b%s	%a\n" (condition_name bit) print_label lbl
    | Pbne lbl ->
      fprintf oc "	bne	%a\n" print_label lbl
    | Pbsymb(id, sg) ->
      fprintf oc "	b	%a\n" symbol id
    | Pbreg(r, sg) ->
      fprintf oc "	bx	%a\n" ireg r
    | Pblsymb(id, sg) ->
      fprintf oc "	bl	%a\n" symbol id
    | Pblreg(r, sg) ->
      fprintf oc "	blx	%a\n" ireg r
    | Pbic(r1, r2, so) ->
      fprintf oc "	bic%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Pclz (r1,r2) ->
      fprintf oc "	clz	%a, %a\n" ireg r1 ireg r2
    | Pcmp(r1, so) ->
      fprintf oc "	cmp	%a, %a\n" ireg r1 shift_op so
    | Pcmn(r1, so) ->
      fprintf oc "	cmn	%a, %a\n" ireg r1 shift_op so
    | Pdmb ->
      fprintf oc "	dmb\n"
    | Pdsb ->
      fprintf oc "	dsb\n"
    |  Peor(r1, r2, so) ->
      fprintf oc "	eor%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Pisb ->
      fprintf oc "	isb\n"
    | Pldr(r1, r2, sa) | Pldr_a(r1, r2, sa) ->
      fprintf oc "	ldr	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pldrb(r1, r2, sa) ->
      fprintf oc "	ldrb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pldrh(r1, r2, sa) ->
      fprintf oc "	ldrh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pldr_p(r1, r2, sa)  ->
      fprintf oc "	ldr	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pldrb_p(r1, r2, sa) ->
      fprintf oc "	ldrb	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pldrh_p(r1, r2, sa) ->
      fprintf oc "	ldrh	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pldrsb(r1, r2, sa) ->
      fprintf oc "	ldrsb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pldrsh(r1, r2, sa) ->
      fprintf oc "	ldrsh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Plsl(r1, r2, r3) ->
      fprintf oc "	lsl%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 ireg r3
    | Plsr(r1, r2, r3) ->
      fprintf oc "	lsr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 ireg r3
    | Pmla(r1, r2, r3, r4) ->
      fprintf oc "	mla	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4
    | Pmov(r1, (SOimm _ | SOreg _ as so)) ->
      (* No S flag even in Thumb2 mode *)
      fprintf oc "	mov	%a, %a\n" ireg r1 shift_op so
    | Pmov(r1, so) ->
      fprintf oc "	mov%t	%a, %a\n" thumbS ireg r1 shift_op so
    | Pmovw(r1, n) ->
      fprintf oc "	movw	%a, #%a\n" ireg r1 coqint n
    | Pmovt(r1, n) ->
      fprintf oc "	movt	%a, #%a\n" ireg r1 coqint n
    | Pmul(r1, r2, r3) ->
      fprintf oc "	mul	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
    | Pmvn(r1, so) ->
      fprintf oc "	mvn%t	%a, %a\n" thumbS ireg r1 shift_op so
    | Porr(r1, r2, so) ->
      fprintf oc "	orr%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Prev (r1,r2) ->
      fprintf oc "	rev	%a, %a\n" ireg r1 ireg r2
    | Prev16 (r1,r2) ->
      fprintf oc "	rev16	%a, %a\n" ireg r1 ireg r2
    | Prsb(r1, r2, so) ->
      fprintf oc "	rsb%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Prsbs(r1, r2, so) ->
      fprintf oc "	rsbs	%a, %a, %a\n"
        ireg r1 ireg r2 shift_op so
    | Prsc (r1,r2,so) ->
      fprintf oc "	rsc	%a, %a, %a\n" ireg r1 ireg r2 shift_op so
    | Pfsqrt (f1,f2) ->
      fprintf oc "	vsqrt.f64 %a, %a\n" freg f1 freg f2
    | Psbc (r1,r2,sa) ->
      fprintf oc "	sbc	%a, %a, %a\n" ireg r1 ireg r2 shift_op sa
    | Pnop ->
      fprintf oc "	nop\n"
    | Pstr(r1, r2, sa) | Pstr_a(r1, r2, sa) ->
      fprintf oc "	str	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pstrb(r1, r2, sa) ->
      fprintf oc "	strb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pstrh(r1, r2, sa) ->
      fprintf oc "	strh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_op sa
    | Pstr_p(r1, r2, sa) ->
      fprintf oc "	str	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pstrb_p(r1, r2, sa) ->
      fprintf oc "	strb	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Pstrh_p(r1, r2, sa) ->
      fprintf oc "	strh	%a, [%a], %a\n" ireg r1 ireg r2 shift_op sa
    | Psdiv ->
      if Opt.hardware_idiv then
        fprintf oc "	sdiv	r0, r0, r1\n"
      else
        fprintf oc "	bl	__aeabi_idiv\n"
    | Psbfx(r1, r2, lsb, sz) ->
      fprintf oc "	sbfx	%a, %a, #%a, #%a\n" ireg r1 ireg r2 coqint lsb coqint sz
    | Psmull(r1, r2, r3, r4) ->
      fprintf oc "	smull	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4
    | Psub(r1, r2, so) ->
      fprintf oc "	sub%t	%a, %a, %a\n"
        thumbS ireg r1 ireg r2 shift_op so
    | Psubs(r1, r2, so) ->
      fprintf oc "	subs	%a, %a, %a\n"
        ireg r1 ireg r2 shift_op so
    | Pudiv ->
      if Opt.hardware_idiv then
        fprintf oc "	udiv	r0, r0, r1\n"
      else
         fprintf oc "	bl	__aeabi_uidiv\n"
    | Pumull(r1, r2, r3, r4) ->
      fprintf oc "	umull	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 ireg r4
    (* Floating-point VFD instructions *)
    | Pfcpyd(r1, r2) ->
      fprintf oc "	vmov.f64 %a, %a\n" freg r1 freg r2
    | Pfabsd(r1, r2) ->
      fprintf oc "	vabs.f64 %a, %a\n" freg r1 freg r2
    | Pfnegd(r1, r2) ->
      fprintf oc "	vneg.f64 %a, %a\n" freg r1 freg r2
    | Pfaddd(r1, r2, r3) ->
      fprintf oc "	vadd.f64 %a, %a, %a\n" freg r1 freg r2 freg r3
    | Pfdivd(r1, r2, r3) ->
      fprintf oc "	vdiv.f64 %a, %a, %a\n" freg r1 freg r2 freg r3
    | Pfmuld(r1, r2, r3) ->
      fprintf oc "	vmul.f64 %a, %a, %a\n" freg r1 freg r2 freg r3
    | Pfsubd(r1, r2, r3) ->
      fprintf oc "	vsub.f64 %a, %a, %a\n" freg r1 freg r2 freg r3
    | Pflid(r1, f) ->
      let f = camlint64_of_coqint(Floats.Float.to_bits f) in
      let lbl = label_literal64 f in
      fprintf oc "	movw	r14, #:lower16:.L%d\n" lbl;
      fprintf oc "	movt	r14, #:upper16:.L%d\n" lbl;
      fprintf oc "	vldr	%a, [r14, #0] @ %.12g\n"
        freg r1 (Int64.float_of_bits f)
    | Pfcmpd(r1, r2) ->
      fprintf oc "	vcmp.f64 %a, %a\n" freg r1 freg r2;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"
    | Pfcmpzd(r1) ->
      fprintf oc "	vcmp.f64 %a, #0\n" freg r1;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"
    | Pfsitod(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	vcvt.f64.s32 %a, %a\n" freg r1 freg_single r1
    | Pfuitod(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	vcvt.f64.u32 %a, %a\n" freg r1 freg_single r1
    | Pftosizd(r1, r2) ->
      fprintf oc "	vcvt.s32.f64 %a, %a\n" freg_single FR6 freg r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single FR6
    | Pftouizd(r1, r2) ->
      fprintf oc "	vcvt.u32.f64 %a, %a\n" freg_single FR6 freg r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single FR6
    | Pfabss(r1, r2) ->
      fprintf oc "	vabs.f32 %a, %a\n" freg_single r1 freg_single r2
    | Pfnegs(r1, r2) ->
      fprintf oc "	vneg.f32 %a, %a\n" freg_single r1 freg_single r2
    | Pfadds(r1, r2, r3) ->
      fprintf oc "	vadd.f32 %a, %a, %a\n" freg_single r1 freg_single r2 freg_single r3
    | Pfdivs(r1, r2, r3) ->
      fprintf oc "	vdiv.f32 %a, %a, %a\n" freg_single r1 freg_single r2 freg_single r3
    | Pfmuls(r1, r2, r3) ->
      fprintf oc "	vmul.f32 %a, %a, %a\n" freg_single r1 freg_single r2 freg_single r3
    | Ppush rl ->
      let first = ref true in
      let sep () = if !first then first := false else output_string oc ", " in
      fprintf oc "	push	{%a}\n"  (fun oc rl -> List.iter (fun ir -> sep (); ireg oc ir) rl) rl
    | Pfsubs(r1, r2, r3) ->
      fprintf oc "	vsub.f32 %a, %a, %a\n" freg_single r1 freg_single r2 freg_single r3
    | Pflis(r1, f) -> assert false (* Should be eliminated in expand constants *)
    | Pfcmps(r1, r2) ->
      fprintf oc "	vcmp.f32 %a, %a\n" freg_single r1 freg_single r2;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"
    | Pfcmpzs(r1) ->
      fprintf oc "	vcmp.f32 %a, #0\n" freg_single r1;
      fprintf oc "	vmrs APSR_nzcv, FPSCR\n"
    | Pfsitos(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	vcvt.f32.s32 %a, %a\n" freg_single r1 freg_single r1
    | Pfuitos(r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2;
      fprintf oc "	vcvt.f32.u32 %a, %a\n" freg_single r1 freg_single r1
    | Pftosizs(r1, r2) ->
      fprintf oc "	vcvt.s32.f32 %a, %a\n" freg_single FR6 freg_single r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single FR6
    | Pftouizs(r1, r2) ->
      fprintf oc "	vcvt.u32.f32 %a, %a\n" freg_single FR6 freg_single r2;
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single FR6
    | Pfcvtsd(r1, r2) ->
      fprintf oc "	vcvt.f32.f64 %a, %a\n" freg_single r1 freg r2
    | Pfcvtds(r1, r2) ->
      fprintf oc "	vcvt.f64.f32 %a, %a\n" freg r1 freg_single r2
    | Pfldd(r1, r2, n) | Pfldd_a(r1, r2, n) ->
      fprintf oc "	vldr	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n
    | Pflds(r1, r2, n) ->
      fprintf oc "	vldr	%a, [%a, #%a]\n" freg_single r1 ireg r2 coqint n
    | Pfstd(r1, r2, n) | Pfstd_a(r1, r2, n) ->
      fprintf oc "	vstr	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n
    | Pfsts(r1, r2, n) ->
      fprintf oc "	vstr	%a, [%a, #%a]\n" freg_single r1 ireg r2 coqint n
    (* Pseudo-instructions *)
    | Pallocframe(sz, ofs) ->
      assert false
    | Pfreeframe(sz, ofs) ->
      assert false
    | Plabel lbl ->
      fprintf oc "%a:\n" print_label lbl
    | Ploadsymbol(r1, id, ofs) -> assert false (* Should be eliminated in expand constants *)
    | Pmovite(cond, r1, ifso, ifnot) ->
      fprintf oc "	ite	%s\n" (condition_name cond);
      fprintf oc "	mov%s	%a, %a\n"
        (condition_name cond) ireg r1 shift_op ifso;
      fprintf oc "	mov%s	%a, %a\n"
        (neg_condition_name cond) ireg r1 shift_op ifnot
    | Pbtbl(r, tbl) ->
      if !Clflags.option_mthumb then begin
        fprintf oc "	lsl	r14, %a, #2\n" ireg r;
        fprintf oc "	add	pc, r14\n";   (* 16-bit encoding *)
        fprintf oc "	nop\n";            (* 16-bit encoding *)
        List.iter
          (fun l -> fprintf oc "	b.w	%a\n" print_label l)
          tbl
      end else begin
        fprintf oc "	add	pc, pc, %a, lsl #2\n" ireg r;
        fprintf oc "	nop\n";
        List.iter
          (fun l -> fprintf oc "	b	%a\n" print_label l)
          tbl
      end
    | Pbuiltin(ef, args, res) ->
      begin match ef with
        | EF_annot(kind,txt, targs) ->
            begin match (P.to_int kind) with
              | 1 -> let annot = annot_text preg_annot "sp" (camlstring_of_coqstring txt) args in
                fprintf oc "%s annotation: %S\n" comment annot
              | 2 -> let lbl = new_label () in
                fprintf oc "%a:\n" label lbl;
                AisAnnot.add_ais_annot lbl preg_annot "r13" (camlstring_of_coqstring txt) args
              | _ -> assert false
            end
        | EF_debug(kind, txt, targs) ->
          print_debug_info comment print_file_line preg_annot "sp" oc
            (P.to_int kind) (extern_atom txt) args
        | EF_inline_asm(txt, sg, clob) ->
          fprintf oc "%s begin inline assembly\n\t" comment;
          print_inline_asm preg oc (camlstring_of_coqstring txt) sg args res;
          fprintf oc "%s end inline assembly\n" comment
        | _ ->
          assert false
      end
    | Pcfi_adjust sz -> cfi_adjust oc (camlint_of_coqint sz)
    | Pcfi_rel_offset ofs -> cfi_rel_offset oc "lr" (camlint_of_coqint ofs)
    (* Fixup instructions for calling conventions *)
    | Pfcpy_fs(r1, r2) ->
      fprintf oc "	vmov.f32	%a, %a\n" freg_single r1 freg_param_single r2
    | Pfcpy_sf(r1, r2) ->
      fprintf oc "	vmov.f32	%a, %a\n" freg_param_single r1 freg_single r2
    | Pfcpy_fii (r1, r2, r3) ->
      fprintf oc "	vmov	%a, %a, %a\n" freg r1 ireg r2 ireg r3
    | Pfcpy_fi (r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" freg_single r1 ireg r2
    | Pfcpy_iif (r1, r2, r3) ->
      fprintf oc "	vmov	%a, %a, %a\n" ireg r1 ireg r2 freg r3
    |  Pfcpy_if (r1, r2) ->
      fprintf oc "	vmov	%a, %a\n" ireg r1 freg_single r2
    | Pconstants consts ->
      fprintf oc "	.balign	4\n";
      List.iter (print_constants oc) consts
    | Ploadsymbol_imm (r1,id,ofs) ->
        fprintf oc "	movw	%a, #:lower16:%a\n"
        ireg r1 symbol_offset (id, ofs);
        fprintf oc "	movt	%a, #:upper16:%a\n"
          ireg r1 symbol_offset (id, ofs)
    | Pflid_lbl (r1,lbl,f) ->
      let f = camlint64_of_coqint(Floats.Float.to_bits f) in
      fprintf oc "	vldr	%a, %a %s %.12g\n"
        freg r1 print_label lbl comment (Int64.float_of_bits f)
    | Pflis_lbl (r1,lbl,f) ->
      let f = camlint_of_coqint(Floats.Float32.to_bits f) in
      fprintf oc "	vldr	%a, %a %s %.12g\n"
        freg_single r1 print_label lbl comment (Int32.float_of_bits f)
    | Pflid_imm (r1,f) ->
      let f = camlint64_of_coqint(Floats.Float.to_bits f) in
      fprintf oc "	vmov.f64 %a, #%.15F\n"
        freg r1 (Int64.float_of_bits f)
    | Pflis_imm (r1,f) ->
      let f = camlint_of_coqint(Floats.Float32.to_bits f) in
       fprintf oc "	vmov.f32 %a, #%.15F\n"
         freg_single r1 (Int32.float_of_bits f)
    | Ploadsymbol_lbl (r1,lbl,id,ofs) ->
      fprintf oc "	ldr	%a, %a %s %a\n"
        ireg r1 print_label lbl comment symbol_offset (id, ofs)


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
    List.iter (print_instruction oc) fn.fn_code


  let emit_constants oc lit =
    if not !Constantexpand.literals_in_code && exists_constants () then begin
      section oc lit;
      fprintf oc "	.balign 4\n";
      Hashtbl.iter (print_literal64 oc) literal64_labels;
    end;
    reset_constants ()

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

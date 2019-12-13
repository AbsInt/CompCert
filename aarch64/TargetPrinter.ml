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

(* Printing AArch64 assembly code in asm syntax *)

open Printf
open Camlcoq
open Sections
open AST
open Asm
open AisAnnot
open PrintAsmaux
open Fileinfo

(* Recognition of FP numbers that are supported by the fmov #imm instructions:
   "a normalized binary floating point encoding with 1 sign bit,
    4 bits of fraction and a 3-bit exponent"
*)

let is_immediate_float64 bits =
  let exp = (Int64.(to_int (shift_right_logical bits 52)) land 0x7FF) - 1023 in
  let mant = Int64.logand bits 0xF_FFFF_FFFF_FFFFL in
  exp >= -3 && exp <= 4 && Int64.logand mant 0xF_0000_0000_0000L = mant

let is_immediate_float32 bits =
  let exp = (Int32.(to_int (shift_right_logical bits 23)) land 0xFF) - 127 in
  let mant = Int32.logand bits 0x7F_FFFFl in
  exp >= -3 && exp <= 4 && Int32.logand mant 0x78_0000l = mant

(* Module containing the printing functions *)

module Target : TARGET =
  struct

(* Basic printing functions *)

    let comment = "//"

    let symbol        = elf_symbol
    let symbol_offset = elf_symbol_offset
    let label         = elf_label

    let print_label oc lbl = label oc (transl_label lbl)

    let intsz oc (sz, n) =
      match sz with X -> coqint64 oc n | W -> coqint oc n

    let xreg_name = function
    | X0 -> "x0"   | X1 -> "x1"   | X2 -> "x2"   | X3 -> "x3"
    | X4 -> "x4"   | X5 -> "x5"   | X6 -> "x6"   | X7 -> "x7"
    | X8 -> "x8"   | X9 -> "x9"   | X10 -> "x10" | X11 -> "x11"
    | X12 -> "x12" | X13 -> "x13" | X14 -> "x14" | X15 -> "x15"
    | X16 -> "x16" | X17 -> "x17" | X18 -> "x18" | X19 -> "x19"
    | X20 -> "x20" | X21 -> "x21" | X22 -> "x22" | X23 -> "x23"
    | X24 -> "x24" | X25 -> "x25" | X26 -> "x26" | X27 -> "x27"
    | X28 -> "x28" | X29 -> "x29" | X30 -> "x30"

    let wreg_name = function
    | X0 -> "w0"   | X1 -> "w1"   | X2 -> "w2"   | X3 -> "w3"
    | X4 -> "w4"   | X5 -> "w5"   | X6 -> "w6"   | X7 -> "w7"
    | X8 -> "w8"   | X9 -> "w9"   | X10 -> "w10" | X11 -> "w11"
    | X12 -> "w12" | X13 -> "w13" | X14 -> "w14" | X15 -> "w15"
    | X16 -> "w16" | X17 -> "w17" | X18 -> "w18" | X19 -> "w19"
    | X20 -> "w20" | X21 -> "w21" | X22 -> "w22" | X23 -> "w23"
    | X24 -> "w24" | X25 -> "w25" | X26 -> "w26" | X27 -> "w27"
    | X28 -> "w28" | X29 -> "w29" | X30 -> "w30"

    let xreg0_name = function RR0 r -> xreg_name r | XZR -> "xzr"
    let wreg0_name = function RR0 r -> wreg_name r | XZR -> "wzr"

    let xregsp_name = function RR1 r -> xreg_name r | XSP -> "sp"
    let wregsp_name = function RR1 r -> wreg_name r | XSP -> "wsp"

    let dreg_name = function
    | D0 -> "d0"   | D1 -> "d1"   | D2 -> "d2"   | D3 -> "d3"
    | D4 -> "d4"   | D5 -> "d5"   | D6 -> "d6"   | D7 -> "d7"
    | D8 -> "d8"   | D9 -> "d9"   | D10 -> "d10" | D11 -> "d11"
    | D12 -> "d12" | D13 -> "d13" | D14 -> "d14" | D15 -> "d15"
    | D16 -> "d16" | D17 -> "d17" | D18 -> "d18" | D19 -> "d19"
    | D20 -> "d20" | D21 -> "d21" | D22 -> "d22" | D23 -> "d23"
    | D24 -> "d24" | D25 -> "d25" | D26 -> "d26" | D27 -> "d27"
    | D28 -> "d28" | D29 -> "d29" | D30 -> "d30" | D31 -> "d31"

    let sreg_name = function
    | D0 -> "s0"   | D1 -> "s1"   | D2 -> "s2"   | D3 -> "s3"
    | D4 -> "s4"   | D5 -> "s5"   | D6 -> "s6"   | D7 -> "s7"
    | D8 -> "s8"   | D9 -> "s9"   | D10 -> "s10" | D11 -> "s11"
    | D12 -> "s12" | D13 -> "s13" | D14 -> "s14" | D15 -> "s15"
    | D16 -> "s16" | D17 -> "s17" | D18 -> "s18" | D19 -> "s19"
    | D20 -> "s20" | D21 -> "s21" | D22 -> "s22" | D23 -> "s23"
    | D24 -> "s24" | D25 -> "s25" | D26 -> "s26" | D27 -> "s27"
    | D28 -> "s28" | D29 -> "s29" | D30 -> "s30" | D31 -> "s31"

    let xreg oc r = output_string oc (xreg_name r)
    let wreg oc r = output_string oc (wreg_name r)
    let ireg oc (sz, r) =
      output_string oc (match sz with X -> xreg_name r | W -> wreg_name r)

    let xreg0 oc r = output_string oc (xreg0_name r)
    let wreg0 oc r = output_string oc (wreg0_name r)
    let ireg0 oc (sz, r) =
      output_string oc (match sz with X -> xreg0_name r | W -> wreg0_name r)

    let xregsp oc r = output_string oc (xregsp_name r)
    let iregsp oc (sz, r) =
      output_string oc (match sz with X -> xregsp_name r | W -> wregsp_name r)

    let dreg oc r = output_string oc (dreg_name r)
    let sreg oc r = output_string oc (sreg_name r)
    let freg oc (sz, r) =
      output_string oc (match sz with D -> dreg_name r | S -> sreg_name r)

    let preg_asm oc ty = function
      | IR r -> if ty = Tint then wreg oc r else xreg oc r
      | FR r -> if ty = Tsingle then sreg oc r else dreg oc r
      | _    -> assert false

    let preg_annot = function
      | IR r -> xreg_name r
      | FR r -> dreg_name r
      | _ -> assert false

(* Names of sections *)

    let name_of_section = function
      | Section_text         -> ".text"
      | Section_data i | Section_small_data i ->
          if i then ".data" else common_section ()
      | Section_const i | Section_small_const i ->
          if i || (not !Clflags.option_fcommon) then ".section	.rodata" else "COMM"
      | Section_string       -> ".section	.rodata"
      | Section_literal      -> ".section	.rodata"
      | Section_jumptable    -> ".section	.rodata"
      | Section_debug_info _ -> ".section	.debug_info,\"\",%progbits"
      | Section_debug_loc    -> ".section	.debug_loc,\"\",%progbits"
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",%progbits"
      | Section_debug_line _ -> ".section	.debug_line,\"\",%progbits"
      | Section_debug_ranges -> ".section	.debug_ranges,\"\",%progbits"
      | Section_debug_str    -> ".section	.debug_str,\"MS\",%progbits,1"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
            s (if wr then "w" else "") (if ex then "x" else "")
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",\"\",@note"

    let section oc sec =
      fprintf oc "	%s\n" (name_of_section sec)

(* Associate labels to floating-point constants and to symbols. *)

    let emit_constants oc lit =
      if exists_constants () then begin
         section oc lit;
         if Hashtbl.length literal64_labels > 0 then
           begin
             fprintf oc "	.balign 8\n";
             Hashtbl.iter
               (fun bf lbl -> fprintf oc "%a:	.quad	0x%Lx\n" label lbl bf)
               literal64_labels
           end;
         if Hashtbl.length literal32_labels > 0 then
           begin
             fprintf oc "	.balign	4\n";
             Hashtbl.iter
               (fun bf lbl ->
                  fprintf oc "%a:	.long	0x%lx\n" label lbl bf)
               literal32_labels
           end;
         reset_literals ()
      end

(* Emit .file / .loc debugging directives *)

    let print_file_line oc file line =
      print_file_line oc comment file line

(* Name of testable condition *)

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

(* Print an addressing mode *)

    let addressing oc = function
    | ADimm(base, n) -> fprintf oc "[%a, #%a]" xregsp base coqint64 n
    | ADreg(base, r) -> fprintf oc "[%a, %a]" xregsp base xreg r
    | ADlsl(base, r, n) -> fprintf oc "[%a, %a, lsl #%a]" xregsp base xreg r coqint n
    | ADsxt(base, r, n) -> fprintf oc "[%a, %a, sxtw #%a]" xregsp base wreg r coqint n
    | ADuxt(base, r, n) -> fprintf oc "[%a, %a, uxtw #%a]" xregsp base wreg r coqint n
    | ADadr(base, id, ofs) -> fprintf oc "[%a, #:lo12:%a]" xregsp base symbol_offset (id, ofs)
    | ADpostincr(base, n) -> fprintf oc "[%a], #%a" xregsp base coqint64 n

(* Print a shifted operand *)
    let shiftop oc = function
    | SOnone -> ()
    | SOlsl n -> fprintf oc ", lsl #%a" coqint n
    | SOlsr n -> fprintf oc ", lsr #%a" coqint n
    | SOasr n -> fprintf oc ", asr #%a" coqint n
    | SOror n -> fprintf oc ", ror #%a" coqint n

(* Print a sign- or zero-extended operand *)
    let extendop oc = function
    | EOsxtb n -> fprintf oc ", sxtb #%a" coqint n
    | EOsxth n -> fprintf oc ", sxth #%a" coqint n
    | EOsxtw n -> fprintf oc ", sxtw #%a" coqint n
    | EOuxtb n -> fprintf oc ", uxtb #%a" coqint n
    | EOuxth n -> fprintf oc ", uxth #%a" coqint n
    | EOuxtw n -> fprintf oc ", uxtw #%a" coqint n
    | EOuxtx n -> fprintf oc ", uxtx #%a" coqint n

(* Printing of instructions *)
    let print_instruction oc = function
    (* Branches *)
    | Pb lbl ->
        fprintf oc "	b	%a\n" print_label lbl
    | Pbc(c, lbl) ->
        fprintf oc "	b.%s	%a\n" (condition_name c) print_label lbl
    | Pbl(id, sg) ->
        fprintf oc "	bl	%a\n" symbol id
    | Pbs(id, sg) ->
        fprintf oc "	b	%a\n" symbol id
    | Pblr(r, sg) ->
        fprintf oc "	blr	%a\n" xreg r
    | Pbr(r, sg) ->
        fprintf oc "	br	%a\n" xreg r
    | Pret r ->
        fprintf oc "	ret	%a\n" xreg r
    | Pcbnz(sz, r, lbl) ->
        fprintf oc "	cbnz	%a, %a\n" ireg (sz, r) print_label lbl
    | Pcbz(sz, r, lbl) ->
        fprintf oc "	cbz	%a, %a\n" ireg (sz, r) print_label lbl
    | Ptbnz(sz, r, n, lbl) ->
        fprintf oc "	tbnz	%a, #%a, %a\n" ireg (sz, r) coqint n print_label lbl
    | Ptbz(sz, r, n, lbl) ->
        fprintf oc "	tbz	%a, #%a, %a\n" ireg (sz, r) coqint n print_label lbl
    (* Memory loads and stores *)
    | Pldrw(rd, a) | Pldrw_a(rd, a) ->
        fprintf oc "	ldr	%a, %a\n" wreg rd addressing a
    | Pldrx(rd, a) | Pldrx_a(rd, a) ->
        fprintf oc "	ldr	%a, %a\n" xreg rd addressing a
    | Pldrb(sz, rd, a) ->
        fprintf oc "	ldrb	%a, %a\n" wreg rd addressing a
    | Pldrsb(sz, rd, a) ->
        fprintf oc "	ldrsb	%a, %a\n" ireg (sz, rd) addressing a
    | Pldrh(sz, rd, a) ->
        fprintf oc "	ldrh	%a, %a\n" wreg rd addressing a
    | Pldrsh(sz, rd, a) ->
        fprintf oc "	ldrsh	%a, %a\n" ireg (sz, rd) addressing a
    | Pldrzw(rd, a) ->
        fprintf oc "	ldr	%a, %a\n" wreg rd addressing a
        (* the upper 32 bits of Xrd are set to 0, performing zero-extension *)
    | Pldrsw(rd, a) ->
        fprintf oc "	ldrsw	%a, %a\n" xreg rd addressing a
    | Pldp(rd1, rd2, a) ->
        fprintf oc "	ldp	%a, %a, %a\n" xreg rd1 xreg rd2 addressing a
    | Pstrw(rs, a) | Pstrw_a(rs, a) ->
        fprintf oc "	str	%a, %a\n" wreg rs addressing a
    | Pstrx(rs, a) | Pstrx_a(rs, a) ->
        fprintf oc "	str	%a, %a\n" xreg rs addressing a
    | Pstrb(rs, a) ->
        fprintf oc "	strb	%a, %a\n" wreg rs addressing a
    | Pstrh(rs, a) ->
        fprintf oc "	strh	%a, %a\n" wreg rs addressing a
    | Pstp(rs1, rs2, a) ->
        fprintf oc "	stp	%a, %a, %a\n" xreg rs1 xreg rs2 addressing a
    (* Integer arithmetic, immediate *)
    | Paddimm(sz, rd, r1, n) ->
        fprintf oc "	add	%a, %a, #%a\n" iregsp (sz, rd) iregsp (sz, r1) intsz (sz, n)
    | Psubimm(sz, rd, r1, n) ->
        fprintf oc "	sub	%a, %a, #%a\n" iregsp (sz, rd) iregsp (sz, r1) intsz (sz, n)
    | Pcmpimm(sz, r1, n) ->
        fprintf oc "	cmp	%a, #%a\n" ireg (sz, r1) intsz (sz, n)
    | Pcmnimm(sz, r1, n) ->
        fprintf oc "	cmn	%a, #%a\n" ireg (sz, r1) intsz (sz, n)
    (* Move integer register *)
    | Pmov(rd, r1) ->
        fprintf oc "	mov	%a, %a\n" xregsp rd xregsp r1
    (* Logical, immediate *)
    | Pandimm(sz, rd, r1, n) ->
        fprintf oc "	and	%a, %a, #%a\n" ireg (sz, rd) ireg0 (sz, r1) intsz (sz, n)
    | Peorimm(sz, rd, r1, n) ->
        fprintf oc "	eor	%a, %a, #%a\n" ireg (sz, rd) ireg0 (sz, r1) intsz (sz, n)
    | Porrimm(sz, rd, r1, n) ->
        fprintf oc "	orr	%a, %a, #%a\n" ireg (sz, rd) ireg0 (sz, r1) intsz (sz, n)
    | Ptstimm(sz, r1, n) ->
        fprintf oc "	tst	%a, #%a\n" ireg (sz, r1) intsz (sz, n)
    (* Move wide immediate *)
    | Pmovz(sz, rd, n, pos) ->
        fprintf oc "	movz	%a, #%d, lsl #%d\n" ireg (sz, rd) (Z.to_int n) (Z.to_int pos)
    | Pmovn(sz, rd, n, pos) ->
        fprintf oc "	movn	%a, #%d, lsl #%d\n" ireg (sz, rd) (Z.to_int n) (Z.to_int pos)
    | Pmovk(sz, rd, n, pos) ->
        fprintf oc "	movk	%a, #%d, lsl #%d\n" ireg (sz, rd) (Z.to_int n) (Z.to_int pos)
    (* PC-relative addressing *)
    | Padrp(rd, id, ofs) ->
        fprintf oc "	adrp	%a, %a\n" xreg rd symbol_offset (id, ofs)
    | Paddadr(rd, r1, id, ofs) ->
        fprintf oc "	add	%a, %a, #:lo12:%a\n" xreg rd xreg r1 symbol_offset (id, ofs)
    (* Bit-field operations *)
    | Psbfiz(sz, rd, r1, r, s) ->
        fprintf oc "	sbfiz	%a, %a, %a, %d\n" ireg (sz, rd) ireg (sz, r1) coqint r (Z.to_int s)
    | Psbfx(sz, rd, r1, r, s) ->
        fprintf oc "	sbfx	%a, %a, %a, %d\n" ireg (sz, rd) ireg (sz, r1) coqint r (Z.to_int s)
    | Pubfiz(sz, rd, r1, r, s) ->
        fprintf oc "	ubfiz	%a, %a, %a, %d\n" ireg (sz, rd) ireg (sz, r1) coqint r (Z.to_int s)
    | Pubfx(sz, rd, r1, r, s) ->
        fprintf oc "	ubfx	%a, %a, %a, %d\n" ireg (sz, rd) ireg (sz, r1) coqint r (Z.to_int s)
    (* Integer arithmetic, shifted register *)
    | Padd(sz, rd, r1, r2, s) ->
        fprintf oc "	add	%a, %a, %a%a\n" ireg (sz, rd) ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Psub(sz, rd, r1, r2, s) ->
        fprintf oc "	sub	%a, %a, %a%a\n" ireg (sz, rd) ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Pcmp(sz, r1, r2, s) ->
        fprintf oc "	cmp	%a, %a%a\n" ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Pcmn(sz, r1, r2, s) ->
        fprintf oc "	cmn	%a, %a%a\n" ireg0 (sz, r1) ireg (sz, r2) shiftop s
    (* Integer arithmetic, extending register *)
    | Paddext(rd, r1, r2, x) ->
        fprintf oc "	add	%a, %a, %a%a\n" xregsp rd xregsp r1 wreg r2 extendop x
    | Psubext(rd, r1, r2, x) ->
        fprintf oc "	sub	%a, %a, %a%a\n" xregsp rd xregsp r1 wreg r2 extendop x
    | Pcmpext(r1, r2, x) ->
        fprintf oc "	cmp	%a, %a%a\n" xreg r1 wreg r2 extendop x
    | Pcmnext(r1, r2, x) ->
        fprintf oc "	cmn	%a, %a%a\n" xreg r1 wreg r2 extendop x
    (* Logical, shifted register *)
    | Pand(sz, rd, r1, r2, s) ->
        fprintf oc "	and	%a, %a, %a%a\n" ireg (sz, rd) ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Pbic(sz, rd, r1, r2, s) ->
        fprintf oc "	bic	%a, %a, %a%a\n" ireg (sz, rd) ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Peon(sz, rd, r1, r2, s) ->
        fprintf oc "	eon	%a, %a, %a%a\n" ireg (sz, rd) ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Peor(sz, rd, r1, r2, s) ->
        fprintf oc "	eor	%a, %a, %a%a\n" ireg (sz, rd) ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Porr(sz, rd, r1, r2, s) ->
        fprintf oc "	orr	%a, %a, %a%a\n" ireg (sz, rd) ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Porn(sz, rd, r1, r2, s) ->
        fprintf oc "	orn	%a, %a, %a%a\n" ireg (sz, rd) ireg0 (sz, r1) ireg (sz, r2) shiftop s
    | Ptst(sz, r1, r2, s) ->
        fprintf oc "	tst	%a, %a%a\n" ireg0 (sz, r1) ireg (sz, r2) shiftop s
    (* Variable shifts *)
    | Pasrv(sz, rd, r1, r2) ->
        fprintf oc "	asr	%a, %a, %a\n" ireg (sz, rd) ireg (sz, r1) ireg (sz, r2)
    | Plslv(sz, rd, r1, r2) ->
        fprintf oc "	lsl	%a, %a, %a\n" ireg (sz, rd) ireg (sz, r1) ireg (sz, r2)
    | Plsrv(sz, rd, r1, r2) ->
        fprintf oc "	lsr	%a, %a, %a\n" ireg (sz, rd) ireg (sz, r1) ireg (sz, r2)
    | Prorv(sz, rd, r1, r2) ->
        fprintf oc "	ror	%a, %a, %a\n" ireg (sz, rd) ireg (sz, r1) ireg (sz, r2)
    (* Bit operations *)
    | Pcls(sz, rd, r1) ->
        fprintf oc "	cls	%a, %a\n" ireg (sz, rd) ireg (sz, r1)
    | Pclz(sz, rd, r1) ->
        fprintf oc "	clz	%a, %a\n" ireg (sz, rd) ireg (sz, r1)
    | Prev(sz, rd, r1) ->
        fprintf oc "	rev	%a, %a\n" ireg (sz, rd) ireg (sz, r1)
    | Prev16(sz, rd, r1) ->
        fprintf oc "	rev16	%a, %a\n" ireg (sz, rd) ireg (sz, r1)
    (* Conditional data processing *)
    | Pcsel(rd, r1, r2, c) ->
        fprintf oc "	csel	%a, %a, %a, %s\n" xreg rd xreg r1 xreg r2 (condition_name c)
    | Pcset(rd, c) ->
        fprintf oc "	cset	%a, %s\n" xreg rd (condition_name c)
    (* Integer multiply/divide *)
    | Pmadd(sz, rd, r1, r2, r3) ->
        fprintf oc "	madd	%a, %a, %a, %a\n" ireg (sz, rd) ireg (sz, r1) ireg (sz, r2) ireg0 (sz, r3)
    | Pmsub(sz, rd, r1, r2, r3) ->
        fprintf oc "	msub	%a, %a, %a, %a\n" ireg (sz, rd) ireg (sz, r1) ireg (sz, r2) ireg0 (sz, r3)
    | Psmulh(rd, r1, r2) ->
        fprintf oc "	smulh	%a, %a, %a\n" xreg rd xreg r1 xreg r2
    | Pumulh(rd, r1, r2) ->
        fprintf oc "	umulh	%a, %a, %a\n" xreg rd xreg r1 xreg r2
    | Psdiv(sz, rd, r1, r2) ->
        fprintf oc "	sdiv	%a, %a, %a\n" ireg (sz, rd) ireg (sz, r1) ireg (sz, r2)
    | Pudiv(sz, rd, r1, r2) ->
        fprintf oc "	udiv	%a, %a, %a\n" ireg (sz, rd) ireg (sz, r1) ireg (sz, r2)
    (* Floating-point loads and stores *)
    | Pldrs(rd, a) ->
        fprintf oc "	ldr	%a, %a\n" sreg rd addressing a
    | Pldrd(rd, a) | Pldrd_a(rd, a) ->
        fprintf oc "	ldr	%a, %a\n" dreg rd addressing a
    | Pstrs(rd, a) ->
        fprintf oc "	str	%a, %a\n" sreg rd addressing a
    | Pstrd(rd, a) | Pstrd_a(rd, a) ->
        fprintf oc "	str	%a, %a\n" dreg rd addressing a
    (* Floating-point move *)
    | Pfmov(rd, r1) ->
        fprintf oc "	fmov	%a, %a\n" dreg rd dreg r1
    | Pfmovimmd(rd, f) ->
        let d = camlint64_of_coqint (Floats.Float.to_bits f) in
        if is_immediate_float64 d then
          fprintf oc "	fmov	%a, #%.7f\n" dreg rd (Int64.float_of_bits d)
        else begin
          let lbl = label_literal64 d in
          fprintf oc "	adrp	x16, %a\n" label lbl;
          fprintf oc "	ldr	%a, [x16, #:lo12:%a] %s %.18g\n" dreg rd label lbl comment (Int64.float_of_bits d)
        end
    | Pfmovimms(rd, f) ->
        let d = camlint_of_coqint (Floats.Float32.to_bits f) in
        if is_immediate_float32 d then
          fprintf oc "	fmov	%a, #%.7f\n" sreg rd (Int32.float_of_bits d)
        else begin
          let lbl = label_literal32 d in
          fprintf oc "	adrp	x16, %a\n" label lbl;
          fprintf oc "	ldr	%a, [x16, #:lo12:%a] %s %.18g\n" sreg rd label lbl comment (Int32.float_of_bits d)
        end
    | Pfmovi(D, rd, r1) ->
        fprintf oc "	fmov	%a, %a\n" dreg rd xreg0 r1
    | Pfmovi(S, rd, r1) ->
        fprintf oc "	fmov	%a, %a\n" sreg rd wreg0 r1
    (* Floating-point conversions *)
    | Pfcvtds(rd, r1) ->
        fprintf oc "	fcvt	%a, %a\n" dreg rd sreg r1 
    | Pfcvtsd(rd, r1) ->
        fprintf oc "	fcvt	%a, %a\n" sreg rd dreg r1 
    | Pfcvtzs(isz, fsz, rd, r1) ->
        fprintf oc "	fcvtzs  %a, %a\n" ireg (isz, rd) freg (fsz, r1)
    | Pfcvtzu(isz, fsz, rd, r1) ->
        fprintf oc "	fcvtzu  %a, %a\n" ireg (isz, rd) freg (fsz, r1)
    | Pscvtf(fsz, isz, rd, r1) ->
        fprintf oc "	scvtf	%a, %a\n" freg (fsz, rd) ireg (isz, r1)
    | Pucvtf(fsz, isz, rd, r1) ->
        fprintf oc "	ucvtf	%a, %a\n" freg (fsz, rd) ireg (isz, r1)
    (* Floating-point arithmetic *)
    | Pfabs(sz, rd, r1) ->
        fprintf oc "	fabs	%a, %a\n" freg (sz, rd) freg (sz, r1)
    | Pfneg(sz, rd, r1) ->
        fprintf oc "	fneg	%a, %a\n" freg (sz, rd) freg (sz, r1)
    | Pfsqrt(sz, rd, r1) ->
        fprintf oc "	fsqrt	%a, %a\n" freg (sz, rd) freg (sz, r1)
    | Pfadd(sz, rd, r1, r2) ->
        fprintf oc "	fadd	%a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2)
    | Pfdiv(sz, rd, r1, r2) ->
        fprintf oc "	fdiv	%a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2)
    | Pfmul(sz, rd, r1, r2) ->
        fprintf oc "	fmul	%a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2)
    | Pfnmul(sz, rd, r1, r2) ->
        fprintf oc "	fnmul	%a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2)
    | Pfsub(sz, rd, r1, r2) ->
        fprintf oc "	fsub	%a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2)
    | Pfmadd(sz, rd, r1, r2, r3) ->
        fprintf oc "	fmadd	%a, %a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2) freg (sz, r3)
    | Pfmsub(sz, rd, r1, r2, r3) ->
        fprintf oc "	fmsub	%a, %a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2) freg (sz, r3)
    | Pfnmadd(sz, rd, r1, r2, r3) ->
        fprintf oc "	fnmadd	%a, %a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2) freg (sz, r3)
    | Pfnmsub(sz, rd, r1, r2, r3) ->
        fprintf oc "	fnmsub	%a, %a, %a, %a\n" freg (sz, rd) freg (sz, r1) freg (sz, r2) freg (sz, r3)
    (* Floating-point comparison *)
    | Pfcmp(sz, r1, r2) ->
        fprintf oc "	fcmp	%a, %a\n" freg (sz, r1) freg (sz, r2)
    | Pfcmp0(sz, r1) ->
        fprintf oc "	fcmp	%a, #0.0\n" freg (sz, r1)
    (* Floating-point conditional select *)
    | Pfsel(rd, r1, r2, c) ->
        fprintf oc "	fcsel	%a, %a, %a, %s\n" dreg rd dreg r1 dreg r2 (condition_name c)
    (* Pseudo-instructions expanded in Asmexpand *)
    | Pallocframe(sz, linkofs) -> assert false
    | Pfreeframe(sz, linkofs) -> assert false
    | Pcvtx2w rd -> assert false
    (* Pseudo-instructions not yet expanded *)
    | Plabel lbl ->
        fprintf oc "%a:\n" print_label lbl
    | Ploadsymbol(rd, id) ->
        fprintf oc "	adrp	%a, :got:%a\n" xreg rd symbol id;
        fprintf oc "	ldr	%a, [%a, #:got_lo12:%a]\n" xreg rd xreg rd symbol id
    | Pcvtsw2x(rd, r1) ->
        fprintf oc "	sxtw	%a, %a\n" xreg rd wreg r1
    | Pcvtuw2x(rd, r1) ->
        fprintf oc "	uxtw	%a, %a\n" xreg rd wreg r1
    | Pbtbl(r1, tbl) ->
        let lbl = new_label() in
        fprintf oc "	adr	x16, %a\n" label lbl;
        fprintf oc "	add	x16, x16, %a, uxtw #2\n" wreg r1;
        fprintf oc "	br	x16\n";
        fprintf oc "%a:" label lbl;
        List.iter (fun l -> fprintf oc "	b	%a\n" print_label l) tbl
    | Pcfi_adjust sz ->
        cfi_adjust oc (camlint_of_coqint sz)
    | Pcfi_rel_offset ofs ->
        cfi_rel_offset oc "lr" (camlint_of_coqint ofs)
    | Pbuiltin(ef, args, res) ->
        begin match ef with
          | EF_annot(kind,txt, targs) ->
            begin match (P.to_int kind) with
              | 1 -> let annot = annot_text preg_annot "sp" (camlstring_of_coqstring txt) args  in
                fprintf oc "%s annotation: %S\n" comment annot
              | 2 -> let lbl = new_label () in
                fprintf oc "%a:\n" label lbl;
                add_ais_annot lbl preg_annot "sp" (camlstring_of_coqstring txt) args
              | _ -> assert false
            end
         | EF_debug(kind, txt, targs) ->
             print_debug_info comment print_file_line preg_annot "sp" oc
                              (P.to_int kind) (extern_atom txt) args
         | EF_inline_asm(txt, sg, clob) ->
             fprintf oc "%s begin inline assembly\n\t" comment;
             print_inline_asm preg_asm oc (camlstring_of_coqstring txt) sg args res;
             fprintf oc "%s end inline assembly\n" comment
         | _ ->
             assert false
        end

    let get_section_names name =
      let (text, lit) =
        match C2C.atom_sections name with
        | t :: l :: _ -> (t, l)
        | _    -> (Section_text, Section_literal) in
      text,lit,Section_jumptable

    let print_align oc alignment =
      fprintf oc "	.balign %d\n" alignment

    let print_jumptable oc jmptbl =
      let print_tbl oc (lbl, tbl) =
        fprintf oc "%a:\n" label lbl;
        List.iter
          (fun l -> fprintf oc "	.long	%a - %a\n"
                               print_label l label lbl)
          tbl in
      if !jumptables <> [] then
        begin
          section oc jmptbl;
          fprintf oc "	.balign 4\n";
          List.iter (print_tbl oc) !jumptables;
          jumptables := []
        end

    let print_fun_info = elf_print_fun_info

    let print_optional_fun_info _ = ()

    let print_var_info = elf_print_var_info

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

(* Data *)

    let address = ".quad"

    let print_prologue oc =
      if !Clflags.option_g then begin
        section oc Section_text;
      end

    let print_epilogue oc =
      if !Clflags.option_g then begin
        Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
        section oc Section_text;
      end

    let default_falignment = 2

    let cfi_startproc oc = ()
    let cfi_endproc oc = ()

  end

let sel_target () =
  (module Target:TARGET)

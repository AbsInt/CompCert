(* $Id: PrintPPC.ml,v 1.2 2005/01/22 11:28:46 xleroy Exp $ *)

(* Printing PPC assembly code in asm syntax *)

open Printf
open Datatypes
open CList
open Camlcoq
open AST
open PPC

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

let print_symb oc symb =
  fprintf oc "_%s" (extern_atom symb)

let print_label oc lbl =
  fprintf oc "L%d" (label_for_label lbl)

let print_symb_ofs oc (symb, ofs) =
  print_symb oc symb;
  if ofs <> 0l then fprintf oc " + %ld" ofs

let print_constant oc = function
  | Cint n ->
      fprintf oc "%ld" (camlint_of_coqint n)
  | Csymbol_low_signed(s, n) ->
      fprintf oc "lo16(%a)" print_symb_ofs (s, camlint_of_coqint n)
  | Csymbol_high_signed(s, n) ->
      fprintf oc "ha16(%a)" print_symb_ofs (s, camlint_of_coqint n)
  | Csymbol_low_unsigned(s, n) ->
      fprintf oc "lo16(%a)" print_symb_ofs (s, camlint_of_coqint n)
  | Csymbol_high_unsigned(s, n) ->
      fprintf oc "hi16(%a)" print_symb_ofs (s, camlint_of_coqint n)

let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3

let print_crbit oc bit =
  fprintf oc "%d" (num_crbit bit)

let print_coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

let int_reg_name = function
  | GPR0 -> "r0"  | GPR1 -> "r1"  | GPR2 -> "r2"  | GPR3 -> "r3"
  | GPR4 -> "r4"  | GPR5 -> "r5"  | GPR6 -> "r6"  | GPR7 -> "r7"
  | GPR8 -> "r8"  | GPR9 -> "r9"  | GPR10 -> "r10" | GPR11 -> "r11"
  | GPR12 -> "r12" | GPR13 -> "r13" | GPR14 -> "r14" | GPR15 -> "r15"
  | GPR16 -> "r16" | GPR17 -> "r17" | GPR18 -> "r18" | GPR19 -> "r19"
  | GPR20 -> "r20" | GPR21 -> "r21" | GPR22 -> "r22" | GPR23 -> "r23"
  | GPR24 -> "r24" | GPR25 -> "r25" | GPR26 -> "r26" | GPR27 -> "r27"
  | GPR28 -> "r28" | GPR29 -> "r29" | GPR30 -> "r30" | GPR31 -> "r31"

let float_reg_name = function
  | FPR0 -> "f0"  | FPR1 -> "f1"  | FPR2 -> "f2"  | FPR3 -> "f3"
  | FPR4 -> "f4"  | FPR5 -> "f5"  | FPR6 -> "f6"  | FPR7 -> "f7"
  | FPR8 -> "f8"  | FPR9 -> "f9"  | FPR10 -> "f10" | FPR11 -> "f11"
  | FPR12 -> "f12" | FPR13 -> "f13" | FPR14 -> "f14" | FPR15 -> "f15"
  | FPR16 -> "f16" | FPR17 -> "f17" | FPR18 -> "f18" | FPR19 -> "f19"
  | FPR20 -> "f20" | FPR21 -> "f21" | FPR22 -> "f22" | FPR23 -> "f23"
  | FPR24 -> "f24" | FPR25 -> "f25" | FPR26 -> "f26" | FPR27 -> "f27"
  | FPR28 -> "f28" | FPR29 -> "f29" | FPR30 -> "f30" | FPR31 -> "f31"

let ireg oc r = output_string oc (int_reg_name r)
let ireg_or_zero oc r = if r = GPR0 then output_string oc "0" else ireg oc r
let freg oc r = output_string oc (float_reg_name r)

(* Printing of instructions *)

module Labelset = Set.Make(struct type t = label let compare = compare end)

let print_instruction oc labels = function
  | Padd(r1, r2, r3) ->
      fprintf oc "	add	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Paddi(r1, r2, c) ->
      fprintf oc "	addi	%a, %a, %a\n" ireg r1 ireg_or_zero r2 print_constant c
  | Paddis(r1, r2, c) ->
      fprintf oc "	addis	%a, %a, %a\n" ireg r1 ireg_or_zero r2 print_constant c
  | Paddze(r1, r2) ->
      fprintf oc "	addze	%a, %a\n" ireg r1 ireg r2
  | Pallocframe(lo, hi) ->
      let lo = camlint_of_coqint lo
      and hi = camlint_of_coqint hi in
      let nsz = Int32.neg (Int32.sub hi lo) in
      fprintf oc "	stwu	r1, %ld(r1)\n" nsz
  | Pand_(r1, r2, r3) ->
      fprintf oc "	and.	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pandc(r1, r2, r3) ->
      fprintf oc "	andc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pandi_(r1, r2, c) ->
      fprintf oc "	andi.	%a, %a, %a\n" ireg r1 ireg r2 print_constant c
  | Pandis_(r1, r2, c) ->
      fprintf oc "	andis.	%a, %a, %a\n" ireg r1 ireg r2 print_constant c
  | Pb lbl ->
      fprintf oc "	b	%a\n" print_label lbl
  | Pbctr ->
      fprintf oc "	bctr\n"
  | Pbctrl ->
      fprintf oc "	bctrl\n"
  | Pbf(bit, lbl) ->
      fprintf oc "	bf	%a, %a\n" print_crbit bit print_label lbl
  | Pbl s ->
      fprintf oc "	bl	%a\n" print_symb s
  | Pblr ->
      fprintf oc "	blr\n"
  | Pbt(bit, lbl) ->
      fprintf oc "	bt	%a, %a\n" print_crbit bit print_label lbl
  | Pcmplw(r1, r2) ->
      fprintf oc "	cmplw	cr0, %a, %a\n" ireg r1 ireg r2
  | Pcmplwi(r1, c) ->
      fprintf oc "	cmplwi	cr0, %a, %a\n" ireg r1 print_constant c
  | Pcmpw(r1, r2) ->
      fprintf oc "	cmpw	cr0, %a, %a\n" ireg r1 ireg r2
  | Pcmpwi(r1, c) ->
      fprintf oc "	cmpwi	cr0, %a, %a\n" ireg r1 print_constant c
  | Pcror(c1, c2, c3) ->
      fprintf oc "	cror	%a, %a, %a\n" print_crbit c1 print_crbit c2 print_crbit c3
  | Pdivw(r1, r2, r3) ->
      fprintf oc "	divw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pdivwu(r1, r2, r3) ->
      fprintf oc "	divwu	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Peqv(r1, r2, r3) ->
      fprintf oc "	eqv	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pextsb(r1, r2) ->
      fprintf oc "	extsb	%a, %a\n" ireg r1 ireg r2
  | Pextsh(r1, r2) ->
      fprintf oc "	extsh	%a, %a\n" ireg r1 ireg r2
  | Pfreeframe ->
      fprintf oc "	lwz	r1, 0(r1)\n"
  | Pfabs(r1, r2) ->
      fprintf oc "	fabs	%a, %a\n" freg r1 freg r2
  | Pfadd(r1, r2, r3) ->
      fprintf oc "	fadd	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfcmpu(r1, r2) ->
      fprintf oc "	fcmpu	cr0, %a, %a\n" freg r1 freg r2
  | Pfcti(r1, r2) ->
      fprintf oc "	fctiwz	f13, %a\n" freg r2;
      fprintf oc "	stfdu	f13, -8(r1)\n";
      fprintf oc "	lwz	%a, 4(r1)\n" ireg r1;
      fprintf oc "	addi	r1, r1, 8\n"
  | Pfdiv(r1, r2, r3) ->
      fprintf oc "	fdiv	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfmadd(r1, r2, r3, r4) ->
      fprintf oc "	fmadd	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
  | Pfmr(r1, r2) ->
      fprintf oc "	fmr	%a, %a\n" freg r1 freg r2
  | Pfmsub(r1, r2, r3, r4) ->
      fprintf oc "	fmsub	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
  | Pfmul(r1, r2, r3) ->
      fprintf oc "	fmul	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfneg(r1, r2) ->
      fprintf oc "	fneg	%a, %a\n" freg r1 freg r2
  | Pfrsp(r1, r2) ->
      fprintf oc "	frsp	%a, %a\n" freg r1 freg r2
  | Pfsub(r1, r2, r3) ->
      fprintf oc "	fsub	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pictf(r1, r2) ->
      let lbl = new_label() in
      fprintf oc "	addis	r2, 0, 0x4330\n";
      fprintf oc "	stwu	r2, -8(r1)\n";
      fprintf oc "	addis	r2, %a, 0x8000\n" ireg r2;
      fprintf oc "	stw	r2, 4(r1)\n";
      fprintf oc "	addis	r2, 0, ha16(L%d)\n" lbl;
      fprintf oc "	lfd	f13, lo16(L%d)(r2)\n" lbl;
      fprintf oc "	lfd	%a, 0(r1)\n" freg r1;
      fprintf oc "	addi	r1, r1, 8\n";
      fprintf oc "	fsub	%a, %a, f13\n" freg r1 freg r1;
      fprintf oc "	.const_data\n";
      fprintf oc "L%d:	.long	0x43300000, 0x80000000\n" lbl;
      fprintf oc "	.text\n"
  | Piuctf(r1, r2) ->
      let lbl = new_label() in
      fprintf oc "	addis	r2, 0, 0x4330\n";
      fprintf oc "	stwu	r2, -8(r1)\n";
      fprintf oc "	stw	%a, 4(r1)\n" ireg r2;
      fprintf oc "	addis	r2, 0, ha16(L%d)\n" lbl;
      fprintf oc "	lfd	f13, lo16(L%d)(r2)\n" lbl;
      fprintf oc "	lfd	%a, 0(r1)\n" freg r1;
      fprintf oc "	addi	r1, r1, 8\n";
      fprintf oc "	fsub	%a, %a, f12\n" freg r1 freg r1;
      fprintf oc "	.const_data\n";
      fprintf oc "L%d:	.long	0x43300000, 0x00000000\n" lbl;
      fprintf oc "	.text\n"
  | Plbz(r1, c, r2) ->
      fprintf oc "	lbz	%a, %a(%a)\n" ireg r1 print_constant c ireg r2
  | Plbzx(r1, r2, r3) ->
      fprintf oc "	lbzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plfd(r1, c, r2) ->
      fprintf oc "	lfd	%a, %a(%a)\n" freg r1 print_constant c ireg r2
  | Plfdx(r1, r2, r3) ->
      fprintf oc "	lfdx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Plfi(r1, c) ->
      let lbl = new_label() in
      fprintf oc "	addis	r2, 0, ha16(L%d)\n" lbl;
      fprintf oc "	lfd	%a, lo16(L%d)(r2)\n" freg r1 lbl;
      fprintf oc "	.const_data\n";
      let n = Int64.bits_of_float c in
      let nlo = Int64.to_int32 n
      and nhi = Int64.to_int32(Int64.shift_right_logical n 32) in
      fprintf oc "L%d:	.long	0x%lx, 0x%lx   ; %f\n" lbl nhi nlo c;
      fprintf oc "	.text\n"
  | Plfs(r1, c, r2) ->
      fprintf oc "	lfs	%a, %a(%a)\n" freg r1 print_constant c ireg r2
  | Plfsx(r1, r2, r3) ->
      fprintf oc "	lfsx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Plha(r1, c, r2) ->
      fprintf oc "	lha	%a, %a(%a)\n" ireg r1 print_constant c ireg r2
  | Plhax(r1, r2, r3) ->
      fprintf oc "	lhax	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plhz(r1, c, r2) ->
      fprintf oc "	lhz	%a, %a(%a)\n" ireg r1 print_constant c ireg r2
  | Plhzx(r1, r2, r3) ->
      fprintf oc "	lhzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plwz(r1, c, r2) ->
      fprintf oc "	lwz	%a, %a(%a)\n" ireg r1 print_constant c ireg r2
  | Plwzx(r1, r2, r3) ->
      fprintf oc "	lwzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pmfcrbit(r1, bit) ->
      fprintf oc "	mfcr	r2\n";
      fprintf oc "	rlwinm	%a, r2, %d, 1\n" ireg r1 (1 + num_crbit bit)
  | Pmflr(r1) ->
      fprintf oc "	mflr	%a\n" ireg r1
  | Pmr(r1, r2) ->
      fprintf oc "	mr	%a, %a\n" ireg r1 ireg r2
  | Pmtctr(r1) ->
      fprintf oc "	mtctr	%a\n" ireg r1
  | Pmtlr(r1) ->
      fprintf oc "	mtlr	%a\n" ireg r1
  | Pmulli(r1, r2, c) ->
      fprintf oc "	mulli	%a, %a, %a\n" ireg r1 ireg r2 print_constant c
  | Pmullw(r1, r2, r3) ->
      fprintf oc "	mullw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pnand(r1, r2, r3) ->
      fprintf oc "	nand	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pnor(r1, r2, r3) ->
      fprintf oc "	nor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Por(r1, r2, r3) ->
      fprintf oc "	or	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Porc(r1, r2, r3) ->
      fprintf oc "	orc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pori(r1, r2, c) ->
      fprintf oc "	ori	%a, %a, %a\n" ireg r1 ireg r2 print_constant c
  | Poris(r1, r2, c) ->
      fprintf oc "	oris	%a, %a, %a\n" ireg r1 ireg r2 print_constant c
  | Prlwinm(r1, r2, c1, c2) ->
      fprintf oc "	rlwinm	%a, %a, %ld, 0x%lx\n"
                ireg r1 ireg r2 (camlint_of_coqint c1) (camlint_of_coqint c2)
  | Pslw(r1, r2, r3) ->
      fprintf oc "	slw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psraw(r1, r2, r3) ->
      fprintf oc "	sraw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psrawi(r1, r2, c) ->
      fprintf oc "	srawi	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint c)
  | Psrw(r1, r2, r3) ->
      fprintf oc "	srw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstb(r1, c, r2) ->
      fprintf oc "	stb	%a, %a(%a)\n" ireg r1 print_constant c ireg r2
  | Pstbx(r1, r2, r3) ->
      fprintf oc "	stbx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstfd(r1, c, r2) ->
      fprintf oc "	stfd	%a, %a(%a)\n" freg r1 print_constant c ireg r2
  | Pstfdx(r1, r2, r3) ->
      fprintf oc "	stfdx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Pstfs(r1, c, r2) ->
      fprintf oc "	stfs	%a, %a(%a)\n" freg r1 print_constant c ireg r2
  | Pstfsx(r1, r2, r3) ->
      fprintf oc "	stfsx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Psth(r1, c, r2) ->
      fprintf oc "	sth	%a, %a(%a)\n" ireg r1 print_constant c ireg r2
  | Psthx(r1, r2, r3) ->
      fprintf oc "	sthx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstw(r1, c, r2) ->
      fprintf oc "	stw	%a, %a(%a)\n" ireg r1 print_constant c ireg r2
  | Pstwx(r1, r2, r3) ->
      fprintf oc "	stwx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psubfc(r1, r2, r3) ->
      fprintf oc "	subfc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psubfic(r1, r2, c) ->
      fprintf oc "	subfic	%a, %a, %a\n" ireg r1 ireg r2 print_constant c
  | Pxor(r1, r2, r3) ->
      fprintf oc "	xor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pxori(r1, r2, c) ->
      fprintf oc "	xori	%a, %a, %a\n" ireg r1 ireg r2 print_constant c
  | Pxoris(r1, r2, c) ->
      fprintf oc "	xoris	%a, %a, %a\n" ireg r1 ireg r2 print_constant c
  | Plabel lbl ->
      if Labelset.mem lbl labels then fprintf oc "%a:\n" print_label lbl
  | Piundef r ->
      fprintf oc "	# undef %a\n" ireg r
  | Pfundef r ->
      fprintf oc "	# undef %a\n" freg r

let rec labels_of_code = function
  | Coq_nil -> Labelset.empty
  | Coq_cons((Pb lbl | Pbf(_, lbl) | Pbt(_, lbl)), c) ->
      Labelset.add lbl (labels_of_code c)
  | Coq_cons(_, c) -> labels_of_code c

let print_function oc (Coq_pair(name, code)) =
  Hashtbl.clear current_function_labels;
  fprintf oc "	.text\n";
  fprintf oc "	.align 2\n";
  fprintf oc "	.globl %a\n" print_symb name;
  fprintf oc "%a:\n" print_symb name;
  coqlist_iter (print_instruction oc (labels_of_code code)) code

let print_var oc (Coq_pair(name, size)) =
  fprintf oc "	.globl	%a\n" print_symb name;
  fprintf oc "%a:\n" print_symb name;
  fprintf oc "	.space	%ld\n" (camlint_of_z size)

let print_program oc p =
  coqlist_iter (print_var oc) p.prog_vars;
  coqlist_iter (print_function oc) p.prog_funct


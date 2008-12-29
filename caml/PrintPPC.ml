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

(* Record identifiers of external functions *)

module IdentSet = Set.Make(struct type t = ident let compare = compare end)

let extfuns = ref IdentSet.empty

let record_extfun (Coq_pair(name, defn)) =
  match defn with
  | Internal _ -> ()
  | External _ -> extfuns := IdentSet.add name !extfuns

(* Basic printing functions *)

let print_symb oc symb =
  if IdentSet.mem symb !extfuns
  then fprintf oc "L%s$stub" (extern_atom symb)
  else fprintf oc "_%s" (extern_atom symb)

let print_label oc lbl =
  fprintf oc "L%d" (label_for_label lbl)

let print_symb_ofs oc (symb, ofs) =
  print_symb oc symb;
  if ofs <> 0l then fprintf oc " + %ld" ofs

let print_constant oc = function
  | Cint n ->
      fprintf oc "%ld" (camlint_of_coqint n)
  | Csymbol_low(s, n) ->
      fprintf oc "lo16(%a)" print_symb_ofs (s, camlint_of_coqint n)
  | Csymbol_high(s, n) ->
      fprintf oc "ha16(%a)" print_symb_ofs (s, camlint_of_coqint n)

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
  | Pallocblock ->
      fprintf oc "	bl	_compcert_alloc\n"
  | Pallocframe(lo, hi, ofs) ->
      let lo = camlint_of_coqint lo
      and hi = camlint_of_coqint hi
      and ofs = camlint_of_coqint ofs in
      let sz = Int32.sub hi lo in
      (* Keep stack 16-aligned *)
      let sz16 = Int32.logand (Int32.add sz 15l) 0xFFFF_FFF0l in
      assert (ofs = 0l);
      fprintf oc "	stwu	r1, %ld(r1)\n" (Int32.neg sz16)
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
  | Pbs s ->
      fprintf oc "	b	%a\n" print_symb s
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
  | Pfreeframe ofs ->
      fprintf oc "	lwz	r1, %ld(r1)\n" (camlint_of_coqint ofs)
  | Pfabs(r1, r2) ->
      fprintf oc "	fabs	%a, %a\n" freg r1 freg r2
  | Pfadd(r1, r2, r3) ->
      fprintf oc "	fadd	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfcmpu(r1, r2) ->
      fprintf oc "	fcmpu	cr0, %a, %a\n" freg r1 freg r2
  | Pfcti(r1, r2) ->
      fprintf oc "	fctiwz	f13, %a\n" freg r2;
      fprintf oc "	stfd	f13, -8(r1)\n";
      fprintf oc "	lwz	%a, -4(r1)\n" ireg r1
  | Pfctiu(r1, r2) ->
      let lbl1 = new_label() in
      let lbl2 = new_label() in
      let lbl3 = new_label() in
      fprintf oc "	addis	r12, 0, ha16(L%d)\n" lbl1;
      fprintf oc "	lfd	f13, lo16(L%d)(r12)\n" lbl1;
      fprintf oc "	fcmpu	cr7, %a, f13\n" freg r2;
      fprintf oc "	cror	30, 29, 30\n";
      fprintf oc "	beq	cr7, L%d\n" lbl2;
      fprintf oc "	fctiwz	f13, %a\n" freg r2;
      fprintf oc "	stfdu	f13, -8(r1)\n";
      fprintf oc "	lwz	%a, 4(r1)\n" ireg r1;
      fprintf oc "	b	L%d\n" lbl3;
      fprintf oc "L%d:	fsub	f13, %a, f13\n" lbl2 freg r2;
      fprintf oc "	fctiwz	f13, f13\n";
      fprintf oc "	stfdu	f13, -8(r1)\n";
      fprintf oc "	lwz	%a, 4(r1)\n" ireg r1;
      fprintf oc "	addis	%a, %a, 0x8000\n" ireg r1 ireg r1;
      fprintf oc "L%d:	addi	r1, r1, 8\n" lbl3;
      fprintf oc "	.const_data\n";
      fprintf oc "L%d:	.long	0x41e00000, 0x00000000\n" lbl1;
      fprintf oc "	.text\n"
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
      fprintf oc "	addis	r12, 0, 0x4330\n";
      fprintf oc "	stw	r12, -8(r1)\n";
      fprintf oc "	addis	r12, %a, 0x8000\n" ireg r2;
      fprintf oc "	stw	r12, -4(r1)\n";
      fprintf oc "	addis	r12, 0, ha16(L%d)\n" lbl;
      fprintf oc "	lfd	f13, lo16(L%d)(r12)\n" lbl;
      fprintf oc "	lfd	%a, -8(r1)\n" freg r1;
      fprintf oc "	fsub	%a, %a, f13\n" freg r1 freg r1;
      fprintf oc "	.const_data\n";
      fprintf oc "L%d:	.long	0x43300000, 0x80000000\n" lbl;
      fprintf oc "	.text\n"
  | Piuctf(r1, r2) ->
      let lbl = new_label() in
      fprintf oc "	addis	r12, 0, 0x4330\n";
      fprintf oc "	stw	r12, -8(r1)\n";
      fprintf oc "	stw	%a, -4(r1)\n" ireg r2;
      fprintf oc "	addis	r12, 0, ha16(L%d)\n" lbl;
      fprintf oc "	lfd	f13, lo16(L%d)(r12)\n" lbl;
      fprintf oc "	lfd	%a, -8(r1)\n" freg r1;
      fprintf oc "	fsub	%a, %a, f13\n" freg r1 freg r1;
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
      fprintf oc "	addis	r12, 0, ha16(L%d)\n" lbl;
      fprintf oc "	lfd	%a, lo16(L%d)(r12)\n" freg r1 lbl;
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

let rec labels_of_code = function
  | [] -> Labelset.empty
  | (Pb lbl | Pbf(_, lbl) | Pbt(_, lbl)) :: c ->
      Labelset.add lbl (labels_of_code c)
  | _ :: c -> labels_of_code c

let print_function oc name code =
  Hashtbl.clear current_function_labels;
  fprintf oc "	.text\n";
  fprintf oc "	.align 2\n";
  fprintf oc "	.globl %a\n" print_symb name;
  fprintf oc "%a:\n" print_symb name;
  List.iter (print_instruction oc (labels_of_code code)) code

(* Generation of stub code for variadic functions, e.g. printf.
   Calling conventions for variadic functions are:
     - always reserve 8 stack words (offsets 24 to 52) so that the
       variadic function can save there the integer registers parameters
       r3 ... r10
     - treat float arguments as pairs of integers, i.e. if we
       must pass them in registers, use a pair of integer registers
       for this purpose.
   The code we generate is:
     - allocate large enough stack frame
     - save return address
     - copy our arguments (registers and stack) to the stack frame,
       starting at offset 24
     - load relevant integer parameter registers r3...r10 from the
       stack frame, limited by the actual number of arguments
     - call the variadic thing
     - deallocate stack frame and return
*)

let variadic_stub oc stub_name fun_name ty_args =
  (* Compute total size of arguments *)
  let arg_size =
    CList.fold_left
     (fun sz ty -> match ty with Tint -> sz + 4 | Tfloat -> sz + 8)
     ty_args 0 in
  (* Stack size is linkage area + argument size, with a minimum of 56 bytes *)
  let frame_size = max 56 (24 + arg_size) in
  fprintf oc "	mflr	r0\n";
  fprintf oc "	stwu	r1, %d(r1)\n" (-frame_size);
  fprintf oc "	stw	r0, %d(r1)\n" (frame_size + 4);
  (* Copy our parameters to our stack frame.
     As an optimization, don't copy parameters that are already in
     integer registers, since these stay in place. *)
  let rec copy gpr fpr src_ofs dst_ofs = function
    | [] -> ()
    | Tint :: rem ->
        if gpr > 10 then begin
          fprintf oc "	lwz	r0, %d(r1)\n" src_ofs;
          fprintf oc "	stw	r0, %d(r1)\n" dst_ofs
        end;
        copy (gpr + 1) fpr (src_ofs + 4) (dst_ofs + 4) rem
    | Tfloat :: rem ->
        if fpr <= 10 then begin
          fprintf oc "	stfd	f%d, %d(r1)\n" fpr dst_ofs
        end else begin
          fprintf oc "	lfd	f0, %d(r1)\n" src_ofs;
          fprintf oc "	stfd	f0, %d(r1)\n" dst_ofs
        end;
        copy (gpr + 2) (fpr + 1) (src_ofs + 8) (dst_ofs + 8) rem
  in copy 3 1 (frame_size + 24) 24 ty_args;
  (* Load the first parameters into integer registers.
     As an optimization, don't load parameters that are already
     in the correct integer registers. *)
  let rec load gpr ofs = function
    | [] -> ()
    | Tint :: rem ->
        load (gpr + 1) (ofs + 4) rem
    | Tfloat :: rem ->
        if gpr <= 10 then
          fprintf oc "	lwz	r%d, %d(r1)\n" gpr ofs;
        if gpr + 1 <= 10 then
          fprintf oc "	lwz	r%d, %d(r1)\n" (gpr + 1) (ofs + 4);
        load (gpr + 2) (ofs + 8) rem
  in load 3 24 ty_args;
  (* Call the function *)
  fprintf oc "	addis	r11, 0, ha16(L%s$ptr)\n" stub_name;
  fprintf oc "	lwz	r11, lo16(L%s$ptr)(r11)\n" stub_name;
  fprintf oc "	mtctr	r11\n";
  fprintf oc "	bctrl\n";
  (* Free our frame and return *)
  fprintf oc "	lwz	r0, %d(r1)\n" (frame_size + 4);
  fprintf oc "	mtlr	r0\n";
  fprintf oc "	addi	r1, r1, %d\n" frame_size;
  fprintf oc "	blr\n";
  (* The function pointer *)
  fprintf oc "	.non_lazy_symbol_pointer\n";
  fprintf oc "L%s$ptr:\n" stub_name;
  fprintf oc "	.indirect_symbol _%s\n" fun_name;
  fprintf oc "	.long	0\n"

(* Stubs for fixed-type functions are much simpler *)

let non_variadic_stub oc name =
  fprintf oc "	addis	r11, 0, ha16(L%s$ptr)\n" name;
  fprintf oc "	lwz	r11, lo16(L%s$ptr)(r11)\n" name;
  fprintf oc "	mtctr	r11\n";
  fprintf oc "	bctr\n";
  fprintf oc "	.non_lazy_symbol_pointer\n";
  fprintf oc "L%s$ptr:\n" name;
  fprintf oc "	.indirect_symbol _%s\n" name;
  fprintf oc "	.long	0\n"

let re_variadic_stub = Str.regexp "\\(.*\\)\\$[if]*$"

let print_external_function oc name ef =
  let name = extern_atom name in
  fprintf oc "	.text\n";
  fprintf oc "	.align 2\n";
  fprintf oc "L%s$stub:\n" name;
  if Str.string_match re_variadic_stub name 0
  then variadic_stub oc name (Str.matched_group 1 name) ef.ef_sig.sig_args
  else non_variadic_stub oc name

let print_fundef oc (Coq_pair(name, defn)) =
  match defn with
  | Internal code -> print_function oc name code
  | External ef -> print_external_function oc name ef

let init_data_queue = ref []

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
  | Init_float32 n ->
      fprintf oc "	.long	%ld ; %g \n" (Int32.bits_of_float n) n
  | Init_float64 n ->
      (* .quad not working on all versions of the MacOSX assembler *)
      let b = Int64.bits_of_float n in
      fprintf oc "	.long	%Ld, %Ld ; %g \n"
                 (Int64.shift_right_logical b 32)
                 (Int64.logand b 0xFFFFFFFFL)
                 n
  | Init_space n ->
      let n = camlint_of_z n in
      if n > 0l then fprintf oc "	.space	%ld\n" n
  | Init_pointer id ->
      let lbl = new_label() in
      fprintf oc "	.long	L%d\n" lbl;
      init_data_queue := (lbl, id) :: !init_data_queue

let print_init_data oc id =
  init_data_queue := [];
  List.iter (print_init oc) id;
  let rec print_remainder () =
    match !init_data_queue with
    | [] -> ()
    | (lbl, id) :: rem ->
        init_data_queue := rem;
        fprintf oc "L%d:\n" lbl;
        List.iter (print_init oc) id;
        print_remainder()
  in print_remainder()

let print_var oc (Coq_pair(Coq_pair(name, init_data), _)) =
  match init_data with
  | [] -> ()
  | _  ->
      fprintf oc "	.data\n";
      fprintf oc "	.align	3\n";
      fprintf oc "	.globl	%a\n" print_symb name;
      fprintf oc "%a:\n" print_symb name;
      print_init_data oc init_data

let print_program oc p =
  extfuns := IdentSet.empty;
  List.iter record_extfun p.prog_funct;
  List.iter (print_var oc) p.prog_vars;
  List.iter (print_fundef oc) p.prog_funct


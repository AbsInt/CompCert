(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(* Printing RISC-V assembly code in asm syntax *)

open Printf
open Camlcoq
open Sections
open AST
open Asm
open AisAnnot
open PrintAsmaux
open Fileinfo

(* Module containing the printing functions *)

module Target : TARGET =
  struct

(* Basic printing functions *)

    let comment = "#"

    let symbol        = elf_symbol
    let symbol_offset = elf_symbol_offset
    let label         = elf_label

    let print_label oc lbl = label oc (transl_label lbl)

    let use_abi_name = false

    let int_reg_num_name = function
                     | X1  -> "x1"  | X2  -> "x2"  | X3  -> "x3"
      | X4  -> "x4"  | X5  -> "x5"  | X6  -> "x6"  | X7  -> "x7"
      | X8  -> "x8"  | X9  -> "x9"  | X10 -> "x10" | X11 -> "x11"
      | X12 -> "x12" | X13 -> "x13" | X14 -> "x14" | X15 -> "x15"
      | X16 -> "x16" | X17 -> "x17" | X18 -> "x18" | X19 -> "x19"
      | X20 -> "x20" | X21 -> "x21" | X22 -> "x22" | X23 -> "x23"
      | X24 -> "x24" | X25 -> "x25" | X26 -> "x26" | X27 -> "x27"
      | X28 -> "x28" | X29 -> "x29" | X30 -> "x30" | X31 -> "x31"

    let int_reg_abi_name = function
                     | X1  -> "ra"  | X2  -> "sp"  | X3  -> "gp"
      | X4  -> "tp"  | X5  -> "t0"  | X6  -> "t1"  | X7  -> "t2"
      | X8  -> "s0"  | X9  -> "s1"  | X10 -> "a0"  | X11 -> "a1"
      | X12 -> "a2"  | X13 -> "a3"  | X14 -> "a4"  | X15 -> "a5"
      | X16 -> "a6"  | X17 -> "a7"  | X18 -> "s2"  | X19 -> "s3"
      | X20 -> "s4"  | X21 -> "s5"  | X22 -> "s6"  | X23 -> "s7"
      | X24 -> "s8"  | X25 -> "s9"  | X26 -> "s10" | X27 -> "s11"
      | X28 -> "t3"  | X29 -> "t4"  | X30 -> "t5"  | X31 -> "t6"

    let float_reg_num_name = function
      | F0  -> "f0"  | F1  -> "f1"  | F2  -> "f2"  | F3  -> "f3"
      | F4  -> "f4"  | F5  -> "f5"  | F6  -> "f6"  | F7  -> "f7"
      | F8  -> "f8"  | F9  -> "f9"  | F10 -> "f10" | F11 -> "f11"
      | F12 -> "f12" | F13 -> "f13" | F14 -> "f14" | F15 -> "f15"
      | F16 -> "f16" | F17 -> "f17" | F18 -> "f18" | F19 -> "f19"
      | F20 -> "f20" | F21 -> "f21" | F22 -> "f22" | F23 -> "f23"
      | F24 -> "f24" | F25 -> "f25" | F26 -> "f26" | F27 -> "f27"
      | F28 -> "f28" | F29 -> "f29" | F30 -> "f30" | F31 -> "f31"

    let float_reg_abi_name = function
      | F0  -> "ft0" | F1  -> "ft1" | F2  -> "ft2" | F3  -> "ft3"
      | F4  -> "ft4" | F5  -> "ft5" | F6  -> "ft6" | F7  -> "ft7"
      | F8  -> "fs0" | F9  -> "fs1" | F10 -> "fa0" | F11 -> "fa1"
      | F12 -> "fa2" | F13 -> "fa3" | F14 -> "fa4" | F15 -> "fa5"
      | F16 -> "fa6" | F17 -> "fa7" | F18 -> "fs2" | F19 -> "fs3"
      | F20 -> "fs4" | F21 -> "fs5" | F22 -> "fs6" | F23 -> "fs7"
      | F24 -> "fs8" | F25 -> "fs9" | F26 ->"fs10" | F27 -> "fs11"
      | F28 -> "ft3" | F29 -> "ft4" | F30 -> "ft5" | F31 -> "ft6"

    let int_reg_name   = if use_abi_name then int_reg_abi_name   else int_reg_num_name
    let float_reg_name = if use_abi_name then float_reg_abi_name else float_reg_num_name

    let ireg oc r = output_string oc (int_reg_name r)
    let freg oc r = output_string oc (float_reg_name r)

    let ireg0 oc = function
      | X0 -> output_string oc "x0"
      | X r -> ireg oc r

    let preg oc = function
      | IR r -> ireg oc r
      | FR r -> freg oc r
      | _    -> assert false

    let preg_annot = function
      | IR r -> int_reg_name r
      | FR r -> float_reg_name r
      | _ -> assert false

(* Names of sections *)

    let name_of_section = function
      | Section_text         -> ".text"
      | Section_data i | Section_small_data i ->
          if i then ".data" else "COMM"
      | Section_const i | Section_small_const i ->
          if i then ".section	.rodata" else "COMM"
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
             fprintf oc "	.align 3\n";
             Hashtbl.iter
               (fun bf lbl -> fprintf oc "%a:	.quad	0x%Lx\n" label lbl bf)
               literal64_labels
           end;
         if Hashtbl.length literal32_labels > 0 then
           begin
             fprintf oc "	.align	2\n";
             Hashtbl.iter
               (fun bf lbl ->
                  fprintf oc "%a:	.long	0x%lx\n" label lbl bf)
               literal32_labels
           end;
         reset_literals ()
      end

(* Generate code to load the address of id + ofs in register r *)

    let loadsymbol oc r id ofs =
      if Archi.pic_code () then begin
        assert (ofs = Integers.Ptrofs.zero);
        fprintf oc "	la	%a, %s\n" ireg r (extern_atom id)
      end else begin
        fprintf oc "	lui	%a, %%hi(%a)\n"
                                ireg r symbol_offset (id, ofs);
        fprintf oc "	addi	%a, %a, %%lo(%a)\n"
                                ireg r ireg r symbol_offset (id, ofs)
      end

(* Emit .file / .loc debugging directives *)

    let print_file_line oc file line =
      print_file_line oc comment file line

(*
    let print_location oc loc =
      if loc <> Cutil.no_loc then print_file_line oc (fst loc) (snd loc)
*)

(* Add "w" suffix to 32-bit instructions if we are in 64-bit mode *)
  
    let w oc =
      if Archi.ptr64 then output_string oc "w"

(* Offset part of a load or store *)

    let offset oc = function
    | Ofsimm n -> ptrofs oc n
    | Ofslow(id, ofs) -> fprintf oc "%%lo(%a)" symbol_offset (id, ofs)

(* Printing of instructions *)
    let print_instruction oc = function
      | Pmv(rd, rs) ->
         fprintf oc "	mv	%a, %a\n"     ireg rd ireg rs

      (* 32-bit integer register-immediate instructions *)
      | Paddiw (rd, rs, imm) ->
         fprintf oc "	addi%t	%a, %a, %a\n" w ireg rd ireg0 rs coqint imm
      | Psltiw (rd, rs, imm) ->
         fprintf oc "	slti	%a, %a, %a\n" ireg rd ireg0 rs coqint imm
      | Psltiuw (rd, rs, imm) ->
         fprintf oc "	sltiu	%a, %a, %a\n" ireg rd ireg0 rs coqint imm
      | Pandiw (rd, rs, imm) ->
         fprintf oc "	andi	%a, %a, %a\n" ireg rd ireg0 rs coqint imm
      | Poriw (rd, rs, imm) ->
         fprintf oc "	ori	%a, %a, %a\n" ireg rd ireg0 rs coqint imm
      | Pxoriw (rd, rs, imm) ->
         fprintf oc "	xori	%a, %a, %a\n" ireg rd ireg0 rs coqint imm
      | Pslliw (rd, rs, imm) ->
         fprintf oc "	slli%t	%a, %a, %a\n" w ireg rd ireg0 rs coqint imm
      | Psrliw (rd, rs, imm) ->
         fprintf oc "	srli%t	%a, %a, %a\n" w ireg rd ireg0 rs coqint imm
      | Psraiw (rd, rs, imm) ->
         fprintf oc "	srai%t	%a, %a, %a\n" w ireg rd ireg0 rs coqint imm
      | Pluiw (rd, imm) ->
         fprintf oc "	lui	%a, %a\n"     ireg rd coqint imm

      (* 32-bit integer register-register instructions *)
      | Paddw(rd, rs1, rs2) ->
         fprintf oc "	add%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2
      | Psubw(rd, rs1, rs2) ->
         fprintf oc "	sub%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2

      | Pmulw(rd, rs1, rs2) ->
         fprintf oc "	mul%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2
      | Pmulhw(rd, rs1, rs2) ->  assert (not Archi.ptr64);
         fprintf oc "	mulh	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Pmulhuw(rd, rs1, rs2) ->  assert (not Archi.ptr64);
         fprintf oc "	mulhu	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2

      | Pdivw(rd, rs1, rs2) ->
         fprintf oc "	div%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2
      | Pdivuw(rd, rs1, rs2) ->
         fprintf oc "	divu%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2
      | Premw(rd, rs1, rs2) ->
         fprintf oc "	rem%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2
      | Premuw(rd, rs1, rs2) ->
         fprintf oc "	remu%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2

      | Psltw(rd, rs1, rs2) ->
         fprintf oc "	slt	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Psltuw(rd, rs1, rs2) ->
         fprintf oc "	sltu	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2

      | Pandw(rd, rs1, rs2) ->
         fprintf oc "	and	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Porw(rd, rs1, rs2) ->
         fprintf oc "	or	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Pxorw(rd, rs1, rs2) ->
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Psllw(rd, rs1, rs2) ->
         fprintf oc "	sll%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2
      | Psrlw(rd, rs1, rs2) ->
         fprintf oc "	srl%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2
      | Psraw(rd, rs1, rs2) ->
         fprintf oc "	sra%t	%a, %a, %a\n" w ireg rd ireg0 rs1 ireg0 rs2

      (* 64-bit integer register-immediate instructions *)
      | Paddil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	addi	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Psltil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	slti	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Psltiul (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	sltiu	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Pandil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	andi	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Poril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	ori	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Pxoril (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	xori	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Psllil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	slli	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Psrlil (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	srli	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Psrail (rd, rs, imm) -> assert Archi.ptr64;
         fprintf oc "	srai	%a, %a, %a\n" ireg rd ireg0 rs coqint64 imm
      | Pluil (rd, imm) -> assert Archi.ptr64;
         fprintf oc "	lui	%a, %a\n"     ireg rd coqint64 imm

      (* 64-bit integer register-register instructions *)
      | Paddl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	add	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Psubl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	sub	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2

      | Pmull(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	mul	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Pmulhl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	mulh	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Pmulhul(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	mulhu	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2

      | Pdivl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	div	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Pdivul(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	divu	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Preml(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	rem	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Premul(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	remu	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2

      | Psltl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	slt	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Psltul(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	sltu	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2

      | Pandl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	and	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Porl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	or	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Pxorl(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Pslll(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	sll	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Psrll(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	srl	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
      | Psral(rd, rs1, rs2) -> assert Archi.ptr64;
         fprintf oc "	sra	%a, %a, %a\n" ireg rd ireg0 rs1 ireg0 rs2
  
      (* Unconditional jumps.  Links are always to X1/RA. *)
      (* TODO: fix up arguments for calls to variadics, to move *)
      (* floating point arguments to integer registers.  How? *)
      | Pj_l(l) ->
         fprintf oc "	j	%a\n" print_label l
      | Pj_s(s, sg) ->
         fprintf oc "	j	%a\n" symbol s
      | Pj_r(r, sg) ->
         fprintf oc "	jr	%a\n" ireg r
      | Pjal_s(s, sg) ->
         fprintf oc "	call	%a\n" symbol s
      | Pjal_r(r, sg) ->
         fprintf oc "	jalr	%a\n" ireg r

      (* Conditional branches, 32-bit comparisons *)
      | Pbeqw(rs1, rs2, l) ->
         fprintf oc "	beq	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbnew(rs1, rs2, l) ->
         fprintf oc "	bne	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbltw(rs1, rs2, l) ->
         fprintf oc "	blt	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbltuw(rs1, rs2, l) ->
         fprintf oc "	bltu	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbgew(rs1, rs2, l) ->
         fprintf oc "	bge	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbgeuw(rs1, rs2, l) ->
         fprintf oc "	bgeu	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l

      (* Conditional branches, 64-bit comparisons *)
      | Pbeql(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	beq	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbnel(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	bne	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbltl(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	blt	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbltul(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	bltu	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbgel(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	bge	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l
      | Pbgeul(rs1, rs2, l) -> assert Archi.ptr64;
         fprintf oc "	bgeu	%a, %a, %a\n" ireg0 rs1 ireg0 rs2 print_label l

      (* Loads and stores *)
      | Plb(rd, ra, ofs) ->
         fprintf oc "	lb	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Plbu(rd, ra, ofs) ->
         fprintf oc "	lbu	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Plh(rd, ra, ofs) ->
         fprintf oc "	lh	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Plhu(rd, ra, ofs) ->
         fprintf oc "	lhu	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Plw(rd, ra, ofs) | Plw_a(rd, ra, ofs) ->
         fprintf oc "	lw	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Pld(rd, ra, ofs) | Pld_a(rd, ra, ofs) -> assert Archi.ptr64;
         fprintf oc "	ld	%a, %a(%a)\n" ireg rd offset ofs ireg ra

      | Psb(rd, ra, ofs) ->
         fprintf oc "	sb	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Psh(rd, ra, ofs) ->
         fprintf oc "	sh	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Psw(rd, ra, ofs) | Psw_a(rd, ra, ofs) ->
         fprintf oc "	sw	%a, %a(%a)\n" ireg rd offset ofs ireg ra
      | Psd(rd, ra, ofs) | Psd_a(rd, ra, ofs) -> assert Archi.ptr64;
         fprintf oc "	sd	%a, %a(%a)\n" ireg rd offset ofs ireg ra


      (* Synchronization *)
      | Pfence ->
         fprintf oc "	fence\n"

      (* floating point register move.
         fmv.d preserves single-precision register contents, and hence
         is applicable to both single- and double-precision moves.
       *)
      | Pfmv (fd,fs) ->
         fprintf oc "	fmv.d	%a, %a\n"     freg fd freg fs
      | Pfmvxs (rd,fs) ->
         fprintf oc "	fmv.x.s	%a, %a\n"     ireg rd freg fs
      | Pfmvxd (rd,fs) ->
         fprintf oc "	fmv.x.d	%a, %a\n"     ireg rd freg fs

      (* 32-bit (single-precision) floating point *)
      | Pfls (fd, ra, ofs) ->
         fprintf oc "	flw	%a, %a(%a)\n" freg fd offset ofs ireg ra
      | Pfss (fs, ra, ofs) ->
         fprintf oc "	fsw	%a, %a(%a)\n" freg fs offset ofs ireg ra

      | Pfnegs (fd, fs) ->
         fprintf oc "	fneg.s	%a, %a\n"     freg fd freg fs
      | Pfabss (fd, fs) ->
         fprintf oc "	fabs.s	%a, %a\n"     freg fd freg fs

      | Pfadds (fd, fs1, fs2) ->
         fprintf oc "	fadd.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfsubs (fd, fs1, fs2) ->
         fprintf oc "	fsub.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmuls (fd, fs1, fs2) ->
         fprintf oc "	fmul.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfdivs (fd, fs1, fs2) ->
         fprintf oc "	fdiv.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmins (fd, fs1, fs2) ->
         fprintf oc "	fmin.s	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmaxs (fd, fs1, fs2) ->
         fprintf oc "	fmax.s	%a, %a, %a\n" freg fd freg fs1 freg fs2

      | Pfeqs (rd, fs1, fs2) ->
         fprintf oc "	feq.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2
      | Pflts (rd, fs1, fs2) ->
         fprintf oc "	flt.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2
      | Pfles (rd, fs1, fs2) ->
         fprintf oc "	fle.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2

      | Pfsqrts (fd, fs) ->
         fprintf oc "	fsqrt.s %a, %a\n"     freg fd freg fs

      | Pfmadds (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmadd.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfmsubs (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmsub.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfnmadds (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmadd.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfnmsubs (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmsub.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3

      | Pfcvtws (rd, fs) ->
         fprintf oc "	fcvt.w.s	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtwus (rd, fs) ->
         fprintf oc "	fcvt.wu.s	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtsw (fd, rs) ->
         fprintf oc "	fcvt.s.w	%a, %a\n" freg fd ireg0 rs
      | Pfcvtswu (fd, rs) ->
         fprintf oc "	fcvt.s.wu	%a, %a\n" freg fd ireg0 rs

      | Pfcvtls (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.l.s	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtlus (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.lu.s	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtsl (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.s.l	%a, %a\n" freg fd ireg0 rs
      | Pfcvtslu (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.s.lu	%a, %a\n" freg fd ireg0 rs

      (* 64-bit (double-precision) floating point *)
      | Pfld (fd, ra, ofs) | Pfld_a (fd, ra, ofs) ->
         fprintf oc "	fld	%a, %a(%a)\n" freg fd offset ofs ireg ra
      | Pfsd (fs, ra, ofs) | Pfsd_a (fs, ra, ofs) ->
         fprintf oc "	fsd	%a, %a(%a)\n" freg fs offset ofs ireg ra

      | Pfnegd (fd, fs) ->
         fprintf oc "	fneg.d	%a, %a\n"     freg fd freg fs
      | Pfabsd (fd, fs) ->
         fprintf oc "	fabs.d	%a, %a\n"     freg fd freg fs

      | Pfaddd (fd, fs1, fs2) ->
         fprintf oc "	fadd.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfsubd (fd, fs1, fs2) ->
         fprintf oc "	fsub.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmuld (fd, fs1, fs2) ->
         fprintf oc "	fmul.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfdivd (fd, fs1, fs2) ->
         fprintf oc "	fdiv.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmind (fd, fs1, fs2) ->
         fprintf oc "	fmin.d	%a, %a, %a\n" freg fd freg fs1 freg fs2
      | Pfmaxd (fd, fs1, fs2) ->
         fprintf oc "	fmax.d	%a, %a, %a\n" freg fd freg fs1 freg fs2

      | Pfeqd (rd, fs1, fs2) ->
         fprintf oc "	feq.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2
      | Pfltd (rd, fs1, fs2) ->
         fprintf oc "	flt.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2
      | Pfled (rd, fs1, fs2) ->
         fprintf oc "	fle.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2

      | Pfsqrtd (fd, fs) ->
         fprintf oc "	fsqrt.d	%a, %a\n" freg fd freg fs

      | Pfmaddd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmadd.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfmsubd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmsub.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfnmaddd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmadd.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3
      | Pfnmsubd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmsub.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3

      | Pfcvtwd (rd, fs) ->
         fprintf oc "	fcvt.w.d	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtwud (rd, fs) ->
         fprintf oc "	fcvt.wu.d	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtdw (fd, rs) ->
         fprintf oc "	fcvt.d.w	%a, %a\n" freg fd ireg0 rs
      | Pfcvtdwu (fd, rs) ->
         fprintf oc "	fcvt.d.wu	%a, %a\n" freg fd ireg0 rs

      | Pfcvtld (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.l.d	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtlud (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.lu.d	%a, %a, rtz\n" ireg rd freg fs
      | Pfcvtdl (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.d.l	%a, %a\n" freg fd ireg0 rs
      | Pfcvtdlu (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	fcvt.d.lu	%a, %a\n" freg fd ireg0 rs

      | Pfcvtds (fd, fs) ->
         fprintf oc "	fcvt.d.s	%a, %a\n" freg fd freg fs
      | Pfcvtsd (fd, fs) ->
         fprintf oc "	fcvt.s.d	%a, %a\n" freg fd freg fs

      (* Pseudo-instructions expanded in Asmexpand *)
      | Pallocframe(sz, ofs) ->
         assert false
      | Pfreeframe(sz, ofs) ->
         assert false
      | Pseqw _ | Psnew _ | Pseql _ | Psnel _ | Pcvtl2w _ | Pcvtw2l _ ->
         assert false

      (* Pseudo-instructions that remain *)
      | Plabel lbl ->
         fprintf oc "%a:\n" print_label lbl
      | Ploadsymbol(rd, id, ofs) ->
         loadsymbol oc rd id ofs
      | Ploadsymbol_high(rd, id, ofs) ->
         fprintf oc "	lui	%a, %%hi(%a)\n" ireg rd symbol_offset (id, ofs)
      | Ploadli(rd, n) ->
         let d = camlint64_of_coqint n in
         let lbl = label_literal64 d in
         fprintf oc "	ld	%a, %a %s %Lx\n" ireg rd label lbl comment d
      | Ploadfi(rd, f) ->
         let d   = camlint64_of_coqint(Floats.Float.to_bits f) in
         let lbl = label_literal64 d in
         fprintf oc "	fld	%a, %a, x31 %s %.18g\n"
                    freg rd label lbl comment (camlfloat_of_coqfloat f)
      | Ploadsi(rd, f) ->
         let s   = camlint_of_coqint(Floats.Float32.to_bits f) in
         let lbl = label_literal32 s in
         fprintf oc "	flw	%a, %a, x31 %s %.18g\n"
                    freg rd label lbl comment (camlfloat_of_coqfloat32 f)
      | Pbtbl(r, tbl) ->
         let lbl = new_label() in
         fprintf oc "%s jumptable [ " comment;
         List.iter (fun l -> fprintf oc "%a " print_label l) tbl;
         fprintf oc "]\n";
         fprintf oc "	sll	x5, %a, 2\n" ireg r;
         fprintf oc "	la	x31, %a\n" label lbl;
         fprintf oc "	add	x5, x31, x5\n";
         fprintf oc "	lw	x5, 0(x5)\n";
         fprintf oc "	add	x5, x31, x5\n";
         fprintf oc "	jr	x5\n";
         jumptables := (lbl, tbl) :: !jumptables;
         fprintf oc "%s end pseudoinstr btbl\n" comment
      | Pnop ->
        fprintf oc "	nop\n"
      | Pbuiltin(ef, args, res) ->
         begin match ef with
           | EF_annot(kind,txt, targs) ->
             begin match (P.to_int kind) with
               | 1 -> let annot = annot_text preg_annot "x2" (camlstring_of_coqstring txt) args  in
                 fprintf oc "%s annotation: %S\n" comment annot
               | 2 -> let lbl = new_label () in
                 fprintf oc "%a:\n" label lbl;
                 add_ais_annot lbl preg_annot "x2" (camlstring_of_coqstring txt) args
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

    let address = if Archi.ptr64 then ".quad" else ".long"

    let print_prologue oc =
      fprintf oc "	.option %s\n" (if Archi.pic_code() then "pic" else "nopic");
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

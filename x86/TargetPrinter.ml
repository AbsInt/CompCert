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

(* Printing x86-64 assembly code in asm syntax *)

open Printf
open Camlcoq
open Sections
open AST
open Asm
open AisAnnot
open PrintAsmaux
open Fileinfo

module StringSet = Set.Make(String)

(* Basic printing functions used in definition of the systems *)

let int64_reg_name = function
  | RAX -> "%rax"  | RBX -> "%rbx"  | RCX -> "%rcx"  | RDX -> "%rdx"
  | RSI -> "%rsi"  | RDI -> "%rdi"  | RBP -> "%rbp"  | RSP -> "%rsp"
  | R8  -> "%r8"   | R9  -> "%r9"   | R10 -> "%r10"  | R11 -> "%r11"
  | R12 -> "%r12"  | R13 -> "%r13"  | R14 -> "%r14"  | R15 -> "%r15"

let int32_reg_name = function
  | RAX -> "%eax"  | RBX -> "%ebx"  | RCX -> "%ecx"  | RDX -> "%edx"
  | RSI -> "%esi"  | RDI -> "%edi"  | RBP -> "%ebp"  | RSP -> "%esp"
  | R8  -> "%r8d"  | R9  -> "%r9d"  | R10 -> "%r10d" | R11 -> "%r11d"
  | R12 -> "%r12d" | R13 -> "%r13d" | R14 -> "%r14d" | R15 -> "%r15d"

let int8_reg_name = function
  | RAX -> "%al"  | RBX -> "%bl"  | RCX -> "%cl"  | RDX -> "%dl"
  | RSI -> "%sil" | RDI -> "%dil" | RBP -> "%bpl" | RSP -> "%spl"
  | R8  -> "%r8b"  | R9  -> "%r9b"  | R10 -> "%r10b" | R11 -> "%r11b"
  | R12 -> "%r12b" | R13 -> "%r13b" | R14 -> "%r14b" | R15 -> "%r15b"

let int16_reg_name = function
  | RAX -> "%ax"  | RBX -> "%bx"  | RCX -> "%cx"  | RDX -> "%dx"
  | RSI -> "%si"  | RDI -> "%di"  | RBP -> "%bp"  | RSP -> "%sp"
  | R8  -> "%r8w"  | R9  -> "%r9w"  | R10 -> "%r10w" | R11 -> "%r11w"
  | R12 -> "%r12w" | R13 -> "%r13w" | R14 -> "%r14w" | R15 -> "%r15w"

let float_reg_name = function
  | XMM0 -> "%xmm0"  | XMM1 -> "%xmm1"  | XMM2 -> "%xmm2"  | XMM3 -> "%xmm3"
  | XMM4 -> "%xmm4"  | XMM5 -> "%xmm5"  | XMM6 -> "%xmm6"  | XMM7 -> "%xmm7"
  | XMM8 -> "%xmm8"  | XMM9 -> "%xmm9"  | XMM10 -> "%xmm10" | XMM11 -> "%xmm11"
  | XMM12 -> "%xmm12" | XMM13 -> "%xmm13" | XMM14 -> "%xmm14" | XMM15 -> "%xmm15"

let ireg8 oc r = output_string oc (int8_reg_name r)
let ireg16 oc r = output_string oc (int16_reg_name r)
let ireg32 oc r = output_string oc (int32_reg_name r)
let ireg64 oc r = output_string oc (int64_reg_name r)
let ireg = if Archi.ptr64 then ireg64 else ireg32
let freg oc r = output_string oc (float_reg_name r)

let preg oc = function
  | IR r -> ireg oc r
  | FR r -> freg oc r
  | _    -> assert false

let preg_annot = function
  | IR r -> if Archi.ptr64 then int64_reg_name r else int32_reg_name r
  | FR r -> float_reg_name r
  | _ -> assert false

let ais_int64_reg_name = function
  | RAX -> "rax"  | RBX -> "rbx"  | RCX -> "rcx"  | RDX -> "rdx"
  | RSI -> "rsi"  | RDI -> "rdi"  | RBP -> "rbp"  | RSP -> "rsp"
  | R8  -> "r8"   | R9  -> "r9"   | R10 -> "r10"  | R11 -> "r11"
  | R12 -> "r12"  | R13 -> "r13"  | R14 -> "r14"  | R15 -> "r15"

let ais_int32_reg_name = function
  | RAX -> "eax"  | RBX -> "ebx"  | RCX -> "ecx"  | RDX -> "edx"
  | RSI -> "esi"  | RDI -> "edi"  | RBP -> "ebp"  | RSP -> "esp"
  | R8  -> "r8d"  | R9  -> "r9d"  | R10 -> "r10d" | R11 -> "r11d"
  | R12 -> "r12d" | R13 -> "r13d" | R14 -> "r14d" | R15 -> "r15d"

let preg_ais_annot = function
  | IR r -> if Archi.ptr64 then ais_int64_reg_name r else ais_int32_reg_name r
  | FR r -> float_reg_name r
  | _ -> assert false

let z oc n = output_string oc (Z.to_string n)

(* 32/64 bit dependencies *)

let data_pointer = if Archi.ptr64 then ".quad" else ".long"

(* The comment deliminiter *)
let comment = "#"

(* Base-2 log of a Caml integer *)
let rec log2 n =
  assert (n > 0);
  if n = 1 then 0 else 1 + log2 (n lsr 1)

(* System dependend printer functions *)
module type SYSTEM =
    sig
      val raw_symbol: out_channel -> string -> unit
      val symbol: out_channel -> P.t -> unit
      val label: out_channel -> int -> unit
      val name_of_section: section_name -> string
      val stack_alignment: int
      val print_align: out_channel -> int -> unit
      val print_mov_rs: out_channel -> ireg -> ident -> unit
      val print_fun_info:  out_channel -> P.t -> unit
      val print_var_info: out_channel -> P.t -> unit
      val print_epilogue: out_channel -> unit
      val print_comm_decl: out_channel -> P.t -> Z.t -> int -> unit
      val print_lcomm_decl: out_channel -> P.t -> Z.t -> int -> unit
    end

(* Printer functions for ELF *)
module ELF_System : SYSTEM =
  struct

    let raw_symbol oc s =
      fprintf oc "%s" s

    let symbol = elf_symbol

    let label = elf_label

    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i | Section_small_data i ->
          if i then ".data" else "COMM"
      | Section_const i | Section_small_const i ->
          if i then ".section	.rodata" else "COMM"
      | Section_string -> ".section	.rodata"
      | Section_literal -> ".section	.rodata.cst8,\"aM\",@progbits,8"
      | Section_jumptable -> ".text"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",@progbits"
            s (if wr then "w" else "") (if ex then "x" else "")
      | Section_debug_info _ -> ".section	.debug_info,\"\",@progbits"
      | Section_debug_loc -> ".section	.debug_loc,\"\",@progbits"
      | Section_debug_line _ -> ".section	.debug_line,\"\",@progbits"
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",@progbits"
      | Section_debug_ranges -> ".section	.debug_ranges,\"\",@progbits"
      | Section_debug_str -> ".section	.debug_str,\"MS\",@progbits,1"
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",\"\",@note"

    let stack_alignment = 16

    let print_align oc n =
      fprintf oc "	.align	%d\n" n

    let print_mov_rs oc rd id =
      if Archi.ptr64
      then fprintf oc "	movq    %a@GOTPCREL(%%rip), %a\n" symbol id ireg64 rd
      else fprintf oc "	movl	$%a, %a\n" symbol id ireg32 rd

    let print_fun_info = elf_print_fun_info

    let print_var_info = elf_print_var_info

    let print_epilogue _ = ()

    let print_comm_decl oc name sz al =
      fprintf oc "	.comm	%a, %s, %d\n" symbol name (Z.to_string sz) al

    let print_lcomm_decl oc name sz al =
      fprintf oc "	.local	%a\n" symbol name;
      print_comm_decl oc name sz al

  end

(* Printer functions for MacOS *)
module MacOS_System : SYSTEM =
  struct

    let raw_symbol oc s =
     fprintf oc "_%s" s

    let symbol oc symb =
      raw_symbol oc (extern_atom symb)

    let label oc lbl =
      fprintf oc "L%d" lbl

    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i | Section_small_data i ->
          if i then ".data" else "COMM"
      | Section_const i  | Section_small_const i ->
          if i then ".const" else "COMM"
      | Section_string -> ".const"
      | Section_literal -> ".literal8"
      | Section_jumptable -> ".text"  (* needed in 64 bits, not a problem in 32 bits *)
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\", %s, %s"
            (if wr then "__DATA" else "__TEXT") s
            (if ex then "regular, pure_instructions" else "regular")
      | Section_debug_info _ ->	".section	__DWARF,__debug_info,regular,debug"
      | Section_debug_loc  -> ".section	__DWARF,__debug_loc,regular,debug"
      | Section_debug_line _ -> ".section	__DWARF,__debug_line,regular,debug"
      | Section_debug_str -> ".section	__DWARF,__debug_str,regular,debug"
      | Section_debug_ranges -> ".section	__DWARF,__debug_ranges,regular,debug"
      | Section_debug_abbrev -> ".section	__DWARF,__debug_abbrev,regular,debug"
      | Section_ais_annotation -> assert false (* Not supported under MacOS *)


    let stack_alignment =  16 (* mandatory *)

    let print_align oc n =
      fprintf oc "	.align	%d\n" (log2 n)

    let indirect_symbols : StringSet.t ref = ref StringSet.empty

    let print_mov_rs oc rd id =
      if Archi.ptr64 then begin
        fprintf oc "	movq    %a@GOTPCREL(%%rip), %a\n" symbol id ireg64 rd
      end else begin
        let id = extern_atom id in
        indirect_symbols := StringSet.add id !indirect_symbols;
        fprintf oc "	movl	L%a$non_lazy_ptr, %a\n" raw_symbol id ireg rd
      end

    let print_fun_info _ _ = ()

    let print_var_info _ _ = ()

    let print_epilogue oc =
      if not Archi.ptr64 then begin
        fprintf oc "	.section __IMPORT,__pointers,non_lazy_symbol_pointers\n";
        StringSet.iter
          (fun s ->
            fprintf oc "L%a$non_lazy_ptr:\n" raw_symbol s;
            fprintf oc "	.indirect_symbol %a\n" raw_symbol s;
            fprintf oc "	.long	0\n")
          !indirect_symbols;
        indirect_symbols := StringSet.empty
      end

    let print_comm_decl oc name sz al =
      fprintf oc "	.comm	%a, %s, %d\n"
                 symbol name (Z.to_string sz) (log2 al)

    let print_lcomm_decl oc name sz al =
      fprintf oc "	.lcomm	%a, %s, %d\n"
                 symbol name (Z.to_string sz) (log2 al)

  end

(* Printer functions for Cygwin *)
module Cygwin_System : SYSTEM =
  struct

    let raw_symbol oc s =
       fprintf oc "_%s" s

    let symbol oc symb =
      raw_symbol oc (extern_atom symb)

    let label oc lbl =
       fprintf oc "L%d" lbl

    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i | Section_small_data i ->
          if i then ".data" else "COMM"
      | Section_const i | Section_small_const i ->
          if i then ".section	.rdata,\"dr\"" else "COMM"
      | Section_string -> ".section	.rdata,\"dr\""
      | Section_literal -> ".section	.rdata,\"dr\""
      | Section_jumptable -> ".text"
      | Section_user(s, wr, ex) ->
          sprintf ".section	%s, \"%s\"\n"
            s (if ex then "xr" else if wr then "d" else "dr")
      | Section_debug_info _ -> ".section	.debug_info,\"dr\""
      | Section_debug_loc ->  ".section	.debug_loc,\"dr\""
      | Section_debug_line _ -> ".section	.debug_line,\"dr\""
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"dr\""
      | Section_debug_ranges -> ".section	.debug_ranges,\"dr\""
      | Section_debug_str-> assert false (* Should not be used *)
      | Section_ais_annotation -> assert false (* Not supported for coff binaries *)

    let stack_alignment = 8 (* minimum is 4, 8 is better for perfs *)

    let print_align oc n =
      fprintf oc "	.balign	%d\n" n

    let print_mov_rs oc rd id =
      fprintf oc "	movl	$%a, %a\n" symbol id ireg rd

    let print_fun_info _ _  = ()

    let print_var_info _ _ = ()

    let print_epilogue _ = ()

    let print_comm_decl oc name sz al =
      fprintf oc "	.comm   %a, %s, %d\n" 
                 symbol name (Z.to_string sz) (log2 al)

    let print_lcomm_decl oc name sz al =
      fprintf oc "	.lcomm   %a, %s, %d\n" 
                 symbol name (Z.to_string sz) (log2 al)

  end


module Target(System: SYSTEM):TARGET =
  struct
    open System
    let symbol = symbol

(*  Basic printing functions *)

    let addressing_gen ireg oc (Addrmode(base, shift, cst)) =
      begin match cst with
      | Datatypes.Coq_inl n ->
          fprintf oc "%s" (Z.to_string n)
      | Datatypes.Coq_inr(id, ofs) ->
          if Archi.ptr64 then begin
            (* RIP-relative addressing *)
            let ofs' = Z.to_int64 ofs in
            if ofs' = 0L
            then fprintf oc "%a(%%rip)" symbol id
            else fprintf oc "(%a + %Ld)(%%rip)" symbol id ofs'
          end else begin
            (* Absolute addressing *)
            let ofs' = Z.to_int32 ofs in
            if ofs' = 0l
            then fprintf oc "%a" symbol id
            else fprintf oc "(%a + %ld)" symbol id ofs'
          end
      end;
      begin match base, shift with
      | None, None -> ()
      | Some r1, None -> fprintf oc "(%a)" ireg r1
      | None, Some(r2,sc) -> fprintf oc "(,%a,%a)" ireg r2 z sc
      | Some r1, Some(r2,sc) -> fprintf oc "(%a,%a,%a)" ireg r1 ireg r2 z sc
      end

    let addressing32 = addressing_gen ireg32
    let addressing64 = addressing_gen ireg64
    let addressing = addressing_gen ireg

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

    let section oc sec =
      fprintf oc "	%s\n" (name_of_section sec)

(* For "abs" and "neg" FP operations *)

    let need_masks = ref false

(* Emit .file / .loc debugging directives *)

    let print_file_line oc file line =
      print_file_line oc comment file line

(* In 64-bit mode use RIP-relative addressing to designate labels *)

    let rip_rel =
      if Archi.ptr64 then "(%rip)" else ""

(* Large 64-bit immediates (bigger than a 32-bit signed integer) are
   not supported by the processor.  Turn them into memory operands. *)

    let intconst64 oc n =
      let n1 = camlint64_of_coqint n in
      let n2 = Int64.to_int32 n1 in
      if n1 = Int64.of_int32 n2 then
        (* fit in a 32-bit signed integer, can use as immediate *)
        fprintf oc "$%ld" n2
      else begin
        (* put the constant in memory and use a PC-relative memory operand *)
        let lbl = label_literal64 n1 in
        fprintf oc "%a(%%rip)" label lbl
      end



(* Printing of instructions *)

(* Reminder on AT&T syntax: op source, dest *)

    let print_instruction oc = function
        (* Moves *)
      | Pmov_rr(rd, r1) ->
          if Archi.ptr64
          then fprintf oc "	movq	%a, %a\n" ireg64 r1 ireg64 rd
          else fprintf oc "	movl	%a, %a\n" ireg32 r1 ireg32 rd
      | Pmovl_ri(rd, n) ->
          fprintf oc "	movl	$%ld, %a\n" (camlint_of_coqint n) ireg32 rd
      | Pmovq_ri(rd, n) ->
          let n1 = camlint64_of_coqint n in
          let n2 = Int64.to_int32 n1 in
          if n1 = Int64.of_int32 n2 then
            fprintf oc "	movq	$%ld, %a\n" n2 ireg64 rd
          else
            fprintf oc "	movabsq	$%Ld, %a\n" n1 ireg64 rd
      | Pmov_rs(rd, id) ->
          print_mov_rs oc rd id
      | Pmovl_rm(rd, a) ->
          fprintf oc "	movl	%a, %a\n" addressing a ireg32 rd
      | Pmovq_rm(rd, a) ->
          fprintf oc "	movq	%a, %a\n" addressing a ireg64 rd
      | Pmov_rm_a(rd, a) ->
          if Archi.ptr64
          then fprintf oc "	movq	%a, %a\n" addressing a ireg64 rd
          else fprintf oc "	movl	%a, %a\n" addressing a ireg32 rd
      | Pmovl_mr(a, r1) ->
          fprintf oc "	movl	%a, %a\n" ireg32 r1 addressing a
      | Pmovq_mr(a, r1) ->
          fprintf oc "	movq	%a, %a\n" ireg64 r1 addressing a
      | Pmov_mr_a(a, r1) ->
          if Archi.ptr64
          then fprintf oc "	movq	%a, %a\n" ireg64 r1 addressing a
          else fprintf oc "	movl	%a, %a\n" ireg32 r1 addressing a
      | Pmovsd_ff(rd, r1) ->
          fprintf oc "	movapd	%a, %a\n" freg r1 freg rd
      | Pmovsd_fi(rd, n) ->
          let b = camlint64_of_coqint (Floats.Float.to_bits n) in
          let lbl = label_literal64 b in
          fprintf oc "	movsd	%a%s, %a %s %.18g\n"
                     label lbl rip_rel
                     freg rd comment (camlfloat_of_coqfloat n)
      | Pmovsd_fm(rd, a) | Pmovsd_fm_a(rd, a) ->
          fprintf oc "	movsd	%a, %a\n" addressing a freg rd
      | Pmovsd_mf(a, r1) | Pmovsd_mf_a(a, r1) ->
          fprintf oc "	movsd	%a, %a\n" freg r1 addressing a
      | Pmovss_fi(rd, n) ->
          let b = camlint_of_coqint (Floats.Float32.to_bits n) in
          let lbl = label_literal32 b in
          fprintf oc "	movss	%a%s, %a %s %.18g\n"
                     label lbl rip_rel
                     freg rd comment (camlfloat_of_coqfloat32 n)
      | Pmovss_fm(rd, a) ->
          fprintf oc "	movss	%a, %a\n" addressing a freg rd
      | Pmovss_mf(a, r1) ->
          fprintf oc "	movss	%a, %a\n" freg r1 addressing a
      | Pfldl_m(a) ->
          fprintf oc "	fldl	%a\n" addressing a
      | Pfstpl_m(a) ->
          fprintf oc "	fstpl	%a\n" addressing a
      | Pflds_m(a) ->
          fprintf oc "	flds	%a\n" addressing a
      | Pfstps_m(a) ->
          fprintf oc "	fstps	%a\n" addressing a
            (* Moves with conversion *)
      | Pmovb_mr(a, r1) ->
          fprintf oc "	movb	%a, %a\n" ireg8 r1 addressing a
      | Pmovw_mr(a, r1) ->
          fprintf oc "	movw	%a, %a\n" ireg16 r1 addressing a
      | Pmovzb_rr(rd, r1) ->
          fprintf oc "	movzbl	%a, %a\n" ireg8 r1 ireg32 rd
      | Pmovzb_rm(rd, a) ->
          fprintf oc "	movzbl	%a, %a\n" addressing a ireg32 rd
      | Pmovsb_rr(rd, r1) ->
          fprintf oc "	movsbl	%a, %a\n" ireg8 r1 ireg32 rd
      | Pmovsb_rm(rd, a) ->
          fprintf oc "	movsbl	%a, %a\n" addressing a ireg32 rd
      | Pmovzw_rr(rd, r1) ->
          fprintf oc "	movzwl	%a, %a\n" ireg16 r1 ireg32 rd
      | Pmovzw_rm(rd, a) ->
          fprintf oc "	movzwl	%a, %a\n" addressing a ireg32 rd
      | Pmovsw_rr(rd, r1) ->
          fprintf oc "	movswl	%a, %a\n" ireg16 r1 ireg32 rd
      | Pmovsw_rm(rd, a) ->
          fprintf oc "	movswl	%a, %a\n" addressing a ireg32 rd
      | Pmovzl_rr(rd, r1) ->
          fprintf oc "	movl	%a, %a\n" ireg32 r1 ireg32 rd
          (* movl sets the high 32 bits of the destination to zero *)
      | Pmovsl_rr(rd, r1) ->
          fprintf oc "	movslq	%a, %a\n" ireg32 r1 ireg64 rd
      | Pmovls_rr(rd) ->
          ()   (* nothing to do *)
      | Pcvtsd2ss_ff(rd, r1) ->
          fprintf oc "	cvtsd2ss %a, %a\n" freg r1 freg rd
      | Pcvtss2sd_ff(rd, r1) ->
          fprintf oc "	cvtss2sd %a, %a\n" freg r1 freg rd
      | Pcvttsd2si_rf(rd, r1) ->
          fprintf oc "	cvttsd2si %a, %a\n" freg r1 ireg32 rd
      | Pcvtsi2sd_fr(rd, r1) ->
          fprintf oc "	cvtsi2sd %a, %a\n" ireg32 r1 freg rd
      | Pcvttss2si_rf(rd, r1) ->
          fprintf oc "	cvttss2si %a, %a\n" freg r1 ireg32 rd
      | Pcvtsi2ss_fr(rd, r1) ->
          fprintf oc "	cvtsi2ss %a, %a\n" ireg32 r1 freg rd
      | Pcvttsd2sl_rf(rd, r1) ->
          fprintf oc "	cvttsd2si %a, %a\n" freg r1 ireg64 rd
      | Pcvtsl2sd_fr(rd, r1) ->
          fprintf oc "	cvtsi2sdq %a, %a\n" ireg64 r1 freg rd
      | Pcvttss2sl_rf(rd, r1) ->
          fprintf oc "	cvttss2si %a, %a\n" freg r1 ireg64 rd
      | Pcvtsl2ss_fr(rd, r1) ->
          fprintf oc "	cvtsi2ssq %a, %a\n" ireg64 r1 freg rd
            (* Arithmetic and logical operations over integers *)
      | Pleal(rd, a) ->
          fprintf oc "	leal	%a, %a\n" addressing32 a ireg32 rd
      | Pleaq(rd, a) ->
          fprintf oc "	leaq	%a, %a\n" addressing64 a ireg64 rd
      | Pnegl(rd) ->
          fprintf oc "	negl	%a\n" ireg32 rd
      | Pnegq(rd) ->
          fprintf oc "	negq	%a\n" ireg64 rd
      | Paddl_ri (res,n) ->
	  fprintf oc "	addl	$%ld, %a\n" (camlint_of_coqint n) ireg32 res
      | Paddq_ri (res,n) ->
	  fprintf oc "	addq	%a, %a\n" intconst64 n ireg64 res
      | Psubl_rr(rd, r1) ->
          fprintf oc "	subl	%a, %a\n" ireg32 r1 ireg32 rd
      | Psubq_rr(rd, r1) ->
          fprintf oc "	subq	%a, %a\n" ireg64 r1 ireg64 rd
      | Pimull_rr(rd, r1) ->
          fprintf oc "	imull	%a, %a\n" ireg32 r1 ireg32 rd
      | Pimulq_rr(rd, r1) ->
          fprintf oc "	imulq	%a, %a\n" ireg64 r1 ireg64 rd
      | Pimull_ri(rd, n) ->
          fprintf oc "	imull	$%a, %a\n" coqint n ireg32 rd
      | Pimulq_ri(rd, n) ->
          fprintf oc "	imulq	%a, %a\n" intconst64 n ireg64 rd
      | Pimull_r(r1) ->
          fprintf oc "	imull	%a\n" ireg32 r1
      | Pimulq_r(r1) ->
          fprintf oc "	imulq	%a\n" ireg64 r1
      | Pmull_r(r1) ->
          fprintf oc "	mull	%a\n" ireg32 r1
      | Pmulq_r(r1) ->
          fprintf oc "	mulq	%a\n" ireg64 r1
      | Pcltd ->
          fprintf oc "	cltd\n"
      | Pcqto ->
          fprintf oc "	cqto\n";
      | Pdivl(r1) ->
          fprintf oc "	divl	%a\n" ireg32 r1
      | Pdivq(r1) ->
          fprintf oc "	divq	%a\n" ireg64 r1
      | Pidivl(r1) ->
          fprintf oc "	idivl	%a\n" ireg32 r1
      | Pidivq(r1) ->
          fprintf oc "	idivq	%a\n" ireg64 r1
      | Pandl_rr(rd, r1) ->
          fprintf oc "	andl	%a, %a\n" ireg32 r1 ireg32 rd
      | Pandq_rr(rd, r1) ->
          fprintf oc "	andq	%a, %a\n" ireg64 r1 ireg64 rd
      | Pandl_ri(rd, n) ->
          fprintf oc "	andl	$%a, %a\n" coqint n ireg32 rd
      | Pandq_ri(rd, n) ->
          fprintf oc "	andq	%a, %a\n" intconst64 n ireg64 rd
      | Porl_rr(rd, r1) ->
          fprintf oc "	orl	%a, %a\n" ireg32 r1 ireg32 rd
      | Porq_rr(rd, r1) ->
          fprintf oc "	orq	%a, %a\n" ireg64 r1 ireg64 rd
      | Porl_ri(rd, n) ->
          fprintf oc "	orl	$%a, %a\n" coqint n ireg32 rd
      | Porq_ri(rd, n) ->
          fprintf oc "	orq	%a, %a\n" intconst64 n ireg64 rd
      | Pxorl_r(rd) ->
          fprintf oc "	xorl	%a, %a\n" ireg32 rd ireg32 rd
      | Pxorq_r(rd) ->
          fprintf oc "	xorq	%a, %a\n" ireg64 rd ireg64 rd
      | Pxorl_rr(rd, r1) ->
          fprintf oc "	xorl	%a, %a\n" ireg32 r1 ireg32 rd
      | Pxorq_rr(rd, r1) ->
          fprintf oc "	xorq	%a, %a\n" ireg64 r1 ireg64 rd
      | Pxorl_ri(rd, n) ->
          fprintf oc "	xorl	$%a, %a\n" coqint n ireg32 rd
      | Pxorq_ri(rd, n) ->
          fprintf oc "	xorq	%a, %a\n" intconst64 n ireg64 rd
      | Pnotl(rd) ->
          fprintf oc "	notl	%a\n" ireg32 rd
      | Pnotq(rd) ->
          fprintf oc "	notq	%a\n" ireg64 rd
      | Psall_rcl(rd) ->
          fprintf oc "	sall	%%cl, %a\n" ireg32 rd
      | Psalq_rcl(rd) ->
          fprintf oc "	salq	%%cl, %a\n" ireg64 rd
      | Psall_ri(rd, n) ->
          fprintf oc "	sall	$%a, %a\n" coqint n ireg32 rd
      | Psalq_ri(rd, n) ->
          fprintf oc "	salq	$%a, %a\n" coqint n ireg64 rd
      | Pshrl_rcl(rd) ->
          fprintf oc "	shrl	%%cl, %a\n" ireg32 rd
      | Pshrq_rcl(rd) ->
          fprintf oc "	shrq	%%cl, %a\n" ireg64 rd
      | Pshrl_ri(rd, n) ->
          fprintf oc "	shrl	$%a, %a\n" coqint n ireg32 rd
      | Pshrq_ri(rd, n) ->
          fprintf oc "	shrq	$%a, %a\n" coqint n ireg64 rd
      | Psarl_rcl(rd) ->
          fprintf oc "	sarl	%%cl, %a\n" ireg32 rd
      | Psarq_rcl(rd) ->
          fprintf oc "	sarq	%%cl, %a\n" ireg64 rd
      | Psarl_ri(rd, n) ->
          fprintf oc "	sarl	$%a, %a\n" coqint n ireg32 rd
      | Psarq_ri(rd, n) ->
          fprintf oc "	sarq	$%a, %a\n" coqint n ireg64 rd
      | Pshld_ri(rd, r1, n) ->
          fprintf oc "	shldl	$%a, %a, %a\n" coqint n ireg32 r1 ireg32 rd
      | Prorl_ri(rd, n) ->
          fprintf oc "	rorl	$%a, %a\n" coqint n ireg32 rd
      | Prorq_ri(rd, n) ->
          fprintf oc "	rorq	$%a, %a\n" coqint n ireg64 rd
      | Pcmpl_rr(r1, r2) ->
          fprintf oc "	cmpl	%a, %a\n" ireg32 r2 ireg32 r1
      | Pcmpq_rr(r1, r2) ->
          fprintf oc "	cmpq	%a, %a\n" ireg64 r2 ireg64 r1
      | Pcmpl_ri(r1, n) ->
          fprintf oc "	cmpl	$%a, %a\n" coqint n ireg32 r1
      | Pcmpq_ri(r1, n) ->
          fprintf oc "	cmpq	%a, %a\n" intconst64 n ireg64 r1
      | Ptestl_rr(r1, r2) ->
          fprintf oc "	testl	%a, %a\n" ireg32 r2 ireg32 r1
      | Ptestq_rr(r1, r2) ->
          fprintf oc "	testq	%a, %a\n" ireg64 r2 ireg64 r1
      | Ptestl_ri(r1, n) ->
          fprintf oc "	testl	$%a, %a\n" coqint n ireg32 r1
      | Ptestq_ri(r1, n) ->
          fprintf oc "	testl	%a, %a\n" intconst64 n ireg64 r1
      | Pcmov(c, rd, r1) ->
          fprintf oc "	cmov%s	%a, %a\n" (name_of_condition c) ireg r1 ireg rd
      | Psetcc(c, rd) ->
          fprintf oc "	set%s	%a\n" (name_of_condition c) ireg8 rd;
          fprintf oc "	movzbl	%a, %a\n" ireg8 rd ireg32 rd
            (* Arithmetic operations over floats *)
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
          fprintf oc "	xorpd	%a%s, %a\n"
                     raw_symbol "__negd_mask" rip_rel freg rd
      | Pabsd (rd) ->
          need_masks := true;
          fprintf oc "	andpd	%a%s, %a\n"
                     raw_symbol "__absd_mask" rip_rel freg rd
      | Pcomisd_ff(r1, r2) ->
          fprintf oc "	comisd	%a, %a\n" freg r2 freg r1
      | Pxorpd_f (rd) ->
          fprintf oc "	xorpd	%a, %a\n" freg rd freg rd
      | Padds_ff(rd, r1) ->
          fprintf oc "	addss	%a, %a\n" freg r1 freg rd
      | Psubs_ff(rd, r1) ->
          fprintf oc "	subss	%a, %a\n" freg r1 freg rd
      | Pmuls_ff(rd, r1) ->
          fprintf oc "	mulss	%a, %a\n" freg r1 freg rd
      | Pdivs_ff(rd, r1) ->
          fprintf oc "	divss	%a, %a\n" freg r1 freg rd
      | Pnegs (rd) ->
          need_masks := true;
          fprintf oc "	xorpd	%a%s, %a\n"
                     raw_symbol "__negs_mask" rip_rel freg rd
      | Pabss (rd) ->
          need_masks := true;
          fprintf oc "	andpd	%a%s, %a\n"
                     raw_symbol "__abss_mask" rip_rel freg rd
      | Pcomiss_ff(r1, r2) ->
          fprintf oc "	comiss	%a, %a\n" freg r2 freg r1
      | Pxorps_f (rd) ->
          fprintf oc "	xorpd	%a, %a\n" freg rd freg rd
            (* Branches and calls *)
      | Pjmp_l(l) ->
          fprintf oc "	jmp	%a\n" label (transl_label l)
      | Pjmp_s(f, sg) ->
          fprintf oc "	jmp	%a\n" symbol f
      | Pjmp_r(r, sg) ->
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
          jumptables := (l, tbl) :: !jumptables;
          if Archi.ptr64 then begin
            let (tmp1, tmp2) =
              if r = RAX then (RDX, RAX) else (RAX, RDX) in
            fprintf oc "	leaq	%a(%%rip), %a\n" label l ireg tmp1;
            fprintf oc "	movslq	(%a, %a, 4), %a\n" ireg tmp1 ireg r ireg tmp2;
            fprintf oc "	addq	%a, %a\n" ireg tmp2 ireg tmp1;
            fprintf oc "	jmp	*%a\n" ireg tmp1
          end else begin
            fprintf oc "	jmp	*%a(, %a, 4)\n" label l ireg r
          end
      | Pcall_s(f, sg) ->
          fprintf oc "	call	%a\n" symbol f;
          if (not Archi.ptr64) && sg.sig_cc.cc_structret then
            fprintf oc "	pushl	%%eax\n"
      | Pcall_r(r, sg) ->
          fprintf oc "	call	*%a\n" ireg r;
          if (not Archi.ptr64) && sg.sig_cc.cc_structret then
            fprintf oc "	pushl	%%eax\n"
      | Pret ->
          if (not Archi.ptr64)
          && (!current_function_sig).sig_cc.cc_structret then begin
            fprintf oc "	movl	0(%%esp), %%eax\n";
            fprintf oc "	ret	$4\n"
          end else begin
            fprintf oc "	ret\n"
          end
      (* Instructions produced by Asmexpand *)
      | Padcl_ri (res,n) ->
	 fprintf oc "  	adcl	$%ld, %a\n" (camlint_of_coqint n) ireg32 res;
      | Padcl_rr (res,a1) ->
	 fprintf oc "  	adcl	%a, %a\n" ireg32 a1 ireg32 res;
      | Paddl_rr (res,a1) ->
	 fprintf oc "	addl	%a, %a\n" ireg32 a1 ireg32 res;
      | Paddl_mi (addr,n) ->
	 fprintf oc "	addl	$%ld, %a\n" (camlint_of_coqint n) addressing addr
      | Pbsfl (res,a1) ->
	 fprintf oc "	bsfl	%a, %a\n" ireg32 a1 ireg32 res
      | Pbsfq (res,a1) ->
	 fprintf oc "	bsfq	%a, %a\n" ireg64 a1 ireg64 res
      | Pbsrl (res,a1) ->
	 fprintf oc "	bsrl	%a, %a\n" ireg32 a1 ireg32 res
      | Pbsrq (res,a1) ->
	 fprintf oc "	bsrq	%a, %a\n" ireg64 a1 ireg64 res
      | Pbswap64 res ->
	 fprintf oc "	bswap	%a\n" ireg64 res
      | Pbswap32 res ->
	 fprintf oc "	bswap	%a\n" ireg32 res
      | Pbswap16 res ->
	 fprintf oc "	rolw	$8, %a\n" ireg16 res
      | Pcfi_adjust sz ->
	 cfi_adjust oc (camlint_of_coqint sz)
      | Pfmadd132 (res,a1,a2) ->
	 fprintf oc "	vfmadd132sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfmadd213 (res,a1,a2) ->
	 fprintf oc "	vfmadd213sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfmadd231 (res,a1,a2) ->
	 fprintf oc "	vfmadd231sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfmsub132 (res,a1,a2) ->
	 fprintf oc "	vfmsub132sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfmsub213 (res,a1,a2) ->
	 fprintf oc "	vfmsub213sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfmsub231 (res,a1,a2) ->
	 fprintf oc "	vfmsub231sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfnmadd132 (res,a1,a2) ->
	 fprintf oc "	vfnmadd132sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfnmadd213 (res,a1,a2) ->
	 fprintf oc "	vfnmadd213sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfnmadd231 (res,a1,a2) ->
	 fprintf oc "	vfnmadd231sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfnmsub132 (res,a1,a2) ->
	 fprintf oc "	vfnmsub132sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfnmsub213 (res,a1,a2) ->
	 fprintf oc "	vfnmsub213sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pfnmsub231 (res,a1,a2) ->
	 fprintf oc "	vfnmsub231sd	%a, %a, %a\n" freg a1 freg a2 freg res
      | Pmaxsd (res,a1) ->
	 fprintf oc "	maxsd	%a, %a\n" freg a1 freg res
      | Pminsd (res,a1) ->
	 fprintf oc "	minsd	%a, %a\n" freg a1 freg res
      | Pmovb_rm (rd,a) ->
	 fprintf oc "	movb	%a, %a\n" addressing a ireg8 rd
      | Pmovsq_mr(a, rs) ->
          fprintf oc "	movq	%a, %a\n" freg rs addressing a
      | Pmovsq_rm(rd, a) ->
          fprintf oc "	movq	%a, %a\n" addressing a freg rd
      | Pmovsb ->
	 fprintf oc "	movsb\n";
      | Pmovsw ->
	 fprintf oc "	movsw\n";
      | Pmovw_rm (rd, a) ->
          fprintf oc "	movw	%a, %a\n" addressing a ireg16 rd
      | Pnop ->
          fprintf oc "	nop\n"
      | Prep_movsl ->
	 fprintf oc "	rep	movsl\n"
      | Psbbl_rr (res,a1) ->
	 fprintf oc "	sbbl	%a, %a\n" ireg32 a1 ireg32 res
      | Psqrtsd (res,a1) ->
	 fprintf oc "	sqrtsd	%a, %a\n" freg a1 freg res
      | Psubl_ri (res,n) ->
	  fprintf oc "	subl	$%ld, %a\n" (camlint_of_coqint n) ireg32 res;
      | Psubq_ri (res,n) ->
	  fprintf oc "	subq	%a, %a\n" intconst64 n ireg64 res;
      (* Pseudo-instructions *)
      | Plabel(l) ->
          fprintf oc "%a:\n" label (transl_label l)
      | Pallocframe(sz, ofs_ra, ofs_link)
      | Pfreeframe(sz, ofs_ra, ofs_link) ->
	 assert false
      | Pbuiltin(ef, args, res) ->
          begin match ef with
            | EF_annot(kind,txt, targs) ->
                begin match (P.to_int kind) with
                  | 1 ->  let annot = annot_text preg_annot "esp" (camlstring_of_coqstring txt) args in
                    fprintf oc "%s annotation: %S\n" comment annot
                  | 2 -> let lbl = new_label () in
                    fprintf oc "%a:\n" label lbl;
                    let sp = if Archi.ptr64 then "rsp" else "esp" in
                    add_ais_annot lbl preg_ais_annot sp (camlstring_of_coqstring txt) args
                  | _ -> assert false
                end
          | EF_debug(kind, txt, targs) ->
              print_debug_info comment print_file_line preg_annot "%esp" oc
                               (P.to_int kind) (extern_atom txt) args
          | EF_inline_asm(txt, sg, clob) ->
              fprintf oc "%s begin inline assembly\n\t" comment;
              print_inline_asm preg oc (camlstring_of_coqstring txt) sg args res;
              fprintf oc "%s end inline assembly\n" comment
          | _ ->
              assert false
          end

    let print_literal64 oc n lbl =
      fprintf oc "%a:	.quad	0x%Lx\n" label lbl n
    let print_literal32 oc n lbl =
      fprintf oc "%a:	.long	0x%lx\n" label lbl n

    let print_jumptable oc jmptbl =
      let print_jumptable (lbl, tbl) =
        let print_entry l =
          if Archi.ptr64 then
            fprintf oc "	.long	%a - %a\n" label (transl_label l) label lbl
          else
            fprintf oc "	.long	%a\n" label (transl_label l)
        in
        fprintf oc "%a:" label lbl;
        List.iter print_entry tbl
      in
      if !jumptables <> [] then begin
        section oc jmptbl;
        print_align oc 4;
        List.iter print_jumptable !jumptables;
        jumptables := []
      end

    let print_align = print_align

    let print_comm_symb oc sz name align =
      if C2C.atom_is_static name
      then System.print_lcomm_decl oc name sz align
      else System.print_comm_decl oc name sz align

    let name_of_section = name_of_section

    let emit_constants oc lit =
       if exists_constants () then begin
         section oc lit;
         print_align oc 8;
         Hashtbl.iter (print_literal64 oc) literal64_labels;
         Hashtbl.iter (print_literal32 oc) literal32_labels;
         reset_literals ()
       end

    let cfi_startproc = cfi_startproc
    let cfi_endproc = cfi_endproc

    let print_instructions oc fn =
      current_function_sig := fn.fn_sig;
      List.iter (print_instruction oc) fn.fn_code

    let print_optional_fun_info _ = ()

    let get_section_names name =
      match C2C.atom_sections name with
      | [t;l;j] -> (t, l, j)
      |    _    -> (Section_text, Section_literal, Section_jumptable)

    let print_fun_info = print_fun_info

    let print_var_info = print_var_info

    let print_prologue oc =
      need_masks := false;
      if !Clflags.option_g then begin
        section oc Section_text;
        if Configuration.system <> "bsd" then cfi_section oc
      end

    let print_epilogue oc =
      if !need_masks then begin
        section oc (Section_const true);
        (* not Section_literal because not 8-bytes *)
        print_align oc 16;
        fprintf oc "%a:	.quad   0x8000000000000000, 0\n"
          raw_symbol "__negd_mask";
        fprintf oc "%a:	.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF\n"
          raw_symbol "__absd_mask";
        fprintf oc "%a:	.long   0x80000000, 0, 0, 0\n"
          raw_symbol "__negs_mask";
        fprintf oc "%a:	.long   0x7FFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF\n"
          raw_symbol "__abss_mask"
      end;
      System.print_epilogue oc;
      if !Clflags.option_g then begin
        Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
        section oc Section_text;
      end

    let comment = comment

    let default_falignment = 16

    let label = label

    let address = if Archi.ptr64 then ".quad" else ".long"

end

let sel_target () =
 let module S = (val (match Configuration.system with
  | "linux" | "bsd" -> (module ELF_System:SYSTEM)
  | "macosx" -> (module MacOS_System:SYSTEM)
  | "cygwin" -> (module Cygwin_System:SYSTEM)
  | _ -> invalid_arg ("System " ^ Configuration.system ^ " not supported")  ):SYSTEM) in
 (module Target(S):TARGET)

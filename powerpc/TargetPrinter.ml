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
open Fileinfo
open Maps
open Camlcoq
open Sections
open AST
open Asm
open PrintAsmaux
open AisAnnot

(* Recognition of target ABI and asm syntax *)

module type SYSTEM =
    sig
      val comment: string
      val constant: out_channel -> constant -> unit
      val ireg: out_channel -> ireg -> unit
      val freg: out_channel -> freg -> unit
      val name_of_section: section_name -> string
      val creg: out_channel -> int -> unit
      val print_file_line: out_channel -> string -> int -> unit
      val cfi_startproc: out_channel -> unit
      val cfi_endproc: out_channel -> unit
      val cfi_adjust: out_channel -> int32 -> unit
      val cfi_rel_offset: out_channel -> string -> int32 -> unit
      val print_prologue: out_channel -> unit
      val print_epilogue: out_channel -> unit
      val section: out_channel -> section_name -> unit
      val debug_section: out_channel -> section_name -> unit
      val address: string
    end

let symbol = elf_symbol

let symbol_offset = elf_symbol_offset

let symbol_fragment oc s n op =
      fprintf oc "(%a)%s" symbol_offset (s, n) op


let int_reg_name = function
  | GPR0 -> "0"  | GPR1 -> "1"  | GPR2 -> "2"  | GPR3 -> "3"
  | GPR4 -> "4"  | GPR5 -> "5"  | GPR6 -> "6"  | GPR7 -> "7"
  | GPR8 -> "8"  | GPR9 -> "9"  | GPR10 -> "10" | GPR11 -> "11"
  | GPR12 -> "12" | GPR13 -> "13" | GPR14 -> "14" | GPR15 -> "15"
  | GPR16 -> "16" | GPR17 -> "17" | GPR18 -> "18" | GPR19 -> "19"
  | GPR20 -> "20" | GPR21 -> "21" | GPR22 -> "22" | GPR23 -> "23"
  | GPR24 -> "24" | GPR25 -> "25" | GPR26 -> "26" | GPR27 -> "27"
  | GPR28 -> "28" | GPR29 -> "29" | GPR30 -> "30" | GPR31 -> "31"

let float_reg_name = function
  | FPR0 -> "0"  | FPR1 -> "1"  | FPR2 -> "2"  | FPR3 -> "3"
  | FPR4 -> "4"  | FPR5 -> "5"  | FPR6 -> "6"  | FPR7 -> "7"
  | FPR8 -> "8"  | FPR9 -> "9"  | FPR10 -> "10" | FPR11 -> "11"
  | FPR12 -> "12" | FPR13 -> "13" | FPR14 -> "14" | FPR15 -> "15"
  | FPR16 -> "16" | FPR17 -> "17" | FPR18 -> "18" | FPR19 -> "19"
  | FPR20 -> "20" | FPR21 -> "21" | FPR22 -> "22" | FPR23 -> "23"
  | FPR24 -> "24" | FPR25 -> "25" | FPR26 -> "26" | FPR27 -> "27"
  | FPR28 -> "28" | FPR29 -> "29" | FPR30 -> "30" | FPR31 -> "31"

let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3
  | CRbit_6 -> 6


let label = elf_label

module Linux_System : SYSTEM =
  struct

    let comment = "#"

    let constant oc cst =
      match cst with
      | Cint n ->
          fprintf oc "%ld" (camlint_of_coqint n)
      | Csymbol_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_high(s, n) ->
          symbol_fragment oc s n "@ha"
      | Csymbol_sda(s, n) ->
          symbol_fragment oc s n "@sda21"
            (* 32-bit relative addressing is supported by the Diab tools but not by
               GNU binutils.  In the latter case, for testing purposes, we treat
               them as absolute addressings.  The default base register being GPR0,
               this produces correct code, albeit with absolute addresses. *)
      | Csymbol_rel_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_rel_high(s, n) ->
          symbol_fragment oc s n "@ha"

    let ireg oc r =
      output_string oc (int_reg_name r)

    let freg oc r =
      output_string oc (float_reg_name r)

    let creg oc r =
      fprintf oc "%d" r

    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i ->
          if i then ".data" else "COMM"
      | Section_small_data i ->
          if i then ".section	.sdata,\"aw\",@progbits" else "COMM"
      | Section_const i ->
          if i then ".rodata" else "COMM"
      | Section_small_const i ->
          if i then ".section	.sdata2,\"a\",@progbits" else "COMM"
      | Section_string -> ".rodata"
      | Section_literal -> ".section	.rodata.cst8,\"aM\",@progbits,8"
      | Section_jumptable -> ".text"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",@progbits"
            s (if wr then "w" else "") (if ex then "x" else "")
      | Section_debug_info _ -> ".section	.debug_info,\"\",@progbits"
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",@progbits"
      | Section_debug_loc -> ".section	.debug_loc,\"\",@progbits"
      | Section_debug_line _ ->  ".section	.debug_line,\"\",@progbits"
      | Section_debug_ranges -> ".section	.debug_ranges,\"\",@progbits"
      | Section_debug_str -> ".section	.debug_str,\"MS\",@progbits,1"
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",\"\",@note"


    let section oc sec =
      let name = name_of_section sec in
      assert (name <> "COMM");
      fprintf oc "	%s\n" name


    let print_file_line oc file line =
      print_file_line oc comment file line

    (* Emit .cfi directives *)
    let cfi_startproc = cfi_startproc

    let cfi_endproc = cfi_endproc

    let cfi_adjust = cfi_adjust

    let cfi_rel_offset = cfi_rel_offset

    let print_prologue oc =
      if !Clflags.option_g then  begin
        section oc Section_text;
        cfi_section oc
      end

    let print_epilogue oc =
      if !Clflags.option_g then
        begin
          Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
          section oc Section_text;
        end

    let debug_section _ _ = ()

    let address = if Archi.ptr64 then ".quad" else ".4byte"
  end

module Diab_System : SYSTEM =
  struct

    let comment = ";"

    let constant oc cst =
      match cst with
      | Cint n ->
          fprintf oc "%ld" (camlint_of_coqint n)
      | Csymbol_low(s, n) ->
          symbol_fragment oc s n "@l"
      | Csymbol_high(s, n) ->
          symbol_fragment oc s n "@ha"
      | Csymbol_sda(s, n) ->
          symbol_fragment oc s n "@sdarx"
      | Csymbol_rel_low(s, n) ->
          symbol_fragment oc s n "@sdax@l"
      | Csymbol_rel_high(s, n) ->
          symbol_fragment oc s n "@sdarx@ha"

    let ireg oc r =
      output_char oc 'r';
      output_string oc (int_reg_name r)

    let freg oc r =
      output_char oc 'f';
      output_string oc (float_reg_name r)

    let creg oc r =
      fprintf oc "cr%d" r

    let name_of_section = function
      | Section_text -> ".text"
      | Section_data i -> if i then ".data" else "COMM"
      | Section_small_data i -> if i then ".sdata" else ".sbss"
      | Section_const _ -> ".text"
      | Section_small_const _ -> ".sdata2"
      | Section_string -> ".text"
      | Section_literal -> ".text"
      | Section_jumptable -> ".text"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",,%c"
               s
            (match wr, ex with
            | true, true -> 'm'                 (* text+data *)
            | true, false -> 'd'                (* data *)
            | false, true -> 'c'                (* text *)
            | false, false -> 'r')              (* const *)
      | Section_debug_info (Some s) ->
          sprintf ".section	.debug_info%s,,n" s
      | Section_debug_info None ->
          sprintf ".section	.debug_info,,n"
      | Section_debug_abbrev -> ".section	.debug_abbrev,,n"
      | Section_debug_loc -> ".section	.debug_loc,,n"
      | Section_debug_line (Some s) ->
          sprintf ".section	.debug_line.%s,,n\n" s
      | Section_debug_line None ->
          sprintf ".section	.debug_line,,n\n"
      | Section_debug_ranges
      | Section_debug_str -> assert false (* Should not be used *)
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",,n"

    let section oc sec =
      let name = name_of_section sec in
      assert (name <> "COMM");
      match sec with
      | Section_debug_info (Some s) ->
          fprintf oc "	%s\n" name;
          fprintf oc "	.sectionlink	.debug_info\n"
      | _ ->
          fprintf oc "	%s\n" name

    let print_file_line oc file line =
      print_file_line_d2 oc comment file line

    (* Emit .cfi directives *)
    let cfi_startproc oc = ()

    let cfi_endproc oc = ()

    let cfi_adjust oc delta = ()

    let cfi_rel_offset oc reg ofs = ()

    let debug_section oc sec =
      match sec with
      | Section_debug_abbrev
      | Section_debug_info _
      | Section_debug_str
      | Section_debug_loc -> ()
      | sec ->
          let name = match sec with
          | Section_user (name,_,_) -> name
          | _ -> name_of_section sec in
          if not (Debug.exists_section sec) then
            let line_start = new_label ()
            and low_pc = new_label ()
            and debug_info = new_label () in
            Debug.add_diab_info sec line_start debug_info low_pc;
            let line_name = ".debug_line" ^(if name <> ".text" then name else "") in
            section oc (Section_debug_line (if name <> ".text" then Some name else None));
            fprintf oc "	.section	%s,,n\n" line_name;
            if name <> ".text" then
              fprintf oc "	.sectionlink	.debug_line\n";
            fprintf oc "%a:\n" label line_start;
            section oc sec;
            fprintf oc "%a:\n" label low_pc;
            fprintf oc "	.0byte	%a\n" label debug_info;
            fprintf oc "	.d2_line_start	%s\n" line_name
          else
            ()

    let print_prologue oc =
      fprintf oc "	.xopt	align-fill-text=0x60000000\n";
      debug_section oc Section_text

    let print_epilogue oc =
      let end_label sec =
        fprintf oc "\n";
        section oc sec;
        let label_end = new_label () in
        fprintf oc "%a:\n" label label_end;
        label_end
      and entry_label f =
        let label = new_label () in
        fprintf oc ".L%d:	.d2filenum \"%s\"\n" label f;
        label
      and end_line () =   fprintf oc "	.d2_line_end\n" in
      Debug.compute_diab_file_enum end_label entry_label end_line

    let address = assert (not Archi.ptr64); ".4byte"

  end

module Target (System : SYSTEM):TARGET =
  struct
    include System

    (* Basic printing functions *)
    let symbol = symbol

    let label = label

    let label_low oc lbl =
      fprintf oc ".L%d@l" lbl

    let label_high oc lbl =
      fprintf oc ".L%d@ha" lbl

    let crbit oc bit =
      fprintf oc "%d" (num_crbit bit)

    let ireg_or_zero oc r =
      if r = GPR0 then output_string oc "0" else ireg oc r

    let preg oc = function
      | IR r -> ireg oc r
      | FR r -> freg oc r
      | _    -> assert false

    (* For printing annotations, use the full register names [rN] and [fN]
       to avoid ambiguity with constants. *)
    let preg_annot = function
      | IR r -> sprintf "r%s" (int_reg_name r)
      | FR r -> sprintf "f%s" (float_reg_name r)
      | _    -> assert false

    (* Encoding masks for rlwinm instructions *)

    let rolm_mask n =
      let mb = ref 0       (* location of last 0->1 transition *)
      and me = ref 32      (* location of last 1->0 transition *)
      and last = ref ((Int32.logand n 1l) <> 0l)  (* last bit seen *)
      and count = ref 0    (* number of transitions *)
      and mask = ref 0x8000_0000l in
      for mx = 0 to 31 do
        if Int32.logand n !mask <> 0l then
          if !last then () else (incr count; mb := mx; last := true)
        else
          if !last then (incr count; me := mx; last := false) else ();
        mask := Int32.shift_right_logical !mask 1
      done;
      if !me = 0 then me := 32;
      assert (!count = 2 || (!count = 0 && !last));
      (!mb, !me-1)

    (* Encoding 64-bit masks for rldic PPC64 instructions *)

    let rolm64_mask n =
      let rec leftmost_one pos mask =
        assert (pos < 64);
        let mask' = Int64.shift_right_logical mask 1 in
        if Int64.logand n mask = 0L
        then leftmost_one (pos + 1) mask'
        else (pos, rightmost_one (pos + 1) mask')
      and rightmost_one pos mask =
        if pos >= 64 then
          63
        else if Int64.logand n mask > 0L then
          rightmost_one (pos + 1) (Int64.shift_right_logical mask 1)
        else if Int64.logand n (Int64.pred mask) = 0L then
          pos - 1
        else
          assert false
      in leftmost_one 0 0x8000_0000_0000_0000L

    (* Determine if the displacement of a conditional branch fits the short form *)

    let short_cond_branch tbl pc lbl_dest =
      match PTree.get lbl_dest tbl with
      | None -> assert false
      | Some pc_dest ->
          let disp = pc_dest - pc in -0x2000 <= disp && disp < 0x2000

    (* Printing of instructions *)

    let print_instruction oc tbl pc fallthrough = function
      | Padd(r1, r2, r3) | Padd64(r1, r2, r3) ->
          fprintf oc "	add	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Paddc(r1, r2, r3) ->
          fprintf oc "	addc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Padde(r1, r2, r3) ->
          fprintf oc "	adde	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Paddi(r1, r2, c) ->
          fprintf oc "	addi	%a, %a, %a\n" ireg r1 ireg_or_zero r2 constant c
      | Paddi64(r1, r2, n) ->
          fprintf oc "	addi	%a, %a, %Ld\n" ireg r1 ireg_or_zero r2 (camlint64_of_coqint n)
      | Paddic(r1, r2, c) ->
          fprintf oc "	addic	%a, %a, %a\n" ireg r1 ireg_or_zero r2 constant c
      | Paddis(r1, r2, c) ->
          fprintf oc "	addis	%a, %a, %a\n" ireg r1 ireg_or_zero r2 constant c
      | Paddis64(r1, r2, n) ->
          fprintf oc "	addis	%a, %a, %Ld\n" ireg r1 ireg_or_zero r2 (camlint64_of_coqint n)
      | Paddze(r1, r2) | Paddze64(r1, r2) ->
          fprintf oc "	addze	%a, %a\n" ireg r1 ireg r2
      | Pallocframe(sz, ofs, _) ->
          assert false
      | Pand_(r1, r2, r3) | Pand_64(r1, r2, r3) ->
          fprintf oc "	and.	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pandc(r1, r2, r3) ->
          fprintf oc "	andc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pandi_(r1, r2, c) ->
          fprintf oc "	andi.	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Pandi_64(r1, r2, n) ->
          fprintf oc "	andi.	%a, %a, %Ld\n" ireg r1 ireg r2 (camlint64_of_coqint n)
      | Pandis_(r1, r2, c) ->
          fprintf oc "	andis.	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Pandis_64(r1, r2, n) ->
          fprintf oc "	andis.	%a, %a, %Ld\n" ireg r1 ireg r2 (camlint64_of_coqint n)
      | Pb lbl ->
          fprintf oc "	b	%a\n" label (transl_label lbl)
      | Pbctr sg ->
          fprintf oc "	bctr\n"
      | Pbctrl sg ->
          fprintf oc "	bctrl\n"
      | Pbdnz lbl ->
          fprintf oc "	bdnz	%a\n" label (transl_label lbl)
      | Pbf(bit, lbl) ->
          if !Clflags.option_faligncondbranchs > 0 then
            fprintf oc "	.balign	%d\n" !Clflags.option_faligncondbranchs;
          if short_cond_branch tbl pc lbl then
            fprintf oc "	bf	%a, %a\n" crbit bit label (transl_label lbl)
          else begin
            let next = new_label() in
            fprintf oc "	bt	%a, %a\n" crbit bit label next;
            fprintf oc "	b	%a\n" label (transl_label lbl);
            fprintf oc "%a:\n" label next
          end
      | Pbl(s, sg) ->
          fprintf oc "	bl	%a\n" symbol s
      | Pbs(s, sg) ->
          fprintf oc "	b	%a\n" symbol s
      | Pblr ->
          fprintf oc "	blr\n"
      | Pbt(bit, lbl) ->
          if !Clflags.option_faligncondbranchs > 0 then
            fprintf oc "	.balign	%d\n" !Clflags.option_faligncondbranchs;
          if short_cond_branch tbl pc lbl then
            fprintf oc "	bt	%a, %a\n" crbit bit label (transl_label lbl)
          else begin
            let next = new_label() in
            fprintf oc "	bf	%a, %a\n" crbit bit label next;
            fprintf oc "	b	%a\n" label (transl_label lbl);
            fprintf oc "%a:\n" label next
          end
      | Pbtbl(r, tbl) ->
          let lbl = new_label() in
          fprintf oc "%s begin pseudoinstr btbl(%a)\n" comment ireg r;
          fprintf oc "%s jumptable [ " comment;
          List.iter (fun l -> fprintf oc "%a " label (transl_label l)) tbl;
          fprintf oc "]\n";
          fprintf oc "	slwi    %a, %a, 2\n" ireg GPR12 ireg r;
          fprintf oc "	addis	%a, %a, %a\n" ireg GPR12 ireg GPR12 label_high lbl;
          fprintf oc "	lwz	%a, %a(%a)\n" ireg GPR12 label_low lbl ireg GPR12;
          fprintf oc "	mtctr	%a\n" ireg GPR12;
          fprintf oc "	bctr\n";
          jumptables := (lbl, tbl) :: !jumptables;
          fprintf oc "%s end pseudoinstr btbl\n" comment
      | Pcmpb (r1, r2, r3) ->
          fprintf oc "	cmpb	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pcmpld(r1, r2) ->
          fprintf oc "	cmpld	%a, %a, %a\n" creg 0 ireg r1 ireg r2
      | Pcmpldi(r1, n) ->
          fprintf oc "	cmpldi	%a, %a, %Ld\n" creg 0 ireg r1 (camlint64_of_coqint n)
      | Pcmplw(r1, r2) ->
          fprintf oc "	cmplw	%a, %a, %a\n" creg 0 ireg r1 ireg r2
      | Pcmplwi(r1, c) ->
          fprintf oc "	cmplwi	%a, %a, %a\n" creg 0 ireg r1 constant c
      | Pcmpd(r1, r2) ->
          fprintf oc "	cmpd	%a, %a, %a\n" creg 0 ireg r1 ireg r2
      | Pcmpdi(r1, n) ->
          fprintf oc "	cmpdi	%a, %a, %Ld\n" creg 0 ireg r1 (camlint64_of_coqint n)
      | Pcmpw(r1, r2) ->
          fprintf oc "	cmpw	%a, %a, %a\n" creg 0 ireg r1 ireg r2
      | Pcmpwi(r1, c) ->
          fprintf oc "	cmpwi	%a, %a, %a\n" creg 0 ireg r1 constant c
      | Pcntlzd(r1, r2) ->
          fprintf oc "	cntlzd	%a, %a\n" ireg r1 ireg r2
      | Pcntlzw(r1, r2) ->
          fprintf oc "	cntlzw	%a, %a\n" ireg r1 ireg r2
      | Pcreqv(c1, c2, c3) ->
          fprintf oc "	creqv	%a, %a, %a\n" crbit c1 crbit c2 crbit c3
      | Pcror(c1, c2, c3) ->
          fprintf oc "	cror	%a, %a, %a\n" crbit c1 crbit c2 crbit c3
      | Pcrxor(c1, c2, c3) ->
          fprintf oc "	crxor	%a, %a, %a\n" crbit c1 crbit c2 crbit c3
      | Pdcbf (r1,r2) ->
          fprintf oc "	dcbf	%a, %a\n" ireg r1 ireg r2
      | Pdcbi (r1,r2) ->
          fprintf oc "	dcbi	%a, %a\n" ireg r1 ireg r2
      | Pdcbt (c,r1,r2) ->
          fprintf oc "	dcbt	%ld, %a, %a\n" (camlint_of_coqint c) ireg r1  ireg r2
      | Pdcbtst (c,r1,r2) ->
          fprintf oc "	dcbtst	%ld, %a, %a\n"  (camlint_of_coqint c) ireg r1 ireg r2
      | Pdcbtls (c,r1,r2) ->
          fprintf oc "	dcbtls	%ld, %a, %a\n" (camlint_of_coqint c) ireg r1 ireg r2
      | Pdcbz (r1,r2) ->
          fprintf oc "	dcbz	%a, %a\n" ireg r1 ireg r2
      | Pdivw(r1, r2, r3) ->
          fprintf oc "	divw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pdivwu(r1, r2, r3) ->
          fprintf oc "	divwu	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pdivd(r1, r2, r3) ->
          fprintf oc "	divd	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pdivdu(r1, r2, r3) ->
          fprintf oc "	divdu	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Peieio ->
          fprintf oc "	eieio\n"
      | Peqv(r1, r2, r3) ->
          fprintf oc "	eqv	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pextsb(r1, r2) ->
          fprintf oc "	extsb	%a, %a\n" ireg r1 ireg r2
      | Pextsh(r1, r2) ->
          fprintf oc "	extsh	%a, %a\n" ireg r1 ireg r2
      | Pextsw(r1, r2) ->
          fprintf oc "	extsw	%a, %a\n" ireg r1 ireg r2
      | Pextzw(r1, r2) ->
          assert false
      | Pfreeframe(sz, ofs) ->
          assert false
      | Pfabs(r1, r2) | Pfabss(r1, r2) ->
          fprintf oc "	fabs	%a, %a\n" freg r1 freg r2
      | Pfadd(r1, r2, r3) ->
          fprintf oc "	fadd	%a, %a, %a\n" freg r1 freg r2 freg r3
      | Pfadds(r1, r2, r3) ->
          fprintf oc "	fadds	%a, %a, %a\n" freg r1 freg r2 freg r3
      | Pfcmpu(r1, r2) ->
          fprintf oc "	fcmpu	%a, %a, %a\n" creg 0 freg r1 freg r2
      | Pfcfi(r1, r2) ->
          assert false
      | Pfcfl(r1, r2) ->
          assert false
      | Pfcfid(r1, r2) ->
          fprintf oc "	fcfid	%a, %a\n" freg r1 freg r2
      | Pfcfiu(r1, r2) ->
          assert false
      | Pfcti(r1, r2) ->
          assert false
      | Pfctid(r1, r2) ->
          assert false
      | Pfctidz(r1, r2) ->
          fprintf oc "	fctidz	%a, %a\n" freg r1 freg r2
      | Pfctiu(r1, r2) ->
          assert false
      | Pfctiw(r1, r2) ->
          fprintf oc "	fctiw	%a, %a\n" freg r1 freg r2
      | Pfctiwz(r1, r2) ->
          fprintf oc "	fctiwz	%a, %a\n" freg r1 freg r2
      | Pfdiv(r1, r2, r3) ->
          fprintf oc "	fdiv	%a, %a, %a\n" freg r1 freg r2 freg r3
      | Pfdivs(r1, r2, r3) ->
          fprintf oc "	fdivs	%a, %a, %a\n" freg r1 freg r2 freg r3
      | Pfmake(rd, r1, r2) ->
          assert false
      | Pfmr(r1, r2) ->
          fprintf oc "	fmr	%a, %a\n" freg r1 freg r2
      | Pfmul(r1, r2, r3) ->
          fprintf oc "	fmul	%a, %a, %a\n" freg r1 freg r2 freg r3
      | Pfmuls(r1, r2, r3) ->
          fprintf oc "	fmuls	%a, %a, %a\n" freg r1 freg r2 freg r3
      | Pfneg(r1, r2) | Pfnegs(r1, r2) ->
          fprintf oc "	fneg	%a, %a\n" freg r1 freg r2
      | Pfrsp(r1, r2) ->
          fprintf oc "	frsp	%a, %a\n" freg r1 freg r2
      | Pfxdp(r1, r2) ->
          assert false
      | Pfsub(r1, r2, r3) ->
          fprintf oc "	fsub	%a, %a, %a\n" freg r1 freg r2 freg r3
      | Pfsubs(r1, r2, r3) ->
          fprintf oc "	fsubs	%a, %a, %a\n" freg r1 freg r2 freg r3
      | Pfmadd(r1, r2, r3, r4) ->
          fprintf oc "	fmadd	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
      | Pfmsub(r1, r2, r3, r4) ->
          fprintf oc "	fmsub	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
      | Pfnmadd(r1, r2, r3, r4) ->
          fprintf oc "	fnmadd	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
      | Pfnmsub(r1, r2, r3, r4) ->
          fprintf oc "	fnmsub	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
      | Pfsqrt(r1, r2) ->
          fprintf oc "	fsqrt	%a, %a\n" freg r1 freg r2
      | Pfrsqrte(r1, r2) ->
          fprintf oc "	frsqrte	%a, %a\n" freg r1 freg r2
      | Pfres(r1, r2) ->
          fprintf oc "	fres	%a, %a\n" freg r1 freg r2
      | Pfsel(r1, r2, r3, r4) ->
          fprintf oc "	fsel	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
      | Pisel (r1,r2,r3,cr) ->
          fprintf oc "	isel	%a, %a, %a, %a\n" ireg r1 ireg r2 ireg r3 crbit cr
      | Picbi (r1,r2) ->
          fprintf oc "	icbi	%a, %a\n" ireg r1 ireg r2
      | Picbtls (n,r1,r2) ->
          fprintf oc "	icbtls	%ld, %a, %a\n" (camlint_of_coqint n) ireg r1 ireg r2
      | Pisync ->
          fprintf oc "	isync\n"
      | Plwsync ->
          fprintf oc "	lwsync\n"
      | Plbz(r1, c, r2) ->
          fprintf oc "	lbz	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Plbzx(r1, r2, r3) ->
          fprintf oc "	lbzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pld(r1, c, r2) | Pld_a(r1, c, r2) ->
          fprintf oc "	ld	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pldbrx(r1, r2, r3) ->
          fprintf oc "	ldbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pldx(r1, r2, r3) | Pldx_a(r1, r2, r3) ->
          fprintf oc "	ldx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plfd(r1, c, r2)  | Plfd_a(r1, c, r2) ->
          fprintf oc "	lfd	%a, %a(%a)\n" freg r1 constant c ireg r2
      | Plfdx(r1, r2, r3) | Plfdx_a(r1, r2, r3) ->
          fprintf oc "	lfdx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
      | Plfs(r1, c, r2) ->
          fprintf oc "	lfs	%a, %a(%a)\n" freg r1 constant c ireg r2
      | Plfsx(r1, r2, r3) ->
          fprintf oc "	lfsx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
      | Plha(r1, c, r2) ->
          fprintf oc "	lha	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Plhax(r1, r2, r3) ->
          fprintf oc "	lhax	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plhbrx(r1, r2, r3) ->
          fprintf oc "	lhbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plhz(r1, c, r2) ->
          fprintf oc "	lhz	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Plhzx(r1, r2, r3) ->
          fprintf oc "	lhzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pldi(r1, c) ->
          let c = camlint64_of_coqint c in
          let lbl = label_literal64 c in
          fprintf oc "	addis	%a, 0, %a\n" ireg GPR12 label_high lbl;
          fprintf oc "	ld	%a, %a(%a) %s %Ld\n" ireg r1 label_low lbl ireg GPR12 comment c
      | Plmake(_, _, _) ->
          assert false
      | Pllo _ ->
          assert false
      | Plhi(_, _) ->
          assert false
      | Plfi(r1, c) ->
          let lbl = label_literal64 (camlint64_of_coqint (Floats.Float.to_bits c)) in
          fprintf oc "	addis	%a, 0, %a\n" ireg GPR12 label_high lbl;
          fprintf oc "	lfd	%a, %a(%a) %s %.18g\n" freg r1 label_low lbl ireg GPR12 comment (camlfloat_of_coqfloat c)
      | Plfis(r1, c) ->
          let lbl = label_literal32 (camlint_of_coqint (Floats.Float32.to_bits c)) in
          fprintf oc "	addis	%a, 0, %a\n" ireg GPR12 label_high lbl;
          fprintf oc "	lfs	%a, %a(%a) %s %.18g\n" freg r1 label_low lbl ireg GPR12 comment (camlfloat_of_coqfloat32 c)
      | Plwarx(r1, r2, r3) ->
          fprintf oc "	lwarx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plwbrx(r1, r2, r3) ->
          fprintf oc "	lwbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Plwz(r1, c, r2) | Plwz_a(r1, c, r2) ->
          fprintf oc "	lwz	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Plwzu(r1, c, r2) ->
          fprintf oc "	lwzu	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Plwzx(r1, r2, r3) | Plwzx_a(r1, r2, r3) ->
          fprintf oc "	lwzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pmbar mo ->
          fprintf oc "	mbar	%ld\n" (camlint_of_coqint mo)
      | Pmfcr(r1) ->
          fprintf oc "	mfcr	%a\n" ireg r1
      | Pmfcrbit(r1, bit) ->
          assert false
      | Pmflr(r1) ->
          fprintf oc "	mflr	%a\n" ireg r1
      | Pmr(r1, r2) ->
          fprintf oc "	mr	%a, %a\n" ireg r1 ireg r2
      | Pmtctr(r1) ->
          fprintf oc "	mtctr	%a\n" ireg r1
      | Pmtlr(r1) ->
          fprintf oc "	mtlr	%a\n" ireg r1
      | Pmfspr(rd, spr) ->
          fprintf oc "	mfspr	%a, %ld\n" ireg rd (camlint_of_coqint spr)
      | Pmtspr(spr, rs) ->
          fprintf oc "	mtspr	%ld, %a\n" (camlint_of_coqint spr) ireg rs
      | Pmulld(r1, r2, r3) ->
          fprintf oc "	mulld	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pmulli(r1, r2, c) ->
          fprintf oc "	mulli	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Pmullw(r1, r2, r3) ->
          fprintf oc "	mullw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pmulhw(r1, r2, r3) ->
          fprintf oc "	mulhw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pmulhwu(r1, r2, r3) ->
          fprintf oc "	mulhwu	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pmulhd (r1,r2,r3) ->
          fprintf oc "	mulhd	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pmulhdu (r1,r2,r3) ->
          fprintf oc "	mulhdu	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pnand(r1, r2, r3) ->
          fprintf oc "	nand	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pnor(r1, r2, r3) | Pnor64(r1, r2, r3) ->
          fprintf oc "	nor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Por(r1, r2, r3) | Por64(r1, r2, r3) ->
          fprintf oc "	or	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Porc(r1, r2, r3) ->
          fprintf oc "	orc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pori(r1, r2, c) ->
          fprintf oc "	ori	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Pori64(r1, r2, n) ->
          fprintf oc "	ori	%a, %a, %Ld\n" ireg r1 ireg r2 (camlint64_of_coqint n)
      | Poris(r1, r2, c) ->
          fprintf oc "	oris	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Poris64(r1, r2, n) ->
          fprintf oc "	oris	%a, %a, %Ld\n" ireg r1 ireg r2 (camlint64_of_coqint n)
      | Prldicl(r1, r2, c1, c2) ->
          fprintf oc "	rldicl	%a, %a, %ld, %ld\n"
            ireg r1 ireg r2 (camlint_of_coqint c1) (camlint_of_coqint c2)
      | Prldinm(r1, r2, c1, c2) ->
          let amount = camlint64_of_coqint c1 in
          let mask = camlint64_of_coqint c2 in
          let (first, last) = rolm64_mask mask in
          if last = 63 then
            fprintf oc "	rldicl	%a, %a, %Ld, %d %s 0x%Lx\n"
              ireg r1 ireg r2 amount first comment mask
          else if first = 0 then
            fprintf oc "	rldicr	%a, %a, %Ld, %d %s 0x%Lx\n"
              ireg r1 ireg r2 amount last comment mask
          else if last = 63 - Int64.to_int amount then
            fprintf oc "	rldic	%a, %a, %Ld, %d %s 0x%Lx\n"
              ireg r1 ireg r2 amount first comment mask
          else
            assert false
      | Prldimi(r1, r2, c1, c2) ->
          let amount = camlint64_of_coqint c1 in
          let mask = camlint64_of_coqint c2 in
          let (first, last) = rolm64_mask mask in
          assert (last = 63 - Int64.to_int amount);
          fprintf oc "	rldimi	%a, %a, %Ld, %d %s 0x%Lx\n"
            ireg r1 ireg r2 amount first comment mask
      | Prlwinm(r1, r2, c1, c2) ->
          let (mb, me) = rolm_mask (camlint_of_coqint c2) in
          fprintf oc "	rlwinm	%a, %a, %ld, %d, %d %s 0x%lx\n"
            ireg r1 ireg r2 (camlint_of_coqint c1) mb me
            comment (camlint_of_coqint c2)
      | Prlwimi(r1, r2, c1, c2) ->
          let (mb, me) = rolm_mask (camlint_of_coqint c2) in
          fprintf oc "	rlwimi	%a, %a, %ld, %d, %d %s 0x%lx\n"
            ireg r1 ireg r2 (camlint_of_coqint c1) mb me
            comment (camlint_of_coqint c2)
      | Psld(r1, r2, r3) ->
          fprintf oc "	sld	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pslw(r1, r2, r3) ->
          fprintf oc "	slw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psrad(r1, r2, r3) ->
          fprintf oc "	srad	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psradi(r1, r2, c) ->
          fprintf oc "	sradi	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint c)
      | Psraw(r1, r2, r3) ->
          fprintf oc "	sraw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psrawi(r1, r2, c) ->
          fprintf oc "	srawi	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint c)
      | Psrd(r1, r2, r3) ->
          fprintf oc "	srd	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psrw(r1, r2, r3) ->
          fprintf oc "	srw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstb(r1, c, r2) ->
          fprintf oc "	stb	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pstbx(r1, r2, r3) ->
          fprintf oc "	stbx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstd(r1, c, r2) | Pstd_a(r1, c, r2) ->
          fprintf oc "	std	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pstdbrx(r1, r2, r3) ->
          fprintf oc "	stdbrx  %a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstdx(r1, r2, r3) | Pstdx_a(r1, r2, r3) ->
          fprintf oc "	stdx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstdu(r1, c, r2) ->
          fprintf oc "	stdu	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pstfd(r1, c, r2) | Pstfd_a(r1, c, r2) ->
          fprintf oc "	stfd	%a, %a(%a)\n" freg r1 constant c ireg r2
      | Pstfdu(r1, c, r2) ->
          fprintf oc "	stfdu	%a, %a(%a)\n" freg r1 constant c ireg r2
      | Pstfdx(r1, r2, r3) | Pstfdx_a(r1, r2, r3) ->
          fprintf oc "	stfdx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
      | Pstfs(r1, c, r2) ->
          fprintf oc "	stfs	%a, %a(%a)\n" freg r1 constant c ireg r2
      | Pstfsx(r1, r2, r3) ->
          fprintf oc "	stfsx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
      | Psth(r1, c, r2) ->
          fprintf oc "	sth	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Psthx(r1, r2, r3) ->
          fprintf oc "	sthx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psthbrx(r1, r2, r3) ->
          fprintf oc "	sthbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstw(r1, c, r2) | Pstw_a(r1, c, r2) ->
          fprintf oc "	stw	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pstwu(r1, c, r2) ->
          fprintf oc "	stwu	%a, %a(%a)\n" ireg r1 constant c ireg r2
      | Pstwx(r1, r2, r3) | Pstwx_a(r1, r2, r3) ->
          fprintf oc "	stwx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstwux(r1, r2, r3) ->
          fprintf oc "	stwux	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstwbrx(r1, r2, r3) ->
          fprintf oc "	stwbrx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pstwcx_(r1, r2, r3) ->
          fprintf oc "	stwcx.	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psubfc(r1, r2, r3) | Psubfc64(r1, r2, r3) ->
          fprintf oc "	subfc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psubfe(r1, r2, r3) ->
          fprintf oc "	subfe	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Psubfze(r1, r2) ->
          fprintf oc "	subfze	%a, %a\n" ireg r1 ireg r2
      | Psubfic(r1, r2, c) ->
          fprintf oc "	subfic	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Psubfic64(r1, r2, n) ->
          fprintf oc "	subfic	%a, %a, %Ld\n" ireg r1 ireg r2 (camlint64_of_coqint n)
      | Psync ->
          fprintf oc "	sync\n"
      | Ptrap ->
          fprintf oc "	trap\n"
      | Pxor(r1, r2, r3) | Pxor64(r1, r2, r3) ->
          fprintf oc "	xor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
      | Pxori(r1, r2, c) ->
          fprintf oc "	xori	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Pxori64(r1, r2, n) ->
          fprintf oc "	xori	%a, %a, %Ld\n" ireg r1 ireg r2 (camlint64_of_coqint n)
      | Pxoris(r1, r2, c) ->
          fprintf oc "	xoris	%a, %a, %a\n" ireg r1 ireg r2 constant c
      | Pxoris64(r1, r2, n) ->
          fprintf oc "	xoris	%a, %a, %Ld\n" ireg r1 ireg r2 (camlint64_of_coqint n)
      | Plabel lbl ->
          if (not fallthrough) && !Clflags.option_falignbranchtargets > 0 then
            fprintf oc "	.balign	%d\n" !Clflags.option_falignbranchtargets;
          fprintf oc "%a:\n" label (transl_label lbl)
      | Pbuiltin(ef, args, res) ->
        begin match ef with
          | EF_annot(kind,txt, targs) ->
            begin match (P.to_int kind) with
              | 1 -> let annot = annot_text preg_annot "sp" (camlstring_of_coqstring txt) args in
                fprintf oc "%s annotation: %S\n" comment annot

              | 2 -> let lbl = new_label () in
                fprintf oc "%a:\n" label lbl;
                add_ais_annot lbl preg_annot "r1" (camlstring_of_coqstring txt) args
              | _ -> assert false
              end
          | EF_debug(kind, txt, targs) ->
              print_debug_info comment print_file_line preg_annot "r1" oc
                               (P.to_int kind) (extern_atom txt) args
          | EF_inline_asm(txt, sg, clob) ->
              fprintf oc "%s begin inline assembly\n\t" comment;
              print_inline_asm preg oc (camlstring_of_coqstring txt) sg args res;
              fprintf oc "%s end inline assembly\n" comment
          | _ ->
              assert false
          end
      | Pcfi_adjust n ->
          cfi_adjust oc (camlint_of_coqint n)
      | Pcfi_rel_offset n ->
          cfi_rel_offset oc "lr" (camlint_of_coqint n)

    (* Determine if an instruction falls through *)

    let instr_fall_through = function
      | Pb _ -> false
      | Pbctr _ -> false
      | Pbs _ -> false
      | Pblr -> false
      | _ -> true

    (* Estimate the size of an Asm instruction encoding, in number of actual
       PowerPC instructions.  We can over-approximate. *)

    let instr_size = function
      | Pbf(bit, lbl) -> 2
      | Pbt(bit, lbl) -> 2
      | Pbtbl(r, tbl) -> 5
      | Pldi (r1,c) -> 2
      | Plfi(r1, c) -> 2
      | Plfis(r1, c) -> 2
      | Plabel lbl -> 0
      | Pbuiltin((EF_annot _ | EF_debug _), args, res) -> 0
      | Pbuiltin(ef, args, res) -> 3
      | Pcfi_adjust _ | Pcfi_rel_offset _ -> 0
      | _ -> 1

   (* Build a table label -> estimated position in generated code.
      Used to predict if relative conditional branches can use the short form. *)

    let rec label_positions tbl pc = function
      | [] -> tbl
      | Plabel lbl :: c -> label_positions (PTree.set lbl pc tbl) pc c
      | i :: c -> label_positions tbl (pc + instr_size i) c

    (* Emit a sequence of instructions *)

    let print_instructions oc fn =
      let rec aux  oc tbl pc fallthrough = function
      | [] -> ()
      | i :: c ->
          print_instruction oc tbl pc fallthrough i;
         aux oc tbl (pc + instr_size i) (instr_fall_through i) c in
      aux oc (label_positions PTree.empty 0 fn.fn_code) 0 true fn.fn_code

    (* Print the code for a function *)

    let print_literal64 oc n lbl =
      let nlo = Int64.to_int32 n
      and nhi = Int64.to_int32(Int64.shift_right_logical n 32) in
      fprintf oc "%a:	.long	0x%lx, 0x%lx\n" label lbl nhi nlo

    let print_literal32 oc n lbl =
      fprintf oc "%a:	.long	0x%lx\n" label lbl n

    let print_fun_info = elf_print_fun_info

    let emit_constants oc lit =
      if exists_constants () then begin
        section oc lit;
        fprintf oc "	.balign 8\n";
        Hashtbl.iter (print_literal64 oc) literal64_labels;
        Hashtbl.iter (print_literal32 oc) literal32_labels;
      end;
      reset_literals ()

    let print_optional_fun_info _ = ()

    let get_section_names name =
      match C2C.atom_sections name with
      | [t;l;j] -> (t, l, j)
      |    _    -> (Section_text, Section_literal, Section_jumptable)

    let print_var_info = elf_print_var_info

    let print_comm_symb oc sz name align =
      fprintf oc "	%s	%a, %s, %d\n"
        (if C2C.atom_is_static name then ".lcomm" else ".comm")
        symbol name
        (Z.to_string sz)
        align

    let print_align oc align  =
      fprintf oc "	.balign	%d\n" align

    let print_jumptable oc jmptbl =
      let print_jumptable oc (lbl, tbl) =
        fprintf oc "%a:" label lbl;
        List.iter
          (fun l -> fprintf oc "	.long	%a\n" label (transl_label l))
          tbl in
      if !jumptables <> [] then begin
        section oc jmptbl;
        fprintf oc "	.balign 4\n";
        List.iter (print_jumptable oc) !jumptables;
        jumptables := []
      end

    let default_falignment = 4

    let address = address

    let section oc sec =
      section oc sec;
      match sec with
      | Section_ais_annotation -> ()
      | _ -> debug_section oc sec
  end

let sel_target () =
  let module S  = (val
    (match Configuration.system with
    | "linux"  -> (module Linux_System:SYSTEM)
    | "diab"   -> (module Diab_System:SYSTEM)
    | _        -> invalid_arg ("System " ^ Configuration.system ^ " not supported")):SYSTEM) in
  (module Target(S):TARGET)

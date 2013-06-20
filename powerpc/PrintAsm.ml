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
open Maps
open Camlcoq
open Sections
open AST
open Memdata
open Asm

(* Recognition of target ABI and asm syntax *)

type target = Linux | Diab

let target = 
  match Configuration.system with
  | "linux"  -> Linux
  | "diab"   -> Diab
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

(* Record identifiers of functions that need a special stub *)

module IdentSet = Set.Make(struct type t = ident let compare = compare end)

let stubbed_functions = ref IdentSet.empty

(* Basic printing functions *)

let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

let raw_symbol oc s =
  fprintf oc "%s" s

let symbol oc symb =
  if IdentSet.mem symb !stubbed_functions
  then fprintf oc ".L%s$stub" (extern_atom symb)
  else fprintf oc "%s" (extern_atom symb)

let symbol_offset oc (symb, ofs) =
  symbol oc symb;
  if ofs <> 0l then fprintf oc " + %ld" ofs

let label oc lbl =
  fprintf oc ".L%d" lbl

let label_low oc lbl =
  fprintf oc ".L%d@l" lbl

let label_high oc lbl =
  fprintf oc ".L%d@ha" lbl

let comment =
  match target with
  | Linux -> "#"
  | Diab -> ";"

let constant oc cst =
  match cst with
  | Cint n ->
      fprintf oc "%ld" (camlint_of_coqint n)
  | Csymbol_low(s, n) ->
      fprintf oc "(%a)@l" symbol_offset (s, camlint_of_coqint n)
  | Csymbol_high(s, n) ->
      fprintf oc "(%a)@ha" symbol_offset (s, camlint_of_coqint n)
  | Csymbol_sda(s, n) ->
      begin match target with
      | Linux ->
          fprintf oc "(%a)@sda21" symbol_offset (s, camlint_of_coqint n)
      | Diab ->
          fprintf oc "(%a)@sdarx" symbol_offset (s, camlint_of_coqint n)
      end

let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3

let crbit oc bit =
  fprintf oc "%d" (num_crbit bit)

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

let ireg oc r =
  begin match target with
  | Diab  -> output_char oc 'r'
  | Linux -> ()
  end;
  output_string oc (int_reg_name r)

let ireg_or_zero oc r =
  if r = GPR0 then output_string oc "0" else ireg oc r

let freg oc r =
  begin match target with
  | Diab  -> output_char oc 'f'
  | Linux -> ()
  end;
  output_string oc (float_reg_name r)

let creg oc r =
  match target with
  | Diab  -> fprintf oc "cr%d" r
  | Linux -> fprintf oc "%d" r

let preg oc = function
  | IR r -> ireg oc r
  | FR r -> freg oc r
  | _    -> assert false

(* Names of sections *)

let name_of_section_Linux = function
  | Section_text -> ".text"
  | Section_data i -> if i then ".data" else "COMM"
  | Section_small_data i -> if i then ".sdata" else "COMM"
  | Section_const -> ".rodata"
  | Section_small_const -> ".sdata2"
  | Section_string -> ".rodata"
  | Section_literal -> ".section	.rodata.cst8,\"aM\",@progbits,8"
  | Section_jumptable -> ".text"
  | Section_user(s, wr, ex) ->
       sprintf ".section	\"%s\",\"a%s%s\",@progbits"
               s (if wr then "w" else "") (if ex then "x" else "")

let name_of_section_Diab = function
  | Section_text -> ".text"
  | Section_data i -> if i then ".data" else ".bss"
  | Section_small_data i -> if i then ".sdata" else ".sbss"
  | Section_const -> ".text"
  | Section_small_const -> ".sdata2"
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

let name_of_section =
  match target with
  | Linux -> name_of_section_Linux
  | Diab  -> name_of_section_Diab

let section oc sec =
  let name = name_of_section sec in
  assert (name <> "COMM");
  fprintf oc "	%s\n" name

(* Emit .file / .loc debugging directives *)

module DebugLinux = struct
  let filename_num : (string, int) Hashtbl.t = Hashtbl.create 7
  let reset () = Hashtbl.clear filename_num
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
end

module DebugDiab = struct
  let last_file = ref ""
  let reset () = last_file := ""
  let print_file_line oc file line =
    if !Clflags.option_g && file <> "" then begin
      if file <> !last_file then begin
        fprintf oc "	.d1file	%S\n" file;
        last_file := file
      end;
      fprintf oc "	.d1line	%s\n" line
    end
end

let print_file_line =
  match target with
  | Linux -> DebugLinux.print_file_line
  | Diab  -> DebugDiab.print_file_line

let print_location oc loc =
  if loc <> Cutil.no_loc then
    print_file_line oc (fst loc) (string_of_int (snd loc))

let reset_file_line =
  match target with
  | Linux -> DebugLinux.reset
  | Diab  -> DebugDiab.reset

(* Emit .cfi directives *)

let cfi_startproc oc =
  if Configuration.asm_supports_cfi then
    match target with
    | Linux -> fprintf oc "	.cfi_startproc\n"
    | Diab  -> ()

let cfi_endproc oc =
  if Configuration.asm_supports_cfi then
    match target with
    | Linux -> fprintf oc "	.cfi_endproc\n"
    | Diab  -> ()

let cfi_adjust oc delta =
  if Configuration.asm_supports_cfi then
    match target with
    | Linux -> fprintf oc "	.cfi_adjust_cfa_offset	%ld\n" delta
    | Diab  -> ()

let cfi_rel_offset oc reg ofs =
  if Configuration.asm_supports_cfi then
    match target with
    | Linux -> fprintf oc "	.cfi_rel_offset	%s, %ld\n" reg ofs
    | Diab  -> ()

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

(* Built-ins.  They come in three flavors: 
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers; preserve all registers except the reserved temporaries
     (GPR0, GPR11, GPR12, FPR13);
   - inlined while printing asm code; take their arguments in
     locations dictated by the calling conventions; preserve
     callee-save regs only. *)

(* Handling of annotations *)

let re_file_line = Str.regexp "#line:\\(.*\\):\\([1-9][0-9]*\\)$"

let print_annot_stmt oc txt targs args =
  if Str.string_match re_file_line txt 0 then begin
    print_file_line oc (Str.matched_group 1 txt) (Str.matched_group 2 txt)
  end else begin
    fprintf oc "%s annotation: " comment;
    PrintAnnot.print_annot_stmt preg "R1" oc txt targs args
  end

let print_annot_val oc txt args res =
  fprintf oc "%s annotation: " comment;
  PrintAnnot.print_annot_val preg oc txt args;
  match args, res with
  | [IR src], [IR dst] ->
      if dst <> src then fprintf oc "	mr	%a, %a\n" ireg dst ireg src 
  | [FR src], [FR dst] ->
      if dst <> src then fprintf oc "	fmr	%a, %a\n" freg dst freg src 
  | _, _ ->
      assert false

(* Handling of memcpy *)

(* On the PowerPC, unaligned accesses to 16- and 32-bit integers are
   fast, but unaligned accesses to 64-bit floats can be slow
   (not so much on G5, but clearly so on Power7).
   So, use 64-bit accesses only if alignment >= 4.
   Note that lfd and stfd cannot trap on ill-formed floats. *)

let print_builtin_memcpy_small oc sz al src dst =
  let rec copy ofs sz =
    if sz >= 8 && al >= 4 then begin
      fprintf oc "	lfd	%a, %d(%a)\n" freg FPR13 ofs ireg src;
      fprintf oc "	stfd	%a, %d(%a)\n" freg FPR13 ofs ireg dst;
      copy (ofs + 8) (sz - 8)
    end else if sz >= 4 then begin
      fprintf oc "	lwz	%a, %d(%a)\n" ireg GPR0 ofs ireg src;
      fprintf oc "	stw	%a, %d(%a)\n" ireg GPR0 ofs ireg dst;
      copy (ofs + 4) (sz - 4)
    end else if sz >= 2 then begin
      fprintf oc "	lhz	%a, %d(%a)\n" ireg GPR0 ofs ireg src;
      fprintf oc "	sth	%a, %d(%a)\n" ireg GPR0 ofs ireg dst;
      copy (ofs + 2) (sz - 2)
    end else if sz >= 1 then begin
      fprintf oc "	lbz	%a, %d(%a)\n" ireg GPR0 ofs ireg src;
      fprintf oc "	stb	%a, %d(%a)\n" ireg GPR0 ofs ireg dst;
      copy (ofs + 1) (sz - 1)
    end in
  copy 0 sz

let print_builtin_memcpy_big oc sz al src dst =
  assert (sz >= 4);
  fprintf oc "	li	%a, %d\n" ireg GPR0 (sz / 4);
  fprintf oc "	mtctr	%a\n" ireg GPR0;
  let (s,d) = if dst <> GPR11 then (GPR11, GPR12) else (GPR12, GPR11) in
  fprintf oc "	addi	%a, %a, -4\n" ireg s ireg src;
  fprintf oc "	addi	%a, %a, -4\n" ireg d ireg dst;
  let lbl = new_label() in
  fprintf oc "%a:	lwzu	%a, 4(%a)\n" label lbl ireg GPR0 ireg s;
  fprintf oc "	stwu	%a, 4(%a)\n" ireg GPR0 ireg d;
  fprintf oc "	bdnz	%a\n" label lbl;
  (* s and d lag behind by 4 bytes *)
  match sz land 3 with
  | 1 -> fprintf oc "	lbz	%a, 4(%a)\n" ireg GPR0 ireg s;
         fprintf oc "	stb	%a, 4(%a)\n" ireg GPR0 ireg d
  | 2 -> fprintf oc "	lhz	%a, 4(%a)\n" ireg GPR0 ireg s;
         fprintf oc "	sth	%a, 4(%a)\n" ireg GPR0 ireg d
  | 3 -> fprintf oc "	lhz	%a, 4(%a)\n" ireg GPR0 ireg s;
         fprintf oc "	sth	%a, 4(%a)\n" ireg GPR0 ireg d;
         fprintf oc "	lbz	%a, 6(%a)\n" ireg GPR0 ireg s;
         fprintf oc "	stb	%a, 6(%a)\n" ireg GPR0 ireg d
  | _ -> ()

let print_builtin_memcpy oc sz al args =
  let (dst, src) =
    match args with [IR d; IR s] -> (d, s) | _ -> assert false in
  fprintf oc "%s begin builtin __builtin_memcpy_aligned, size = %d, alignment = %d\n"
          comment sz al;
  if sz <= 64
  then print_builtin_memcpy_small oc sz al src dst
  else print_builtin_memcpy_big oc sz al src dst;
  fprintf oc "%s end builtin __builtin_memcpy_aligned\n" comment

(* Handling of volatile reads and writes *)

let print_builtin_vload_common oc chunk base offset res =
  match chunk, res with
  | Mint8unsigned, IR res ->
      fprintf oc "	lbz	%a, %a(%a)\n" ireg res constant offset ireg base
  | Mint8signed, IR res ->
      fprintf oc "	lbz	%a, %a(%a)\n" ireg res constant offset ireg base;
      fprintf oc "	extsb	%a, %a\n" ireg res ireg res
  | Mint16unsigned, IR res ->
      fprintf oc "	lhz	%a, %a(%a)\n" ireg res constant offset ireg base
  | Mint16signed, IR res ->
      fprintf oc "	lha	%a, %a(%a)\n" ireg res constant offset ireg base
  | Mint32, IR res ->
      fprintf oc "	lwz	%a, %a(%a)\n" ireg res constant offset ireg base
  | Mfloat32, FR res ->
      fprintf oc "	lfs	%a, %a(%a)\n" freg res constant offset ireg base
  | (Mfloat64 | Mfloat64al32), FR res ->
      fprintf oc "	lfd	%a, %a(%a)\n" freg res constant offset ireg base
  (* Mint64 is special-cased below *)
  | _ ->
      assert false

let print_builtin_vload oc chunk args res =
  fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
  begin match args, res with
  | [IR addr], [res] when chunk <> Mint64 ->
      print_builtin_vload_common oc chunk addr (Cint Integers.Int.zero) res
  | [IR addr], [IR res1; IR res2] when chunk = Mint64 ->
      if addr <> res1 then begin
        fprintf oc "	lwz	%a, 0(%a)\n" ireg res1 ireg addr;
        fprintf oc "	lwz	%a, 4(%a)\n" ireg res2 ireg addr
      end else begin
        fprintf oc "	lwz	%a, 4(%a)\n" ireg res2 ireg addr;
        fprintf oc "	lwz	%a, 0(%a)\n" ireg res1 ireg addr
      end
  | _ ->
      assert false
  end;
  fprintf oc "%s end builtin __builtin_volatile_read\n" comment

let print_builtin_vload_global oc chunk id ofs args res =
  fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
  begin match res with
  | [res] when chunk <> Mint64 ->
      fprintf oc "	addis	%a, %a, %a\n"
                 ireg GPR11 ireg_or_zero GPR0 constant (Csymbol_high(id, ofs));
      print_builtin_vload_common oc chunk GPR11 (Csymbol_low(id, ofs)) res
  | [IR res1; IR res2] when chunk = Mint64 ->
      fprintf oc "	addis	%a, %a, %a\n"
                 ireg res1 ireg_or_zero GPR0 constant (Csymbol_high(id, ofs));
      fprintf oc "	lwz	%a, %a(%a)\n"
                 ireg res1 constant (Csymbol_low(id, ofs)) ireg res1;
      let ofs = Integers.Int.add ofs (coqint_of_camlint 4l) in
      fprintf oc "	addis	%a, %a, %a\n"
                 ireg res2 ireg_or_zero GPR0 constant (Csymbol_high(id, ofs));
      fprintf oc "	lwz	%a, %a(%a)\n"
                 ireg res2 constant (Csymbol_low(id, ofs)) ireg res2
  | _ ->
      assert false
  end;
  fprintf oc "%s end builtin __builtin_volatile_read\n" comment

let print_builtin_vstore_common oc chunk base offset src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), IR src ->
      fprintf oc "	stb	%a, %a(%a)\n" ireg src constant offset ireg base
  | (Mint16signed | Mint16unsigned), IR src ->
      fprintf oc "	sth	%a, %a(%a)\n" ireg src constant offset ireg base
  | Mint32, IR src ->
      fprintf oc "	stw	%a, %a(%a)\n" ireg src constant offset ireg base
  | Mfloat32, FR src ->
      fprintf oc "	frsp	%a, %a\n" freg FPR13 freg src;
      fprintf oc "	stfs	%a, %a(%a)\n" freg FPR13 constant offset ireg base
  | (Mfloat64 | Mfloat64al32), FR src ->
      fprintf oc "	stfd	%a, %a(%a)\n" freg src constant offset ireg base
  (* Mint64 is special-cased below *)
  | _ ->
      assert false

let print_builtin_vstore oc chunk args =
  fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
  begin match args with
  | [IR addr; src] when chunk <> Mint64 ->
      print_builtin_vstore_common oc chunk addr (Cint Integers.Int.zero) src
  | [IR addr; IR src1; IR src2] when chunk = Mint64 ->
      fprintf oc "	stw	%a, 0(%a)\n" ireg src1 ireg addr;
      fprintf oc "	stw	%a, 4(%a)\n" ireg src2 ireg addr
  | _ ->
      assert false
  end;
  fprintf oc "%s end builtin __builtin_volatile_write\n" comment

let print_builtin_vstore_global oc chunk id ofs args =
  fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
  begin match args with
  | [src] when chunk <> Mint64 ->
      let tmp = if src = IR GPR11 then GPR12 else GPR11 in
      fprintf oc "	addis	%a, %a, %a\n"
                 ireg tmp ireg_or_zero GPR0 constant (Csymbol_high(id, ofs));
      print_builtin_vstore_common oc chunk tmp (Csymbol_low(id, ofs)) src
  | [IR src1; IR src2] when chunk = Mint64 ->
      let tmp =
        if not (List.mem GPR12 [src1; src2]) then GPR12 else
        if not (List.mem GPR11 [src1; src2]) then GPR11 else GPR10 in
      fprintf oc "	addis	%a, %a, %a\n"
                 ireg tmp ireg_or_zero GPR0 constant (Csymbol_high(id, ofs));
      fprintf oc "	stw	%a, %a(%a)\n"
                 ireg src1 constant (Csymbol_low(id, ofs)) ireg tmp;
      let ofs = Integers.Int.add ofs (coqint_of_camlint 4l) in
      fprintf oc "	addis	%a, %a, %a\n"
                 ireg tmp ireg_or_zero GPR0 constant (Csymbol_high(id, ofs));
      fprintf oc "	stw	%a, %a(%a)\n"
                 ireg src2 constant (Csymbol_low(id, ofs)) ireg tmp
  | _ ->
      assert false
  end;
  fprintf oc "%s end builtin __builtin_volatile_write\n" comment

(* Handling of compiler-inlined builtins *)

let print_builtin_inline oc name args res =
  fprintf oc "%s begin builtin %s\n" comment name;
  (* Can use as temporaries: GPR0, FPR13 *)
  begin match name, args, res with
  (* Integer arithmetic *)
  | "__builtin_mulhw", [IR a1; IR a2], [IR res] ->
      fprintf oc "	mulhw	%a, %a, %a\n" ireg res ireg a1 ireg a2
  | "__builtin_mulhwu", [IR a1; IR a2], [IR res] ->
      fprintf oc "	mulhwu	%a, %a, %a\n" ireg res ireg a1 ireg a2
  | "__builtin_cntlz", [IR a1], [IR res] ->
      fprintf oc "	cntlzw	%a, %a\n" ireg res ireg a1
  | ("__builtin_bswap" | "__builtin_bswap32"), [IR a1], [IR res] ->
      fprintf oc "	stwu	%a, -8(%a)\n" ireg a1 ireg GPR1;
      cfi_adjust oc 8l;
      fprintf oc "	lwbrx	%a, %a, %a\n" ireg res ireg_or_zero GPR0 ireg GPR1;
      fprintf oc "	addi	%a, %a, 8\n" ireg GPR1 ireg GPR1;
      cfi_adjust oc (-8l)
  | "__builtin_bswap16", [IR a1], [IR res] ->
      fprintf oc "	rlwinm	%a, %a, 8, 16, 23\n" ireg GPR0 ireg a1;
      fprintf oc "	rlwinm	%a, %a, 24, 24, 31\n" ireg res ireg a1;
      fprintf oc "	or	%a, %a, %a\n" ireg res ireg GPR0 ireg res
  (* Float arithmetic *)
  | "__builtin_fmadd", [FR a1; FR a2; FR a3], [FR res] ->
      fprintf oc "	fmadd	%a, %a, %a, %a\n" freg res freg a1 freg a2 freg a3
  | "__builtin_fmsub", [FR a1; FR a2; FR a3], [FR res] ->
      fprintf oc "	fmsub	%a, %a, %a, %a\n" freg res freg a1 freg a2 freg a3
  | "__builtin_fnmadd", [FR a1; FR a2; FR a3], [FR res] ->
      fprintf oc "	fnmadd	%a, %a, %a, %a\n" freg res freg a1 freg a2 freg a3
  | "__builtin_fnmsub", [FR a1; FR a2; FR a3], [FR res] ->
      fprintf oc "	fnmsub	%a, %a, %a, %a\n" freg res freg a1 freg a2 freg a3
  | "__builtin_fabs", [FR a1], [FR res] ->
      fprintf oc "	fabs	%a, %a\n" freg res freg a1
  | "__builtin_fsqrt", [FR a1], [FR res] ->
      fprintf oc "	fsqrt	%a, %a\n" freg res freg a1
  | "__builtin_frsqrte", [FR a1], [FR res] ->
      fprintf oc "	frsqrte	%a, %a\n" freg res freg a1
  | "__builtin_fres", [FR a1], [FR res] ->
      fprintf oc "	fres	%a, %a\n" freg res freg a1
  | "__builtin_fsel", [FR a1; FR a2; FR a3], [FR res] ->
      fprintf oc "	fsel	%a, %a, %a, %a\n" freg res freg a1 freg a2 freg a3
  | "__builtin_fcti", [FR a1], [IR res] ->
      fprintf oc "	fctiw	%a, %a\n" freg FPR13 freg a1;
      fprintf oc "	stfdu	%a, -8(%a)\n" freg FPR13 ireg GPR1;
      cfi_adjust oc 8l;
      fprintf oc "	lwz	%a, 4(%a)\n" ireg res ireg GPR1;
      fprintf oc "	addi	%a, %a, 8\n" ireg GPR1 ireg GPR1;
      cfi_adjust oc (-8l)
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [IR ah; IR al], [IR rh; IR rl] ->
      if rl = ah then begin
        fprintf oc "	subfic	%a, %a, 0\n" ireg GPR0 ireg al;
        fprintf oc "	subfze	%a, %a\n" ireg rh ireg ah;
        fprintf oc "	mr	%a, %a\n" ireg rl ireg GPR0
      end else begin
        fprintf oc "	subfic	%a, %a, 0\n" ireg rl ireg al;
        fprintf oc "	subfze	%a, %a\n" ireg rh ireg ah
      end
  | "__builtin_addl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
      if rl = ah || rl = bh then begin
        fprintf oc "	addc	%a, %a, %a\n" ireg GPR0 ireg al ireg bl;
        fprintf oc "	adde	%a, %a, %a\n" ireg rh ireg ah ireg bh;
        fprintf oc "	mr	%a, %a\n" ireg rl ireg GPR0
      end else begin
        fprintf oc "	addc	%a, %a, %a\n" ireg rl ireg al ireg bl;
        fprintf oc "	adde	%a, %a, %a\n" ireg rh ireg ah ireg bh
      end
  | "__builtin_subl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
      if rl = ah || rl = bh then begin
        fprintf oc "	subfc	%a, %a, %a\n" ireg GPR0 ireg bl ireg al;
        fprintf oc "	subfe	%a, %a, %a\n" ireg rh ireg bh ireg ah;
        fprintf oc "	mr	%a, %a\n" ireg rl ireg GPR0
      end else begin
        fprintf oc "	subfc	%a, %a, %a\n" ireg rl ireg bl ireg al;
        fprintf oc "	subfe	%a, %a, %a\n" ireg rh ireg bh ireg ah
      end
  | "__builtin_mull", [IR a; IR b], [IR rh; IR rl] ->
      if rl = a || rl = b then begin
        fprintf oc "	mullw	%a, %a, %a\n" ireg GPR0 ireg a ireg b;
        fprintf oc "	mulhwu	%a, %a, %a\n" ireg rh ireg a ireg b;
        fprintf oc "	mr	%a, %a\n" ireg rl ireg GPR0
      end else begin
        fprintf oc "	mullw	%a, %a, %a\n" ireg rl ireg a ireg b;
        fprintf oc "	mulhwu	%a, %a, %a\n" ireg rh ireg a ireg b
      end
  (* Memory accesses *)
  | "__builtin_read16_reversed", [IR a1], [IR res] ->
      fprintf oc "	lhbrx	%a, %a, %a\n" ireg res ireg_or_zero GPR0 ireg a1
  | "__builtin_read32_reversed", [IR a1], [IR res] ->
      fprintf oc "	lwbrx	%a, %a, %a\n" ireg res ireg_or_zero GPR0 ireg a1
  | "__builtin_write16_reversed", [IR a1; IR a2], _ ->
      fprintf oc "	sthbrx	%a, %a, %a\n" ireg a2 ireg_or_zero GPR0 ireg a1
  | "__builtin_write32_reversed", [IR a1; IR a2], _ ->
      fprintf oc "	stwbrx	%a, %a, %a\n" ireg a2 ireg_or_zero GPR0 ireg a1
  (* Synchronization *)
  | "__builtin_eieio", [], _ ->
      fprintf oc "	eieio\n"
  | "__builtin_sync", [], _ ->
      fprintf oc "	sync\n"
  | "__builtin_isync", [], _ ->
      fprintf oc "	isync\n"
  | "__builtin_trap", [], _ ->
      fprintf oc "	trap\n"
  (* Catch-all *)
  | _ ->
      invalid_arg ("unrecognized builtin " ^ name)
  end;
  fprintf oc "%s end builtin %s\n" comment name

(* Determine if the displacement of a conditional branch fits the short form *)

let short_cond_branch tbl pc lbl_dest =
  match PTree.get lbl_dest tbl with
  | None -> assert false
  | Some pc_dest -> 
      let disp = pc_dest - pc in -0x2000 <= disp && disp < 0x2000

(* Printing of instructions *)

let float_literals : (int * int64) list ref = ref []
let jumptables : (int * label list) list ref = ref []

let print_instruction oc tbl pc fallthrough = function
  | Padd(r1, r2, r3) ->
      fprintf oc "	add	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Padde(r1, r2, r3) ->
      fprintf oc "	adde	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Paddi(r1, r2, c) ->
      fprintf oc "	addi	%a, %a, %a\n" ireg r1 ireg_or_zero r2 constant c
  | Paddic(r1, r2, c) ->
      fprintf oc "	addic	%a, %a, %a\n" ireg r1 ireg_or_zero r2 constant c
  | Paddis(r1, r2, c) ->
      fprintf oc "	addis	%a, %a, %a\n" ireg r1 ireg_or_zero r2 constant c
  | Paddze(r1, r2) ->
      fprintf oc "	addze	%a, %a\n" ireg r1 ireg r2
  | Pallocframe(sz, ofs) ->
      let sz = camlint_of_coqint sz
      and ofs = camlint_of_coqint ofs in
      assert (ofs = 0l);
      let adj = Int32.neg sz in
      if adj >= -0x8000l then
        fprintf oc "	stwu	%a, %ld(%a)\n" ireg GPR1 adj ireg GPR1
      else begin
        fprintf oc "	addis	%a, 0, %ld\n" ireg GPR0 (Int32.shift_right_logical adj 16);
        fprintf oc "	ori	%a, %a, %ld\n" ireg GPR0 ireg GPR0 (Int32.logand adj 0xFFFFl);
        fprintf oc "	stwux	%a, %a, %a\n" ireg GPR1 ireg GPR1 ireg GPR0
      end;
      cfi_adjust oc sz
  | Pand_(r1, r2, r3) ->
      fprintf oc "	and.	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pandc(r1, r2, r3) ->
      fprintf oc "	andc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pandi_(r1, r2, c) ->
      fprintf oc "	andi.	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pandis_(r1, r2, c) ->
      fprintf oc "	andis.	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pb lbl ->
      fprintf oc "	b	%a\n" label (transl_label lbl)
  | Pbctr ->
      fprintf oc "	bctr\n"
  | Pbctrl ->
      fprintf oc "	bctrl\n"
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
  | Pbl s ->
      fprintf oc "	bl	%a\n" symbol s
  | Pbs s ->
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
  | Pcmplw(r1, r2) ->
      fprintf oc "	cmplw	%a, %a, %a\n" creg 0 ireg r1 ireg r2
  | Pcmplwi(r1, c) ->
      fprintf oc "	cmplwi	%a, %a, %a\n" creg 0 ireg r1 constant c
  | Pcmpw(r1, r2) ->
      fprintf oc "	cmpw	%a, %a, %a\n" creg 0 ireg r1 ireg r2
  | Pcmpwi(r1, c) ->
      fprintf oc "	cmpwi	%a, %a, %a\n" creg 0 ireg r1 constant c
  | Pcror(c1, c2, c3) ->
      fprintf oc "	cror	%a, %a, %a\n" crbit c1 crbit c2 crbit c3
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
  | Pfreeframe(sz, ofs) ->
      let sz = camlint_of_coqint sz
      and ofs = camlint_of_coqint ofs in
      if sz < 0x8000l then
        fprintf oc "	addi	%a, %a, %ld\n" ireg GPR1 ireg GPR1 sz
      else
        fprintf oc "	lwz	%a, %ld(%a)\n" ireg GPR1 ofs ireg GPR1
  | Pfabs(r1, r2) ->
      fprintf oc "	fabs	%a, %a\n" freg r1 freg r2
  | Pfadd(r1, r2, r3) ->
      fprintf oc "	fadd	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfcmpu(r1, r2) ->
      fprintf oc "	fcmpu	%a, %a, %a\n" creg 0 freg r1 freg r2
  | Pfcti(r1, r2) ->
      fprintf oc "%s begin pseudoinstr %a = fcti(%a)\n" comment ireg r1 freg r2;
      fprintf oc "	fctiwz	%a, %a\n" freg FPR13 freg r2;
      fprintf oc "	stfdu	%a, -8(%a)\n" freg FPR13 ireg GPR1;
      cfi_adjust oc 8l;
      fprintf oc "	lwz	%a, 4(%a)\n" ireg r1 ireg GPR1;
      fprintf oc "	addi	%a, %a, 8\n" ireg GPR1 ireg GPR1;
      cfi_adjust oc (-8l);
      fprintf oc "%s end pseudoinstr fcti\n" comment
  | Pfdiv(r1, r2, r3) ->
      fprintf oc "	fdiv	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfmake(rd, r1, r2) ->
      fprintf oc "%s begin pseudoinstr %a = fmake(%a, %a)\n"
              comment freg rd ireg r1 ireg r2;
      fprintf oc "	stwu	%a, -8(%a)\n" ireg r1 ireg GPR1;
      cfi_adjust oc 8l;
      fprintf oc "	stw	%a, 4(%a)\n" ireg r2 ireg GPR1;
      fprintf oc "	lfd	%a, 0(%a)\n" freg rd ireg GPR1;
      fprintf oc "	addi	%a, %a, 8\n" ireg GPR1 ireg GPR1;
      cfi_adjust oc (-8l);
      fprintf oc "%s end pseudoinstr fmake\n" comment
  | Pfmr(r1, r2) ->
      fprintf oc "	fmr	%a, %a\n" freg r1 freg r2
  | Pfmul(r1, r2, r3) ->
      fprintf oc "	fmul	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfneg(r1, r2) ->
      fprintf oc "	fneg	%a, %a\n" freg r1 freg r2
  | Pfrsp(r1, r2) ->
      fprintf oc "	frsp	%a, %a\n" freg r1 freg r2
  | Pfsub(r1, r2, r3) ->
      fprintf oc "	fsub	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Plbz(r1, c, r2) ->
      fprintf oc "	lbz	%a, %a(%a)\n" ireg r1 constant c ireg r2
  | Plbzx(r1, r2, r3) ->
      fprintf oc "	lbzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plfd(r1, c, r2) ->
      fprintf oc "	lfd	%a, %a(%a)\n" freg r1 constant c ireg r2
  | Plfdx(r1, r2, r3) ->
      fprintf oc "	lfdx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Plfi(r1, c) ->
      let lbl = new_label() in
      fprintf oc "	addis	%a, 0, %a\n" ireg GPR12 label_high lbl;
      fprintf oc "	lfd	%a, %a(%a) %s %.18g\n" freg r1 label_low lbl ireg GPR12 comment (camlfloat_of_coqfloat c);
      float_literals := (lbl, camlint64_of_coqint (Floats.Float.bits_of_double c)) :: !float_literals;
  | Plfs(r1, c, r2) ->
      fprintf oc "	lfs	%a, %a(%a)\n" freg r1 constant c ireg r2
  | Plfsx(r1, r2, r3) ->
      fprintf oc "	lfsx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Plha(r1, c, r2) ->
      fprintf oc "	lha	%a, %a(%a)\n" ireg r1 constant c ireg r2
  | Plhax(r1, r2, r3) ->
      fprintf oc "	lhax	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plhz(r1, c, r2) ->
      fprintf oc "	lhz	%a, %a(%a)\n" ireg r1 constant c ireg r2
  | Plhzx(r1, r2, r3) ->
      fprintf oc "	lhzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plwz(r1, c, r2) ->
      fprintf oc "	lwz	%a, %a(%a)\n" ireg r1 constant c ireg r2
  | Plwzx(r1, r2, r3) ->
      fprintf oc "	lwzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pmfcrbit(r1, bit) ->
      fprintf oc "	mfcr	%a\n" ireg r1;
      fprintf oc "	rlwinm	%a, %a, %d, 31, 31\n" ireg r1  ireg r1 (1 + num_crbit bit)
  | Pmflr(r1) ->
      fprintf oc "	mflr	%a\n" ireg r1;
      cfi_rel_offset oc "lr" 8l
  | Pmr(r1, r2) ->
      fprintf oc "	mr	%a, %a\n" ireg r1 ireg r2
  | Pmtctr(r1) ->
      fprintf oc "	mtctr	%a\n" ireg r1
  | Pmtlr(r1) ->
      fprintf oc "	mtlr	%a\n" ireg r1
  | Pmulli(r1, r2, c) ->
      fprintf oc "	mulli	%a, %a, %a\n" ireg r1 ireg r2 constant c
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
      fprintf oc "	ori	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Poris(r1, r2, c) ->
      fprintf oc "	oris	%a, %a, %a\n" ireg r1 ireg r2 constant c
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
  | Pslw(r1, r2, r3) ->
      fprintf oc "	slw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psraw(r1, r2, r3) ->
      fprintf oc "	sraw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psrawi(r1, r2, c) ->
      fprintf oc "	srawi	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint c)
  | Psrw(r1, r2, r3) ->
      fprintf oc "	srw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstb(r1, c, r2) ->
      fprintf oc "	stb	%a, %a(%a)\n" ireg r1 constant c ireg r2
  | Pstbx(r1, r2, r3) ->
      fprintf oc "	stbx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstfd(r1, c, r2) ->
      fprintf oc "	stfd	%a, %a(%a)\n" freg r1 constant c ireg r2
  | Pstfdx(r1, r2, r3) ->
      fprintf oc "	stfdx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Pstfs(r1, c, r2) ->
      fprintf oc "	frsp	%a, %a\n" freg FPR13 freg r1;
      fprintf oc "	stfs	%a, %a(%a)\n" freg FPR13 constant c ireg r2
  | Pstfsx(r1, r2, r3) ->
      fprintf oc "	frsp	%a, %a\n" freg FPR13 freg r1;
      fprintf oc "	stfsx	%a, %a, %a\n" freg FPR13 ireg r2 ireg r3
  | Psth(r1, c, r2) ->
      fprintf oc "	sth	%a, %a(%a)\n" ireg r1 constant c ireg r2
  | Psthx(r1, r2, r3) ->
      fprintf oc "	sthx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstw(r1, c, r2) ->
      fprintf oc "	stw	%a, %a(%a)\n" ireg r1 constant c ireg r2
  | Pstwx(r1, r2, r3) ->
      fprintf oc "	stwx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psubfc(r1, r2, r3) ->
      fprintf oc "	subfc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psubfe(r1, r2, r3) ->
      fprintf oc "	subfe	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psubfic(r1, r2, c) ->
      fprintf oc "	subfic	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pxor(r1, r2, r3) ->
      fprintf oc "	xor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pxori(r1, r2, c) ->
      fprintf oc "	xori	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pxoris(r1, r2, c) ->
      fprintf oc "	xoris	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Plabel lbl ->
      if (not fallthrough) && !Clflags.option_falignbranchtargets > 0 then
        fprintf oc "	.balign	%d\n" !Clflags.option_falignbranchtargets;
      fprintf oc "%a:\n" label (transl_label lbl)
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

(* Determine if an instruction falls through *)

let instr_fall_through = function
  | Pb _ -> false
  | Pbctr -> false
  | Pbs _ -> false
  | Pblr -> false
  | _ -> true

(* Estimate the size of an Asm instruction encoding, in number of actual
   PowerPC instructions.  We can over-approximate. *)

let instr_size = function
  | Pallocframe(sz, ofs) -> 3
  | Pbf(bit, lbl) -> 2
  | Pbt(bit, lbl) -> 2
  | Pbtbl(r, tbl) -> 4
  | Pfcti(r1, r2) -> 4
  | Pfmake(rd, r1, r2) -> 4
  | Plfi(r1, c) -> 2
  | Pmfcrbit(r1, bit) -> 2
  | Pstfs(r1, c, r2) -> 2
  | Pstfsx(r1, r2, r3) -> 2
  | Plabel lbl -> 0
  | Pbuiltin(ef, args, res) ->
      begin match ef with
      | EF_builtin(name, sg) ->
          begin match extern_atom name with
          | "__builtin_bswap" | "__builtin_bswap32" | "__builtin_bswap16" -> 3
          | "__builtin_fcti" -> 4
          | _ -> 1
          end
      | EF_vload chunk ->
          if chunk = Mint8signed then 2 else 1
      | EF_vstore chunk ->
          if chunk = Mfloat32 then 2 else 1
      | EF_vload_global(chunk, id, ofs) ->
          if chunk = Mint8signed then 3 else 2
      | EF_vstore_global(chunk, id, ofs) ->
          if chunk = Mfloat32 then 3 else 2
      | EF_memcpy(sz, al) ->
          let sz = Int32.to_int (camlint_of_coqint sz) in
          if sz <= 64 then (sz / 4) * 2 + 6 else 11
      | EF_annot_val(txt, targ) ->
          0
      | EF_inline_asm txt ->
          8 (* reasonable? default *)
      | _ ->
          assert false
      end
  | Pannot(ef, args) -> 0
  | _ -> 1

(* Build a table label -> estimated position in generated code.
   Used to predict if relative conditional branches can use the short form. *)

let rec label_positions tbl pc = function
  | [] -> tbl
  | Plabel lbl :: c -> label_positions (PTree.set lbl pc tbl) pc c
  | i :: c -> label_positions tbl (pc + instr_size i) c

(* Emit a sequence of instructions *)

let rec print_instructions oc tbl pc fallthrough = function
  | [] -> ()
  | i :: c ->
      print_instruction oc tbl pc fallthrough i;
      print_instructions oc tbl (pc + instr_size i) (instr_fall_through i) c

(* Print the code for a function *)

let print_literal oc (lbl, n) =
  let nlo = Int64.to_int32 n
  and nhi = Int64.to_int32(Int64.shift_right_logical n 32) in
  fprintf oc "%a:	.long	0x%lx, 0x%lx\n" label lbl nhi nlo

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
    match !Clflags.option_falignfunctions with Some n -> n | None -> 4 in
  fprintf oc "	.balign %d\n" alignment;
  if not (C2C.atom_is_static name) then
    fprintf oc "	.globl %a\n" symbol name;
  fprintf oc "%a:\n" symbol name;
  print_location oc (C2C.atom_location name);
  cfi_startproc oc;
  print_instructions oc (label_positions PTree.empty 0 code) 0 true code;
  cfi_endproc oc;
  fprintf oc "	.type	%a, @function\n" symbol name;
  fprintf oc "	.size	%a, . - %a\n" symbol name symbol name;
  if !float_literals <> [] then begin
    section oc lit;
    fprintf oc "	.balign 8\n";
    List.iter (print_literal oc) !float_literals;
    float_literals := []
  end;
  if !jumptables <> [] then begin
    section oc jmptbl;
    fprintf oc "	.balign 4\n";
    List.iter (print_jumptable oc) !jumptables;
    jumptables := []
  end

(* Generation of stub functions *)

let re_variadic_stub = Str.regexp "\\(.*\\)\\$[ifl]*$"

(* Stubs for EABI *)

let variadic_stub oc stub_name fun_name args =
  section oc Section_text;
  fprintf oc "	.balign 4\n";
  fprintf oc ".L%s$stub:\n" stub_name;
  (* bit 6 must be set if at least one argument is a float; clear otherwise *)
  if List.mem Tfloat args
  then fprintf oc "	creqv	6, 6, 6\n"
  else fprintf oc "	crxor	6, 6, 6\n";
  fprintf oc "	b	%s\n" fun_name

let stub_function oc name sg =
  let name = extern_atom name in
  (* Only variadic functions need a stub *)
  if Str.string_match re_variadic_stub name 0
  then variadic_stub oc name (Str.matched_group 1 name) sg.sig_args

let function_needs_stub name =
  Str.string_match re_variadic_stub (extern_atom name) 0

(* Generation of whole programs *)

let print_fundef oc name defn =
  match defn with
  | Internal code ->
      print_function oc name code
  | External ((EF_external _ | EF_malloc | EF_free) as ef) ->
      if function_needs_stub name then stub_function oc name (ef_sig ef)
  | External _ ->
      ()

let record_extfun (name, gd) =
  match gd with
  | Gfun(External (EF_external _ | EF_malloc | EF_free)) ->
      if function_needs_stub name then
        stubbed_functions := IdentSet.add name !stubbed_functions
  | _ -> ()

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
  | Init_int64 n ->
      let b = camlint64_of_coqint n in
      fprintf oc "	.long	0x%Lx, 0x%Lx\n"
                 (Int64.shift_right_logical b 32)
                 (Int64.logand b 0xFFFFFFFFL)
  | Init_float32 n ->
      fprintf oc "	.long	0x%lx %s %.18g\n"
                 (camlint_of_coqint (Floats.Float.bits_of_single n))
                 comment (camlfloat_of_coqfloat n)
  | Init_float64 n ->
      let b = camlint64_of_coqint (Floats.Float.bits_of_double n) in
      fprintf oc "	.long	0x%Lx, 0x%Lx %s %.18g\n"
                 (Int64.shift_right_logical b 32)
                 (Int64.logand b 0xFFFFFFFFL)
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
        | None -> 8 in (* 8-alignment is a safe default *)
      let name_sec =
        name_of_section sec in
      if name_sec <> "COMM" then begin
        fprintf oc "	%s\n" name_sec;
        fprintf oc "	.balign	%d\n" align;
        if not (C2C.atom_is_static name) then
          fprintf oc "	.globl	%a\n" symbol name;
        fprintf oc "%a:\n" symbol name;
        print_init_data oc name v.gvar_init;
        fprintf oc "	.type	%a, @object\n" symbol name;
        fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
      end else begin
        let sz =
          match v.gvar_init with [Init_space sz] -> sz | _ -> assert false in
        fprintf oc "	%s	%a, %s, %d\n"
          (if C2C.atom_is_static name then ".lcomm" else ".comm")
          symbol name
          (Z.to_string sz)
          (1 lsl align)
      end

let print_globdef oc (name, gdef) =
  match gdef with
  | Gfun f -> print_fundef oc name f
  | Gvar v -> print_var oc name v

let print_prologue oc =
  match target with
  | Linux ->
      ()
  | Diab ->
      fprintf oc "	.xopt	align-fill-text=0x60000000\n";
      if !Clflags.option_g then
        fprintf oc "	.xopt	asm-debug-on\n"

let print_program oc p =
  stubbed_functions := IdentSet.empty;
  List.iter record_extfun p.prog_defs;
  reset_file_line();
  print_prologue oc;
  List.iter (print_globdef oc) p.prog_defs


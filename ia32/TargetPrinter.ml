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

(* Printing IA32 assembly code in asm syntax *)

open Printf
open Datatypes
open Camlcoq
open Sections
open AST
open Memdata
open Asm
open PrintAsmaux

module StringSet = Set.Make(String)

(* Basic printing functions used in definition of the systems *)

let int_reg_name = function
  | EAX -> "%eax"  | EBX -> "%ebx"  | ECX -> "%ecx"  | EDX -> "%edx"
  | ESI -> "%esi"  | EDI -> "%edi"  | EBP -> "%ebp"  | ESP -> "%esp"

let int8_reg_name = function
  | EAX -> "%al"  | EBX -> "%bl"  | ECX -> "%cl"  | EDX -> "%dl"
  | _ -> assert false

let high_int8_reg_name = function
  | EAX -> "%ah"  | EBX -> "%bh"  | ECX -> "%ch"  | EDX -> "%dh"
  | _ -> assert false

let int16_reg_name = function
  | EAX -> "%ax"  | EBX -> "%bx"  | ECX -> "%cx"  | EDX -> "%dx"
  | ESI -> "%si"  | EDI -> "%di"  | EBP -> "%bp"  | ESP -> "%sp"

let float_reg_name = function
  | XMM0 -> "%xmm0"  | XMM1 -> "%xmm1"  | XMM2 -> "%xmm2"  | XMM3 -> "%xmm3"
  | XMM4 -> "%xmm4"  | XMM5 -> "%xmm5"  | XMM6 -> "%xmm6"  | XMM7 -> "%xmm7"

let ireg oc r = output_string oc (int_reg_name r)
let ireg8 oc r = output_string oc (int8_reg_name r)
let high_ireg8 oc r = output_string oc (high_int8_reg_name r)
let ireg16 oc r = output_string oc (int16_reg_name r)
let freg oc r = output_string oc (float_reg_name r)

let preg oc = function
  | IR r -> ireg oc r
  | FR r -> freg oc r
  | _    -> assert false

(* The comment deliminiter *)
let comment = "#"

(* System dependend printer functions *)
module type SYSTEM =
    sig
      val raw_symbol: out_channel -> string -> unit
      val symbol: out_channel -> P.t -> unit
      val label: out_channel -> int -> unit
      val name_of_section: section_name -> string
      val stack_alignment: int
      val print_align: out_channel -> int -> unit
      val print_mov_ra: out_channel -> ireg -> ident -> unit
      val print_fun_info:  out_channel -> P.t -> unit
      val print_var_info: out_channel -> P.t -> unit
      val print_epilogue: out_channel -> unit
      val print_comm_decl: out_channel -> P.t -> Z.t -> int -> unit
      val print_lcomm_decl: out_channel -> P.t -> Z.t -> int -> unit
    end

(* Printer functions for cygwin *)
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
          sprintf ".section	\"%s\", \"%s\"\n"
            s (if ex then "xr" else if wr then "d" else "dr")
      | Section_debug_info
      | Section_debug_abbrev -> "" (* Dummy value *)

    let stack_alignment = 8 (* minimum is 4, 8 is better for perfs *)

    let print_align oc n =
      fprintf oc "	.align	%d\n" n
    
    let print_mov_ra oc rd id =   
      fprintf oc "	movl	$%a, %a\n" symbol id ireg rd

    let print_fun_info _ _  = ()
        
    let print_var_info _ _ = ()

    let print_epilogue _ = ()

    let print_comm_decl oc name sz al =
      fprintf oc "	.comm	%a, %s, %d\n" symbol name (Z.to_string sz) al

    let print_lcomm_decl oc name sz al =
      fprintf oc "	.local	%a\n" symbol name;
      print_comm_decl oc name sz al

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
      | Section_debug_info
      | Section_debug_abbrev -> "" (* Dummy value *)
            
    let stack_alignment = 8 (* minimum is 4, 8 is better for perfs *)
                    
    let print_align oc n =
      fprintf oc "	.align	%d\n" n
        
    let print_mov_ra  oc rd id = 
         fprintf oc "	movl	$%a, %a\n" symbol id ireg rd

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
      | Section_jumptable -> ".const"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\", %s, %s"
            (if wr then "__DATA" else "__TEXT") s
            (if ex then "regular, pure_instructions" else "regular")
      | Section_debug_info
      | Section_debug_abbrev -> "" (* Dummy value *)
    
    let stack_alignment =  16 (* mandatory *)
         
    (* Base-2 log of a Caml integer *)           
    let rec log2 n =
      assert (n > 0);
      if n = 1 then 0 else 1 + log2 (n lsr 1)

    let print_align oc n =
      fprintf oc "	.align	%d\n" (log2 n)
        
    let indirect_symbols : StringSet.t ref = ref StringSet.empty

    let print_mov_ra oc rd id = 
      let id = extern_atom id in
      indirect_symbols := StringSet.add id !indirect_symbols;
      fprintf oc "	movl	L%a$non_lazy_ptr, %a\n" raw_symbol id ireg rd

    let print_fun_info _ _ = ()
 
    let print_var_info _ _ = ()
    
    let print_epilogue oc = 
      fprintf oc "	.section __IMPORT,__pointers,non_lazy_symbol_pointers\n";
      StringSet.iter
        (fun s ->
          fprintf oc "L%a$non_lazy_ptr:\n" raw_symbol s;
          fprintf oc "	.indirect_symbol %a\n" raw_symbol s;
          fprintf oc "	.long	0\n")
        !indirect_symbols;
      indirect_symbols := StringSet.empty

    let print_comm_decl oc name sz al =
      fprintf oc "	.comm	%a, %s, %d\n"
                 symbol name (Z.to_string sz) (log2 al)

    let print_lcomm_decl oc name sz al =
      fprintf oc "	.lcomm	%a, %s, %d\n"
                 symbol name (Z.to_string sz) (log2 al)

  end


module Target(System: SYSTEM):TARGET =
  struct
    open System
    let symbol = symbol

(*  Basic printing functions *)

    let symbol_offset oc (symb, ofs) =
      symbol oc symb;
      if ofs <> 0l then fprintf oc " + %ld" ofs


    let addressing oc (Addrmode(base, shift, cst)) =
      begin match cst with
      | Coq_inl n ->
          let n = camlint_of_coqint n in
          fprintf oc "%ld" n
      | Coq_inr(id, ofs) -> 
          let ofs = camlint_of_coqint ofs in
          if ofs = 0l
          then symbol oc id
          else fprintf oc "(%a + %ld)" symbol id ofs
      end;
      begin match base, shift with
      | None, None -> ()
      | Some r1, None -> fprintf oc "(%a)" ireg r1
      | None, Some(r2,sc) -> fprintf oc "(,%a,%a)" ireg r2 coqint sc
      | Some r1, Some(r2,sc) -> fprintf oc "(%a,%a,%a)" ireg r1 ireg r2 coqint sc
      end

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

(* SP adjustment to allocate or free a stack frame *)

    let int32_align n a =
      if n >= 0l
      then Int32.logand (Int32.add n (Int32.of_int (a-1))) (Int32.of_int (-a))
      else Int32.logand n (Int32.of_int (-a))

    let sp_adjustment sz =
      let sz = camlint_of_coqint sz in
      (* Preserve proper alignment of the stack *)
      let sz = int32_align sz stack_alignment in
      (* The top 4 bytes have already been allocated by the "call" instruction. *)
      let sz = Int32.sub sz 4l in
      sz

(* Base-2 log of a Caml integer *)

    let rec log2 n =
      assert (n > 0);
      if n = 1 then 0 else 1 + log2 (n lsr 1)

(* Emit a align directive *)

    let need_masks = ref false

(* Emit .file / .loc debugging directives *)

    let print_file_line oc file line =
      PrintAnnot.print_file_line oc comment file line

    let print_location oc loc =
      if loc <> Cutil.no_loc then print_file_line oc (fst loc) (snd loc)


(* Built-in functions *)

(* Built-ins.  They come in two flavors: 
   - annotation statements: take their arguments in registers or stack
   locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
   registers; preserve all registers except ECX, EDX, XMM6 and XMM7. *)

(* Handling of annotations *)

    let print_annot_stmt oc txt targs args =
      if Str.string_match re_file_line txt 0 then begin
        print_file_line oc (Str.matched_group 1 txt)
          (int_of_string (Str.matched_group 2 txt))
      end else begin
        fprintf oc "%s annotation: " comment;
        PrintAnnot.print_annot_stmt preg "%esp" oc txt targs args
      end

    let print_annot_val oc txt args res =
      fprintf oc "%s annotation: " comment;
      PrintAnnot.print_annot_val preg oc txt args;
      match args, res with
      | [IR src], [IR dst] ->
          if dst <> src then fprintf oc "	movl	%a, %a\n" ireg src ireg dst
      | [FR src], [FR dst] ->
          if dst <> src then fprintf oc "	movapd	%a, %a\n" freg src freg dst
      | _, _ -> assert false

(* Handling of memcpy *)

(* Unaligned memory accesses are quite fast on IA32, so use large
   memory accesses regardless of alignment. *)

    let print_builtin_memcpy_small oc sz al src dst =
      assert (src = EDX && dst = EAX);
      let rec copy ofs sz =
        if sz >= 8 && !Clflags.option_ffpu then begin
          fprintf oc "	movq	%d(%a), %a\n" ofs ireg src freg XMM7;
          fprintf oc "	movq	%a, %d(%a)\n" freg XMM7 ofs ireg dst;
          copy (ofs + 8) (sz - 8)
        end else if sz >= 4 then begin
          fprintf oc "	movl	%d(%a), %a\n" ofs ireg src ireg ECX;
          fprintf oc "	movl	%a, %d(%a)\n" ireg ECX ofs ireg dst;
          copy (ofs + 4) (sz - 4)
        end else if sz >= 2 then begin
          fprintf oc "	movw	%d(%a), %a\n" ofs ireg src ireg16 ECX;
          fprintf oc "	movw	%a, %d(%a)\n" ireg16 ECX ofs ireg dst;
          copy (ofs + 2) (sz - 2)
        end else if sz >= 1 then begin
          fprintf oc "	movb	%d(%a), %a\n" ofs ireg src ireg8 ECX;
          fprintf oc "	movb	%a, %d(%a)\n" ireg8 ECX ofs ireg dst;
          copy (ofs + 1) (sz - 1)
        end in
      copy 0 sz

    let print_builtin_memcpy_big oc sz al src dst =
      assert (src = ESI && dst = EDI);
      fprintf oc "	movl	$%d, %a\n" (sz / 4) ireg ECX;
      fprintf oc "	rep	movsl\n";
      if sz mod 4 >= 2 then fprintf oc "	movsw\n";
      if sz mod 2 >= 1 then fprintf oc "	movsb\n"

    let print_builtin_memcpy oc sz al args =
      let (dst, src) =
        match args with [IR d; IR s] -> (d, s) | _ -> assert false in
      fprintf oc "%s begin builtin __builtin_memcpy_aligned, size = %d, alignment = %d\n"
        comment sz al;
      if sz <= 32
      then print_builtin_memcpy_small oc sz al src dst
      else print_builtin_memcpy_big oc sz al src dst;
      fprintf oc "%s end builtin __builtin_memcpy_aligned\n" comment

(* Handling of volatile reads and writes *)

    let offset_addressing (Addrmode(base, ofs, cst)) delta =
      Addrmode(base, ofs,
               match cst with
               | Coq_inl n -> Coq_inl(Integers.Int.add n delta)
               | Coq_inr(id, n) -> Coq_inr(id, Integers.Int.add n delta))

    let print_builtin_vload_common oc chunk addr res =
      match chunk, res with
      | Mint8unsigned, [IR res] ->
          fprintf oc "	movzbl	%a, %a\n" addressing addr ireg res
      | Mint8signed, [IR res] ->
          fprintf oc "	movsbl	%a, %a\n" addressing addr ireg res
      | Mint16unsigned, [IR res] ->
          fprintf oc "	movzwl	%a, %a\n" addressing addr ireg res
      | Mint16signed, [IR res] ->
          fprintf oc "	movswl	%a, %a\n" addressing addr ireg res
      | Mint32, [IR res] ->
          fprintf oc "	movl	%a, %a\n" addressing addr ireg res
      | Mint64, [IR res1; IR res2] ->
          let addr' = offset_addressing addr (coqint_of_camlint 4l) in
          if not (Asmgen.addressing_mentions addr res2) then begin
            fprintf oc "	movl	%a, %a\n" addressing addr ireg res2;
            fprintf oc "	movl	%a, %a\n" addressing addr' ireg res1
          end else begin
            fprintf oc "	movl	%a, %a\n" addressing addr' ireg res1;
            fprintf oc "	movl	%a, %a\n" addressing addr ireg res2
          end
      | Mfloat32, [FR res] ->
          fprintf oc "	movss	%a, %a\n" addressing addr freg res
      | Mfloat64, [FR res] ->
          fprintf oc "	movsd	%a, %a\n" addressing addr freg res
      | _ ->
          assert false

    let print_builtin_vload oc chunk args res =
      fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
      begin match args with
      | [IR addr] ->
          print_builtin_vload_common oc chunk
            (Addrmode(Some addr, None, Coq_inl Integers.Int.zero)) res
      | _ ->
          assert false
      end;
      fprintf oc "%s end builtin __builtin_volatile_read\n" comment

    let print_builtin_vload_global oc chunk id ofs args res =
      fprintf oc "%s begin builtin __builtin_volatile_read\n" comment;
      print_builtin_vload_common oc chunk
        (Addrmode(None, None, Coq_inr(id,ofs))) res;
      fprintf oc "%s end builtin __builtin_volatile_read\n" comment

    let print_builtin_vstore_common oc chunk addr src tmp =
      match chunk, src with
      | (Mint8signed | Mint8unsigned), [IR src] ->
          if Asmgen.low_ireg src then
            fprintf oc "	movb	%a, %a\n" ireg8 src addressing addr
          else begin
            fprintf oc "	movl	%a, %a\n" ireg src ireg tmp;
            fprintf oc "	movb	%a, %a\n" ireg8 tmp addressing addr
          end
      | (Mint16signed | Mint16unsigned), [IR src] ->
          fprintf oc "	movw	%a, %a\n" ireg16 src addressing addr
      | Mint32, [IR src] ->
          fprintf oc "	movl	%a, %a\n" ireg src addressing addr
      | Mint64, [IR src1; IR src2] ->
          let addr' = offset_addressing addr (coqint_of_camlint 4l) in
          fprintf oc "	movl	%a, %a\n" ireg src2 addressing addr;
          fprintf oc "	movl	%a, %a\n" ireg src1 addressing addr'
      | Mfloat32, [FR src] ->
          fprintf oc "	movss	%a, %a\n" freg src addressing addr
      | Mfloat64, [FR src] ->
          fprintf oc "	movsd	%a, %a\n" freg src addressing addr
      | _ ->
          assert false

    let print_builtin_vstore oc chunk args =
      fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
      begin match args with
      | IR addr :: src ->
          print_builtin_vstore_common oc chunk
            (Addrmode(Some addr, None, Coq_inl Integers.Int.zero)) src
            (if addr = EAX then ECX else EAX)
      | _ ->
          assert false
      end;
      fprintf oc "%s end builtin __builtin_volatile_write\n" comment

    let print_builtin_vstore_global oc chunk id ofs args =
      fprintf oc "%s begin builtin __builtin_volatile_write\n" comment;
      print_builtin_vstore_common oc chunk
        (Addrmode(None, None, Coq_inr(id,ofs))) args EAX;
      fprintf oc "%s end builtin __builtin_volatile_write\n" comment

(* Handling of varargs *)

    let print_builtin_va_start oc r =
      if not (!current_function_sig).sig_cc.cc_vararg then
        invalid_arg "Fatal error: va_start used in non-vararg function";
      let ofs =
        Int32.(add (add !current_function_stacksize 4l)
                 (mul 4l (Z.to_int32 (Conventions1.size_arguments
                                        !current_function_sig)))) in
      fprintf oc "	movl	%%esp, 0(%a)\n" ireg r;
      fprintf oc "	addl	$%ld, 0(%a)\n" ofs ireg r

(* Handling of compiler-inlined builtins *)

    let print_builtin_inline oc name args res =
      fprintf oc "%s begin builtin %s\n" comment name;
      begin match name, args, res with
        (* Integer arithmetic *)
      | ("__builtin_bswap"| "__builtin_bswap32"), [IR a1], [IR res] ->
          if a1 <> res then
            fprintf oc "	movl	%a, %a\n" ireg a1 ireg res;
          fprintf oc "	bswap	%a\n" ireg res
      | "__builtin_bswap16", [IR a1], [IR res] ->
          if a1 <> res then
            fprintf oc "	movl	%a, %a\n" ireg a1 ireg res;
          fprintf oc "	rolw	$8, %a\n" ireg16 res
      | "__builtin_clz", [IR a1], [IR res] ->
          fprintf oc "	bsrl	%a, %a\n" ireg a1 ireg res;
          fprintf oc "	xorl	$31, %a\n" ireg res
      | "__builtin_ctz", [IR a1], [IR res] ->
          fprintf oc "	bsfl	%a, %a\n" ireg a1 ireg res
            (* Float arithmetic *)
      | "__builtin_fabs", [FR a1], [FR res] ->
          need_masks := true;
          if a1 <> res then
            fprintf oc "	movapd	%a, %a\n" freg a1 freg res;
          fprintf oc "	andpd	%a, %a\n" raw_symbol "__absd_mask" freg res
      | "__builtin_fsqrt", [FR a1], [FR res] ->
          fprintf oc "	sqrtsd	%a, %a\n" freg a1 freg res
      | "__builtin_fmax", [FR a1; FR a2], [FR res] ->
          if res = a1 then
            fprintf oc "	maxsd	%a, %a\n" freg a2 freg res
          else if res = a2 then
            fprintf oc "	maxsd	%a, %a\n" freg a1 freg res
          else begin
            fprintf oc "	movapd	%a, %a\n" freg a1 freg res;
            fprintf oc "	maxsd	%a, %a\n" freg a2 freg res
          end
      | "__builtin_fmin", [FR a1; FR a2], [FR res] ->
          if res = a1 then
            fprintf oc "	minsd	%a, %a\n" freg a2 freg res
          else if res = a2 then
            fprintf oc "	minsd	%a, %a\n" freg a1 freg res
          else begin
            fprintf oc "	movapd	%a, %a\n" freg a1 freg res;
            fprintf oc "	minsd	%a, %a\n" freg a2 freg res
          end
      | ("__builtin_fmadd"|"__builtin_fmsub"|"__builtin_fnmadd"|"__builtin_fnmsub"),
            [FR a1; FR a2; FR a3], [FR res] ->
              let opcode =
                match name with
                | "__builtin_fmadd" -> "vfmadd"
                | "__builtin_fmsub" -> "vfmsub"
                | "__builtin_fnmadd" -> "vfnmadd"
                | "__builtin_fnmsub" -> "vfnmsub"
                | _ -> assert false in
              if res = a1 then
                fprintf oc "	%s132sd	%a, %a, %a\n" opcode freg a2 freg a3 freg res
              else if res = a2 then
                fprintf oc "	%s213sd	%a, %a, %a\n" opcode freg a3 freg a1 freg res
              else if res = a3 then
                fprintf oc "	%s231sd	%a, %a, %a\n" opcode freg a1 freg a2 freg res
              else begin
                fprintf oc "	movapd	%a, %a\n" freg a3 freg res;
                fprintf oc "	%s231sd	%a, %a, %a\n" opcode freg a1 freg a2 freg res
              end
                  (* 64-bit integer arithmetic *)
      | "__builtin_negl", [IR ah; IR al], [IR rh; IR rl] ->
          assert (ah = EDX && al = EAX && rh = EDX && rl = EAX);
          fprintf oc "	negl	%a\n" ireg EAX;
          fprintf oc "	adcl	$0, %a\n" ireg EDX;
          fprintf oc "	negl	%a\n" ireg EDX
      | "__builtin_addl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
          assert (ah = EDX && al = EAX && bh = ECX && bl = EBX && rh = EDX && rl = EAX);
          fprintf oc "	addl	%a, %a\n" ireg EBX ireg EAX;
          fprintf oc "	adcl	%a, %a\n" ireg ECX ireg EDX
      | "__builtin_subl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
          assert (ah = EDX && al = EAX && bh = ECX && bl = EBX && rh = EDX && rl = EAX);
          fprintf oc "	subl	%a, %a\n" ireg EBX ireg EAX;
          fprintf oc "	sbbl	%a, %a\n" ireg ECX ireg EDX
      | "__builtin_mull", [IR a; IR b], [IR rh; IR rl] ->
          assert (a = EAX && b = EDX && rh = EDX && rl = EAX);
          fprintf oc "	mull    %a\n" ireg EDX
            (* Memory accesses *)
      | "__builtin_read16_reversed", [IR a1], [IR res] ->
          fprintf oc "	movzwl	0(%a), %a\n" ireg a1 ireg res;
          fprintf oc "	rolw	$8, %a\n" ireg16 res
      | "__builtin_read32_reversed", [IR a1], [IR res] ->
          fprintf oc "	movl	0(%a), %a\n" ireg a1 ireg res;
          fprintf oc "	bswap	%a\n" ireg res
      | "__builtin_write16_reversed", [IR a1; IR a2], _ ->
          let tmp = if a1 = ECX then EDX else ECX in
          if a2 <> tmp then
            fprintf oc "	movl	%a, %a\n" ireg a2 ireg tmp;
          fprintf oc "	xchg	%a, %a\n" ireg8 tmp high_ireg8 tmp;
          fprintf oc "	movw	%a, 0(%a)\n" ireg16 tmp ireg a1
      | "__builtin_write32_reversed", [IR a1; IR a2], _ ->
          let tmp = if a1 = ECX then EDX else ECX in
          if a2 <> tmp then
            fprintf oc "	movl	%a, %a\n" ireg a2 ireg tmp;
          fprintf oc "	bswap	%a\n" ireg tmp;
          fprintf oc "	movl	%a, 0(%a)\n" ireg tmp ireg a1
            (* Synchronization *)
      | "__builtin_membar", [], _ ->
          ()
            (* Vararg stuff *)
      | "__builtin_va_start", [IR a], _ ->
          print_builtin_va_start oc a
            (* Catch-all *)  
      | _ ->
          invalid_arg ("unrecognized builtin " ^ name)
      end;
      fprintf oc "%s end builtin %s\n" comment name

(* Printing of instructions *)

(* Reminder on AT&T syntax: op source, dest *)

    let print_instruction oc = function
        (* Moves *)
      | Pmov_rr(rd, r1) ->
          fprintf oc "	movl	%a, %a\n" ireg r1 ireg rd
      | Pmov_ri(rd, n) ->
          fprintf oc "	movl	$%ld, %a\n" (camlint_of_coqint n) ireg rd
      | Pmov_ra(rd, id) ->
          print_mov_ra oc rd id
      | Pmov_rm(rd, a) | Pmov_rm_a(rd, a) ->
          fprintf oc "	movl	%a, %a\n" addressing a ireg rd
      | Pmov_mr(a, r1) | Pmov_mr_a(a, r1) ->
          fprintf oc "	movl	%a, %a\n" ireg r1 addressing a
      | Pmovsd_ff(rd, r1) ->
          fprintf oc "	movapd	%a, %a\n" freg r1 freg rd
      | Pmovsd_fi(rd, n) ->
          let b = camlint64_of_coqint (Floats.Float.to_bits n) in
          let lbl = new_label() in
          fprintf oc "	movsd	%a, %a %s %.18g\n" label lbl freg rd comment (camlfloat_of_coqfloat n);
          float64_literals := (lbl, b) :: !float64_literals
      | Pmovsd_fm(rd, a) | Pmovsd_fm_a(rd, a) ->
          fprintf oc "	movsd	%a, %a\n" addressing a freg rd
      | Pmovsd_mf(a, r1) | Pmovsd_mf_a(a, r1) ->
          fprintf oc "	movsd	%a, %a\n" freg r1 addressing a
      | Pmovss_fi(rd, n) ->
          let b = camlint_of_coqint (Floats.Float32.to_bits n) in
          let lbl = new_label() in
          fprintf oc "	movss	%a, %a %s %.18g\n" label lbl freg rd comment (camlfloat_of_coqfloat32 n);
          float32_literals := (lbl, b) :: !float32_literals
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
      | Pxchg_rr(r1, r2) ->
          fprintf oc "	xchgl	%a, %a\n" ireg r1 ireg r2
            (** Moves with conversion *)
      | Pmovb_mr(a, r1) ->
          fprintf oc "	movb	%a, %a\n" ireg8 r1 addressing a
      | Pmovw_mr(a, r1) ->
          fprintf oc "	movw	%a, %a\n" ireg16 r1 addressing a
      | Pmovzb_rr(rd, r1) ->
          fprintf oc "	movzbl	%a, %a\n" ireg8 r1 ireg rd
      | Pmovzb_rm(rd, a) ->
          fprintf oc "	movzbl	%a, %a\n" addressing a ireg rd
      | Pmovsb_rr(rd, r1) ->
          fprintf oc "	movsbl	%a, %a\n" ireg8 r1 ireg rd
      | Pmovsb_rm(rd, a) ->
          fprintf oc "	movsbl	%a, %a\n" addressing a ireg rd
      | Pmovzw_rr(rd, r1) ->
          fprintf oc "	movzwl	%a, %a\n" ireg16 r1 ireg rd
      | Pmovzw_rm(rd, a) ->
          fprintf oc "	movzwl	%a, %a\n" addressing a ireg rd
      | Pmovsw_rr(rd, r1) ->
          fprintf oc "	movswl	%a, %a\n" ireg16 r1 ireg rd
      | Pmovsw_rm(rd, a) ->
          fprintf oc "	movswl	%a, %a\n" addressing a ireg rd
      | Pcvtsd2ss_ff(rd, r1) ->
          fprintf oc "	cvtsd2ss %a, %a\n" freg r1 freg rd
      | Pcvtss2sd_ff(rd, r1) ->
          fprintf oc "	cvtss2sd %a, %a\n" freg r1 freg rd
      | Pcvttsd2si_rf(rd, r1) ->
          fprintf oc "	cvttsd2si %a, %a\n" freg r1 ireg rd
      | Pcvtsi2sd_fr(rd, r1) ->
          fprintf oc "	cvtsi2sd %a, %a\n" ireg r1 freg rd
      | Pcvttss2si_rf(rd, r1) ->
          fprintf oc "	cvttss2si %a, %a\n" freg r1 ireg rd
      | Pcvtsi2ss_fr(rd, r1) ->
          fprintf oc "	cvtsi2ss %a, %a\n" ireg r1 freg rd
            (** Arithmetic and logical operations over integers *)
      | Plea(rd, a) ->
          fprintf oc "	leal	%a, %a\n" addressing a ireg rd
      | Pneg(rd) ->
          fprintf oc "	negl	%a\n" ireg rd
      | Psub_rr(rd, r1) ->
          fprintf oc "	subl	%a, %a\n" ireg r1 ireg rd
      | Pimul_rr(rd, r1) ->
          fprintf oc "	imull	%a, %a\n" ireg r1 ireg rd
      | Pimul_ri(rd, n) ->
          fprintf oc "	imull	$%a, %a\n" coqint n ireg rd
      | Pimul_r(r1) ->
          fprintf oc "	imull	%a\n" ireg r1
      | Pmul_r(r1) ->
          fprintf oc "	mull	%a\n" ireg r1
      | Pdiv(r1) ->
          fprintf oc "	xorl	%%edx, %%edx\n";
          fprintf oc "	divl	%a\n" ireg r1
      | Pidiv(r1) ->
          fprintf oc "	cltd\n";
          fprintf oc "	idivl	%a\n" ireg r1
      | Pand_rr(rd, r1) ->
          fprintf oc "	andl	%a, %a\n" ireg r1 ireg rd
      | Pand_ri(rd, n) ->
          fprintf oc "	andl	$%a, %a\n" coqint n ireg rd
      | Por_rr(rd, r1) ->
          fprintf oc "	orl	%a, %a\n" ireg r1 ireg rd
      | Por_ri(rd, n) ->
          fprintf oc "	orl	$%a, %a\n" coqint n ireg rd
      | Pxor_r(rd) ->
          fprintf oc "	xorl	%a, %a\n" ireg rd ireg rd
      | Pxor_rr(rd, r1) ->
          fprintf oc "	xorl	%a, %a\n" ireg r1 ireg rd
      | Pxor_ri(rd, n) ->
          fprintf oc "	xorl	$%a, %a\n" coqint n ireg rd
      | Pnot(rd) ->
          fprintf oc "	notl	%a\n" ireg rd
      | Psal_rcl(rd) ->
          fprintf oc "	sall	%%cl, %a\n" ireg rd
      | Psal_ri(rd, n) ->
          fprintf oc "	sall	$%a, %a\n" coqint n ireg rd
      | Pshr_rcl(rd) ->
          fprintf oc "	shrl	%%cl, %a\n" ireg rd
      | Pshr_ri(rd, n) ->
          fprintf oc "	shrl	$%a, %a\n" coqint n ireg rd
      | Psar_rcl(rd) ->
          fprintf oc "	sarl	%%cl, %a\n" ireg rd
      | Psar_ri(rd, n) ->
          fprintf oc "	sarl	$%a, %a\n" coqint n ireg rd
      | Pshld_ri(rd, r1, n) ->
          fprintf oc "	shldl	$%a, %a, %a\n" coqint n ireg r1 ireg rd
      | Pror_ri(rd, n) ->
          fprintf oc "	rorl	$%a, %a\n" coqint n ireg rd
      | Pcmp_rr(r1, r2) ->
          fprintf oc "	cmpl	%a, %a\n" ireg r2 ireg r1
      | Pcmp_ri(r1, n) ->
          fprintf oc "	cmpl	$%a, %a\n" coqint n ireg r1
      | Ptest_rr(r1, r2) ->
          fprintf oc "	testl	%a, %a\n" ireg r2 ireg r1
      | Ptest_ri(r1, n) ->
          fprintf oc "	testl	$%a, %a\n" coqint n ireg r1
      | Pcmov(c, rd, r1) ->
          fprintf oc "	cmov%s	%a, %a\n" (name_of_condition c) ireg r1 ireg rd
      | Psetcc(c, rd) ->
          fprintf oc "	set%s	%a\n" (name_of_condition c) ireg8 rd;
          fprintf oc "	movzbl	%a, %a\n" ireg8 rd ireg rd
            (** Arithmetic operations over floats *)
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
          fprintf oc "	xorpd	%a, %a\n" raw_symbol "__negd_mask" freg rd
      | Pabsd (rd) ->
          need_masks := true;
          fprintf oc "	andpd	%a, %a\n" raw_symbol "__absd_mask" freg rd
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
          fprintf oc "	xorpd	%a, %a\n" raw_symbol "__negs_mask" freg rd
      | Pabss (rd) ->
          need_masks := true;
          fprintf oc "	andpd	%a, %a\n" raw_symbol "__abss_mask" freg rd
      | Pcomiss_ff(r1, r2) ->
          fprintf oc "	comiss	%a, %a\n" freg r2 freg r1
      | Pxorps_f (rd) ->
          fprintf oc "	xorpd	%a, %a\n" freg rd freg rd
            (** Branches and calls *)
      | Pjmp_l(l) ->
          fprintf oc "	jmp	%a\n" label (transl_label l)
      | Pjmp_s(f, sg) ->
          assert (not sg.sig_cc.cc_structret);
          fprintf oc "	jmp	%a\n" symbol f
      | Pjmp_r(r, sg) ->
          assert (not sg.sig_cc.cc_structret);
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
          fprintf oc "	jmp	*%a(, %a, 4)\n" label l ireg r;
          jumptables := (l, tbl) :: !jumptables
      | Pcall_s(f, sg) ->
          fprintf oc "	call	%a\n" symbol f;
          if sg.sig_cc.cc_structret then
            fprintf oc "	pushl	%%eax\n"
      | Pcall_r(r, sg) ->
          fprintf oc "	call	*%a\n" ireg r;
          if sg.sig_cc.cc_structret then
            fprintf oc "	pushl	%%eax\n"
      | Pret ->
          if (!current_function_sig).sig_cc.cc_structret then begin
            fprintf oc "	movl	0(%%esp), %%eax\n";
            fprintf oc "	ret	$4\n"
          end else begin
            fprintf oc "	ret\n"
          end
      (** Pseudo-instructions *)
      | Plabel(l) ->
          fprintf oc "%a:\n" label (transl_label l)
      | Pallocframe(sz, ofs_ra, ofs_link) ->
          let sz = sp_adjustment sz in
          let ofs_link = camlint_of_coqint ofs_link in
          fprintf oc "	subl	$%ld, %%esp\n" sz;
          cfi_adjust oc sz;
          fprintf oc "	leal	%ld(%%esp), %%edx\n" (Int32.add sz 4l);
          fprintf oc "	movl	%%edx, %ld(%%esp)\n" ofs_link;
          current_function_stacksize := sz
      | Pfreeframe(sz, ofs_ra, ofs_link) ->
          let sz = sp_adjustment sz in
          fprintf oc "	addl	$%ld, %%esp\n" sz
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
          | EF_inline_asm(txt, sg, clob) ->
              fprintf oc "%s begin inline assembly\n" comment;
              fprintf oc "\t";
              PrintAnnot.print_inline_asm preg oc (extern_atom txt) sg args res;
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
            
    let print_literal64 oc (lbl, n) =
      fprintf oc "%a:	.quad	0x%Lx\n" label lbl n
    let print_literal32 oc (lbl, n) =
      fprintf oc "%a:	.long	0x%lx\n" label lbl n
        
    let print_jumptable oc jmptbl = 
      let print_jumptable oc (lbl, tbl) =
        fprintf oc "%a:" label lbl;
        List.iter
          (fun l -> fprintf oc "	.long	%a\n" label (transl_label l))
          tbl in
      if !jumptables <> [] then begin
        section oc jmptbl;
        print_align oc 4;
        List.iter (print_jumptable oc) !jumptables;
        jumptables := []
      end
          
    let print_init oc = function
      | Init_int8 n ->
          fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
      | Init_int16 n ->
          fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
      | Init_int32 n ->
          fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
      | Init_int64 n ->
          fprintf oc "	.quad	%Ld\n" (camlint64_of_coqint n)
      | Init_float32 n ->
          fprintf oc "	.long	%ld %s %.18g\n"
	    (camlint_of_coqint (Floats.Float32.to_bits n))
	    comment (camlfloat_of_coqfloat n)
      | Init_float64 n ->
          fprintf oc "	.quad	%Ld %s %.18g\n"
	    (camlint64_of_coqint (Floats.Float.to_bits n))
	    comment (camlfloat_of_coqfloat n)
      | Init_space n ->
          if Z.gt n Z.zero then
            fprintf oc "	.space	%s\n" (Z.to_string n)
      | Init_addrof(symb, ofs) ->
          fprintf oc "	.long	%a\n" 
            symbol_offset (symb, camlint_of_coqint ofs)

    let print_align = print_align

    let print_comm_symb oc sz name align =
      if C2C.atom_is_static name
      then System.print_lcomm_decl oc name sz align
      else System.print_comm_decl oc name sz align

    let name_of_section = name_of_section

    let emit_constants oc lit =
       if !float64_literals <> [] || !float32_literals <> [] then begin
         section oc lit;
         print_align oc 8;
         List.iter (print_literal64 oc) !float64_literals;
         float64_literals := [];
         List.iter (print_literal32 oc) !float32_literals;
         float32_literals := []
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

    let reset_constants = reset_constants

    let print_fun_info = print_fun_info
        
    let print_var_info = print_var_info

    let print_prologue _ = 
      need_masks := false
    
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
      System.print_epilogue oc
      
    let comment = comment

    let default_falignment = 16

    let get_start_addr () = -1 (* Dummy constant *)
        
    let get_end_addr () = -1 (* Dummy constant *)

    let get_stmt_list_addr () = -1 (* Dummy constant *)

    module DwarfAbbrevs = DwarfUtil.DefaultAbbrevs (* Dummy Abbrev types *)

    let label = label
       
    let new_label = new_label
        
    let print_file_loc _ _ = () (* Dummy function *)

end

let sel_target () =
 let module S = (val (match Configuration.system with
  | "macosx" -> (module MacOS_System:SYSTEM)
  | "linux" 
  | "bsd" -> (module ELF_System:SYSTEM)
  | "cygwin" -> (module Cygwin_System:SYSTEM)
  | _ -> invalid_arg ("System " ^ Configuration.system ^ " not supported")  ):SYSTEM) in
 (module Target(S):TARGET)

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
open Datatypes
open Camlcoq
open Sections
open AST
open Asm

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

(* Record identifiers of external functions that need stub code *)

module IdentSet = Set.Make(struct type t = ident let compare = compare end)

let extfuns = (ref IdentSet.empty)

let need_stub ef = List.mem Tfloat ef.ef_sig.sig_args

let record_extfun (Coq_pair(name, defn)) =
  match defn with
  | Internal f -> ()
  | External ef -> if need_stub ef then extfuns := IdentSet.add name !extfuns

(* Basic printing functions *)

let strip_variadic_suffix name =
  try String.sub name 0 (String.index name '$')
  with Not_found -> name

let print_symb oc symb =
  if IdentSet.mem symb !extfuns
  then fprintf oc ".L%s$stub" (extern_atom symb)
  else fprintf oc "%s" (strip_variadic_suffix (extern_atom symb))

let print_label oc lbl =
  fprintf oc ".L%d" (label_for_label lbl)

let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

let comment = "@"

let print_symb_ofs oc (symb, ofs) =
  print_symb oc symb;
  let ofs = camlint_of_coqint ofs in
  if ofs <> 0l then fprintf oc " + %ld" ofs

let int_reg_name = function
  | IR0 -> "r0" | IR1 -> "r1" | IR2 -> "r2" | IR3 -> "r3"
  | IR4 -> "r4" | IR5 -> "r5" | IR6 -> "r6" | IR7 -> "r7"
  | IR8 -> "r8" | IR9 -> "r9" | IR10 -> "r10" | IR11 -> "r11"
  | IR12 -> "r12" | IR13 -> "sp" | IR14 -> "lr"

let float_reg_name = function
  | FR0 -> "f0"  | FR1 -> "f1"  | FR2 -> "f2"  | FR3 -> "f3"
  | FR4 -> "f4"  | FR5 -> "f5"  | FR6 -> "f6"  | FR7 -> "f7"

let ireg oc r = output_string oc (int_reg_name r)
let freg oc r = output_string oc (float_reg_name r)

let preg oc = function
  | IR r -> ireg oc r
  | FR r -> freg oc r
  | _    -> assert false

let condition_name = function
  | CReq -> "eq"
  | CRne -> "ne"
  | CRhs -> "hs"
  | CRlo -> "lo"
  | CRmi -> "mi"
  | CRpl -> "pl"
  | CRhi -> "hi"
  | CRls -> "ls"
  | CRge -> "ge"
  | CRlt -> "lt"
  | CRgt -> "gt"
  | CRle -> "le"

(* Names of sections *)

let name_of_section_ELF = function
  | Section_text -> ".text"
  | Section_data i | Section_small_data i -> if i then ".data" else ".bss"
  | Section_const | Section_small_const -> ".section	.rodata"
  | Section_string -> ".section	.rodata"
  | Section_literal -> ".text"
  | Section_jumptable -> ".text"
  | Section_user(s, wr, ex) ->
       sprintf ".section	%s,\"a%s%s\",%%progbits"
               s (if wr then "w" else "") (if ex then "x" else "")

let section oc sec =
  fprintf oc "	%s\n" (name_of_section_ELF sec)

(* Record current code position and latest position at which to
   emit float and symbol constants. *)

let currpos = ref 0
let size_constants = ref 0
let max_pos_constants = ref max_int

let distance_to_emit_constants () =
  !max_pos_constants - (!currpos + !size_constants)

(* Associate labels to floating-point constants and to symbols *)

let float_labels = (Hashtbl.create 39 : (int64, int) Hashtbl.t)

let label_float f =
  let bf = Int64.bits_of_float f in
  try
    Hashtbl.find float_labels bf
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add float_labels bf lbl';
    size_constants := !size_constants + 8;
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
  Hashtbl.clear symbol_labels;
  size_constants := 0;
  max_pos_constants := max_int

let emit_constants oc =
  Hashtbl.iter
    (fun bf lbl ->
      (* Floats are mixed-endian on this flavor of ARM *)
      let bfhi = Int64.shift_right_logical bf 32
      and bflo = Int64.logand bf 0xFFFF_FFFFL in
      fprintf oc ".L%d:	.word	0x%Lx, 0x%Lx\n"
          lbl bfhi bflo)
    float_labels;
  Hashtbl.iter
    (fun (id, ofs) lbl ->
      fprintf oc ".L%d:	.word	%a\n"
          lbl print_symb_ofs (id, ofs))
    symbol_labels;
  reset_constants ()

(* Simulate instructions by calling helper functions *)

let print_list_ireg oc l =
  match l with
  | [] -> assert false
  | r1 :: rs -> ireg oc r1; List.iter (fun r -> fprintf oc ", %a" ireg r) rs

let rec remove l r =
  match l with
  | [] -> []
  | hd :: tl -> if hd = r then remove tl r else hd :: remove tl r

let call_helper oc fn dst arg1 arg2 =
  (* Preserve caller-save registers r0...r3 except dst *)
  let tosave = remove [IR0; IR1; IR2; IR3] dst in
  fprintf oc "	stmfd	sp!, {%a}\n" print_list_ireg tosave;
  (* Copy arg1 to R0 and arg2 to R1 *)
  let moves =
    Parmov.parmove2 (=) (fun _ -> IR14) [arg1; arg2] [IR0; IR1] in
  List.iter
    (fun (Coq_pair(s, d)) ->
      fprintf oc "	mov	%a, %a\n" ireg d ireg s)
    moves;
  (* Call the helper function *)
  fprintf oc "	bl	%s\n" fn;
  (* Move result to dst *)
  begin match dst with
  | IR0 -> ()
  | _   -> fprintf oc "	mov	%a, r0\n" ireg dst
  end;
  (* Restore the other caller-save registers *)
  fprintf oc "	ldmfd	sp!, {%a}\n" print_list_ireg tosave;
  (* ... for a total of at most 7 instructions *)
  7

(* Built-ins.  They come in two flavors: 
   - inlined by the compiler: take their arguments in arbitrary
     registers; preserve all registers except IR14
   - inlined while printing asm code; take their arguments in
     locations dictated by the calling conventions; preserve
     callee-save regs only. *)

(* Handling of __builtin_annotation *)

let re_builtin_annotation = Str.regexp "__builtin_annotation_\"\\(.*\\)\"$"

let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"

let print_annotation oc txt args res =
  fprintf oc "%s annotation: " comment;
  let print_fragment = function
  | Str.Text s ->
      output_string oc s
  | Str.Delim "%%" ->
      output_char oc '%'
  | Str.Delim s ->
      let n = int_of_string (String.sub s 1 (String.length s - 1)) in
      try
        preg oc (List.nth args (n-1))
      with Failure _ ->
        fprintf oc "<bad parameter %s>" s in
  List.iter print_fragment (Str.full_split re_annot_param txt);
  fprintf oc "\n";
  begin match args, res with
  | [], _ -> 0
  | IR src :: _, IR dst ->
      if dst = src then 0 else (fprintf oc "	mr	%a, %a\n" ireg dst ireg src; 1)
  | FR src :: _, FR dst ->
      if dst = src then 0 else (fprintf oc "	fmr	%a, %a\n" freg dst freg src; 1)
  | _, _ -> assert false
  end

(* Handling of __builtin_memcpy_alX_szY *)

let re_builtin_memcpy =
   Str.regexp "__builtin_memcpy\\(_al\\([248]\\)\\)?_sz\\([0-9]+\\)$"

(* The ARM has strict alignment constraints. *)

let print_builtin_memcpy oc sz al dst src =
  let rec copy ofs sz ninstr =
    if sz >= 4 && al >= 4 then begin
      fprintf oc "	ldr	%a, [%a, #%d]\n" ireg IR14 ireg src ofs;
      fprintf oc "	str	%a, [%a, #%d]\n" ireg IR14 ireg dst ofs;
      copy (ofs + 4) (sz - 4) (ninstr + 2)
    end else if sz >= 2 && al >= 2 then begin
      fprintf oc "	ldrh	%a, [%a, #%d]\n" ireg IR14 ireg src ofs;
      fprintf oc "	strh	%a, [%a, #%d]\n" ireg IR14 ireg dst ofs;
      copy (ofs + 2) (sz - 2) (ninstr + 2)
    end else if sz >= 1 then begin
      fprintf oc "	ldrb	%a, [%a, #%d]\n" ireg IR14 ireg src ofs;
      fprintf oc "	strb	%a, [%a, #%d]\n" ireg IR14 ireg dst ofs;
      copy (ofs + 1) (sz - 1) (ninstr + 2)
    end else
      ninstr in
  copy 0 sz 0

(* Handling of compiler-inlined builtins *)

let print_builtin_inlined oc name args res =
  fprintf oc "%s begin %s\n" comment name;
  let n = match name, args, res with
  (* Volatile reads *)
  | "__builtin_volatile_read_int8unsigned", [IR addr], IR res ->
      fprintf oc "	ldrb	%a, [%a, #0]\n" ireg res ireg addr; 1
  | "__builtin_volatile_read_int8signed", [IR addr], IR res ->
      fprintf oc "	ldrsb	%a, [%a, #0]\n" ireg res ireg addr; 1
  | "__builtin_volatile_read_int16unsigned", [IR addr], IR res ->
      fprintf oc "	ldrh	%a, [%a, #0]\n" ireg res ireg addr; 1
  | "__builtin_volatile_read_int16signed", [IR addr], IR res ->
      fprintf oc "	ldrsh	%a, [%a, #0]\n" ireg res ireg addr; 1
  | ("__builtin_volatile_read_int32"|"__builtin_volatile_read_pointer"), [IR addr], IR res ->
      fprintf oc "	ldr	%a, [%a, #0]\n" ireg res ireg addr; 1
  | "__builtin_volatile_read_float32", [IR addr], FR res ->
      fprintf oc "	ldfs	%a, [%a, #0]\n" freg res ireg addr;
      fprintf oc "	mvfd	%a, %a\n" freg res freg res; 2
  | "__builtin_volatile_read_float64", [IR addr], FR res ->
      fprintf oc "	ldfd	%a, [%a, #0]\n" freg res ireg addr; 1
  (* Volatile writes *)
  | ("__builtin_volatile_write_int8unsigned"|"__builtin_volatile_write_int8signed"), [IR addr; IR src], _ ->
      fprintf oc "	strb	%a, [%a, #0]\n" ireg src ireg addr; 1
  | ("__builtin_volatile_write_int16unsigned"|"__builtin_volatile_write_int16signed"), [IR addr; IR src], _ ->
      fprintf oc "	strh	%a, [%a, #0]\n" ireg src ireg addr; 1
  | ("__builtin_volatile_write_int32"|"__builtin_volatile_write_pointer"), [IR addr; IR src], _ ->
      fprintf oc "	str	%a, [%a, #0]\n" ireg src ireg addr; 1
  | "__builtin_volatile_write_float32", [IR addr; FR src], _ ->
      fprintf oc "	mvfs	%a, %a\n" freg FR2 freg src;
      fprintf oc "	stfs	%a, [%a, #0]\n" freg FR2 ireg addr; 2
  | "__builtin_volatile_write_float64", [IR addr; FR src], _ ->
      fprintf oc "	stfd	%a, [%a, #0]\n" freg src ireg addr; 1
  (* Float arithmetic *)
  | "__builtin_fabs", [FR a1], FR res ->
      fprintf oc "	absd	%a, %a\n" freg res freg a1; 1
  (* Inlined memcpy *)
  | name, [IR dst; IR src], _ when Str.string_match re_builtin_memcpy name 0 ->
      let sz = int_of_string (Str.matched_group 3 name) in
      let al = try int_of_string (Str.matched_group 2 name) with Not_found -> 1 in
      print_builtin_memcpy oc sz al dst src
  (* Catch-all *)
  | _ ->
      invalid_arg ("unrecognized builtin " ^ name)
  in
  fprintf oc "%s end %s\n" comment name;
  n

(* Handling of other builtins *)

let re_builtin_function = Str.regexp "__builtin_"

let is_builtin_function s =
  Str.string_match re_builtin_function (extern_atom s) 0

let print_memcpy oc load store sz log2sz =
  let lbl1 = new_label() in
  let lbl2 = new_label() in
  if sz = 1
  then fprintf oc "	cmp	%a, #0\n" ireg IR2
  else fprintf oc "	movs	%a, %a, lsr #%d\n" ireg IR2 ireg IR2 log2sz;
  fprintf oc "	beq	.L%d\n" lbl1;
  fprintf oc ".L%d:	%s	%a, [%a], #%d\n" lbl2 load ireg IR3 ireg IR1 sz;
  fprintf oc "	subs	%a, %a, #1\n" ireg IR2 ireg IR2;
  fprintf oc "	%s	%a, [%a], #%d\n" store ireg IR3 ireg IR0 sz;
  fprintf oc "	bne	.L%d\n" lbl2;
  fprintf oc ".L%d:\n" lbl1;
  7

let print_builtin_function oc s =
  fprintf oc "%s begin %s\n" comment (extern_atom s);
  (* int args: IR0-IR3     float args: FR0, FR1
     int res:  IR0        float res:  FR0 *)
  let n = match extern_atom s with
  (* Block copy *)
  | "__builtin_memcpy" ->
      print_memcpy oc "ldrb" "strb" 1 0
  | "__builtin_memcpy_al2" ->
      print_memcpy oc "ldrh" "strh" 2 1
  | "__builtin_memcpy_al4" | "__builtin_memcpy_al8" ->
      print_memcpy oc "ldr" "str" 4 2
  (* Catch-all *)
  | s ->
      invalid_arg ("unrecognized builtin function " ^ s)
  in
  fprintf oc "%s end %s\n" comment (extern_atom s);
  n

(* Printing of instructions *)

let shift_op oc = function
  | SOimm n -> fprintf oc "#%a" coqint n
  | SOreg r -> ireg oc r
  | SOlslimm(r, n) -> fprintf oc "%a, lsl #%a" ireg r coqint n
  | SOlslreg(r, r') -> fprintf oc "%a, lsl %a" ireg r ireg r'
  | SOlsrimm(r, n) -> fprintf oc "%a, lsr #%a" ireg r coqint n
  | SOlsrreg(r, r') -> fprintf oc "%a, lsr %a" ireg r ireg r'
  | SOasrimm(r, n) -> fprintf oc "%a, asr #%a" ireg r coqint n
  | SOasrreg(r, r') -> fprintf oc "%a, asr %a" ireg r ireg r'
  | SOrorimm(r, n) -> fprintf oc "%a, ror #%a" ireg r coqint n
  | SOrorreg(r, r') -> fprintf oc "%a, ror %a" ireg r ireg r'

let shift_addr oc = function
  | SAimm n -> fprintf oc "#%a" coqint n
  | SAreg r -> ireg oc r
  | SAlsl(r, n) -> fprintf oc "%a, lsl #%a" ireg r coqint n
  | SAlsr(r, n) -> fprintf oc "%a, lsr #%a" ireg r coqint n
  | SAasr(r, n) -> fprintf oc "%a, asr #%a" ireg r coqint n
  | SAror(r, n) -> fprintf oc "%a, ror #%a" ireg r coqint n

let print_instruction oc = function
  (* Core instructions *)
  | Padd(r1, r2, so) ->
      fprintf oc "	add	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pand(r1, r2, so) ->
      fprintf oc "	and	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pb lbl ->
      fprintf oc "	b	%a\n" print_label lbl; 1
  | Pbc(bit, lbl) ->
      fprintf oc "	b%s	%a\n" (condition_name bit) print_label lbl; 1
  | Pbsymb id ->
      if not (is_builtin_function id) then begin
        fprintf oc "	b	%a\n" print_symb id; 1
      end else begin
        let n = print_builtin_function oc id in
        fprintf oc "	mov	pc, r14\n";
        n + 1
      end
  | Pbreg r ->
      fprintf oc "	mov	pc, %a\n" ireg r; 1
  | Pblsymb id ->
      if not (is_builtin_function id) then begin
        fprintf oc "	bl	%a\n" print_symb id; 1
      end else begin
        print_builtin_function oc id
      end
  | Pblreg r ->
      fprintf oc "	mov	lr, pc\n";
      fprintf oc "	mov	pc, %a\n" ireg r; 2
  | Pbic(r1, r2, so) ->
      fprintf oc "	bic	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pcmp(r1, so) ->
      fprintf oc "	cmp	%a, %a\n" ireg r1 shift_op so; 1
  | Peor(r1, r2, so) ->
      fprintf oc "	eor	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pldr(r1, r2, sa) ->
      fprintf oc "	ldr	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pldrb(r1, r2, sa) ->
      fprintf oc "	ldrb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pldrh(r1, r2, sa) ->
      fprintf oc "	ldrh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pldrsb(r1, r2, sa) ->
      fprintf oc "	ldrsb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pldrsh(r1, r2, sa) ->
      fprintf oc "	ldrsh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pmov(r1, so) ->
      fprintf oc "	mov	%a, %a\n" ireg r1 shift_op so; 1
  | Pmovc(bit, r1, so) ->
      fprintf oc "	mov%s	%a, %a\n" (condition_name bit) ireg r1 shift_op so; 1
  | Pmul(r1, r2, r3) ->
      fprintf oc "	mul	%a, %a, %a\n" ireg r1 ireg r2 ireg r3; 1
  | Pmvn(r1, so) ->
      fprintf oc "	mvn	%a, %a\n" ireg r1 shift_op so; 1
  | Porr(r1, r2, so) ->
      fprintf oc "	orr	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Prsb(r1, r2, so) ->
      fprintf oc "	rsb	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pstr(r1, r2, sa) ->
      fprintf oc "	str	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pstrb(r1, r2, sa) ->
      fprintf oc "	strb	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Pstrh(r1, r2, sa) ->
      fprintf oc "	strh	%a, [%a, %a]\n" ireg r1 ireg r2 shift_addr sa; 1
  | Psdiv(r1, r2, r3) ->
      call_helper oc "__divsi3" r1 r2 r3
  | Psub(r1, r2, so) ->
      fprintf oc "	sub	%a, %a, %a\n" ireg r1 ireg r2 shift_op so; 1
  | Pudiv(r1, r2, r3) ->
      call_helper oc "__udivsi3" r1 r2 r3
  (* Floating-point coprocessor instructions *)
  | Pabsd(r1, r2) ->
      fprintf oc "	absd	%a, %a\n" freg r1 freg r2; 1
  | Padfd(r1, r2, r3) ->
      fprintf oc "	adfd	%a, %a, %a\n" freg r1 freg r2 freg r3; 1
  | Pcmf(r1, r2) ->
      fprintf oc "	cmf	%a, %a\n" freg r1 freg r2; 1
  | Pdvfd(r1, r2, r3) ->
      fprintf oc "	dvfd	%a, %a, %a\n" freg r1 freg r2 freg r3; 1
  | Pfixz(r1, r2) ->
      fprintf oc "	fixz	%a, %a\n" ireg r1 freg r2; 1
  | Pfltd(r1, r2) ->
      fprintf oc "	fltd	%a, %a\n" freg r1 ireg r2; 1
  | Pldfd(r1, r2, n) ->
      fprintf oc "	ldfd	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n; 1
  | Pldfs(r1, r2, n) ->
      fprintf oc "	ldfs	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n;
      fprintf oc "	mvfd	%a, %a\n" freg r1 freg r1; 2
  | Plifd(r1, f) ->
      if Int64.bits_of_float f = 0L (* +0.0 *) then begin
        fprintf oc "	mvfd	%a, #0.0\n" freg r1; 1
      end else begin
        let lbl = label_float f in
        fprintf oc "	ldfd	%a, .L%d @ %.12g\n" freg r1 lbl f; 1
      end
  | Pmnfd(r1, r2) ->
      fprintf oc "	mnfd	%a, %a\n" freg r1 freg r2; 1
  | Pmvfd(r1, r2) ->
      fprintf oc "	mvfd	%a, %a\n" freg r1 freg r2; 1
  | Pmvfs(r1, r2) ->
      fprintf oc "	mvfs	%a, %a\n" freg r1 freg r2;
      fprintf oc "	mvfd	%a, %a\n" freg r2 freg r2; 2
  | Pmufd(r1, r2, r3) ->
      fprintf oc "	mufd	%a, %a, %a\n" freg r1 freg r2 freg r3; 1
  | Pstfd(r1, r2, n) ->
      fprintf oc "	stfd	%a, [%a, #%a]\n" freg r1 ireg r2 coqint n; 1
  | Pstfs(r1, r2, n) ->
      fprintf oc "	mvfs	f3, %a\n" freg r1;
      fprintf oc "	stfs	f3, [%a, #%a]\n" ireg r2 coqint n; 2
  | Psufd(r1, r2, r3) ->
      fprintf oc "	sufd	%a, %a, %a\n" freg r1 freg r2 freg r3; 1
  (* Pseudo-instructions *)
  | Pallocframe(sz, ofs) ->
      fprintf oc "	mov	r12, sp\n";
      let ninstr = ref 0 in
      List.iter
        (fun n ->
           fprintf oc "	sub	sp, sp, #%a\n" coqint n;
           incr ninstr)
        (Asmgen.decompose_int sz);
      fprintf oc "	str	r12, [sp, #%a]\n" coqint ofs;
      2 + !ninstr
  | Pfreeframe(sz, ofs) ->
      if Asmgen.is_immed_arith sz
      then fprintf oc "	add	sp, sp, #%a\n" coqint sz
      else fprintf oc "	ldr	sp, [sp, #%a]\n" coqint ofs;
      1
  | Plabel lbl ->
      fprintf oc "%a:\n" print_label lbl; 0
  | Ploadsymbol(r1, id, ofs) ->
      let lbl = label_symbol id ofs in
      fprintf oc "	ldr	%a, .L%d @ %a\n" 
         ireg r1 lbl print_symb_ofs (id, ofs); 1
  | Pbtbl(r, tbl) ->
      fprintf oc "	ldr	pc, [pc, %a]\n" ireg r;
      fprintf oc "	mov	r0, r0\n"; (* no-op *)
      List.iter
        (fun l -> fprintf oc "	.word	%a\n" print_label l)
        tbl;
      2 + List.length tbl
  | Pbuiltin(ef, args, res) ->
      let name = extern_atom ef.ef_id in
      if Str.string_match re_builtin_annotation name 0
      then print_annotation oc (Str.matched_group 1 name) args res
      else print_builtin_inlined oc name args res

let no_fallthrough = function
  | Pb _ -> true
  | Pbsymb _ -> true
  | Pbreg _ -> true
  | _ -> false

let rec print_instructions oc instrs =
  match instrs with
  | [] -> ()
  | i :: il ->
      let n = print_instruction oc i in
      currpos := !currpos + n * 4;
      let d = distance_to_emit_constants() in
      if d < 256 && no_fallthrough i then
        emit_constants oc
      else if d < 16 then begin
        let lbl = new_label() in
        fprintf oc "	b	.L%d\n" lbl;
        emit_constants oc;
        fprintf oc ".L%d:\n" lbl
      end;
      print_instructions oc il

let print_function oc name code =
  Hashtbl.clear current_function_labels;
  reset_constants();
  currpos := 0;
  let (text, _, _) = sections_for_function name in
  section oc text;
  fprintf oc "	.align 2\n";
  if not (C2C.atom_is_static name) then
    fprintf oc "	.global	%a\n" print_symb name;
  fprintf oc "%a:\n" print_symb name;
  print_instructions oc code;
  emit_constants oc;
  fprintf oc "	.type	%a, %%function\n" print_symb name;
  fprintf oc "	.size	%a, . - %a\n" print_symb name print_symb name

(* Generation of stub code for external functions that take floats.
   Compcert passes the first two float arguments in F0 and F1,
   while gcc passes them in pairs of integer registers. *)

let print_external_function oc name sg =
  let name = extern_atom name in
  let rec move_args ty_args int_regs float_regs =
    match ty_args with
    | [] -> ()
    | Tint :: tys ->
        begin match int_regs with
        | [] -> move_args tys [] float_regs
        | ir :: irs -> move_args tys irs float_regs
        end
    | Tfloat :: tys ->
        begin match float_regs, int_regs with
        | fr :: frs, ir1 :: ir2 :: irs ->
            (* transfer fr to the pair (ir1, ir2) *)
            fprintf oc "	stfd	%a, [sp, #-8]!\n" freg fr;
            fprintf oc "	ldmfd	sp!, {%a, %a}\n" ireg ir1 ireg ir2;
            move_args tys irs frs
        | fr :: frs, ir1 :: [] ->
            (* transfer fr to ir1 and the bottom stack word *)
            fprintf oc "	stfd	%a, [sp, #-4]!\n" freg fr;
            fprintf oc "	ldmfd	sp!, {%a}\n" ireg ir1;
            move_args tys [] frs
        | _, _ ->
            (* no more float regs, or no more int regs:
               float arg is already on stack, where it should be *)
            move_args tys int_regs float_regs
        end
  in
  section oc Section_text;
  fprintf oc "	.align 2\n";
  fprintf oc ".L%s$stub:\n" name;
  move_args sg.sig_args [IR0;IR1;IR2;IR3] [FR0;FR1];
  (* Remove variadic prefix $iiff if any *)
  let real_name = strip_variadic_suffix name in
  fprintf oc "	b	%s\n" real_name

let print_fundef oc (Coq_pair(name, defn)) =
  match defn with
  | Internal code ->
      print_function oc name code
  | External ef ->
      if need_stub ef && not(is_builtin_function name)
      then print_external_function oc name ef.ef_sig

(* Data *)

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.word	%ld\n" (camlint_of_coqint n)
  | Init_float32 n ->
      fprintf oc "	.word	0x%lx @ %.15g \n" (Int32.bits_of_float n) n
  | Init_float64 n ->
      (* Floats are mixed-endian on this flavor of ARM *)
      let bf = Int64.bits_of_float n in
      let bfhi = Int64.shift_right_logical bf 32
      and bflo = Int64.logand bf 0xFFFF_FFFFL in
      fprintf oc "	.word	0x%Lx, 0x%Lx @ %.15g\n" bfhi bflo n
  | Init_space n ->
      let n = camlint_of_z n in
      if n > 0l then fprintf oc "	.space	%ld\n" n
  | Init_addrof(symb, ofs) ->
      fprintf oc "	.word	%a\n" print_symb_ofs (symb, ofs)

let print_init_data oc name id =
  if Str.string_match PrintCsyntax.re_string_literal (extern_atom name) 0
  && List.for_all (function Init_int8 _ -> true | _ -> false) id
  then
    fprintf oc "	.ascii	\"%s\"\n" (PrintCsyntax.string_of_init id)
  else
    List.iter (print_init oc) id

(* Base-2 log of a Caml integer *)

let rec log2 n =
  assert (n > 0);
  if n = 1 then 0 else 1 + log2 (n lsr 1)

let print_var oc (Coq_pair(name, v)) =
  match v.gvar_init with
  | [] -> ()
  | _  ->
      let init =
        match v.gvar_init with [Init_space _] -> false | _ -> true in
      let sec =
        Sections.section_for_variable name init
      and align =
        match C2C.atom_alignof name with
        | Some a -> log2 a
        | None -> 3 (* 8-alignment is a safe default *)
      in
      section oc sec;
      fprintf oc "	.align	%d\n" align;
      if not (C2C.atom_is_static name) then
        fprintf oc "	.global	%a\n" print_symb name;
      fprintf oc "%a:\n" print_symb name;
      print_init_data oc name v.gvar_init;
      fprintf oc "	.type	%a, %%object\n" print_symb name;
      fprintf oc "	.size	%a, . - %a\n" print_symb name print_symb name

let print_program oc p =
  extfuns := IdentSet.empty;
  List.iter record_extfun p.prog_funct;
  List.iter (print_var oc) p.prog_vars;
  List.iter (print_fundef oc) p.prog_funct


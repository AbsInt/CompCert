(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
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

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the RISC-V assembly code. *)

open Asm
open Asmexpandaux
open AST
open Camlcoq
open! Integers
open Locations

exception Error of string

(* Useful constants and helper functions *)

let _0  = Integers.Int.zero
let _1  = Integers.Int.one
let _2  = coqint_of_camlint 2l
let _4  = coqint_of_camlint 4l
let _8  = coqint_of_camlint 8l
let _16  = coqint_of_camlint 16l
let _m1 = coqint_of_camlint (-1l)

let wordsize = if Archi.ptr64 then 8 else 4

let align n a = (n + a - 1) land (-a)

(* Emit instruction sequences that set or offset a register by a constant. *)

let expand_loadimm32 dst n =
  List.iter emit (Asmgen.loadimm32 dst n [])
let expand_addptrofs dst src n =
  List.iter emit (Asmgen.addptrofs dst src n [])
let expand_storeind_ptr src base ofs =
  List.iter emit (Asmgen.storeind_ptr src base ofs [])

(* Fix-up code around function calls and function entry.
   Some floating-point arguments residing in FP registers need to be
   moved to integer registers or register pairs.
   Symmetrically, some floating-point parameter passed in integer
   registers or register pairs need to be moved to FP registers. *)

let int_param_regs = [| X10; X11; X12; X13; X14; X15; X16; X17 |]

let move_single_arg fr i =
  emit (Pfmvxs(int_param_regs.(i), fr))

let move_double_arg fr i =
  if Archi.ptr64 then begin
    emit (Pfmvxd(int_param_regs.(i), fr))
  end else begin
    emit (Paddiw(X2, X X2, Integers.Int.neg _16));
    emit (Pfsd(fr, X2, Ofsimm _0));
    emit (Plw(int_param_regs.(i), X2, Ofsimm _0));
    if i < 7 then begin
      emit (Plw(int_param_regs.(i + 1), X2, Ofsimm _4))
    end else begin
      emit (Plw(X31, X2, Ofsimm _4));
      emit (Psw(X31, X2, Ofsimm _16))
    end;
    emit (Paddiw(X2, X X2, _16))
  end

let move_single_param fr i =
  emit (Pfmvsx(fr, int_param_regs.(i)))

let move_double_param fr i =
  if Archi.ptr64 then begin
    emit (Pfmvdx(fr, int_param_regs.(i)))
  end else begin
    emit (Paddiw(X2, X X2, Integers.Int.neg _16));
    emit (Psw(int_param_regs.(i), X2, Ofsimm _0));
    if i < 7 then begin
      emit (Psw(int_param_regs.(i + 1), X2, Ofsimm _4))
    end else begin
      emit (Plw(X31, X2, Ofsimm _16));
      emit (Psw(X31, X2, Ofsimm _4))
    end;
    emit (Pfld(fr, X2, Ofsimm _0));
    emit (Paddiw(X2, X X2, _16))
  end

let float_extra_index = function
  | Machregs.F0 -> Some (F0, 0)
  | Machregs.F1 -> Some (F1, 1)
  | Machregs.F2 -> Some (F2, 2)
  | Machregs.F3 -> Some (F3, 3)
  | Machregs.F4 -> Some (F4, 4)
  | Machregs.F5 -> Some (F5, 5)
  | Machregs.F6 -> Some (F6, 6)
  | Machregs.F7 -> Some (F7, 7)
  | _  -> None

let fixup_gen single double sg =
  let fixup ty loc =
    match ty, loc with
    | Tsingle, One (R r) ->
        begin match float_extra_index r with
        | Some(r, i) -> single r i
        | None -> ()
        end
    | (Tfloat | Tany64), One (R r) ->
        begin match float_extra_index r with
        | Some(r, i) -> double r i
        | None -> ()
        end
    | _, _ -> ()
  in
    List.iter2 fixup sg.sig_args (Conventions1.loc_arguments sg)

let fixup_call sg =
  fixup_gen move_single_arg move_double_arg sg

let fixup_function_entry sg =
  fixup_gen move_single_param move_double_param sg

(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers.
*)

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmv (dst, src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pfmv (dst, src))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_val")

(* Handling of memcpy *)

(* Unaligned accesses are slow on RISC-V, so don't use them *)

let offset_in_range ofs =
  let ofs = Z.to_int64 ofs in -2048L <= ofs && ofs < 2048L
  
let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (IR r) ->
      (r, _0)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Ptrofs.add ofs (Ptrofs.repr (Z.of_uint sz)))
      then (X2, ofs)
      else begin expand_addptrofs tmp X2 ofs; (tmp, _0) end
  | _ ->
      assert false

let expand_builtin_memcpy_small sz al src dst =
  let tsrc = if dst <> BA (IR X5) then X5 else X6 in
  let tdst = if src <> BA (IR X6) then X6 else X5 in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  let rec copy osrc odst sz =
    if sz >= 8 && al >= 8 then
      begin
        emit (Pfld (F0, rsrc, Ofsimm osrc));
        emit (Pfsd (F0, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _8) (Ptrofs.add odst _8) (sz - 8)
      end
    else if sz >= 4 && al >= 4 then
      begin
        emit (Plw (X31, rsrc, Ofsimm osrc));
        emit (Psw (X31, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _4) (Ptrofs.add odst _4) (sz - 4)
      end
    else if sz >= 2 && al >= 2 then
      begin
        emit (Plh (X31, rsrc, Ofsimm osrc));
        emit (Psh (X31, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _2) (Ptrofs.add odst _2) (sz - 2)
      end
    else if sz >= 1 then
      begin
        emit (Plb (X31, rsrc, Ofsimm osrc));
        emit (Psb (X31, rdst, Ofsimm odst));
        copy (Ptrofs.add osrc _1) (Ptrofs.add odst _1) (sz - 1)
      end
  in copy osrc odst sz

let memcpy_big_arg sz arg tmp =
  match arg with
  | BA (IR r) -> if r <> tmp then emit (Pmv(tmp, r))
  | BA_addrstack ofs ->
      expand_addptrofs tmp X2 ofs
  | _ ->
      assert false

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= al);
  assert (sz mod al = 0);
  let (s, d) =
    if dst <> BA (IR X5) then (X5, X6) else (X6, X5) in
  memcpy_big_arg sz src s;
  memcpy_big_arg sz dst d;
  (* Use X7 as loop count, X1 and F0 as ld/st temporaries. *)
  let (load, store, chunksize) =
    if al >= 8 then
      (Pfld (F0, s, Ofsimm _0), Pfsd (F0, d, Ofsimm _0), 8)
    else if al >= 4 then
      (Plw (X31, s, Ofsimm _0), Psw (X31, d, Ofsimm _0), 4)
    else if al = 2 then
      (Plh (X31, s, Ofsimm _0), Psh (X31, d, Ofsimm _0), 2)
    else
      (Plb (X31, s, Ofsimm _0), Psb (X31, d, Ofsimm _0), 1) in
  expand_loadimm32 X7 (Z.of_uint (sz / chunksize));
  let delta = Z.of_uint chunksize in
  let lbl = new_label () in
  emit (Plabel lbl);
  emit load;
  expand_addptrofs s s delta;
  emit (Paddiw(X7, X X7, _m1));
  emit store;
  expand_addptrofs d d delta;
  emit (Pbnew (X X7, X0, lbl))

let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if sz <= 32
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | Mint8unsigned, BR(IR res) ->
     emit (Plbu (res, base, Ofsimm ofs))
  | Mint8signed, BR(IR res) ->
     emit (Plb  (res, base, Ofsimm ofs))
  | Mint16unsigned, BR(IR res) ->
     emit (Plhu (res, base, Ofsimm ofs))
  | Mint16signed, BR(IR res) ->
     emit (Plh  (res, base, Ofsimm ofs))
  | Mint32, BR(IR res) ->
     emit (Plw  (res, base, Ofsimm ofs))
  | Mint64, BR(IR res) ->
     emit (Pld  (res, base, Ofsimm ofs))
  | Mint64, BR_splitlong(BR(IR res1), BR(IR res2)) ->
     let ofs' = Ptrofs.add ofs _4 in
     if base <> res2 then begin
         emit (Plw (res2, base, Ofsimm ofs));
         emit (Plw (res1, base, Ofsimm ofs'))
       end else begin
         emit (Plw (res1, base, Ofsimm ofs'));
         emit (Plw (res2, base, Ofsimm ofs))
       end
  | Mfloat32, BR(FR res) ->
     emit (Pfls (res, base, Ofsimm ofs))
  | Mfloat64, BR(FR res) ->
     emit (Pfld (res, base, Ofsimm ofs))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [BA(IR addr)] ->
      expand_builtin_vload_common chunk addr _0 res
  | [BA_addrstack ofs] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vload_common chunk X2 ofs res
      else begin
        expand_addptrofs X31 X2 ofs; (* X31 <- sp + ofs *)
        expand_builtin_vload_common chunk X31 _0 res
      end
  | [BA_addptr(BA(IR addr), (BA_int ofs | BA_long ofs))] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vload_common chunk addr ofs res
      else begin
        expand_addptrofs X31 addr ofs; (* X31 <- addr + ofs *)
        expand_builtin_vload_common chunk X31 _0 res
      end
  | _ ->
      assert false

let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) ->
     emit (Psb (src, base, Ofsimm ofs))
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Psh (src, base, Ofsimm ofs))
  | Mint32, BA(IR src) ->
     emit (Psw (src, base, Ofsimm ofs))
  | Mint64, BA(IR src) ->
     emit (Psd (src, base, Ofsimm ofs))
  | Mint64, BA_splitlong(BA(IR src1), BA(IR src2)) ->
     let ofs' = Ptrofs.add ofs _4 in
     emit (Psw (src2, base, Ofsimm ofs));
     emit (Psw (src1, base, Ofsimm ofs'))
  | Mfloat32, BA(FR src) ->
     emit (Pfss (src, base, Ofsimm ofs))
  | Mfloat64, BA(FR src) ->
     emit (Pfsd (src, base, Ofsimm ofs))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA(IR addr); src] ->
      expand_builtin_vstore_common chunk addr _0 src
  | [BA_addrstack ofs; src] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vstore_common chunk X2 ofs src
      else begin
        expand_addptrofs X31 X2 ofs; (* X31 <- sp + ofs *)
        expand_builtin_vstore_common chunk X31 _0 src
      end
  | [BA_addptr(BA(IR addr), (BA_int ofs | BA_long ofs)); src] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vstore_common chunk addr ofs src
      else begin
        expand_addptrofs X31 addr ofs; (* X31 <- addr + ofs *)
        expand_builtin_vstore_common chunk X31 _0 src
      end
  | _ ->
      assert false

(* Handling of varargs *)

(* Number of integer registers, FP registers, and stack words
   used to pass the (fixed) arguments to a function. *)

let arg_int_size ri rf ofs k =
  if ri < 8
  then k (ri + 1) rf ofs
  else k ri rf (ofs + 1)

let arg_single_size ri rf ofs k =
  if rf < 8
  then k ri (rf + 1) ofs
  else arg_int_size ri rf ofs k

let arg_long_size ri rf ofs k =
  if Archi.ptr64 then
    if ri < 8
    then k (ri + 1) rf ofs
    else k ri rf (ofs + 1)
  else
    if ri < 7 then k (ri + 2) rf ofs
    else if ri = 7 then k (ri + 1) rf (ofs + 1)
    else k ri rf (align ofs 2 + 2)

let arg_double_size ri rf ofs k =
  if rf < 8
  then k ri (rf + 1) ofs
  else arg_long_size ri rf ofs k

let rec args_size l ri rf ofs =
  match l with
  | [] -> (ri, rf, ofs)
  | (Tint | Tany32) :: l ->
      arg_int_size ri rf ofs (args_size l)
  | Tsingle :: l ->
      arg_single_size ri rf ofs (args_size l)
  | Tlong :: l ->
      arg_long_size ri rf ofs (args_size l)
  | (Tfloat | Tany64) :: l ->
      arg_double_size ri rf ofs (args_size l)

(* Size in words of the arguments to a function.  This includes both
   arguments passed in integer registers and arguments passed on stack,
   but not arguments passed in FP registers. *)

let arguments_size sg =
  let (ri, _, ofs) = args_size sg.sig_args 0 0 0 in
  ri + ofs

let save_arguments first_reg base_ofs =
  for i = first_reg to 7 do
    expand_storeind_ptr
      int_param_regs.(i)
      X2
      (Ptrofs.repr (Z.add base_ofs (Z.of_uint ((i - first_reg) * wordsize))))
  done

let vararg_start_ofs : Z.t option ref = ref None

let expand_builtin_va_start r =
  match !vararg_start_ofs with
  | None ->
      invalid_arg "Fatal error: va_start used in non-vararg function"
  | Some ofs ->
      expand_addptrofs X31 X2 (Ptrofs.repr ofs);
      expand_storeind_ptr X31 r Ptrofs.zero

(* Auxiliary for 64-bit integer arithmetic built-ins.  They expand to
   two instructions, one computing the low 32 bits of the result,
   followed by another computing the high 32 bits.  In cases where
   the first instruction would overwrite arguments to the second
   instruction, we must go through X31 to hold the low 32 bits of the result.
*)

let expand_int64_arith conflict rl fn =
  if conflict then (fn X31; emit (Pmv(rl, X31))) else fn rl

(* Byte swaps.  There are no specific instructions, so we use standard,
   not-very-efficient formulas. *)

let expand_bswap16 d s =
  (* d = (s & 0xFF) << 8 | (s >> 8) & 0xFF *)
  emit (Pandiw(X31, X s, coqint_of_camlint 0xFFl));
  emit (Pslliw(X31, X X31, _8));
  emit (Psrliw(d, X s, _8));
  emit (Pandiw(d, X d, coqint_of_camlint 0xFFl));
  emit (Porw(d, X X31, X d))

let expand_bswap32 d s =
  (* d = (s << 24)
       | (((s >> 8) & 0xFF) << 16)
       | (((s >> 16) & 0xFF) << 8)
       | (s >> 24)  *)
  emit (Pslliw(X1, X s, coqint_of_camlint 24l));
  emit (Psrliw(X31, X s, _8));
  emit (Pandiw(X31, X X31, coqint_of_camlint 0xFFl));
  emit (Pslliw(X31, X X31, _16));
  emit (Porw(X1, X X1, X X31));
  emit (Psrliw(X31, X s, _16));
  emit (Pandiw(X31, X X31, coqint_of_camlint 0xFFl));
  emit (Pslliw(X31, X X31, _8));
  emit (Porw(X1, X X1, X X31));
  emit (Psrliw(X31, X s, coqint_of_camlint 24l));
  emit (Porw(d, X X1, X X31))

let expand_bswap64 d s =
  (* d = s << 56
         | (((s >> 8) & 0xFF) << 48)
         | (((s >> 16) & 0xFF) << 40)
         | (((s >> 24) & 0xFF) << 32)
         | (((s >> 32) & 0xFF) << 24)
         | (((s >> 40) & 0xFF) << 16)
         | (((s >> 48) & 0xFF) << 8)
         | s >> 56 *)
  emit (Psllil(X1, X s, coqint_of_camlint 56l));
  List.iter
    (fun (n1, n2) ->
      emit (Psrlil(X31, X s, coqint_of_camlint n1));
      emit (Pandil(X31, X X31, coqint_of_camlint 0xFFl));
      emit (Psllil(X31, X X31, coqint_of_camlint n2));
      emit (Porl(X1, X X1, X X31)))
    [(8l,48l); (16l,40l); (24l,32l); (32l,24l); (40l,16l); (48l,8l)];
  emit (Psrlil(X31, X s, coqint_of_camlint 56l));
  emit (Porl(d, X X1, X X31))

(* Count leading zeros.  Algorithm 5-7 from Hacker's Delight,
   re-rolled as a loop to produce more compact code. *)

let expand_clz ~sixtyfour ~splitlong =
  (* Input:  X in X5 or (X5, X6) if splitlong
     Result: N in X7
     Temporaries: S in X8, Y in X9 *)
  let lbl1 = new_label() in
  let lbl2 = new_label() in
  (* N := bitsize of X's type (32 or 64) *)
  expand_loadimm32 X7 (coqint_of_camlint
                         (if sixtyfour || splitlong then 64l else 32l));
  (* S := initial shift amount (16 or 32) *)                         
  expand_loadimm32 X8 (coqint_of_camlint (if sixtyfour then 32l else 16l));
  if splitlong then begin
    (* if (Xhigh == 0) goto lbl1 *)
    emit (Pbeqw(X X6, X0, lbl1));
    (* N := 32 *)
    expand_loadimm32 X7 (coqint_of_camlint 32l);
    (* X := Xhigh *)
    emit (Pmv(X5, X6))
  end;
  (* lbl1: *)
  emit (Plabel lbl1);
  (* Y := X >> S *)
  emit (if sixtyfour then Psrll(X9, X X5, X X8) else Psrlw(X9, X X5, X X8));
  (* if (Y == 0) goto lbl2 *)
  emit (if sixtyfour then Pbeql(X X9, X0, lbl2) else Pbeqw(X X9, X0, lbl2));
  (* N := N - S *)
  emit (Psubw(X7, X X7, X X8));
  (* X := Y *)
  emit (Pmv(X5, X9));
  (* lbl2: *)
  emit (Plabel lbl2);
  (* S := S / 2 *)
  emit (Psrliw(X8, X X8, _1));
  (* if (S != 0) goto lbl1; *)
  emit (Pbnew(X X8, X0, lbl1));
  (* N := N - X *)
  emit (Psubw(X7, X X7, X X5))

(* Count trailing zeros.  Algorithm 5-14 from Hacker's Delight,
   re-rolled as a loop to produce more compact code. *)

let expand_ctz ~sixtyfour ~splitlong =
  (* Input:  X in X6 or (X5, X6) if splitlong
     Result: N in X7
     Temporaries: S in X8, Y in X9 *)
  let lbl1 = new_label() in
  let lbl2 = new_label() in
  (* N := bitsize of X's type (32 or 64) *)
  expand_loadimm32 X7 (coqint_of_camlint
                         (if sixtyfour || splitlong then 64l else 32l));
  (* S := initial shift amount (16 or 32) *)                         
  expand_loadimm32 X8 (coqint_of_camlint (if sixtyfour then 32l else 16l));
  if splitlong then begin
    (* if (Xlow == 0) goto lbl1 *)
    emit (Pbeqw(X X5, X0, lbl1));
    (* N := 32 *)
    expand_loadimm32 X7 (coqint_of_camlint 32l);
    (* X := Xlow *)
    emit (Pmv(X6, X5))
  end;
  (* lbl1: *)
  emit (Plabel lbl1);
  (* Y := X >> S *)
  emit (if sixtyfour then Pslll(X9, X X6, X X8) else Psllw(X9, X X6, X X8));
  (* if (Y == 0) goto lbl2 *)
  emit (if sixtyfour then Pbeql(X X9, X0, lbl2) else Pbeqw(X X9, X0, lbl2));
  (* N := N - S *)
  emit (Psubw(X7, X X7, X X8));
  (* X := Y *)
  emit (Pmv(X6, X9));
  (* lbl2: *)
  emit (Plabel lbl2);
  (* S := S / 2 *)
  emit (Psrliw(X8, X X8, _1));
  (* if (S != 0) goto lbl1; *)
  emit (Pbnew(X X8, X0, lbl1));
  (* N := N - most significant bit of X *)
  emit (if sixtyfour then Psrlil(X6, X X6, coqint_of_camlint 63l)
                     else Psrliw(X6, X X6, coqint_of_camlint 31l));
  emit (Psubw(X7, X X7, X X6))

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
     ()
  | "__builtin_fence", [], _ ->
     emit Pfence
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     expand_builtin_va_start a
  (* Byte swaps *)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     expand_bswap16 res a1
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     expand_bswap32 res a1
  | "__builtin_bswap64", [BA(IR a1)], BR(IR res) ->
     expand_bswap64 res a1
  | "__builtin_bswap64", [BA_splitlong(BA(IR ah), BA(IR al))],
                         BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (ah = X6 && al = X5 && rh = X5 && rl = X6);
     expand_bswap32 X5 X5;
     expand_bswap32 X6 X6
  (* Count zeros *)
  | "__builtin_clz", [BA(IR a)], BR(IR res) ->
     assert (a = X5 && res = X7);
     expand_clz ~sixtyfour:false ~splitlong:false
  | "__builtin_clzl", [BA(IR a)], BR(IR res) ->
     assert (a = X5 && res = X7);
     expand_clz ~sixtyfour:Archi.ptr64 ~splitlong:false
  | "__builtin_clzll", [BA(IR a)], BR(IR res) ->
     assert (a = X5 && res = X7);
     expand_clz ~sixtyfour:true ~splitlong:false
  | "__builtin_clzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
     assert (al = X5 && ah = X6 && res = X7);
     expand_clz ~sixtyfour:false ~splitlong:true
  | "__builtin_ctz", [BA(IR a)], BR(IR res) ->
     assert (a = X6 && res = X7);
     expand_ctz ~sixtyfour:false ~splitlong:false
  | "__builtin_ctzl", [BA(IR a)], BR(IR res) ->
     assert (a = X6 && res = X7);
     expand_ctz ~sixtyfour:Archi.ptr64 ~splitlong:false
  | "__builtin_ctzll", [BA(IR a)], BR(IR res) ->
     assert (a = X6 && res = X7);
     expand_ctz ~sixtyfour:true ~splitlong:false
  | "__builtin_ctzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
     assert (al = X5 && ah = X6 && res = X7);
     expand_ctz ~sixtyfour:false ~splitlong:true
  (* Float arithmetic *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA(FR a1)], BR(FR res) ->
     emit (Pfsqrtd(res, a1))
  | "__builtin_fmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmaddd(res, a1, a2, a3))
  | "__builtin_fmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmsubd(res, a1, a2, a3))
  | "__builtin_fnmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmaddd(res, a1, a2, a3))
  | "__builtin_fnmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmsubd(res, a1, a2, a3))
  | "__builtin_fmin", [BA(FR a1); BA(FR a2)], BR(FR res) ->
      emit (Pfmind(res, a1, a2))
  | "__builtin_fmax", [BA(FR a1); BA(FR a2)], BR(FR res) ->
      emit (Pfmaxd(res, a1, a2))
  (* 64-bit integer arithmetic for a 32-bit platform *)
  | "__builtin_negl", [BA_splitlong(BA(IR ah), BA(IR al))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = ah) rl
			(fun rl ->
                         emit (Psltuw (X1, X0, X al));
			 emit (Psubw (rl, X0, X al));
			 emit (Psubw (rh, X0, X ah));
			 emit (Psubw (rh, X rh, X X1)))
  | "__builtin_addl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = bl || rl = ah || rl = bh) rl
			(fun rl ->
			 emit (Paddw (rl, X al, X bl));
                         emit (Psltuw (X1, X rl, X bl));
			 emit (Paddw (rh, X ah, X bh));
			 emit (Paddw (rh, X rh, X X1)))
  | "__builtin_subl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = ah || rl = bh) rl
			(fun rl ->
                         emit (Psltuw (X1, X al, X bl));
			 emit (Psubw (rl, X al, X bl));
			 emit (Psubw (rh, X ah, X bh));
			 emit (Psubw (rh, X rh, X X1)))
  | "__builtin_mull", [BA(IR a); BA(IR b)],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = a || rl = b) rl
                        (fun rl ->
                          emit (Pmulw (rl, X a, X b));
                          emit (Pmulhuw (rh, X a, X b)))
  (* No operation *)
  | "__builtin_nop", [], _ ->
     emit Pnop
  (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (* Catch-all *)
  | _ ->
     raise (Error ("unrecognized builtin " ^ name))

(* Expansion of instructions *)

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs) ->
      let sg = get_current_function_sig() in
      emit (Pmv (X30, X2));
      if (sg.sig_cc.cc_vararg <> None) then begin
        let n = arguments_size sg in
        let extra_sz = if n >= 8 then 0 else align ((8 - n) * wordsize) 16 in
        let full_sz = Z.add sz (Z.of_uint extra_sz) in
        expand_addptrofs X2 X2 (Ptrofs.repr (Z.neg full_sz));
        expand_storeind_ptr X30 X2 ofs;
        let va_ofs =
          Z.add full_sz (Z.of_sint ((n - 8) * wordsize)) in
        vararg_start_ofs := Some va_ofs;
        save_arguments n va_ofs
      end else begin
        expand_addptrofs X2 X2 (Ptrofs.repr (Z.neg sz));
        expand_storeind_ptr X30 X2 ofs;
        vararg_start_ofs := None
      end
  | Pfreeframe (sz, ofs) ->
     let sg = get_current_function_sig() in
     let extra_sz =
      if (sg.sig_cc.cc_vararg <> None) then begin
        let n = arguments_size sg in
        if n >= 8 then 0 else align ((8 - n) * wordsize) 16
      end else 0 in
     expand_addptrofs X2 X2 (Ptrofs.repr (Z.add sz (Z.of_uint extra_sz)))

  | Pseqw(rd, rs1, rs2) ->
      (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltiuw(rd, rs1, Int.one))
      end else begin
        emit (Pxorw(rd, rs1, rs2)); emit (Psltiuw(rd, X rd, Int.one))
      end
  | Psnew(rd, rs1, rs2) ->
      (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltuw(rd, X0, rs1))
      end else begin
        emit (Pxorw(rd, rs1, rs2)); emit (Psltuw(rd, X0, X rd))
      end
  | Pseql(rd, rs1, rs2) ->
      (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltiul(rd, rs1, Int64.one))
      end else begin
        emit (Pxorl(rd, rs1, rs2)); emit (Psltiul(rd, X rd, Int64.one))
      end
  | Psnel(rd, rs1, rs2) ->
      (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
      if rs2 = X0 then begin
        emit (Psltul(rd, X0, rs1))
      end else begin
        emit (Pxorl(rd, rs1, rs2)); emit (Psltul(rd, X0, X rd))
      end
  | Pcvtl2w(rd, rs) ->
      assert Archi.ptr64;
      emit (Paddiw(rd, rs, Int.zero))  (* 32-bit sign extension *)
  | Pcvtw2l(r) ->
      assert Archi.ptr64
      (* no-operation because the 32-bit integer was kept sign extended already *)

  | Pjal_r(r, sg) ->
      fixup_call sg; emit instr
  | Pjal_s(symb, sg) ->
      fixup_call sg; emit instr
  | Pj_r(r, sg) when r <> X1 ->
      fixup_call sg; emit instr
  | Pj_s(symb, sg) ->
      fixup_call sg; emit instr

  | Pbuiltin (ef,args,res) ->
     begin match ef with
     | EF_builtin (name,sg) ->
        expand_builtin_inline (camlstring_of_coqstring name) args res
     | EF_vload chunk ->
        expand_builtin_vload chunk args res
     | EF_vstore chunk ->
        expand_builtin_vstore chunk args
     | EF_annot_val (kind,txt,targ) ->
        expand_annot_val kind txt targ args res
     | EF_memcpy(sz, al) ->
        expand_builtin_memcpy (Z.to_int sz) (Z.to_int al) args
     | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit instr
     | _ ->
        assert false
     end
  | _ ->
     emit instr

(* NOTE: Dwarf register maps for RV32G are not yet specified
   officially.  This is just a placeholder.  *)
let int_reg_to_dwarf = function
               | X1  -> 1  | X2  -> 2  | X3  -> 3
   | X4  -> 4  | X5  -> 5  | X6  -> 6  | X7  -> 7
   | X8  -> 8  | X9  -> 9  | X10 -> 10 | X11 -> 11
   | X12 -> 12 | X13 -> 13 | X14 -> 14 | X15 -> 15
   | X16 -> 16 | X17 -> 17 | X18 -> 18 | X19 -> 19
   | X20 -> 20 | X21 -> 21 | X22 -> 22 | X23 -> 23
   | X24 -> 24 | X25 -> 25 | X26 -> 26 | X27 -> 27
   | X28 -> 28 | X29 -> 29 | X30 -> 30 | X31 -> 31

let float_reg_to_dwarf = function
   | F0  -> 32 | F1  -> 33 | F2  -> 34 | F3  -> 35
   | F4  -> 36 | F5  -> 37 | F6  -> 38 | F7  -> 39
   | F8  -> 40 | F9  -> 41 | F10 -> 42 | F11 -> 43
   | F12 -> 44 | F13 -> 45 | F14 -> 46 | F15 -> 47
   | F16 -> 48 | F17 -> 49 | F18 -> 50 | F19 -> 51
   | F20 -> 52 | F21 -> 53 | F22 -> 54 | F23 -> 55
   | F24 -> 56 | F25 -> 57 | F26 -> 58 | F27 -> 59
   | F28 -> 60 | F29 -> 61 | F30 -> 62 | F31 -> 63

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | FR r -> float_reg_to_dwarf r
   | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    fixup_function_entry fn.fn_sig;
    expand id (* sp= *) 2 preg_to_dwarf expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with Error s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p

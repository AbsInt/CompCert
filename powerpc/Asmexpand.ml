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

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the PPC assembly code. *)

open Datatypes
open Camlcoq
open Integers
open AST
open Memdata
open Asm

(* Buffering the expanded code *)

let current_code = ref ([]: instruction list)

let emit i = current_code := i :: !current_code

let emit_loadimm r n =
  List.iter emit (Asmgen.loadimm r n [])

let emit_addimm rd rs n =
  List.iter emit (Asmgen.addimm rd rs n [])

let get_code () =
  let c = List.rev !current_code in current_code := []; c

(* Generation of fresh labels *)

let dummy_function = { fn_code = []; fn_sig = signature_main }
let current_function = ref dummy_function
let next_label = ref (None : label option)

let new_label () =
  let lbl =
    match !next_label with
    | Some l -> l
    | None ->
        (* on-demand computation of the next available label *)
        List.fold_left
          (fun next instr ->
            match instr with
            | Plabel l -> if P.lt l next then next else P.succ l
            | _ -> next)
          P.one (!current_function).fn_code
  in
    next_label := Some (P.succ lbl);
    lbl

let set_current_function f =
  current_function := f; next_label := None

(* Useful constants *)

let _0 = Integers.Int.zero
let _1 = Integers.Int.one
let _2 = coqint_of_camlint 2l
let _4 = coqint_of_camlint 4l
let _6 = coqint_of_camlint 6l
let _8 = coqint_of_camlint 8l
let _m4 = coqint_of_camlint (-4l)
let _m8 = coqint_of_camlint (-8l)

(* Handling of annotations *)

let expand_annot_val txt targ args res =
  emit (Pannot(EF_annot(txt, [targ]), List.map (fun r -> AA_base r) args));
  begin match args, res with
  | [IR src], [IR dst] ->
      if dst <> src then emit (Pmr(dst, src))
  | [FR src], [FR dst] ->
      if dst <> src then emit (Pfmr(dst, src))
  | _, _ ->
      assert false
  end

(* Handling of memcpy *)

(* On the PowerPC, unaligned accesses to 16- and 32-bit integers are
   fast, but unaligned accesses to 64-bit floats can be slow
   (not so much on G5, but clearly so on Power7).
   So, use 64-bit accesses only if alignment >= 4.
   Note that lfd and stfd cannot trap on ill-formed floats. *)

let expand_builtin_memcpy_small sz al src dst =
  let rec copy ofs sz =
    if sz >= 8 && al >= 4 && !Clflags.option_ffpu then begin
      emit (Plfd(FPR13, Cint ofs, src));
      emit (Pstfd(FPR13, Cint ofs, dst));
      copy (Int.add ofs _8) (sz - 8)
    end else if sz >= 4 then begin
      emit (Plwz(GPR0, Cint ofs, src));
      emit (Pstw(GPR0, Cint ofs, dst));
      copy (Int.add ofs _4) (sz - 4)
    end else if sz >= 2 then begin
      emit (Plhz(GPR0, Cint ofs, src));
      emit (Psth(GPR0, Cint ofs, dst));
      copy (Int.add ofs _2) (sz - 2)
    end else if sz >= 1 then begin
      emit (Plbz(GPR0, Cint ofs, src));
      emit (Pstb(GPR0, Cint ofs, dst));
      copy (Int.add ofs _1) (sz - 1)
    end in
  copy _0 sz

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= 4);
  emit_loadimm GPR0 (Z.of_uint (sz / 4));
  emit (Pmtctr GPR0);
  let (s,d) = if dst <> GPR11 then (GPR11, GPR12) else (GPR12, GPR11) in
  emit (Paddi(s, src, Cint _m4));
  emit (Paddi(d, dst, Cint _m4));
  let lbl = new_label() in
  emit (Plabel lbl);
  emit (Plwzu(GPR0, Cint _4, s));
  emit (Pstwu(GPR0, Cint _4, d));
  emit (Pbdnz lbl);
  (* s and d lag behind by 4 bytes *)
  match sz land 3 with
  | 1 -> emit (Plbz(GPR0, Cint _4, s));
         emit (Pstb(GPR0, Cint _4, d))
  | 2 -> emit (Plhz(GPR0, Cint _4, s));
         emit (Psth(GPR0, Cint _4, d))
  | 3 -> emit (Plhz(GPR0, Cint _4, s));
         emit (Psth(GPR0, Cint _4, d));
         emit (Plbz(GPR0, Cint _6, s));
         emit (Pstb(GPR0, Cint _6, d))
  | _ -> ()

let expand_builtin_memcpy sz al args =
  let (dst, src) =
    match args with [IR d; IR s] -> (d, s) | _ -> assert false in
  if sz <= (if !Clflags.option_ffpu && al >= 4
            then if !Clflags.option_Osize then 35 else 51
	    else if !Clflags.option_Osize then 19 else 27)
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk base offset res =
  match chunk, res with
  | Mint8unsigned, IR res ->
      emit (Plbz(res, offset, base))
  | Mint8signed, IR res ->
      emit (Plbz(res, offset, base));
      emit (Pextsb(res, res))
  | Mint16unsigned, IR res ->
      emit (Plhz(res, offset, base))
  | Mint16signed, IR res ->
      emit (Plha(res, offset, base))
  | (Mint32 | Many32), IR res ->
      emit (Plwz(res, offset, base))
  | Mfloat32, FR res ->
      emit (Plfs(res, offset, base))
  | (Mfloat64 | Many64), FR res ->
      emit (Plfd(res, offset, base))
  (* Mint64 is special-cased below *)
  | _ ->
      assert false

let expand_builtin_vload chunk args res =
  begin match args, res with
  | [IR addr], [res] when chunk <> Mint64 ->
      expand_builtin_vload_common chunk addr (Cint _0) res
  | [IR addr], [IR res1; IR res2] when chunk = Mint64 ->
      if addr <> res1 then begin
        emit (Plwz(res1, Cint _0, addr));
        emit (Plwz(res2, Cint _4, addr))
      end else begin
        emit (Plwz(res2, Cint _4, addr));
        emit (Plwz(res1, Cint _0, addr))
      end
  | _ ->
      assert false
  end

let expand_builtin_vload_global chunk id ofs args res =
  begin match res with
  | [res] when chunk <> Mint64 ->
      emit (Paddis(GPR11, GPR0, Csymbol_high(id, ofs)));
      expand_builtin_vload_common chunk GPR11 (Csymbol_low(id, ofs)) res
  | [IR res1; IR res2] when chunk = Mint64 ->
      emit (Paddis(res1, GPR0, Csymbol_high(id, ofs)));
      emit (Plwz(res1, Csymbol_low(id, ofs), res1));
      let ofs = Int.add ofs _4 in
      emit (Paddis(res2, GPR0, Csymbol_high(id, ofs)));
      emit (Plwz(res2, Csymbol_low(id, ofs), res2))
  | _ ->
      assert false
  end

let expand_builtin_vload_sda chunk id ofs args res =
  begin match res with
  | [res] when chunk <> Mint64 ->
      expand_builtin_vload_common chunk GPR0 (Csymbol_sda(id, ofs)) res
  | [IR res1; IR res2] when chunk = Mint64 ->
      emit (Plwz(res1, Csymbol_sda(id, ofs), GPR0));
      let ofs = Int.add ofs _4 in
      emit (Plwz(res2, Csymbol_sda(id, ofs), GPR0))
  | _ ->
      assert false
  end

let expand_builtin_vload_rel chunk id ofs args res =
  emit (Paddis(GPR11, GPR0, Csymbol_rel_high(id, ofs)));
  emit (Paddi(GPR11, GPR11, Csymbol_rel_low(id, ofs)));
  expand_builtin_vload chunk [IR GPR11] res

let expand_builtin_vstore_common chunk base offset src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), IR src ->
      emit (Pstb(src, offset, base))
  | (Mint16signed | Mint16unsigned), IR src ->
      emit (Psth(src, offset, base))
  | (Mint32 | Many32), IR src ->
      emit (Pstw(src, offset, base))
  | Mfloat32, FR src ->
      emit (Pstfs(src, offset, base))
  | (Mfloat64 | Many64), FR src ->
      emit (Pstfd(src, offset, base))
  (* Mint64 is special-cased below *)
  | _ ->
      assert false

let expand_builtin_vstore chunk args =
  begin match args with
  | [IR addr; src] when chunk <> Mint64 ->
      expand_builtin_vstore_common chunk addr (Cint _0) src
  | [IR addr; IR src1; IR src2] when chunk = Mint64 ->
      emit (Pstw(src1, Cint _0, addr));
      emit (Pstw(src2, Cint _4, addr))
  | _ ->
      assert false
  end

let expand_builtin_vstore_global chunk id ofs args =
  begin match args with
  | [src] when chunk <> Mint64 ->
      let tmp = if src = IR GPR11 then GPR12 else GPR11 in
      emit (Paddis(tmp, GPR0, Csymbol_high(id, ofs)));
      expand_builtin_vstore_common chunk tmp (Csymbol_low(id, ofs)) src
  | [IR src1; IR src2] when chunk = Mint64 ->
      let tmp =
        if not (List.mem GPR12 [src1; src2]) then GPR12 else
        if not (List.mem GPR11 [src1; src2]) then GPR11 else GPR10 in
      emit (Paddis(tmp, GPR0, Csymbol_high(id, ofs)));
      emit (Pstw(src1, Csymbol_low(id, ofs), tmp));
      let ofs = Int.add ofs _4 in
      emit (Paddis(tmp, GPR0, Csymbol_high(id, ofs)));
      emit (Pstw(src2, Csymbol_low(id, ofs), tmp))
  | _ ->
      assert false
  end

let expand_builtin_vstore_sda chunk id ofs args =
  begin match args with
  | [src] when chunk <> Mint64 ->
      expand_builtin_vstore_common chunk GPR0 (Csymbol_sda(id, ofs)) src
  | [IR src1; IR src2] when chunk = Mint64 ->
      emit (Pstw(src1, Csymbol_sda(id, ofs), GPR0));
      let ofs = Int.add ofs _4 in
      emit (Pstw(src2, Csymbol_sda(id, ofs), GPR0))
  | _ ->
      assert false
  end

let expand_builtin_vstore_rel chunk id ofs args =
  let tmp =
    if not (List.mem (IR GPR12) args) then GPR12 else
    if not (List.mem (IR GPR11) args) then GPR11 else GPR10 in
  emit (Paddis(tmp, GPR0, Csymbol_rel_high(id, ofs)));
  emit (Paddi(tmp, tmp, Csymbol_rel_low(id, ofs)));
  expand_builtin_vstore chunk (IR tmp :: args)

(* Handling of varargs *)

let current_function_stacksize = ref 0l

let align n a = (n + a - 1) land (-a)

let rec next_arg_locations ir fr ofs = function
  | [] ->
      (ir, fr, ofs)
  | (Tint | Tany32) :: l ->
      if ir < 8
      then next_arg_locations (ir + 1) fr ofs l
      else next_arg_locations ir fr (ofs + 4) l
  | (Tfloat | Tsingle | Tany64) :: l ->
      if fr < 8
      then next_arg_locations ir (fr + 1) ofs l
      else next_arg_locations ir fr (align ofs 8 + 8) l
  | Tlong :: l ->
      if ir < 7
      then next_arg_locations (align ir 2 + 2) fr ofs l
      else next_arg_locations ir fr (align ofs 8 + 8) l

let expand_builtin_va_start r =
  if not (!current_function).fn_sig.sig_cc.cc_vararg then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let (ir, fr, ofs) =
    next_arg_locations 0 0 0 (!current_function).fn_sig.sig_args in
  emit_loadimm GPR0 (Z.of_uint ir);
  emit (Pstb(GPR0, Cint _0, r));
  emit_loadimm GPR0 (Z.of_uint fr);
  emit (Pstb(GPR0, Cint _1, r));
  emit_addimm GPR0 GPR1 (coqint_of_camlint
                           Int32.(add (add !current_function_stacksize 8l)
                                      (of_int ofs)));
  emit (Pstw(GPR0, Cint _4, r));
  emit_addimm GPR0 GPR1 (coqint_of_camlint
                           Int32.(sub !current_function_stacksize 96l));
  emit (Pstw(GPR0, Cint _8, r))

(* Auxiliary for 64-bit integer arithmetic built-ins.  They expand to
   two instructions, one computing the low 32 bits of the result,
   followed by another computing the high 32 bits.  In cases where
   the first instruction would overwrite arguments to the second
   instruction, we must go through GPR0 to hold the low 32 bits of the result.
*)

let expand_int64_arith conflict rl fn =
  if conflict then (fn GPR0; emit (Pmr(rl, GPR0))) else fn rl

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  (* Can use as temporaries: GPR0, FPR13 *)
  match name, args, res with
  (* Integer arithmetic *)
  | "__builtin_mulhw", [IR a1; IR a2], [IR res] ->
      emit (Pmulhw(res, a1, a2))
  | "__builtin_mulhwu", [IR a1; IR a2], [IR res] ->
      emit (Pmulhwu(res, a1, a2))
  | "__builtin_clz", [IR a1], [IR res] ->
      emit (Pcntlzw(res, a1))
  | ("__builtin_bswap" | "__builtin_bswap32"), [IR a1], [IR res] ->
      emit (Pstwu(a1, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plwbrx(res, GPR0, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  | "__builtin_bswap16", [IR a1], [IR res] ->
      emit (Prlwinm(GPR0, a1, _8, coqint_of_camlint 0x0000FF00l));
      emit (Prlwinm(res, a1, coqint_of_camlint 24l,
                                  coqint_of_camlint 0x000000FFl));
      emit (Por(res, GPR0, res))
  (* Float arithmetic *)
  | "__builtin_fmadd", [FR a1; FR a2; FR a3], [FR res] ->
      emit (Pfmadd(res, a1, a2, a3))
  | "__builtin_fmsub", [FR a1; FR a2; FR a3], [FR res] ->
      emit (Pfmsub(res, a1, a2, a3))
  | "__builtin_fnmadd", [FR a1; FR a2; FR a3], [FR res] ->
      emit (Pfnmadd(res, a1, a2, a3))
  | "__builtin_fnmsub", [FR a1; FR a2; FR a3], [FR res] ->
      emit (Pfnmsub(res, a1, a2, a3))
  | "__builtin_fabs", [FR a1], [FR res] ->
      emit (Pfabs(res, a1))
  | "__builtin_fsqrt", [FR a1], [FR res] ->
      emit (Pfsqrt(res, a1))
  | "__builtin_frsqrte", [FR a1], [FR res] ->
      emit (Pfrsqrte(res, a1))
  | "__builtin_fres", [FR a1], [FR res] ->
      emit (Pfres(res, a1))
  | "__builtin_fsel", [FR a1; FR a2; FR a3], [FR res] ->
      emit (Pfsel(res, a1, a2, a3))
  | "__builtin_fcti", [FR a1], [IR res] ->
      emit (Pfctiw(FPR13, a1));
      emit (Pstfdu(FPR13, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plwz(res, Cint _4, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [IR ah; IR al], [IR rh; IR rl] ->
      expand_int64_arith (rl = ah) rl (fun rl ->
        emit (Psubfic(rl, al, Cint _0));
        emit (Psubfze(rh, ah)))
  | "__builtin_addl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
      expand_int64_arith (rl = ah || rl = bh) rl (fun rl ->
        emit (Paddc(rl, al, bl));
        emit (Padde(rh, ah, bh)))
  | "__builtin_subl", [IR ah; IR al; IR bh; IR bl], [IR rh; IR rl] ->
      expand_int64_arith (rl = ah || rl = bh) rl (fun rl ->
        emit (Psubfc(rl, bl, al));
        emit (Psubfe(rh, bh, ah)))
  | "__builtin_mull", [IR a; IR b], [IR rh; IR rl] ->
      expand_int64_arith (rl = a || rl = b) rl (fun rl ->
        emit (Pmullw(rl, a, b));
        emit (Pmulhwu(rh, a, b)))
  (* Memory accesses *)
  | "__builtin_read16_reversed", [IR a1], [IR res] ->
      emit (Plhbrx(res, GPR0, a1))
  | "__builtin_read32_reversed", [IR a1], [IR res] ->
      emit (Plwbrx(res, GPR0, a1))
  | "__builtin_write16_reversed", [IR a1; IR a2], _ ->
      emit (Psthbrx(a2, GPR0, a1))
  | "__builtin_write32_reversed", [IR a1; IR a2], _ ->
      emit (Pstwbrx(a2, GPR0, a1))
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
      ()
  | "__builtin_eieio", [], _ ->
      emit (Peieio)
  | "__builtin_sync", [], _ ->
      emit (Psync)
  | "__builtin_isync", [], _ ->
      emit (Pisync)
  | "__builtin_trap", [], _ ->
      emit (Ptrap)
  (* Vararg stuff *)
  | "__builtin_va_start", [IR a], _ ->
      expand_builtin_va_start a
  (* Catch-all *)
  | _ ->
      invalid_arg ("unrecognized builtin " ^ name)

(* Calls to variadic functions: condition bit 6 must be set
   if at least one argument is a float; clear otherwise.
   For compatibility with other compilers, do the same if the called
   function is unprototyped. *)

let set_cr6 sg =
  if sg.sig_cc.cc_vararg || sg.sig_cc.cc_unproto then begin
    if List.exists (function Tfloat | Tsingle -> true | _ -> false) sg.sig_args
    then emit (Pcreqv(CRbit_6, CRbit_6, CRbit_6))
    else emit (Pcrxor(CRbit_6, CRbit_6, CRbit_6))
  end

(* Expand instructions *)

let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3
  | CRbit_6 -> 6

let expand_instruction instr =
  match instr with
  | Pallocframe(sz, ofs) ->
      let variadic = (!current_function).fn_sig.sig_cc.cc_vararg in
      let sz = camlint_of_coqint sz in
      assert (ofs = Int.zero);
      let sz = if variadic then Int32.add sz 96l else sz in
      let adj = Int32.neg sz in
      if adj >= -0x8000l then
        emit (Pstwu(GPR1, Cint(coqint_of_camlint adj), GPR1))
      else begin
        emit_loadimm GPR0 (coqint_of_camlint adj);
        emit (Pstwux(GPR1, GPR1, GPR0))
      end;
      emit (Pcfi_adjust (coqint_of_camlint sz));
      if variadic then begin
        emit (Pmflr GPR0);
        emit (Pbl(intern_string "__compcert_va_saveregs",
                  {sig_args = []; sig_res = None; sig_cc = cc_default}));
        emit (Pmtlr GPR0)
      end;
      current_function_stacksize := sz
  | Pbctr sg | Pbctrl sg | Pbl(_, sg) | Pbs(_, sg) ->
      set_cr6 sg;
      emit instr
  | Pfreeframe(sz, ofs) ->
      let variadic = (!current_function).fn_sig.sig_cc.cc_vararg in
      let sz = camlint_of_coqint sz in
      let sz = if variadic then Int32.add sz 96l else sz in
      if sz < 0x8000l then
        emit (Paddi(GPR1, GPR1, Cint(coqint_of_camlint sz)))
      else
        emit (Plwz(GPR1, Cint ofs, GPR1))
  | Pfcti(r1, r2) ->
      emit (Pfctiwz(FPR13, r2));
      emit (Pstfdu(FPR13, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plwz(r1, Cint _4, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  | Pfmake(rd, r1, r2) ->
      emit (Pstwu(r1, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Pstw(r2, Cint _4, GPR1));
      emit (Plfd(rd, Cint _0, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8);
  | Pfxdp(r1, r2) ->
      if r1 <> r2 then emit(Pfmr(r1, r2))
  | Pmfcrbit(r1, bit) ->
      emit (Pmfcr r1);
      emit (Prlwinm(r1, r1, Z.of_uint (1 + num_crbit bit), _1))
  | Pbuiltin(ef, args, res) ->
      begin match ef with
      | EF_builtin(name, sg) ->
          expand_builtin_inline (extern_atom name) args res
      | EF_vload chunk ->
          expand_builtin_vload chunk args res
      | EF_vstore chunk ->
          expand_builtin_vstore chunk args
      | EF_vload_global(chunk, id, ofs) ->
          if symbol_is_small_data id ofs then
             expand_builtin_vload_sda chunk id ofs args res
          else if symbol_is_rel_data id ofs then
             expand_builtin_vload_rel chunk id ofs args res
          else
             expand_builtin_vload_global chunk id ofs args res
      | EF_vstore_global(chunk, id, ofs) ->
          if symbol_is_small_data id ofs then
            expand_builtin_vstore_sda chunk id ofs args
          else if symbol_is_rel_data id ofs then
            expand_builtin_vstore_rel chunk id ofs args
          else
            expand_builtin_vstore_global chunk id ofs args
      | EF_memcpy(sz, al) ->
          expand_builtin_memcpy (Z.to_int sz) (Z.to_int al) args
      | EF_annot_val(txt, targ) ->
          expand_annot_val txt targ args res
      | EF_inline_asm(txt, sg, clob) ->
          emit instr
      | _ ->
          assert false
      end
  | _ ->
      emit instr

let expand_function fn =
  set_current_function fn;
  current_code := [];
  List.iter expand_instruction fn.fn_code;
  let c = get_code() in
  set_current_function dummy_function;
  { fn with fn_code = c }

let expand_fundef = function
  | Internal f -> Internal (expand_function f)
  | External ef -> External ef

let expand_program (p: Asm.program) : Asm.program =
  AST.transform_program expand_fundef p

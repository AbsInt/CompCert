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
open Asmexpandaux

exception Error of string

(* FreeScale's EREF extensions *)

let eref =
  match Configuration.model with
  | "e5500" -> true
  | _ -> false

(* Useful constants and helper functions *)

let _0 = Integers.Int.zero
let _1 = Integers.Int.one
let _2 = coqint_of_camlint 2l
let _4 = coqint_of_camlint 4l
let _6 = coqint_of_camlint 6l
let _8 = coqint_of_camlint 8l
let _m4 = coqint_of_camlint (-4l)
let _m8 = coqint_of_camlint (-8l)

let emit_loadimm r n =
  List.iter emit (Asmgen.loadimm r n [])

let emit_addimm rd rs n =
  List.iter emit (Asmgen.addimm rd rs n [])



(* Handling of annotations *)

let expand_annot_val txt targ args res =
  emit (Pbuiltin(EF_annot(txt, [targ]), args, BR_none));
  begin match args, res with
  | [BA(IR src)], BR(IR dst) ->
      if dst <> src then emit (Pmr(dst, src))
  | [BA(FR src)], BR(FR dst) ->
      if dst <> src then emit (Pfmr(dst, src))
  | _, _ ->
      raise (Error "ill-formed __builtin_annot_val")
  end

(* Handling of memcpy *)

(* On the PowerPC, unaligned accesses to 16- and 32-bit integers are
   fast, but unaligned accesses to 64-bit floats can be slow
   (not so much on G5, but clearly so on Power7).
   So, use 64-bit accesses only if alignment >= 4.
   Note that lfd and stfd cannot trap on ill-formed floats. *)

let offset_in_range ofs =
  Int.eq (Asmgen.high_s ofs) _0

let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (IR r) ->
      (r, _0)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Int.add ofs (Int.repr (Z.of_uint sz)))
      then (GPR1, ofs)
      else begin emit_addimm tmp GPR1 ofs; (tmp, _0) end
  | _ ->
      assert false

let expand_builtin_memcpy_small sz al src dst =
  let (tsrc, tdst) =
    if dst <> BA (IR GPR11) then (GPR11, GPR12) else (GPR12, GPR11) in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  let rec copy osrc odst sz =
    if sz >= 8 && al >= 4 && !Clflags.option_ffpu then begin
      emit (Plfd(FPR13, Cint osrc, rsrc));
      emit (Pstfd(FPR13, Cint odst, rdst));
      copy (Int.add osrc _8) (Int.add odst _8) (sz - 8)
    end else if sz >= 4 then begin
      emit (Plwz(GPR0, Cint osrc, rsrc));
      emit (Pstw(GPR0, Cint odst, rdst));
      copy (Int.add osrc _4) (Int.add odst _4) (sz - 4)
    end else if sz >= 2 then begin
      emit (Plhz(GPR0, Cint osrc, rsrc));
      emit (Psth(GPR0, Cint odst, rdst));
      copy (Int.add osrc _2) (Int.add odst _2) (sz - 2)
    end else if sz >= 1 then begin
      emit (Plbz(GPR0, Cint osrc, rsrc));
      emit (Pstb(GPR0, Cint odst, rdst));
      copy (Int.add osrc _1) (Int.add odst _1) (sz - 1)
    end in
  copy osrc odst sz

let memcpy_big_arg arg tmp =
  (* Set [tmp] to the value of [arg] minus 4 *)
  match arg with
  | BA (IR r) ->
      emit (Paddi(tmp, r, Cint _m4))
  | BA_addrstack ofs ->
      emit_addimm tmp GPR1 (Int.add ofs _m4)
  | _ ->
      assert false

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= 4);
  emit_loadimm GPR0 (Z.of_uint (sz / 4));
  emit (Pmtctr GPR0);
  let (s, d) =
    if dst <> BA (IR GPR11) then (GPR11, GPR12) else (GPR12, GPR11) in
  memcpy_big_arg src s;
  memcpy_big_arg dst d;
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
    match args with [d; s] -> (d, s) | _ -> assert false in
  if sz <= (if !Clflags.option_ffpu && al >= 4
            then if !Clflags.option_Osize then 35 else 51
	    else if !Clflags.option_Osize then 19 else 27)
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let offset_constant cst delta =
  match cst with
  | Cint n ->
      let n' = Int.add n delta in
      if offset_in_range n' then Some (Cint n') else None
  | Csymbol_sda(id, ofs) ->
      Some (Csymbol_sda(id, Int.add ofs delta))
  | _ -> None

let rec expand_builtin_vload_common chunk base offset res =
  match chunk, res with
  | Mint8unsigned, BR(IR res) ->
      emit (Plbz(res, offset, base))
  | Mint8signed, BR(IR res) ->
      emit (Plbz(res, offset, base));
      emit (Pextsb(res, res))
  | Mint16unsigned, BR(IR res) ->
      emit (Plhz(res, offset, base))
  | Mint16signed, BR(IR res) ->
      emit (Plha(res, offset, base))
  | (Mint32 | Many32), BR(IR res) ->
      emit (Plwz(res, offset, base))
  | Mfloat32, BR(FR res) ->
      emit (Plfs(res, offset, base))
  | (Mfloat64 | Many64), BR(FR res) ->
      emit (Plfd(res, offset, base))
  | Mint64, BR_splitlong(BR(IR hi), BR(IR lo)) ->
      begin match offset_constant offset _4 with
      | Some offset' ->
          if hi <> base then begin
            emit (Plwz(hi, offset, base));
            emit (Plwz(lo, offset', base))
          end else begin
            emit (Plwz(lo, offset', base));
            emit (Plwz(hi, offset, base))
          end
      | None ->
          emit (Paddi(GPR11, base, offset));
          expand_builtin_vload_common chunk GPR11 (Cint _0) res
      end
  | _, _ ->
      assert false

let expand_builtin_vload chunk args res =
  match args with
  | [BA(IR addr)] ->
      expand_builtin_vload_common chunk addr (Cint _0) res
  | [BA_addrstack ofs] ->
      if offset_in_range ofs then
        expand_builtin_vload_common chunk GPR1 (Cint ofs) res
      else begin
        emit_addimm GPR11 GPR1 ofs;
        expand_builtin_vload_common chunk GPR11 (Cint _0) res
      end
  | [BA_addrglobal(id, ofs)] ->
      if symbol_is_small_data id ofs then
        expand_builtin_vload_common chunk GPR0 (Csymbol_sda(id, ofs)) res
      else if symbol_is_rel_data id ofs then begin
        emit (Paddis(GPR11, GPR0, Csymbol_rel_high(id, ofs)));
        expand_builtin_vload_common chunk GPR11 (Csymbol_rel_low(id, ofs)) res
      end else begin
        emit (Paddis(GPR11, GPR0, Csymbol_high(id, ofs)));
        expand_builtin_vload_common chunk GPR11 (Csymbol_low(id, ofs)) res
      end
  | _ ->
      assert false

let temp_for_vstore src =
  let rl = AST.params_of_builtin_arg src in
  if not (List.mem (IR GPR11) rl) then GPR11
  else if not (List.mem (IR GPR12) rl) then GPR12
  else GPR10

let expand_builtin_vstore_common chunk base offset src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) ->
      emit (Pstb(src, offset, base))
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
      emit (Psth(src, offset, base))
  | (Mint32 | Many32), BA(IR src) ->
      emit (Pstw(src, offset, base))
  | Mfloat32, BA(FR src) ->
      emit (Pstfs(src, offset, base))
  | (Mfloat64 | Many64), BA(FR src) ->
      emit (Pstfd(src, offset, base))
  | Mint64, BA_splitlong(BA(IR hi), BA(IR lo)) ->
      begin match offset_constant offset _4 with
      | Some offset' ->
          emit (Pstw(hi, offset, base));
          emit (Pstw(lo, offset', base))
      | None ->
          let tmp = temp_for_vstore src in
          emit (Paddi(tmp, base, offset));
          emit (Pstw(hi, Cint _0, tmp));
          emit (Pstw(lo, Cint _4, tmp))
      end
  | _, _ ->
      assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA(IR addr); src] ->
      expand_builtin_vstore_common chunk addr (Cint _0) src
  | [BA_addrstack ofs; src] ->
      if offset_in_range ofs then
        expand_builtin_vstore_common chunk GPR1 (Cint ofs) src
      else begin
        let tmp = temp_for_vstore src in
        emit_addimm tmp GPR1 ofs;
        expand_builtin_vstore_common chunk tmp (Cint _0) src
      end
  | [BA_addrglobal(id, ofs); src] ->
      if symbol_is_small_data id ofs then
        expand_builtin_vstore_common chunk GPR0 (Csymbol_sda(id, ofs)) src
      else if symbol_is_rel_data id ofs then begin
        let tmp = temp_for_vstore src in
        emit (Paddis(tmp, GPR0, Csymbol_rel_high(id, ofs)));
        expand_builtin_vstore_common chunk tmp (Csymbol_rel_low(id, ofs)) src
      end else begin
        let tmp = temp_for_vstore src in
        emit (Paddis(tmp, GPR0, Csymbol_high(id, ofs)));
        expand_builtin_vstore_common chunk tmp (Csymbol_low(id, ofs)) src
      end
  | _ ->
      assert false

(* Handling of varargs *)
let linkregister_offset = ref  _0

let retaddr_offset = ref _0

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
  | "__builtin_mulhw", [BA(IR a1); BA(IR a2)], BR(IR res) ->
      emit (Pmulhw(res, a1, a2))
  | "__builtin_mulhwu", [BA(IR a1); BA(IR a2)], BR(IR res) ->
      emit (Pmulhwu(res, a1, a2))
  | "__builtin_clz", [BA(IR a1)], BR(IR res) ->
      emit (Pcntlzw(res, a1))
  | "__builtin_cmpb",  [BA(IR a1); BA(IR a2)], BR(IR res) ->
      emit (Pcmpb (res,a1,a2))
  | ("__builtin_bswap" | "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
      emit (Pstwu(a1, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plwbrx(res, GPR0, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
      emit (Prlwinm(GPR0, a1, _8, coqint_of_camlint 0x0000FF00l));
      emit (Prlwinm(res, a1, coqint_of_camlint 24l,
                                  coqint_of_camlint 0x000000FFl));
      emit (Por(res, GPR0, res))
  (* Float arithmetic *)
  | "__builtin_fmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmadd(res, a1, a2, a3))
  | "__builtin_fmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmsub(res, a1, a2, a3))
  | "__builtin_fnmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmadd(res, a1, a2, a3))
  | "__builtin_fnmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmsub(res, a1, a2, a3))
  | "__builtin_fabs", [BA(FR a1)], BR(FR res) ->
      emit (Pfabs(res, a1))
  | "__builtin_fsqrt", [BA(FR a1)], BR(FR res) ->
      emit (Pfsqrt(res, a1))
  | "__builtin_frsqrte", [BA(FR a1)], BR(FR res) ->
      emit (Pfrsqrte(res, a1))
  | "__builtin_fres", [BA(FR a1)], BR(FR res) ->
      emit (Pfres(res, a1))
  | "__builtin_fsel", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfsel(res, a1, a2, a3))
  | "__builtin_fcti", [BA(FR a1)], BR(IR res) ->
      emit (Pfctiw(FPR13, a1));
      emit (Pstfdu(FPR13, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plwz(res, Cint _4, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [BA_splitlong(BA(IR ah), BA(IR al))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
      expand_int64_arith (rl = ah) rl (fun rl ->
        emit (Psubfic(rl, al, Cint _0));
        emit (Psubfze(rh, ah)))
  | "__builtin_addl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
      expand_int64_arith (rl = ah || rl = bh) rl (fun rl ->
        emit (Paddc(rl, al, bl));
        emit (Padde(rh, ah, bh)))
  | "__builtin_subl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
      expand_int64_arith (rl = ah || rl = bh) rl (fun rl ->
        emit (Psubfc(rl, bl, al));
        emit (Psubfe(rh, bh, ah)))
  | "__builtin_mull", [BA(IR a); BA(IR b)],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
      expand_int64_arith (rl = a || rl = b) rl (fun rl ->
        emit (Pmullw(rl, a, b));
        emit (Pmulhwu(rh, a, b)))
  (* Memory accesses *)
  | "__builtin_read16_reversed", [BA(IR a1)], BR(IR res) ->
      emit (Plhbrx(res, GPR0, a1))
  | "__builtin_read32_reversed", [BA(IR a1)], BR(IR res) ->
      emit (Plwbrx(res, GPR0, a1))
  | "__builtin_write16_reversed", [BA(IR a1); BA(IR a2)], _ ->
      emit (Psthbrx(a2, GPR0, a1))
  | "__builtin_write32_reversed", [BA(IR a1); BA(IR a2)], _ ->
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
  | "__builtin_lwsync", [], _ ->
      emit (Plwsync)
  | "__builtin_mbar",  [BA_int mo], _ ->
      if not (mo = _0 || mo = _1) then
        raise (Error "the argument of __builtin_mbar must be 0 or 1");
      emit (Pmbar mo)
  | "__builin_mbar",_, _ ->
      raise (Error "the argument of __builtin_mbar must be a constant");
  | "__builtin_trap", [], _ ->
      emit (Ptrap)
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
      expand_builtin_va_start a
  (* Cache control *)
  | "__builtin_dcbf", [BA(IR a1)],_ ->
      emit (Pdcbf (GPR0,a1))
  | "__builtin_dcbi", [BA(IR a1)],_ ->
      emit (Pdcbi (GPR0,a1))
  | "__builtin_icbi", [BA(IR a1)],_ ->
      emit (Picbi(GPR0,a1))
  | "__builtin_dcbtls", [BA (IR a1); BA_int loc],_ ->
      if not ((Int.eq loc _0) || (Int.eq loc _2)) then
        raise (Error "the second argument of __builtin_dcbtls must be 0 or 2");
      emit (Pdcbtls (loc,GPR0,a1))
  | "__builtin_dcbtls",_,_ ->
      raise (Error "the second argument of __builtin_dcbtls must be a constant")
  | "__builtin_icbtls", [BA (IR a1); BA_int loc],_ ->
    if not ((Int.eq loc _0) || (Int.eq loc _2)) then
        raise (Error "the second argument of __builtin_icbtls must be 0 or 2");
      emit (Picbtls (loc,GPR0,a1))
  | "__builtin_icbtls",_,_ ->
      raise (Error "the second argument of __builtin_icbtls must be a constant")
  | "__builtin_prefetch" , [BA (IR a1) ;BA_int rw; BA_int loc],_ ->
      if not (Int.ltu loc _4) then
        raise (Error "the last argument of __builtin_prefetch must be 0, 1 or 2");
      if Int.eq rw _0 then begin
        emit (Pdcbt (loc,GPR0,a1));
      end else if Int.eq rw _1 then begin
        emit (Pdcbtst (loc,GPR0,a1));
      end else
        raise (Error "the second argument of __builtin_prefetch must be 0 or 1")
  | "__builtin_prefetch" ,_,_ ->
      raise (Error "the second and third argument of __builtin_prefetch must be a constant")
  | "__builtin_dcbz",[BA (IR a1)],_ ->
      emit (Pdcbz (GPR0,a1))
  (* Special registers *)
  | "__builtin_get_spr", [BA_int n], BR(IR res) ->
      emit (Pmfspr(res, n))
  | "__builtin_get_spr", _, _ ->
      raise (Error "the argument of __builtin_get_spr must be a constant")
  | "__builtin_set_spr", [BA_int n; BA(IR a1)], _ ->
      emit (Pmtspr(n, a1))
  | "__builtin_set_spr", _, _ ->
      raise (Error "the first argument of __builtin_set_spr must be a constant")
  (* Frame and return address *)
  | "__builtin_call_frame", _,BR (IR res) ->
      let sz = !current_function_stacksize
      and ofs = !linkregister_offset in
      if sz < 0x8000l && sz >= 0l then
        emit (Paddi(res, GPR1, Cint(coqint_of_camlint sz)))
      else
        emit (Plwz(res, Cint ofs, GPR1))
  | "__builtin_return_address",_,BR (IR res) ->
      emit (Plwz (res, Cint! retaddr_offset,GPR1))
  (* Integer selection *)
  | ("__builtin_isel" | "__builtin_uisel"), [BA (IR a1); BA (IR a2); BA (IR a3)],BR (IR res) ->
      if eref then begin
        emit (Pcmpwi (a1,Cint (Int.zero)));
        emit (Pisel (res,a3,a2,CRbit_2))
      end else if a2 = a3 then
        emit (Pmr (res, a2))
      else begin
        (* a1 has type _Bool, hence it is 0 or 1 *)
        emit (Psubfic (GPR0, a1, Cint _0));
        (* r0 = 0xFFFF_FFFF if a1 is true, r0 = 0 if a1 is false *)
        if res <> a3 then begin
          emit (Pand_ (res, a2, GPR0));
          emit (Pandc (GPR0, a3, GPR0))
        end else begin
          emit (Pandc (res, a3, GPR0));
          emit (Pand_ (GPR0, a2, GPR0))
        end;
        emit (Por (res, res, GPR0))
      end
  (* atomic operations *)
  | "__builtin_atomic_exchange", [BA (IR a1); BA (IR a2); BA (IR a3)],_ ->
      emit (Plwz (GPR10,Cint _0,a2));
      emit (Psync);
      let lbl = new_label() in
      emit (Plabel lbl);
      emit (Plwarx (GPR0,GPR0,a1));
      emit (Pstwcx_ (GPR10,GPR0,a1));
      emit (Pbf (CRbit_2,lbl));
      emit (Pisync);
      emit (Pstw (GPR0,Cint _0,a3))
  | "__builtin_atomic_load", [BA (IR a1); BA (IR a2)],_ ->
      let lbl = new_label () in
      emit (Psync);
      emit (Plwz (GPR0,Cint _0,a1));
      emit (Pcmpw (GPR0,GPR0));
      emit (Pbf (CRbit_2,lbl));
      emit (Plabel lbl);
      emit (Pisync);
      emit (Pstw (GPR0,Cint _0, a2))
  | "__builtin_sync_fetch_and_add", [BA (IR a1); BA(IR a2)], BR (IR res) ->
      let lbl = new_label() in
      emit (Psync);
      emit (Plabel lbl);
      emit (Plwarx (res,GPR0,a1));
      emit (Padd (GPR0,res,a2));
      emit (Pstwcx_ (GPR0,GPR0,a1));
      emit (Pbf (CRbit_2, lbl));
      emit (Pisync);
  | "__builtin_atomic_compare_exchange", [BA (IR dst); BA(IR exp); BA (IR des)],  BR (IR res) ->
      let lbls = new_label ()
      and lblneq = new_label ()
      and lblsucc = new_label () in
      emit (Plwz (GPR10,Cint _0,exp));
      emit (Plwz (GPR11,Cint _0,des));
      emit (Psync);
      emit (Plabel lbls);
      emit (Plwarx (GPR0,GPR0,dst));
      emit (Pcmpw (GPR0,GPR10));
      emit (Pbf (CRbit_2,lblneq));
      emit (Pstwcx_ (GPR11,GPR0,dst));
      emit (Pbf (CRbit_2,lbls));
      emit (Plabel lblneq);
      (* Here, CR2 is true if the exchange succeeded, false if it failed *)
      emit (Pisync);
      emit (Pmfcr GPR10);
      emit (Prlwinm (res,GPR10,(Z.of_uint 3),_1));
      (* Update exp with the current value of dst if the exchange failed *)
      emit (Pbt (CRbit_2,lblsucc));
      emit (Pstw (GPR0,Cint _0,exp));
      emit (Plabel lblsucc)
  (* Catch-all *)
  | _ ->
      raise (Error ("unrecognized builtin " ^ name))

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
  | Pallocframe(sz, ofs,retofs) ->
      let variadic = (!current_function).fn_sig.sig_cc.cc_vararg in
      let sz = camlint_of_coqint sz in
      assert (ofs = _0);
      let sz = if variadic then Int32.add sz 96l else sz in
      let adj = Int32.neg sz in
      if adj >= -0x8000l && adj < 0l then
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
      current_function_stacksize := sz;
      linkregister_offset := ofs;
      retaddr_offset := retofs
  | Pbctr sg | Pbctrl sg | Pbl(_, sg) | Pbs(_, sg) ->
      set_cr6 sg;
      emit instr
  | Pfreeframe(sz, ofs) ->
      let variadic = (!current_function).fn_sig.sig_cc.cc_vararg in
      let sz = camlint_of_coqint sz in
      let sz = if variadic then Int32.add sz 96l else sz in
      if sz < 0x8000l && sz >= 0l then
        emit (Paddi(GPR1, GPR1, Cint(coqint_of_camlint sz)))
      else
        emit (Plwz(GPR1, Cint ofs, GPR1))
  | Pfcfi(r1, r2) ->
      assert (Archi.ppc64);
      emit (Pextsw(GPR0, r2));
      emit (Pstdu(GPR0, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plfd(r1, Cint _0, GPR1));
      emit (Pfcfid(r1, r1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  | Pfcfiu(r1, r2) ->
      assert (Archi.ppc64);
      emit (Prldicl(GPR0, r2, _0, coqint_of_camlint 32l));
      emit (Pstdu(GPR0, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plfd(r1, Cint _0, GPR1));
      emit (Pfcfid(r1, r1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  | Pfcti(r1, r2) ->
      emit (Pfctiwz(FPR13, r2));
      emit (Pstfdu(FPR13, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plwz(r1, Cint _4, GPR1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  | Pfctiu(r1, r2) ->
      assert (Archi.ppc64);
      emit (Pfctidz(FPR13, r2));
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
          expand_builtin_inline (camlstring_of_coqstring name) args res
      | EF_vload chunk ->
          expand_builtin_vload chunk args res
      | EF_vstore chunk ->
          expand_builtin_vstore chunk args
      | EF_memcpy(sz, al) ->
          expand_builtin_memcpy (Z.to_int sz) (Z.to_int al) args
      | EF_annot_val(txt, targ) ->
          expand_annot_val txt targ args res
       | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
          emit instr
      | _ ->
          assert false
      end
  | _ ->
      emit instr

(* Translate to the integer identifier of the register as
   the EABI specifies *)

let int_reg_to_dwarf = function
   | GPR0 -> 0  | GPR1 -> 1  | GPR2 -> 2  | GPR3 -> 3
   | GPR4 -> 4  | GPR5 -> 5  | GPR6 -> 6  | GPR7 -> 7
   | GPR8 -> 8  | GPR9 -> 9  | GPR10 -> 10 | GPR11 -> 11
   | GPR12 -> 12 | GPR13 -> 13 | GPR14 -> 14 | GPR15 -> 15
   | GPR16 -> 16 | GPR17 -> 17 | GPR18 -> 18 | GPR19 -> 19
   | GPR20 -> 20 | GPR21 -> 21 | GPR22 -> 22 | GPR23 -> 23
   | GPR24 -> 24 | GPR25 -> 25 | GPR26 -> 26 | GPR27 -> 27
   | GPR28 -> 28 | GPR29 -> 29 | GPR30 -> 30 | GPR31 -> 31

let float_reg_to_dwarf = function
   | FPR0 -> 32  | FPR1 -> 33  | FPR2 -> 34  | FPR3 -> 35
   | FPR4 -> 36  | FPR5 -> 37  | FPR6 -> 38  | FPR7 -> 39
   | FPR8 -> 40  | FPR9 -> 41  | FPR10 -> 42 | FPR11 -> 43
   | FPR12 -> 44 | FPR13 -> 45 | FPR14 -> 46 | FPR15 -> 47
   | FPR16 -> 48 | FPR17 -> 49 | FPR18 -> 50 | FPR19 -> 51
   | FPR20 -> 52 | FPR21 -> 53 | FPR22 -> 54| FPR23 -> 55
   | FPR24 -> 56 | FPR25 -> 57 | FPR26 -> 58 | FPR27 -> 59
   | FPR28 -> 60 | FPR29 -> 61 | FPR30 -> 62 | FPR31 -> 63

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | FR r -> float_reg_to_dwarf r
   | _ -> assert false


let expand_function id fn =
  try
    set_current_function fn;
    if !Clflags.option_g then
      expand_debug id 1 preg_to_dwarf expand_instruction fn.fn_code
    else
      List.iter expand_instruction fn.fn_code;
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
  AST.transform_partial_ident_program expand_fundef p

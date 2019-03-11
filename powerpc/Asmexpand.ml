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

open Camlcoq
open Integers
open AST
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
let _31 = coqint_of_camlint 31l
let _32 = coqint_of_camlint 32l
let _64 = coqint_of_camlint 64l
let _m1 = coqint_of_camlint (-1l)
let _m4 = coqint_of_camlint (-4l)
let _m8 = coqint_of_camlint (-8l)

let _0L = Integers.Int64.zero
let _32L = coqint_of_camlint64 32L
let _64L = coqint_of_camlint64 64L
let _m1L = coqint_of_camlint64 (-1L)
let upper32 = coqint_of_camlint64 0xFFFF_FFFF_0000_0000L
let lower32 = coqint_of_camlint64 0x0000_0000_FFFF_FFFFL

let emit_loadimm r n =
  List.iter emit (Asmgen.loadimm r n [])

let emit_addimm rd rs n =
  List.iter emit (Asmgen.addimm rd rs n [])

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin(EF_annot(kind,txt, [targ]), args, BR_none));
  begin match args, res with
  | [BA(IR src)], BR(IR dst) ->
      if dst <> src then emit (Pmr(dst, src))
  | [BA(FR src)], BR(FR dst) ->
      if dst <> src then emit (Pfmr(dst, src))
  | _, _ ->
      raise (Error "ill-formed __builtin_annot_intval")
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

let expand_volatile_access
       (mk1: ireg -> constant -> unit)
       (mk2: ireg -> ireg -> unit)
       addr temp =
  match addr with
  | BA(IR r) ->
      mk1 r (Cint _0)
  | BA_addrstack ofs ->
      if offset_in_range ofs then
        mk1 GPR1 (Cint ofs)
      else begin
        emit (Paddis(temp, GPR1, Cint (Asmgen.high_s ofs)));
        mk1 temp (Cint (Asmgen.low_s ofs))
      end
  | BA_addrglobal(id, ofs) ->
      if symbol_is_small_data id ofs then
        mk1 GPR0 (Csymbol_sda(id, ofs))
      else if symbol_is_rel_data id ofs then begin
        emit (Paddis(temp, GPR0, Csymbol_rel_high(id, ofs)));
        emit (Paddi(temp, temp, Csymbol_rel_low(id, ofs)));
        mk1 temp (Cint _0)
      end else begin
        emit (Paddis(temp, GPR0, Csymbol_high(id, ofs)));
        mk1 temp (Csymbol_low(id, ofs))
      end
  | BA_addptr(BA(IR r), BA_int n) ->
      if offset_in_range n then
        mk1 r (Cint n)
      else begin
        emit (Paddis(temp, r, Cint (Asmgen.high_s n)));
        mk1 temp (Cint (Asmgen.low_s n))
      end
  | BA_addptr(BA_addrglobal(id, ofs), BA(IR r)) ->
      if symbol_is_small_data id ofs then begin
        emit (Paddi(GPR0, GPR0, Csymbol_sda(id, ofs)));
        mk2 r GPR0
      end else if symbol_is_rel_data id ofs then begin
        emit (Pmr(GPR0, r));
        emit (Paddis(temp, GPR0, Csymbol_rel_high(id, ofs)));
        emit (Paddi(temp, temp, Csymbol_rel_low(id, ofs)));
        mk2 temp GPR0
      end else begin
        emit (Paddis(temp, r, Csymbol_high(id, ofs)));
        mk1 temp (Csymbol_low(id, ofs))
      end
  | BA_addptr(BA(IR r1), BA(IR r2)) ->
      mk2 r1 r2
  | _ ->
      assert false

let offset_constant cst delta =
  match cst with
  | Cint n ->
      let n' = Int.add n delta in
      if offset_in_range n' then Some (Cint n') else None
  | Csymbol_sda(id, ofs) ->
      Some (Csymbol_sda(id, Int.add ofs delta))
  | _ -> None

let expand_load_int64 hi lo base ofs_hi ofs_lo =
  if hi <> base then begin
    emit (Plwz(hi, ofs_hi, base));
    emit (Plwz(lo, ofs_lo, base))
  end else begin
    emit (Plwz(lo, ofs_lo, base));
    emit (Plwz(hi, ofs_hi, base))
  end

let expand_builtin_vload_1 chunk addr res =
  match chunk, res with
  | Mint8unsigned, BR(IR res) ->
      expand_volatile_access
        (fun r c -> emit (Plbz(res, c, r)))
        (fun r1 r2 -> emit (Plbzx(res, r1, r2)))
        addr GPR11
  | Mint8signed, BR(IR res) ->
      expand_volatile_access
        (fun r c -> emit (Plbz(res, c, r)); emit (Pextsb(res, res)))
        (fun r1 r2 -> emit (Plbzx(res, r1, r2)); emit (Pextsb(res, res)))
        addr GPR11
  | Mint16unsigned, BR(IR res) ->
      expand_volatile_access
        (fun r c -> emit (Plhz(res, c, r)))
        (fun r1 r2 -> emit (Plhzx(res, r1, r2)))
        addr GPR11
  | Mint16signed, BR(IR res) ->
      expand_volatile_access
        (fun r c -> emit (Plha(res, c, r)))
        (fun r1 r2 -> emit (Plhax(res, r1, r2)))
        addr GPR11
  | (Mint32 | Many32), BR(IR res) ->
      expand_volatile_access
        (fun r c -> emit (Plwz(res, c, r)))
        (fun r1 r2 -> emit (Plwzx(res, r1, r2)))
        addr GPR11
  | Mfloat32, BR(FR res) ->
      expand_volatile_access
        (fun r c -> emit (Plfs(res, c, r)))
        (fun r1 r2 -> emit (Plfsx(res, r1, r2)))
        addr GPR11
  | (Mfloat64 | Many64), BR(FR res) ->
      expand_volatile_access
        (fun r c -> emit (Plfd(res, c, r)))
        (fun r1 r2 -> emit (Plfdx(res, r1, r2)))
        addr GPR11
  | (Mint64 | Many64), BR(IR res) ->
      expand_volatile_access
        (fun r c -> emit (Pld(res, c, r)))
        (fun r1 r2 -> emit (Pldx(res, r1, r2)))
        addr GPR11
  | Mint64, BR_splitlong(BR(IR hi), BR(IR lo)) ->
      expand_volatile_access
        (fun r c ->
           match offset_constant c _4 with
           | Some c' -> expand_load_int64 hi lo r c c'
           | None ->
               emit (Paddi(GPR11, r, c));
               expand_load_int64 hi lo GPR11 (Cint _0) (Cint _4))
        (fun r1 r2 ->
           emit (Padd(GPR11, r1, r2));
           expand_load_int64 hi lo GPR11 (Cint _0) (Cint _4))
        addr GPR11
  | _, _ ->
      assert false

let expand_builtin_vload chunk args res =
  match args with
  | [addr] -> expand_builtin_vload_1 chunk addr res
  | _ -> assert false

let temp_for_vstore src =
  let rl = AST.params_of_builtin_arg src in
  if not (List.mem (IR GPR11) rl) then GPR11
  else if not (List.mem (IR GPR12) rl) then GPR12
  else GPR10

let expand_store_int64 hi lo base ofs_hi ofs_lo =
  emit (Pstw(hi, ofs_hi, base));
  emit (Pstw(lo, ofs_lo, base))

let expand_builtin_vstore_1 chunk addr src =
  let temp = temp_for_vstore src in
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) ->
      expand_volatile_access
        (fun r c -> emit (Pstb(src, c, r)))
        (fun r1 r2 -> emit (Pstbx(src, r1, r2)))
        addr temp
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
      expand_volatile_access
        (fun r c -> emit (Psth(src, c, r)))
        (fun r1 r2 -> emit (Psthx(src, r1, r2)))
        addr temp
  | (Mint32 | Many32), BA(IR src) ->
      expand_volatile_access
        (fun r c -> emit (Pstw(src, c, r)))
        (fun r1 r2 -> emit (Pstwx(src, r1, r2)))
        addr temp
  | Mfloat32, BA(FR src) ->
      expand_volatile_access
        (fun r c -> emit (Pstfs(src, c, r)))
        (fun r1 r2 -> emit (Pstfsx(src, r1, r2)))
        addr temp
  | (Mfloat64 | Many64), BA(FR src) ->
      expand_volatile_access
        (fun r c -> emit (Pstfd(src, c, r)))
        (fun r1 r2 -> emit (Pstfdx(src, r1, r2)))
        addr temp
  | (Mint64 | Many64), BA(IR src) ->
      expand_volatile_access
        (fun r c -> emit (Pstd(src, c, r)))
        (fun r1 r2 -> emit (Pstdx(src, r1, r2)))
        addr temp
  | Mint64, BA_splitlong(BA(IR hi), BA(IR lo)) ->
      expand_volatile_access
        (fun r c ->
           match offset_constant c _4 with
           | Some c' -> expand_store_int64 hi lo r c c'
           | None ->
               emit (Paddi(temp, r, c));
               expand_store_int64 hi lo temp (Cint _0) (Cint _4))
        (fun r1 r2 ->
           emit (Padd(temp, r1, r2));
           expand_store_int64 hi lo temp (Cint _0) (Cint _4))
        addr temp
  | _, _ ->
      assert false

let expand_builtin_vstore chunk args =
  match args with
  | [addr; src] -> expand_builtin_vstore_1 chunk addr src
  | _ -> assert false

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
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let (ir, fr, ofs) =
    next_arg_locations 0 0 0 (get_current_function_args ()) in
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

(* Expansion of integer conditional moves (__builtin_*sel) *)
(* The generated code works equally well with 32-bit integer registers
   and with 64-bit integer registers. *)

let expand_integer_cond_move a1 a2 a3 res =
  if a2 = a3 then
    emit (Pmr (res, a2))
  else if eref then begin
    emit (Pcmpwi (a1,Cint (Int.zero)));
    emit (Pisel (res,a3,a2,CRbit_2))
  end else begin
    (* a1 has type _Bool, hence it is 0 or 1 *)
    emit (Psubfic (GPR0, a1, Cint _0));
    (* r0 = -1 (all ones) if a1 is true, r0 = 0 if a1 is false *)
    if res <> a3 then begin
      emit (Pand_ (res, a2, GPR0));
      emit (Pandc (GPR0, a3, GPR0))
    end else begin
      emit (Pandc (res, a3, GPR0));
      emit (Pand_ (GPR0, a2, GPR0))
    end;
    emit (Por (res, res, GPR0))
  end

(* Convert integer constant into GPR with corresponding number *)
let int_to_int_reg = function
   | 0 -> Some GPR0  | 1 -> Some GPR1  | 2 -> Some GPR2  | 3 -> Some GPR3
   | 4 -> Some GPR4  | 5 -> Some GPR5  | 6 -> Some GPR6  | 7 -> Some GPR7
   | 8 -> Some GPR8  | 9 -> Some GPR9  | 10 -> Some GPR10 | 11 -> Some GPR11
   | 12 -> Some GPR12 | 13 -> Some GPR13 | 14 -> Some GPR14 | 15 -> Some GPR15
   | 16 -> Some GPR16 | 17 -> Some GPR17 | 18 -> Some GPR18 | 19 -> Some GPR19
   | 20 -> Some GPR20 | 21 -> Some GPR21 | 22 -> Some GPR22 | 23 -> Some GPR23
   | 24 -> Some GPR24 | 25 -> Some GPR25 | 26 -> Some GPR26 | 27 -> Some GPR27
   | 28 -> Some GPR28 | 29 -> Some GPR29 | 30 -> Some GPR30 | 31 -> Some GPR31
   | _ -> None


(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  (* Can use as temporaries: GPR0, FPR13 *)
  match name, args, res with
  (* Integer arithmetic *)
  | "__builtin_mulhw", [BA(IR a1); BA(IR a2)], BR(IR res) ->
      emit (Pmulhw(res, a1, a2))
  | "__builtin_mulhwu", [BA(IR a1); BA(IR a2)], BR(IR res) ->
      emit (Pmulhwu(res, a1, a2))
  | "__builtin_mulhd", [BA(IR a1); BA(IR a2)], BR(IR res) ->
      if Archi.ppc64 then
        emit (Pmulhd(res, a1, a2))
      else
        raise (Error "__builtin_mulhd is only supported for PPC64 targets")
  | "__builtin_mulhdu", [BA(IR a1); BA(IR a2)], BR(IR res) ->
      if Archi.ppc64 then
        emit (Pmulhdu(res, a1, a2))
      else
        raise (Error "__builtin_mulhdu is only supported for PPC64 targets")
  | ("__builtin_clz" | "__builtin_clzl"), [BA(IR a1)], BR(IR res) ->
      emit (Pcntlzw(res, a1))
  | "__builtin_clzll", [BA(IR a1)], BR(IR res) ->
      emit (Pcntlzd(res, a1))
  | "__builtin_clzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
      let lbl = new_label () in
      emit (Pcntlzw(GPR0, al));
      emit (Pcntlzw(res, ah));
      (* less than 32 bits zero? *)
      emit (Pcmpwi (res, Cint _32));
      emit (Pbf (CRbit_2, lbl));
      (* high bits all zero, count bits in low word and increment by 32 *)
      emit (Padd(res, res, GPR0));
      emit (Plabel lbl)
  | ("__builtin_ctz" | "__builtin_ctzl"), [BA(IR a1)], BR(IR res) ->
      emit (Paddi(GPR0, a1, Cint _m1));   (* tmp := x-1 *)
      emit (Pandc(res, GPR0, a1));        (* res := tmp & ~(x) *)
      emit (Pcntlzw(res, res));           (* res := #leading zeros *)
      emit (Psubfic(res, res, Cint _32))  (* res := 32 - #leading zeros *)
  | "__builtin_ctzll", [BA(IR a1)], BR(IR res) ->
      emit (Paddi64(GPR0, a1, _m1L));     (* tmp := x-1 *)
      emit (Pandc(res, GPR0, a1));        (* res := tmp & ~(x) *)
      emit (Pcntlzd(res, res));           (* res := #leading zeros *)
      emit (Psubfic64(res, res, _64L))    (* res := 64 - #leading zeros *)
  | "__builtin_ctzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
      let lbl1 = new_label () in
      let lbl2 = new_label () in
      (* low word equal to zero? *)
      emit (Pcmpwi (al, Cint _0));
      emit (Pbf (CRbit_2, lbl1));
      (* low word is zero, count trailing zeros in high word and increment by 32 *)
      emit (Paddi(GPR0, ah, Cint _m1));
      emit (Pandc(res, GPR0, ah));
      emit (Pcntlzw(res, res));
      emit (Psubfic(res, res, Cint _64));
      emit (Pb lbl2);
      (* count trailing zeros in low word *)
      emit (Plabel lbl1);
      emit (Paddi(GPR0, al, Cint _m1));
      emit (Pandc(res, GPR0, al));
      emit (Pcntlzw(res, res));
      emit (Psubfic(res, res, Cint _32));
      emit (Plabel lbl2)
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
  | "__builtin_read64_reversed", [BA(IR a1)], BR(IR res) ->
      if Archi.ppc64 then
        emit (Pldbrx(res, GPR0, a1))
      else
        raise (Error "__builtin_read64_reversed is only supported for PPC64 targets")
  | "__builtin_write16_reversed", [BA(IR a1); BA(IR a2)], _ ->
      emit (Psthbrx(a2, GPR0, a1))
  | "__builtin_write32_reversed", [BA(IR a1); BA(IR a2)], _ ->
      emit (Pstwbrx(a2, GPR0, a1))
  | "__builtin_write64_reversed", [BA(IR a1); BA(IR a2)], _ ->
      if Archi.ppc64 then
        emit (Pstdbrx(a2, GPR0, a1))
      else
        raise (Error "__builtin_write64_reversed is only supported for PPC64 targets")
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
  | "__builtin_mbar", [BA_int mo], _ ->
      if not (mo = _0 || mo = _1) then
        raise (Error "the argument of __builtin_mbar must be 0 or 1");
      emit (Pmbar mo)
  | "__builtin_mbar", _, _ ->
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
  (* Special registers in 32bit hybrid mode *)
  | "__builtin_get_spr64", [BA_int n], BR(IR r) ->
      if Archi.ppc64 then
        emit (Pmfspr(r, n))
      else
        raise (Error "__builtin_get_spr64 is only supported for PPC64 targets")
  | "__builtin_get_spr64", _, _ ->
      if Archi.ppc64 then
        raise (Error "the argument of __builtin_get_spr64 must be a constant")
      else
        raise (Error "__builtin_get_spr64 is only supported for PPC64 targets")
  | "__builtin_set_spr64", [BA_int n; BA(IR a)], _ ->
      if Archi.ppc64 then
        emit (Pmtspr(n, a))
      else
        raise (Error "__builtin_set_spr64 is only supported for PPC64 targets")
  | "__builtin_set_spr64", _, _ ->
      if Archi.ppc64 then
        raise (Error "the first argument of __builtin_set_spr64 must be a constant")
      else
        raise (Error "__builtin_set_spr64 is only supported for PPC64 targets")
  (* Move registers *)
  | "__builtin_mr", [BA_int dst; BA_int src], _ ->
      (match int_to_int_reg (Z.to_int dst), int_to_int_reg (Z.to_int src) with
       | Some dst, Some src -> emit (Pori (dst, src, Cint _0))
       | _, _ -> raise (Error "the arguments of __builtin_mr must be in the range of 0..31"))
  | "__builtin_mr", _, _ ->
      raise (Error "the arguments of __builtin_mr must be constants")
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
  | ("__builtin_bsel" | "__builtin_isel" | "__builtin_uisel"), [BA (IR a1); BA (IR a2); BA (IR a3)],BR (IR res) ->
      expand_integer_cond_move a1 a2 a3 res
  | ("__builtin_isel64" | "__builtin_uisel64"), [BA (IR a1); BA (IR a2); BA (IR a3)],BR (IR res) ->
    if Archi.ppc64 then
      expand_integer_cond_move a1 a2 a3 res
    else
      raise (Error (name ^" is only supported for PPC64 targets"))
  (* no operation *)
  | "__builtin_nop", [], _ ->
      emit (Pori (GPR0, GPR0, Cint _0))
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
      let variadic = is_current_function_variadic () in
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
  | Pextzw(r1, r2) ->
      emit (Prldinm(r1, r2, _0L, lower32))
  | Pfreeframe(sz, ofs) ->
      let variadic = is_current_function_variadic () in
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
  | Pfcfl(r1, r2) ->
      assert (Archi.ppc64);
      emit (Pstdu(r2, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Plfd(r1, Cint _0, GPR1));
      emit (Pfcfid(r1, r1));
      emit (Paddi(GPR1, GPR1, Cint _8));
      emit (Pcfi_adjust _m8)
  | Pfcfiu(r1, r2) ->
      assert (Archi.ppc64);
      emit (Prldicl(GPR0, r2, _0, _32));
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
  | Pfctid(r1, r2) ->
      assert (Archi.ppc64);
      emit (Pfctidz(FPR13, r2));
      emit (Pstfdu(FPR13, Cint _m8, GPR1));
      emit (Pcfi_adjust _8);
      emit (Pld(r1, Cint _0, GPR1));
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
  | Plmake(r1, rhi, rlo) ->
      if r1 = rlo then
        emit (Prldimi(r1, rhi, _32L, upper32))
      else if r1 = rhi then begin
        emit (Prldinm(r1, rhi, _32L, upper32));
        emit (Prldimi(r1, rlo, _0L, lower32))
      end else begin
        emit (Pmr(r1, rlo));
        emit (Prldimi(r1, rhi, _32L, upper32))
      end
  | Pllo r1 ->
      ()   (* no computational content *)
  | Plhi(r1, r2) ->
      emit (Prldinm(r1, r2, _32L, lower32))
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
      | EF_annot_val(kind,txt, targ) ->
          expand_annot_val kind txt targ args res
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
    expand id 1 preg_to_dwarf expand_instruction fn.fn_code;
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

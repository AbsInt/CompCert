(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(* Simple functions to serialize powerpc Asm to JSON *)

open Asm
open AST
open BinNums
open C2C
open Camlcoq
open Json
open Printf
open Sections

let p_reg oc t n =
  let s = sprintf "%s%s" t n in
  p_jsingle_object oc "Register" p_jstring s

let p_ireg oc reg =
  p_reg oc "r" (TargetPrinter.int_reg_name reg)


let p_freg oc reg =
  p_reg oc "f" (TargetPrinter.float_reg_name reg)

let p_atom oc a = p_jstring oc (extern_atom a)

let p_atom_constant oc a = p_jsingle_object oc "Atom" p_atom a

let p_int oc i = fprintf oc "%ld" (camlint_of_coqint i)
let p_int64 oc i = fprintf oc "%Ld" (camlint64_of_coqint i)
let p_float32 oc f = fprintf oc "%ld" (camlint_of_coqint (Floats.Float32.to_bits f))
let p_float64 oc f = fprintf oc "%Ld" (camlint64_of_coqint (Floats.Float.to_bits f))
let p_z oc z = fprintf oc "%s" (Z.to_string z)

let p_int_constant oc i = p_jsingle_object oc "Integer" p_int i
let p_float64_constant oc f = p_jsingle_object oc "Float" p_float64 f
let p_float32_constant oc f = p_jsingle_object oc "Float" p_float32 f

let p_sep oc = fprintf oc ","

let p_constant oc c =
  let p_symbol oc (i,c) =
    output_string oc "{";
    p_jmember oc "Name" p_atom i;
    p_sep oc;
    p_jmember oc "Offset" p_int c;
    output_string oc "}" in
  match c with
  | Cint i ->  p_int_constant oc i
  | Csymbol_low (i,c) ->
      p_jsingle_object oc "Symbol_low" p_symbol (i,c)
  | Csymbol_high (i,c) ->
      p_jsingle_object oc "Symbol_high" p_symbol (i,c)
  | Csymbol_sda (i,c) ->
      p_jsingle_object oc "Symbol_sda" p_symbol (i,c)
  | Csymbol_rel_low (i,c) ->
      p_jsingle_object oc "Symbol_rel_low" p_symbol (i,c)
  | Csymbol_rel_high (i,c) ->
      p_jsingle_object oc "Symbol_rel_high" p_symbol (i,c)

let p_crbit oc c =
  p_jsingle_object oc "CRbit" p_jint (TargetPrinter.num_crbit c)

let p_label oc l =
  p_jsingle_object oc "Label" p_jint32 (P.to_int32 l)

type instruction_arg =
  | Ireg of ireg
  | Freg of freg
  | Constant of constant
  | Long of Integers.Int.int
  | Id
  | Crbit of crbit
  | ALabel of positive
  | Float32 of Floats.float32
  | Float64 of Floats.float
  | Atom of positive

let id = ref 0

let next_id () =
  let tmp = !id in
  incr id;
  tmp

let reset_id () =
  id := 0

let p_arg oc = function
  | Ireg ir -> p_ireg oc ir
  | Freg fr -> p_freg oc fr
  | Constant c -> p_constant oc c
  | Long i ->  p_jsingle_object oc "Integer" p_int64 i
  | Id -> let i = next_id () in
    p_jsingle_object oc "Integer" (fun oc i -> fprintf oc "%d" i) i
  | Crbit cr -> p_crbit oc cr
  | ALabel lbl -> p_label oc lbl
  | Float32 f -> p_float32_constant oc f
  | Float64 f  -> p_float64_constant oc f
  | Atom a -> p_atom_constant oc a

let p_instruction oc ic =
  let p_args oc l= fprintf oc "%a:%a" p_jstring "Args" (p_jarray p_arg) l
  and inst_name oc s = p_jmember oc  "Instruction Name" p_jstring s in
  let first = ref true in
  let sep oc = if !first then first := false else output_string oc ", " in
  let instruction n args = fprintf oc "\n%t{%a,%a}" sep inst_name n p_args args in
  let instruction = function
  | Padd (ir1,ir2,ir3)
  | Padd64 (ir1,ir2,ir3) -> instruction "Padd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Paddc (ir1,ir2,ir3) -> instruction "Paddc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Padde (ir1,ir2,ir3) -> instruction "Padde" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Paddi (ir1,ir2,c) -> instruction "Paddi" [Ireg ir1; Ireg ir2; Constant c]
  | Paddi64 (ir1,ir2,n) -> instruction "Paddi" [Ireg ir1; Ireg ir2; Constant (Cint n)] (* FIXME, ugly, immediates are int64 but always fit into 16bits *)
  | Paddic  (ir1,ir2,c) -> instruction "Paddic" [Ireg ir1; Ireg ir2; Constant c]
  | Paddis  (ir1,ir2,c) -> instruction "Paddis" [Ireg ir1; Ireg ir2; Constant c]
  | Paddis64 (ir1,ir2,n) -> instruction "Paddis" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Paddze (ir1,ir2)
  | Paddze64 (ir1,ir2) -> instruction "Paddze" [Ireg ir1; Ireg ir2]
  | Pallocframe _ -> assert false (* Should not occur *)
  | Pand_ (ir1,ir2,ir3)
  | Pand_64 (ir1,ir2,ir3) -> instruction "Pand_" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pandc (ir1,ir2,ir3) -> instruction "Pandc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pandi_ (ir1,ir2,c) -> instruction "Pandi_" [Ireg ir1; Ireg ir2; Constant c]
  | Pandi_64 (ir1,ir2,n) -> instruction "Pandi_" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Pandis_ (ir1,ir2,c) -> instruction "Pandis_" [Ireg ir1; Ireg ir2; Constant c]
  | Pandis_64 (ir1,ir2,n) -> instruction "Pandis_" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Pb l -> instruction "Pb" [ALabel l]
  | Pbctr s -> instruction "Pbctr" []
  | Pbctrl s -> instruction "Pbctrl" []
  | Pbdnz l -> instruction "Pbdnz" [ALabel l]
  | Pbf (cr,l) -> instruction "Pbf" [Crbit cr; ALabel l]
  | Pbl (i,s) -> instruction "Pbl" [Atom i]
  | Pbs (i,s) -> instruction "Pbs" [Atom i]
  | Pblr -> instruction "Pblr" []
  | Pbt (cr,l) ->  instruction "Pbt" [Crbit cr; ALabel l]
  | Pbtbl (i,lb) -> instruction "Pbtbl" ((Ireg i)::(List.map (fun a -> ALabel a) lb))
  | Pcmpb (ir1,ir2,ir3) -> instruction "Pcmpb" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pcmpld (ir1,ir2) -> instruction "Pcmpld" [Ireg ir1; Ireg ir2]
  | Pcmpldi (ir,n) -> instruction "Pcmpldi" [Ireg ir; Constant (Cint n)]
  | Pcmplw (ir1,ir2) -> instruction "Pcmplw" [Ireg ir1; Ireg ir2]
  | Pcmplwi (ir,c) -> instruction "Pcmplwi" [Ireg ir; Constant c]
  | Pcmpd (ir1,ir2) -> instruction "Pcmpd" [Ireg ir1; Ireg ir2]
  | Pcmpdi (ir,n) -> instruction "Pcmpdi" [Ireg ir; Constant (Cint n)]
  | Pcmpw (ir1,ir2) -> instruction "Pcmpw" [Ireg ir1; Ireg ir2]
  | Pcmpwi (ir,c) -> instruction "Pcmpwi" [Ireg ir; Constant c]
  | Pcntlzd (ir1,ir2) -> instruction "Pcntlzd" [Ireg ir1; Ireg ir2]
  | Pcntlzw (ir1,ir2) -> instruction "Pcntlzw" [Ireg ir1; Ireg ir2]
  | Pcreqv (cr1,cr2,cr3) -> instruction "Pcreqv" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pcror (cr1,cr2,cr3) -> instruction "Pcror" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pcrxor (cr1,cr2,cr3) -> instruction "Pcrxor" [Crbit cr1; Crbit cr2; Crbit cr3]
  | Pdcbf (ir1,ir2) -> instruction "Pdcbf" [Ireg ir1; Ireg ir2]
  | Pdcbi (ir1,ir2) -> instruction "Pdcbi" [Ireg ir1; Ireg ir2]
  | Pdcbt (n,ir1,ir2) -> instruction "Pdcbt" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbtst (n,ir1,ir2) -> instruction "Pdcbtst" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbtls (n,ir1,ir2) ->  instruction "Pdcbtls" [Constant (Cint n); Ireg ir1; Ireg ir2]
  | Pdcbz (ir1,ir2) -> instruction "Pdcbz" [Ireg ir1; Ireg ir2]
  | Pdivw (ir1,ir2,ir3) -> instruction "Pdivw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pdivd (ir1,ir2,ir3) -> instruction "Pdivd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pdivwu (ir1,ir2,ir3) -> instruction "Pdivwu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pdivdu (ir1,ir2,ir3) -> instruction "Pdivdu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Peieio -> instruction "Peieio" []
  | Peqv (ir1,ir2,ir3) -> instruction "Peqv" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pextsb (ir1,ir2) -> instruction "Pextsb" [Ireg ir1; Ireg ir2]
  | Pextsh (ir1,ir2) -> instruction "Pextsh" [Ireg ir1; Ireg ir2]
  | Pextsw (ir1,ir2) -> instruction "Pextsw" [Ireg ir1; Ireg ir2]
  | Pextzw (ir1,ir2) -> assert false (* Should not occur *)
  | Pfreeframe (c,i) -> assert false (* Should not occur *)
  | Pfabs (fr1,fr2)
  | Pfabss (fr1,fr2) -> instruction "Pfabs" [Freg fr1; Freg fr2]
  | Pfadd (fr1,fr2,fr3) -> instruction "Pfadd" [Freg fr1; Freg fr2; Freg fr3]
  | Pfadds (fr1,fr2,fr3) -> instruction "Pfadds" [Freg fr1; Freg fr2; Freg fr3]
  | Pfcmpu (fr1,fr2) -> instruction "Pfcmpu" [Freg fr1; Freg fr2]
  | Pfcfi (ir,fr)
  | Pfcfl (ir,fr) -> assert false (* Should not occur *)
  | Pfcfid (fr1,fr2) -> instruction "Pfcfid" [Freg fr1; Freg fr2]
  | Pfcfiu _ (* Should not occur *)
  | Pfcti _ (* Should not occur *)
  | Pfctiu _ (* Should not occur *)
  | Pfctid _ -> assert false (* Should not occur *)
  | Pfctidz (fr1,fr2) -> instruction "Pfctidz" [Freg fr1; Freg fr2]
  | Pfctiw (fr1,fr2) -> instruction "Pfctiw" [Freg fr1; Freg fr2]
  | Pfctiwz (fr1,fr2) -> instruction "Pfctiwz" [Freg fr1; Freg fr2]
  | Pfdiv (fr1,fr2,fr3) -> instruction "Pfdiv" [Freg fr1; Freg fr2; Freg fr3]
  | Pfdivs (fr1,fr2,fr3) -> instruction "Pfdivs" [Freg fr1; Freg fr2; Freg fr3]
  | Pfmake (fr,ir1,ir2) -> assert false (* Should not occur *)
  | Pfmr (fr1,fr2) -> instruction "Pfmr" [Freg fr1; Freg fr2]
  | Pfmul (fr1,fr2,fr3) -> instruction "Pfmul" [Freg fr1; Freg fr2; Freg fr3]
  | Pfmuls(fr1,fr2,fr3) -> instruction "Pfmuls" [Freg fr1; Freg fr2; Freg fr3]
  | Pfneg (fr1,fr2)
  | Pfnegs (fr1,fr2) -> instruction "Pfneg" [Freg fr1; Freg fr2]
  | Pfrsp (fr1,fr2) -> instruction "Pfrsp" [Freg fr1; Freg fr2]
  | Pfxdp (fr1,fr2) -> assert false (* Should not occur *)
  | Pfsub (fr1,fr2,fr3) -> instruction "Pfsub" [Freg fr1; Freg fr2; Freg fr3]
  | Pfsubs (fr1,fr2,fr3) ->  instruction "Pfsubs" [Freg fr1; Freg fr2; Freg fr3]
  | Pfmadd (fr1,fr2,fr3,fr4) -> instruction "Pfmadd" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pfmsub (fr1,fr2,fr3,fr4) ->  instruction "Pfmsub" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pfnmadd (fr1,fr2,fr3,fr4) -> instruction "Pfnmadd" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pfnmsub (fr1,fr2,fr3,fr4) -> instruction "Pfnmsub" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pfsqrt (fr1,fr2) -> instruction "Pfsqrt" [Freg fr1; Freg fr2]
  | Pfrsqrte (fr1,fr2) -> instruction "Pfrsqrte" [Freg fr1; Freg fr2]
  | Pfres (fr1,fr2) -> instruction "Pfres" [Freg fr1; Freg fr2]
  | Pfsel (fr1,fr2,fr3,fr4) -> instruction "Pfsel" [Freg fr1; Freg fr2; Freg fr3; Freg fr4]
  | Pisel (ir1,ir2,ir3,cr) ->  instruction "Pisel" [Ireg ir1; Ireg ir2; Ireg ir3; Crbit cr]
  | Picbi (ir1,ir2) -> instruction "Picbi" [Ireg ir1; Ireg ir2]
  | Picbtls (n,ir1,ir2) -> instruction "Picbtls" [Constant (Cint n);Ireg ir1; Ireg ir2]
  | Pisync -> instruction "Pisync" []
  | Plwsync -> instruction "Plwsync" []
  | Plbz (ir1,c,ir2) -> instruction "Plbz" [Ireg ir1; Constant c; Ireg ir2]
  | Plbzx (ir1,ir2,ir3) -> instruction "Plbzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pld (ir1,c,ir2)
  | Pld_a (ir1,c,ir2) -> instruction "Pld" [Ireg ir1; Constant c; Ireg ir2]
  | Pldx (ir1,ir2,ir3)
  | Pldx_a (ir1,ir2,ir3) -> instruction "Pldx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plfd (fr,c,ir)
  | Plfd_a (fr,c,ir) -> instruction "Plfd" [Freg fr; Constant c; Ireg ir]
  | Plfdx (fr,ir1,ir2)
  | Plfdx_a (fr,ir1,ir2) -> instruction "Plfdx" [Freg fr; Ireg ir1; Ireg ir2]
  | Plfs (fr,c,ir) -> instruction "Plfs" [Freg fr; Constant c; Ireg ir]
  | Plfsx  (fr,ir1,ir2) -> instruction "Plfsx" [Freg fr; Ireg ir1; Ireg ir2]
  | Plha (ir1,c,ir2) -> instruction "Plha" [Ireg ir1; Constant c; Ireg ir2]
  | Plhax (ir1,ir2,ir3) -> instruction "Plhax" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plhbrx (ir1,ir2,ir3) -> instruction "Plhbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plhz (ir1,c,ir2) -> instruction "Plhz" [Ireg ir1; Constant c; Ireg ir2]
  | Plhzx (ir1,ir2,ir3) -> instruction "Plhzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pldi (ir,c) -> instruction "Pldi" [Ireg ir; Long c] (* FIXME Cint is too small, we need Clong *)
  | Plmake _ (* Should not occur *)
  | Pllo _ (* Should not occur *)
  | Plhi _ -> assert false (* Should not occur *)
  | Plfi (fr,fc) -> instruction "Plfi" [Freg fr; Float64 fc]
  | Plfis (fr,fc) -> instruction "Plfis" [Freg fr; Float32 fc]
  | Plwz (ir1,c,ir2)
  | Plwz_a (ir1,c,ir2) -> instruction "Plwz" [Ireg ir1;Constant c; Ireg ir2]
  | Plwzu (ir1,c,ir2) -> instruction "Plwzu" [Ireg ir1; Constant c; Ireg ir2]
  | Plwzx (ir1,ir2,ir3)
  | Plwzx_a (ir1,ir2,ir3) -> instruction "Plwzx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plwarx (ir1,ir2,ir3) -> instruction "Plwarx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Plwbrx (ir1,ir2,ir3) -> instruction "Plwbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmbar c -> instruction "Pmbar" [Constant (Cint c)]
  | Pmfcr ir -> instruction "Pmfcr" [Ireg ir]
  | Pmfcrbit (ir,crb) -> assert false (* Should not occur *)
  | Pmflr ir -> instruction "Pmflr" [Ireg ir]
  | Pmr (ir1,ir2) -> instruction "Pmr" [Ireg ir1; Ireg ir2]
  | Pmtctr ir -> instruction "Pmtctr" [Ireg ir]
  | Pmtlr ir -> instruction "Pmtlr" [Ireg ir]
  | Pmfspr(ir, n) -> instruction "Pmfspr" [Ireg ir; Constant (Cint n)]
  | Pmtspr(n, ir) -> instruction "Pmtspr" [Constant (Cint n); Ireg ir]
  | Pmulhd (ir1,ir2,ir3) -> instruction "Pmulhd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhdu (ir1,ir2,ir3) -> instruction "Pmulhdu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulld (ir1,ir2,ir3) -> instruction "Pmulld" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulli (ir1,ir2,c) -> instruction "Pmulli" [Ireg ir1; Ireg ir2; Constant c]
  | Pmullw (ir1,ir2,ir3) -> instruction "Pmullw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhw (ir1,ir2,ir3) -> instruction "Pmulhw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhwu (ir1,ir2,ir3) -> instruction "Pmulhwu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pnand (ir1,ir2,ir3) -> instruction "Pnand" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pnor (ir1,ir2,ir3)
  | Pnor64 (ir1,ir2,ir3) -> instruction "Pnor" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Por (ir1,ir2,ir3)
  | Por64 (ir1,ir2,ir3) -> instruction "Por" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Porc (ir1,ir2,ir3) -> instruction "Porc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pori (ir1,ir2,c) -> instruction "Pori" [Ireg ir1; Ireg ir2; Constant c]
  | Pori64 (ir1,ir2,n) -> instruction "Pori" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Poris (ir1,ir2,c) -> instruction "Poris" [Ireg ir1; Ireg ir2; Constant c]
  | Poris64 (ir1,ir2,n) -> instruction "Poris" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Prldicl (ir1,ir2,ic1,ic2) -> instruction "Prldicl" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Prldinm (ir1,ir2,ic1,ic2) -> instruction "Prldinm" [Ireg ir1; Ireg ir2; Long ic1; Long ic2]
  | Prldimi  (ir1,ir2,ic1,ic2) ->instruction "Prldimi" [Ireg ir1; Ireg ir2; Long ic1; Long ic2]
  | Prlwinm (ir1,ir2,ic1,ic2) -> instruction "Prlwinm" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Prlwimi  (ir1,ir2,ic1,ic2) ->instruction "Prlwimi" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Psld (ir1,ir2,ir3) -> instruction "Psld" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pslw (ir1,ir2,ir3) -> instruction "Pslw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psrad (ir1,ir2,ir3) -> instruction "Psrad" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psradi  (ir1,ir2,ic) -> instruction "Psradi" [Ireg ir1; Ireg ir2; Constant (Cint ic)]
  | Psraw (ir1,ir2,ir3) -> instruction "Psraw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psrawi  (ir1,ir2,ic) -> instruction "Psrawi" [Ireg ir1; Ireg ir2; Constant (Cint ic)]
  | Psrd (ir1,ir2,ir3) -> instruction "Psrd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psrw (ir1,ir2,ir3) -> instruction "Psrw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstb (ir1,c,ir2) -> instruction "Pstb" [Ireg ir1; Constant c; Ireg ir2]
  | Pstbx (ir1,ir2,ir3) -> instruction "Pstbx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstd (ir1,c,ir2)
  | Pstd_a (ir1,c,ir2) -> instruction "Pstd" [Ireg ir1; Constant c; Ireg ir2]
  | Pstdx (ir1,ir2,ir3)
  | Pstdx_a (ir1,ir2,ir3) -> instruction "Pstdx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstdu (ir1,c,ir2) -> instruction "Pstdu" [Ireg ir1; Constant c; Ireg ir2]
  | Pstfd (fr,c,ir)
  | Pstfd_a (fr,c,ir) -> instruction "Pstfd" [Freg fr; Constant c; Ireg ir]
  | Pstfdu (fr,c,ir) -> instruction "Pstfdu" [Freg fr; Constant c; Ireg ir]
  | Pstfdx (fr,ir1,ir2)
  | Pstfdx_a (fr,ir1,ir2) -> instruction "Pstfdx" [Freg fr; Ireg ir1; Ireg ir2]
  | Pstfs (fr,c,ir) -> instruction "Pstfs" [Freg fr; Constant c; Ireg ir]
  | Pstfsx (fr,ir1,ir2) -> instruction "Pstfsx" [Freg fr; Ireg ir1; Ireg ir2]
  | Psth (ir1,c,ir2) -> instruction "Psth"  [Ireg ir1; Constant c; Ireg ir2]
  | Psthx (ir1,ir2,ir3) -> instruction "Psthx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psthbrx (ir1,ir2,ir3) -> instruction "Psthbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstw (ir1,c,ir2)
  | Pstw_a (ir1,c,ir2) -> instruction "Pstw" [Ireg ir1; Constant c; Ireg ir2]
  | Pstwu (ir1,c,ir2) -> instruction "Pstwu" [Ireg ir1; Constant c; Ireg ir2]
  | Pstwx (ir1,ir2,ir3)
  | Pstwx_a (ir1,ir2,ir3) -> instruction "Pstwx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwux (ir1,ir2,ir3) -> instruction "Pstwux" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwbrx (ir1,ir2,ir3) -> instruction "Pstwbrx" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstwcx_ (ir1,ir2,ir3) -> instruction "Pstwcx_" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfc (ir1,ir2,ir3)
  | Psubfc64 (ir1,ir2,ir3) -> instruction "Psubfc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfe (ir1,ir2,ir3) -> instruction "Psubfe" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfze (ir1,ir2) -> instruction "Psubfze" [Ireg ir1; Ireg ir2]
  | Psubfic (ir1,ir2,c) -> instruction "Psubfic" [Ireg ir1; Ireg ir2; Constant c]
  | Psubfic64 (ir1,ir2,n) -> instruction "Psubfic" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Psync -> instruction "Psync" []
  | Ptrap -> instruction "Ptrap" []
  | Pxor (ir1,ir2,ir3)
  | Pxor64 (ir1,ir2,ir3) -> instruction "Pxor" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pxori (ir1,ir2,c) -> instruction "Pxori" [Ireg ir1; Ireg ir2; Constant c]
  | Pxori64 (ir1,ir2,n) -> instruction "Pxori" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Pxoris (ir1,ir2,c) -> instruction "Pxoris" [Ireg ir1; Ireg ir2; Constant c]
  | Pxoris64 (ir1,ir2,n) -> instruction "Pxoris" [Ireg ir1; Ireg ir2; Constant (Cint n)]
  | Plabel l -> instruction "Plabel" [ALabel l]
  | Pbuiltin (ef,_,_) ->
    begin match ef with
      | EF_inline_asm _ ->
        instruction "Pinlineasm" [Id];
        Cerrors.warning ("",-10) Cerrors.Inline_asm_sdump "inline assembler is not supported in sdump"
      | _ -> ()
    end
  | Pcfi_adjust _  (* Only debug relevant *)
  | Pcfi_rel_offset _ -> () in (* Only debug relevant *)
  List.iter instruction ic

let p_storage oc static =
    p_jstring oc (if static then "Static" else "Extern")

let p_section oc = function
  | Section_text -> fprintf oc "{\"Section Name\":\"Text\"}"
  | Section_data init -> fprintf oc "{\"Section Name\":\"Data\",\"Init\":%B}" init
  | Section_small_data init -> fprintf oc "{\"Section Name\":\"Small Data\",\"Init\":%B}" init
  | Section_const init -> fprintf oc "{\"Section Name\":\"Const\",\"Init\":%B}" init
  | Section_small_const init -> fprintf oc "{\"Section Name\":\"Small Const\",\"Init\":%B}" init
  | Section_string -> fprintf oc "{\"Section Name\":\"String\"}"
  | Section_literal -> fprintf oc "{\"Section Name\":\"Literal\"}"
  | Section_jumptable -> fprintf oc "{\"Section Name\":\"Jumptable\"}"
  | Section_user (s,w,e) -> fprintf oc "{\"Section Name\":\"%s\",\"Writable\":%B,\"Executable\":%B}" s w e
  | Section_debug_info _
  | Section_debug_abbrev
  | Section_debug_line _
  | Section_debug_loc
  | Section_debug_ranges
  | Section_debug_str -> () (* There should be no info in the debug sections *)

let p_int_opt oc = function
  | None -> fprintf oc "0"
  | Some i -> fprintf oc "%d" i


let p_fundef oc (name,f) =
  let alignment = atom_alignof name
  and inline = atom_is_inline name
  and static = atom_is_static name
  and c_section,l_section,j_section = match (atom_sections name) with [a;b;c] -> a,b,c | _ -> assert false in
  output_string oc "{";
  p_jmember oc "Fun Name" p_atom name;
  p_sep oc;
  p_jmember oc "Fun Storage Class" p_storage static;
  p_sep oc;
  p_jmember oc "Fun Alignment" p_int_opt alignment;
  p_sep oc;
  p_jmember oc "Fun Section Code" p_section c_section;
  p_sep oc;
  p_jmember oc "Fun Section Literals" p_section l_section;
  p_sep oc;
  p_jmember oc "Fun Section Jumptable" p_section j_section;
  p_sep oc;
  p_jmember oc "Fun Inline" p_jbool inline;
  p_sep oc;
  p_jmember oc "Fun Code" (fun oc a -> fprintf oc "[%a]" p_instruction a) f.fn_code;
  output_string oc "}\n"


let p_init_data oc = function
  | Init_int8 ic -> p_jsingle_object oc "Init_int8" p_int ic
  | Init_int16 ic -> p_jsingle_object oc "Init_int16" p_int ic
  | Init_int32 ic -> p_jsingle_object oc "Init_int32" p_int ic
  | Init_int64 lc -> p_jsingle_object oc "Init_int64" p_int64 lc
  | Init_float32 f -> p_jsingle_object oc "Init_float32" p_float32 f
  | Init_float64 f -> p_jsingle_object oc "Init_float64" p_float64 f
  | Init_space z -> p_jsingle_object oc "Init_space" p_z z
  | Init_addrof (p,i) ->
      let p_addr_of oc (p,i) =
        output_string oc "{";
        p_jmember oc "Addr" p_atom p;
        p_sep oc;
        p_jmember oc "Offset" p_int i;
        output_string oc "}" in
      p_jsingle_object oc "Init_addrof" p_addr_of (p,i)

let p_vardef oc (name,v) =
  let alignment = atom_alignof name
  and static = atom_is_static name
  and section = match  (atom_sections name) with [s] -> s | _ -> assert false in(* Should only have one section *)
  output_string oc "{";
  p_jmember oc "Var Name" p_atom name;
  p_sep oc;
  p_jmember oc "Var Readonly" p_jbool v.gvar_readonly;
  p_sep oc;
  p_jmember oc "Var Volatile" p_jbool v.gvar_volatile;
  p_sep oc;
  p_jmember oc "Var Storage Class" p_storage static;
  p_sep oc;
  p_jmember oc "Var Alignment" p_int_opt alignment;
  p_sep oc;
  p_jmember oc "Var Section" p_section section;
  p_sep oc;
  p_jmember oc "Var Init" (p_jarray p_init_data) v.gvar_init;
  output_string oc "}\n"

let p_program oc prog =
  reset_id ();
  let prog_vars,prog_funs = List.fold_left (fun (vars,funs) (ident,def) ->
    match def with
    | Gfun (Internal f) ->
      if not (atom_is_iso_inline_definition ident) then
        vars,(ident,f)::funs
      else
        vars,funs
    | Gvar v -> (ident,v)::vars,funs
    | _ -> vars,funs) ([],[]) prog.prog_defs in
  fprintf oc "{\"Global Variables\":%a,\n\"Functions\":%a}"
    (p_jarray p_vardef) prog_vars
    (p_jarray p_fundef) prog_funs

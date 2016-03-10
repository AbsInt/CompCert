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

let p_ireg oc reg =
  let num = match reg with
  | GPR0 -> 0
  | GPR1 -> 1
  | GPR2 -> 2
  | GPR3 -> 3
  | GPR4 -> 4
  | GPR5 -> 5
  | GPR6 -> 6
  | GPR7 -> 7
  | GPR8 -> 8
  | GPR9 -> 9
  | GPR10 -> 10
  | GPR11 -> 11
  | GPR12 -> 12
  | GPR13 -> 13
  | GPR14 -> 14
  | GPR15 -> 15
  | GPR16 -> 16
  | GPR17 -> 17
  | GPR18 -> 18
  | GPR19 -> 19
  | GPR20 -> 20
  | GPR21 -> 21
  | GPR22 -> 22
  | GPR23 -> 23
  | GPR24 -> 24
  | GPR25 -> 25
  | GPR26 -> 26
  | GPR27 -> 27
  | GPR28 -> 28
  | GPR29 -> 29
  | GPR30 -> 30
  | GPR31 -> 31
  in output_string oc "{";
    p_jmember oc "Register" (fun oc d -> p_jstring oc ("r"^(string_of_int d))) num;
    output_string oc "}"

let p_freg oc reg =
  let num = match reg with
  | FPR0 -> 0
  | FPR1 -> 1
  | FPR2 -> 2
  | FPR3 -> 3
  | FPR4 -> 4
  | FPR5 -> 5
  | FPR6 -> 6
  | FPR7 -> 7
  | FPR8 -> 8
  | FPR9 -> 9
  | FPR10 -> 10
  | FPR11 -> 11
  | FPR12 -> 12
  | FPR13 -> 13
  | FPR14 -> 14
  | FPR15 -> 15
  | FPR16 -> 16
  | FPR17 -> 17
  | FPR18 -> 18
  | FPR19 -> 19
  | FPR20 -> 20
  | FPR21 -> 21
  | FPR22 -> 22
  | FPR23 -> 23
  | FPR24 -> 24
  | FPR25 -> 25
  | FPR26 -> 26
  | FPR27 -> 27
  | FPR28 -> 28
  | FPR29 -> 29
  | FPR30 -> 30
  | FPR31 -> 31
  in output_string oc "{";
  p_jmember oc "Register" (fun oc d -> p_jstring oc ("f"^(string_of_int d))) num;
  output_string oc "}"


let p_preg oc = function
  | IR ir -> p_ireg oc ir
  | FR fr -> p_freg oc fr
  | _ -> assert false  (* This register should not be used. *)

let p_atom oc a = p_jstring oc (extern_atom a)

let p_atom_constant oc a = fprintf oc "{\"Atom\":%a}" p_atom a

let p_int oc i = fprintf oc "%ld" (camlint_of_coqint i)
let p_int64 oc i = fprintf oc "%Ld" (camlint64_of_coqint i)
let p_float32 oc f = fprintf oc "%ld" (camlint_of_coqint (Floats.Float32.to_bits f))
let p_float64 oc f = fprintf oc "%Ld" (camlint64_of_coqint (Floats.Float.to_bits f))
let p_z oc z = fprintf oc "%s" (Z.to_string z)

let p_int_constant oc i = fprintf oc "{\"Integer\":%a}" p_int i
let p_float64_constant oc f = fprintf oc "{\"Float\":%a}" p_float64 f
let p_float32_constant oc f = fprintf oc "{\"Float\":%a}" p_float32 f
let p_z_constant oc z = fprintf oc "{\"Integer\":%s}" (Z.to_string z)

let p_constant oc  = function
  | Cint i ->  p_int_constant oc i
  | Csymbol_low (i,c) -> fprintf oc "{\"Symbol_low\":{\"Name\":%a,\"Offset\":%a}}" p_atom i p_int c
  | Csymbol_high (i,c) -> fprintf oc "{\"Symbol_high\":{\"Name\":%a,\"Offset\":%a}}" p_atom i p_int c
  | Csymbol_sda (i,c) -> fprintf oc "{\"Symbol_sda\":{\"Name\":%a,\"Offset\":%a}}" p_atom i p_int c
  | Csymbol_rel_low (i,c) -> fprintf oc "{\"Symbol_rel_low\":{\"Name\":%a,\"Offset\":%a}}" p_atom i p_int c
  | Csymbol_rel_high (i,c) -> fprintf oc "{\"Symbol_rel_high\":{\"Name\":%a,\"Offset\":%a}}" p_atom i p_int c

let p_crbit oc c =
  let number = match c with
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3
  | CRbit_6 -> 6 in
  fprintf oc "{\"CRbit\":%d}" number

let p_label oc l = fprintf oc "{\"Label\":%ld}" (P.to_int32 l)

type instruction_arg =
  | Ireg of ireg
  | Freg of freg
  | Constant of constant
  | Crbit of crbit
  | ALabel of positive
  | Float32 of Floats.float32
  | Float64 of Floats.float
  | Atom of positive

let p_arg oc = function
  | Ireg ir -> p_ireg oc ir
  | Freg fr -> p_freg oc fr
  | Constant c -> p_constant oc c
  | Crbit cr -> p_crbit oc cr
  | ALabel lbl -> p_label oc lbl
  | Float32 f -> p_float32_constant oc f
  | Float64 f  -> p_float64_constant oc f
  | Atom a -> p_atom_constant oc a

let p_instruction oc ic =
  let p_args oc l= fprintf oc "%a:%a" p_jstring "Args" (p_jarray p_arg) l
  and inst_name oc s = fprintf  oc"%a:%a" p_jstring "Instruction Name" p_jstring s in
  let first = ref true in
  let sep oc = if !first then first := false else output_string oc ", " in
  let instruction n args = fprintf oc "\n%t{%a,%a}" sep inst_name n p_args args in
  let instruction = function
  | Padd (ir1,ir2,ir3) -> instruction "Padd" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Paddc (ir1,ir2,ir3) -> instruction "Paddc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Padde (ir1,ir2,ir3) -> instruction "Padde" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Paddi (ir1,ir2,c) -> instruction "Paddi" [Ireg ir1; Ireg ir2; Constant c]
  | Paddic  (ir1,ir2,c) -> instruction "Paddic" [Ireg ir1; Ireg ir2; Constant c]
  | Paddis  (ir1,ir2,c) -> instruction "Paddis" [Ireg ir1; Ireg ir2; Constant c]
  | Paddze (ir1,ir2) -> instruction "Paddze" [Ireg ir1; Ireg ir2]
  | Pallocframe _ -> () (* Should not occur *)
  | Pand_ (ir1,ir2,ir3) -> instruction "Pand_" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pandc (ir1,ir2,ir3) -> instruction "Pandc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pandi_ (ir1,ir2,c) -> instruction "Pandi_" [Ireg ir1; Ireg ir2; Constant c]
  | Pandis_ (ir1,ir2,c) -> instruction "Pandis_" [Ireg ir1; Ireg ir2; Constant c]
  | Pb l -> instruction "Pb" [ALabel l]
  | Pbctr _ -> instruction "Pbctr" []
  | Pbctrl _ -> instruction "Pbctrl" []
  | Pbdnz l -> instruction "Pbdnz" [ALabel l]
  | Pbf (cr,l) -> instruction "Pbf" [Crbit cr; ALabel l]
  | Pbl (i,_) -> instruction "Pbl" [Atom i]
  | Pbs (i,_) -> instruction "Pbs" [Atom i]
  | Pblr -> instruction "Pblr" []
  | Pbt (cr,l) ->  instruction "Pbt" [Crbit cr; ALabel l]
  | Pbtbl (i,lb) -> instruction "Pbtbl" ((Ireg i)::(List.map (fun a -> ALabel a) lb))
  | Pcmpb (ir1,ir2,ir3) -> instruction "Pcmpb" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pcmplw (ir1,ir2) -> instruction "Pcmplw" [Ireg ir1; Ireg ir2]
  | Pcmplwi (ir,c) -> instruction "Pcmplwi" [Ireg ir; Constant c]
  | Pcmpw (ir1,ir2) -> instruction "Pcmpw" [Ireg ir1; Ireg ir2]
  | Pcmpwi (ir,c) -> instruction "Pcmpwi" [Ireg ir; Constant c]
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
  | Pdivwu (ir1,ir2,ir3) -> instruction "Pdivwu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Peieio -> instruction "Peieio" []
  | Peqv (ir1,ir2,ir3) -> instruction "Peqv" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pextsb (ir1,ir2) -> instruction "Pextsb" [Ireg ir1; Ireg ir2]
  | Pextsh (ir1,ir2) -> instruction "Pextsh" [Ireg ir1; Ireg ir2]
  | Pextsw (ir1,ir2) -> instruction "Pextsw" [Ireg ir1; Ireg ir2]
  | Pfreeframe _ -> assert false (* Should not occur *)
  | Pfabs (fr1,fr2)
  | Pfabss (fr1,fr2) -> instruction "Pfabs" [Freg fr1; Freg fr2]
  | Pfadd (fr1,fr2,fr3) -> instruction "Pfadd" [Freg fr1; Freg fr2; Freg fr3]
  | Pfadds (fr1,fr2,fr3) -> instruction "Pfadds" [Freg fr1; Freg fr2; Freg fr3]
  | Pfcmpu (fr1,fr2) -> instruction "Pfcmpu" [Freg fr1; Freg fr2]
  | Pfcfi _ -> () (* Should not occur *)
  | Pfcfid (fr1,fr2) -> instruction "Pfcfid" [Freg fr1; Freg fr2]
  | Pfcfiu _ (* Should not occur *)
  | Pfcti _ (* Should not occur *)
  | Pfctiu _ -> () (* Should not occur *)
  | Pfctidz (fr1,fr2) -> instruction "Pfctidz" [Freg fr1; Freg fr2]
  | Pfctiw (fr1,fr2) -> instruction "Pfctiw" [Freg fr1; Freg fr2]
  | Pfctiwz (fr1,fr2) -> instruction "Pfctiwz" [Freg fr1; Freg fr2]
  | Pfdiv (fr1,fr2,fr3) -> instruction "Pfdiv" [Freg fr1; Freg fr2; Freg fr3]
  | Pfdivs (fr1,fr2,fr3) -> instruction "Pfdivs" [Freg fr1; Freg fr2; Freg fr3]
  | Pfmake _ -> ()(* Should not occur *)
  | Pfmr (fr1,fr2) -> instruction "Pfmr" [Freg fr1; Freg fr2]
  | Pfmul (fr1,fr2,fr3) -> instruction "Pfmul" [Freg fr1; Freg fr2; Freg fr3]
  | Pfmuls(fr1,fr2,fr3) -> instruction "Pfmuls" [Freg fr1; Freg fr2; Freg fr3]
  | Pfneg (fr1,fr2)
  | Pfnegs (fr1,fr2) -> instruction "Pfneg" [Freg fr1; Freg fr2]
  | Pfrsp (fr1,fr2) -> instruction "Pfrsp" [Freg fr1; Freg fr2]
  | Pfxdp _ -> () (* Should not occur *)
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
  | Pmfcrbit _ -> () (* Should not occur *)
  | Pmflr ir -> instruction "Pmflr" [Ireg ir]
  | Pmr (ir1,ir2) -> instruction "Pmr" [Ireg ir1; Ireg ir2]
  | Pmtctr ir -> instruction "Pmtctr" [Ireg ir]
  | Pmtlr ir -> instruction "Pmtlr" [Ireg ir]
  | Pmfspr(ir, n) -> instruction "Pmfspr" [Ireg ir; Constant (Cint n)]
  | Pmtspr(n, ir) -> instruction "Pmtspr" [Constant (Cint n); Ireg ir]
  | Pmulli (ir1,ir2,c) -> instruction "Pmulli" [Ireg ir1; Ireg ir2; Constant c]
  | Pmullw (ir1,ir2,ir3) -> instruction "Pmullw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhw (ir1,ir2,ir3) -> instruction "Pmulhw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pmulhwu (ir1,ir2,ir3) -> instruction "Pmulhwu" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pnand (ir1,ir2,ir3) -> instruction "Pnand" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pnor (ir1,ir2,ir3) -> instruction "Pnor" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Por (ir1,ir2,ir3) -> instruction "Por" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Porc (ir1,ir2,ir3) -> instruction "Porc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pori (ir1,ir2,c) -> instruction "Pori" [Ireg ir1; Ireg ir2; Constant c]
  | Poris (ir1,ir2,c) -> instruction "Poris" [Ireg ir1; Ireg ir2; Constant c]
  | Prldicl (ir1,ir2,ic1,ic2) -> instruction "Prldicl" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Prldicr (ir1,ir2,ic1,ic2) -> instruction "Prldicr" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Prlwinm (ir1,ir2,ic1,ic2) -> instruction "Prlwinm" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Prlwimi  (ir1,ir2,ic1,ic2) ->instruction "Prlwimi" [Ireg ir1; Ireg ir2; Constant (Cint ic1); Constant (Cint ic2)]
  | Pslw (ir1,ir2,ir3) -> instruction "Pslw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psraw (ir1,ir2,ir3) -> instruction "Psraw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psrawi  (ir1,ir2,ic) -> instruction "Psrawi" [Ireg ir1; Ireg ir2; Constant (Cint ic)]
  | Psrw (ir1,ir2,ir3) -> instruction "Psrw" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pstb (ir1,c,ir2) -> instruction "Pstb" [Ireg ir1; Constant c; Ireg ir2]
  | Pstbx (ir1,ir2,ir3) -> instruction "Pstbx" [Ireg ir1; Ireg ir2; Ireg ir3]
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
  | Psubfc (ir1,ir2,ir3) -> instruction "Psubfc" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfe (ir1,ir2,ir3) -> instruction "Psubfe" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Psubfze (ir1,ir2) -> instruction "Psubfze" [Ireg ir1; Ireg ir2]
  | Psubfic (ir1,ir2,c) -> instruction "Psubfic" [Ireg ir1; Ireg ir2; Constant c]
  | Psync -> instruction "Psync" []
  | Ptrap -> instruction "Ptrap" []
  | Pxor (ir1,ir2,ir3) -> instruction "Pxor" [Ireg ir1; Ireg ir2; Ireg ir3]
  | Pxori (ir1,ir2,c) ->instruction "Pxori" [Ireg ir1; Ireg ir2; Constant c]
  | Pxoris (ir1,ir2,c) -> instruction "Pxoris" [Ireg ir1; Ireg ir2; Constant c]
  | Plabel l -> instruction "Plabel" [ALabel l]
  | Pbuiltin _ -> ()
  | Pcfi_adjust _  (* Only debug relevant *)
  | Pcfi_rel_offset _ ->  () (* Only debug relevant *) in
  List.iter instruction ic

let p_storage oc static =
  if static then
    fprintf oc "\"Static\""
  else
    fprintf oc "\"Extern\""

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
  fprintf oc "{\"Fun Name\":%a,\n\"Fun Storage Class\":%a,\n\"Fun Alignment\":%a,\n\"Fun Section Code\":%a,\"Fun Section Literals\":%a,\"Fun Section Jumptable\":%a,\n\"Fun Inline\":%B,\n\"Fun Code\":[%a]}\n"
    p_atom name  p_storage static p_int_opt alignment
    p_section c_section p_section l_section p_section j_section inline
    p_instruction f.fn_code

let p_init_data oc = function
  | Init_int8 ic -> fprintf oc "{\"Init_int8\":%a}" p_int ic
  | Init_int16 ic -> fprintf oc "{\"Init_int16\":%a}" p_int ic
  | Init_int32 ic -> fprintf oc "{\"Init_int32\":%a}" p_int ic
  | Init_int64 lc -> fprintf oc "{\"Init_int64\":%a}" p_int64 lc
  | Init_float32 f -> fprintf oc "{\"Init_float32\":%a}" p_float32 f
  | Init_float64 f -> fprintf oc "{\"Init_float64\":%a}" p_float64 f
  | Init_space z -> fprintf oc "{\"Init_space\":%a}" p_z z
  | Init_addrof (p,i) -> fprintf oc "{\"Init_addrof\":{\"Addr\":%a,\"Offset\":%a}}" p_atom p p_int i

let p_vardef oc (name,v) =
  let alignment = atom_alignof name
  and static = atom_is_static name
  and section = match  (atom_sections name) with [s] -> s | _ -> assert false (* Should only have one section *) in
  fprintf oc "{\"Var Name\":%a,\"Var Readonly\":%B,\"Var Volatile\":%B,\n\"Var Storage Class\":%a,\n\"Var Alignment\":%a,\n\"Var Section\":%a,\n\"Var Init\":%a}\n"
    p_atom name v.gvar_readonly v.gvar_volatile
    p_storage static p_int_opt alignment p_section section
    (p_jarray p_init_data) v.gvar_init

let p_program oc prog =
  let prog_vars,prog_funs = List.fold_left (fun (vars,funs) (ident,def) ->
    match def with
    | Gfun (Internal f) -> vars,(ident,f)::funs
    | Gvar v -> (ident,v)::vars,funs
    | _ -> vars,funs) ([],[]) prog.prog_defs in
  fprintf oc "{\"Global Variables\":%a,\n\"Functions\":%a}"
    (p_jarray p_vardef) prog_vars
    (p_jarray p_fundef) prog_funs

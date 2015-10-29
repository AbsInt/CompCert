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
open Printf
open Sections

let p_jstring oc s = fprintf oc "\"%s\"" s

let p_ireg oc = function
  | GPR0 -> fprintf oc "{\"Register\":\"r0\"}"
  | GPR1 -> fprintf oc "{\"Register\":\"r1\"}"
  | GPR2 -> fprintf oc "{\"Register\":\"r2\"}"
  | GPR3 -> fprintf oc "{\"Register\":\"r3\"}"
  | GPR4 -> fprintf oc "{\"Register\":\"r4\"}"
  | GPR5 -> fprintf oc "{\"Register\":\"r5\"}"
  | GPR6 -> fprintf oc "{\"Register\":\"r6\"}"
  | GPR7 -> fprintf oc "{\"Register\":\"r7\"}"
  | GPR8 -> fprintf oc "{\"Register\":\"r8\"}"
  | GPR9 -> fprintf oc "{\"Register\":\"r9\"}"
  | GPR10 -> fprintf oc "{\"Register\":\"r10\"}"
  | GPR11 -> fprintf oc "{\"Register\":\"r11\"}"
  | GPR12 -> fprintf oc "{\"Register\":\"r12\"}"
  | GPR13 -> fprintf oc "{\"Register\":\"r13\"}"
  | GPR14 -> fprintf oc "{\"Register\":\"r14\"}"
  | GPR15 -> fprintf oc "{\"Register\":\"r15\"}"
  | GPR16 -> fprintf oc "{\"Register\":\"r16\"}"
  | GPR17 -> fprintf oc "{\"Register\":\"r17\"}"
  | GPR18 -> fprintf oc "{\"Register\":\"r18\"}"
  | GPR19 -> fprintf oc "{\"Register\":\"r19\"}"
  | GPR20 -> fprintf oc "{\"Register\":\"r20\"}"
  | GPR21 -> fprintf oc "{\"Register\":\"r21\"}"
  | GPR22 -> fprintf oc "{\"Register\":\"r22\"}"
  | GPR23 -> fprintf oc "{\"Register\":\"r23\"}"
  | GPR24 -> fprintf oc "{\"Register\":\"r24\"}"
  | GPR25 -> fprintf oc "{\"Register\":\"r25\"}"
  | GPR26 -> fprintf oc "{\"Register\":\"r26\"}"
  | GPR27 -> fprintf oc "{\"Register\":\"r27\"}"
  | GPR28 -> fprintf oc "{\"Register\":\"r28\"}"
  | GPR29 -> fprintf oc "{\"Register\":\"r29\"}"
  | GPR30 -> fprintf oc "{\"Register\":\"r30\"}"
  | GPR31 -> fprintf oc "{\"Register\":\"r31\"}"

let p_freg oc = function
  | FPR0 -> fprintf oc "{\"Register\":\"f0\"}"
  | FPR1 -> fprintf oc "{\"Register\":\"f1\"}"
  | FPR2 -> fprintf oc "{\"Register\":\"f2\"}"
  | FPR3 -> fprintf oc "{\"Register\":\"f3\"}"
  | FPR4 -> fprintf oc "{\"Register\":\"f4\"}"
  | FPR5 -> fprintf oc "{\"Register\":\"f5\"}"
  | FPR6 -> fprintf oc "{\"Register\":\"f6\"}"
  | FPR7 -> fprintf oc "{\"Register\":\"f7\"}"
  | FPR8 -> fprintf oc "{\"Register\":\"f8\"}"
  | FPR9 -> fprintf oc "{\"Register\":\"f9\"}"
  | FPR10 -> fprintf oc "{\"Register\":\"f10\"}"
  | FPR11 -> fprintf oc "{\"Register\":\"f11\"}"
  | FPR12 -> fprintf oc "{\"Register\":\"f12\"}"
  | FPR13 -> fprintf oc "{\"Register\":\"f13\"}"
  | FPR14 -> fprintf oc "{\"Register\":\"f14\"}"
  | FPR15 -> fprintf oc "{\"Register\":\"f15\"}"
  | FPR16 -> fprintf oc "{\"Register\":\"f16\"}"
  | FPR17 -> fprintf oc "{\"Register\":\"f17\"}"
  | FPR18 -> fprintf oc "{\"Register\":\"f18\"}"
  | FPR19 -> fprintf oc "{\"Register\":\"f19\"}"
  | FPR20 -> fprintf oc "{\"Register\":\"f20\"}"
  | FPR21 -> fprintf oc "{\"Register\":\"f21\"}"
  | FPR22 -> fprintf oc "{\"Register\":\"f22\"}"
  | FPR23 -> fprintf oc "{\"Register\":\"f23\"}"
  | FPR24 -> fprintf oc "{\"Register\":\"f24\"}"
  | FPR25 -> fprintf oc "{\"Register\":\"f25\"}"
  | FPR26 -> fprintf oc "{\"Register\":\"f26\"}"
  | FPR27 -> fprintf oc "{\"Register\":\"f27\"}"
  | FPR28 -> fprintf oc "{\"Register\":\"f28\"}"
  | FPR29 -> fprintf oc "{\"Register\":\"f29\"}"
  | FPR30 -> fprintf oc "{\"Register\":\"f30\"}"
  | FPR31 -> fprintf oc "{\"Register\":\"f31\"}"

let p_preg oc = function
  | IR ir -> p_ireg oc ir
  | FR fr -> p_freg oc fr
  | _ -> assert false  (* This registers should not be used. *)

let p_atom oc a = fprintf oc "\"%s\"" (extern_atom a)

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

let p_char_list oc l = fprintf oc "{\"String\":\"%a\"}" (fun oc -> List.iter (output_char oc)) l

let p_list elem oc l =
  match l with
  | [] -> fprintf oc "[]"
  | hd::tail ->
      output_string oc "["; elem oc hd;List.iter (fprintf oc ",%a" elem) tail;output_string oc "]"

let p_list_cont elem oc l =
  match l with
  | [] -> ()
  | _ ->
      List.iter (fprintf oc ",%a" elem) l

let p_instruction oc ic =
  output_string oc "\n";
  let inst_name oc s = fprintf  oc"%a:%a" p_jstring "Instruction Name" p_jstring s in
  match ic with
  | Padd (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Padd" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Paddc (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Paddc" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Padde (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Padde" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Paddi (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Paddi" p_ireg ir1 p_ireg ir2 p_constant c
  | Paddic  (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Paddic" p_ireg ir1 p_ireg ir2 p_constant c
  | Paddis  (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}"  inst_name  "Paddis" p_ireg ir1 p_ireg ir2 p_constant c
  | Paddze (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Paddze" p_ireg ir1 p_ireg ir2
  | Pallocframe (c,i,r) -> assert false(* Should not occur *)
  | Pand_ (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pand_" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pandc (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pandc" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pandi_ (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pandi_" p_ireg ir1 p_ireg ir2 p_constant c
  | Pandis_ (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pandis_" p_ireg ir1 p_ireg ir2 p_constant c
  | Pb l -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pb" p_label l
  | Pbctr s -> fprintf oc  "{%a,\"Args\":[]}" inst_name "Pbctr"
  | Pbctrl s -> fprintf oc "{%a,\"Args\":[]}" inst_name "Pbctrl"
  | Pbdnz l -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pbdnz" p_label l
  | Pbf (c,l) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pbf" p_crbit c p_label l
  | Pbl (i,s) -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pbl" p_atom_constant i
  | Pbs (i,s) -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pbs" p_atom_constant i
  | Pblr -> fprintf oc "{%a,\"Args\":[]}" inst_name "Pblr"
  | Pbt (cr,l) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pbt" p_crbit cr p_label l
  | Pbtbl (i,lb) -> fprintf oc "{%a,\"Args\":[%a%a]}" inst_name "Pbtl" p_ireg i (p_list_cont p_label) lb
  | Pcmpb (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pcmpb"  p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pcmplw (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pcmplw" p_ireg ir1 p_ireg ir2
  | Pcmplwi (ir,c) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pcmplwi" p_ireg ir p_constant c
  | Pcmpw (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pcmpw" p_ireg ir1 p_ireg ir2
  | Pcmpwi (ir,c) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pcmpwi" p_ireg ir p_constant c
  | Pcntlzw (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pcntlzw" p_ireg ir1 p_ireg ir2
  | Pcreqv (cr1,cr2,cr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pcreqv" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pcror (cr1,cr2,cr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pcror" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pcrxor (cr1,cr2,cr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pcrxor" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pdcbf (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pdcbf" p_ireg ir1 p_ireg ir2
  | Pdcbi (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pdcbi" p_ireg ir1 p_ireg ir2
  | Pdcbt (n,ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pdcbt" p_int_constant n p_ireg ir1 p_ireg ir2
  | Pdcbtst (n,ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pdcbtst" p_int_constant n p_ireg ir1 p_ireg ir2
  | Pdcbtls (n,ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pdcbtls" p_int_constant n p_ireg ir1 p_ireg ir2
  | Pdcbz (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pdcbz" p_ireg ir1 p_ireg ir2
  | Pdivw (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pdivw" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pdivwu (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pdivwu" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Peieio -> fprintf oc "{%a,\"Args\":[]}" inst_name "Peieio"
  | Peqv (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Peqv" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pextsb (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pextsb" p_ireg ir1 p_ireg ir2
  | Pextsh (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pextsh" p_ireg ir1 p_ireg ir2
  | Pextsw (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pextsw" p_ireg ir1 p_ireg ir2
  | Pfreeframe (c,i) -> assert false (* Should not occur *)
  | Pfabs (fr1,fr2)
  | Pfabss (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfabs" p_freg fr1 p_freg fr2
  | Pfadd (fr1,fr2,fr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pfadd" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfadds (fr1,fr2,fr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pfadds" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfcmpu (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfcmpu" p_freg fr1 p_freg fr2
  | Pfcfi (ir,fr) -> assert false (* Should not occur *)
  | Pfcfid (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfcfid" p_freg fr1 p_freg fr2
  | Pfcfiu (ir,fr) -> assert false (* Should not occur *)
  | Pfcti (ir,fr) -> assert false (* Should not occur *)
  | Pfctiu (ir,fr) -> assert false (* Should not occur *)
  | Pfctidz (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfctidz" p_freg fr1 p_freg fr2
  | Pfctiw (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfctiw" p_freg fr1 p_freg fr2
  | Pfctiwz (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfctiwz" p_freg fr1 p_freg fr2
  | Pfdiv (fr1,fr2,fr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pfdiv" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfdivs (fr1,fr2,fr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pfdivs" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfmake (fr,ir1,ir2) -> assert false (* Should not occur *)
  | Pfmr (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfmr" p_freg fr1 p_freg fr2
  | Pfmul (fr1,fr2,fr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pfmul" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfmuls(fr1,fr2,fr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pfmuls" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfneg (fr1,fr2)
  | Pfnegs (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfneg" p_freg fr1 p_freg fr2
  | Pfrsp (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfrsp" p_freg fr1 p_freg fr2
  | Pfxdp (fr1,fr2) -> assert false (* Should not occur *)
  | Pfsub (fr1,fr2,fr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pfsub" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfsubs (fr1,fr2,fr3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pfsubs" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfmadd (fr1,fr2,fr3,fr4) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Pfmadd" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pfmsub (fr1,fr2,fr3,fr4) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Pfmsub" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pfnmadd (fr1,fr2,fr3,fr4) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Pfnmadd" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pfnmsub (fr1,fr2,fr3,fr4) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Pfnmsub" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pfsqrt (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfsqrt" p_freg fr1 p_freg fr2
  | Pfrsqrte (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfrsqrte" p_freg fr1 p_freg fr2
  | Pfres (fr1,fr2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pfres" p_freg fr1 p_freg fr2
  | Pfsel (fr1,fr2,fr3,fr4) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Pfsel" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pisel (ir1,ir2,ir3,cr) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Pisel" p_ireg ir1 p_ireg ir2 p_ireg ir3 p_crbit cr
  | Picbi (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Picbi" p_ireg ir1 p_ireg ir2
  | Picbtls (n,ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Picbtls" p_int_constant n p_ireg ir1 p_ireg ir2
  | Pisync -> fprintf oc "{%a,\"Args\":[]}" inst_name "Pisync"
  | Plwsync -> fprintf oc "{%a,\"Args\":[]}" inst_name "Plwsync"
  | Plbz (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plbz" p_ireg ir1 p_constant c p_ireg ir2
  | Plbzx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plbzx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plfd (fr,c,ir)
  | Plfd_a (fr,c,ir) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plfd" p_freg fr p_constant c p_ireg ir
  | Plfdx (fr,ir1,ir2)
  | Plfdx_a (fr,ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plfdx" p_freg fr p_ireg ir1 p_ireg ir2
  | Plfs (fr,c,ir) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plfs" p_freg fr p_constant c p_ireg ir
  | Plfsx  (fr,ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plfsx" p_freg fr p_ireg ir1 p_ireg ir2
  | Plha (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plha" p_ireg ir1 p_constant c p_ireg ir2
  | Plhax (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plhax" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plhbrx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plhbrx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plhz (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plhz" p_ireg ir1 p_constant c p_ireg ir2
  | Plhzx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plhzx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plfi (fr,fc) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Plfi" p_freg fr p_float64_constant fc
  | Plfis (fr,fc) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Plfis" p_freg fr p_float32_constant fc
  | Plwz (ir1,c,ir2)
  | Plwz_a (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plwz" p_ireg ir1 p_constant c p_ireg ir2
  | Plwzu (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plwzu" p_ireg ir1 p_constant c p_ireg ir2
  | Plwzx (ir1,ir2,ir3)
  | Plwzx_a (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plwzx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plwarx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plwarx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plwbrx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Plwbrx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmbar c -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pmbar" p_int_constant c
  | Pmfcr ir -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pmfcr" p_ireg ir
  | Pmfcrbit (ir,crb) -> assert false (* Should not occur *)
  | Pmflr ir -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pmflr" p_ireg ir
  | Pmr (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pmr" p_ireg ir1 p_ireg ir2
  | Pmtctr ir -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pmtctr" p_ireg ir
  | Pmtlr ir -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Pmtlr" p_ireg ir
  | Pmfspr(ir, n) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pmfspr" p_ireg ir p_int_constant n
  | Pmtspr(n, ir) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Pmtspr" p_int_constant n p_ireg ir
  | Pmulli (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pmulli" p_ireg ir1 p_ireg ir2 p_constant c
  | Pmullw (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pmullw" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmulhw (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pmulhw" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmulhwu (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pmulhwu" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pnand (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pnand" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pnor (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pnor" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Por (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Por" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Porc (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Porc" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pori (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pori" p_ireg ir1 p_ireg ir2 p_constant c
  | Poris (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Poris" p_ireg ir1 p_ireg ir2 p_constant c
  | Prldicl (ir1,ir2,ic1,ic2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Prldicl" p_ireg ir1 p_ireg ir2 p_int_constant ic1 p_int_constant ic2
  | Prlwinm (ir1,ir2,ic1,ic2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Prlwinm" p_ireg ir1 p_ireg ir2 p_int_constant ic1 p_int_constant ic2
  | Prlwimi  (ir1,ir2,ic1,ic2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a,%a]}" inst_name "Prlwimi" p_ireg ir1 p_ireg ir2 p_int_constant ic1 p_int_constant ic2
  | Pslw (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pslw" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psraw (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psraw" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psrawi  (ir1,ir2,ic) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psrawi" p_ireg ir1 p_ireg ir2 p_int_constant ic
  | Psrw (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psrw" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstb (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstb" p_ireg ir1 p_constant c p_ireg ir2
  | Pstbx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstbx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstdu (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstdu" p_ireg ir1 p_constant c p_ireg ir2
  | Pstfd (fr,c,ir)
  | Pstfd_a (fr,c,ir) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstfd" p_freg fr p_constant c p_ireg ir
  | Pstfdu (fr,c,ir) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstfdu" p_freg fr p_constant c p_ireg ir
  | Pstfdx (fr,ir1,ir2)
  | Pstfdx_a (fr,ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstfdx" p_freg fr p_ireg ir1 p_ireg ir2
  | Pstfs (fr,c,ir) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstfs" p_freg fr p_constant c p_ireg ir
  | Pstfsx (fr,ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstfsx" p_freg fr p_ireg ir1 p_ireg ir2
  | Psth (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psth" p_ireg ir1 p_constant c p_ireg ir2
  | Psthx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psthx"  p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psthbrx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psthbrx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstw (ir1,c,ir2)
  | Pstw_a (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstw" p_ireg ir1 p_constant c p_ireg ir2
  | Pstwu (ir1,c,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstwu" p_ireg ir1 p_constant c p_ireg ir2
  | Pstwx (ir1,ir2,ir3)
  | Pstwx_a (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstwx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwux (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstwux" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwbrx (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstwbrx" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwcx_ (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pstwcx_" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfc (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psubfc" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfe (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psubfe" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfze (ir1,ir2) -> fprintf oc "{%a,\"Args\":[%a,%a]}" inst_name "Psubfze" p_ireg ir1 p_ireg ir2
  | Psubfic (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Psubfic" p_ireg ir1 p_ireg ir2 p_constant c
  | Psync -> fprintf oc "{%a,\"Args\":[]}" inst_name "Psync"
  | Ptrap -> fprintf oc "{%a,\"Args\":[]}" inst_name "Ptrap"
  | Pxor (ir1,ir2,ir3) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pxor" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pxori (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pxori" p_ireg ir1 p_ireg ir2 p_constant c
  | Pxoris (ir1,ir2,c) -> fprintf oc "{%a,\"Args\":[%a,%a,%a]}" inst_name "Pxoris" p_ireg ir1 p_ireg ir2 p_constant c
  | Plabel l -> fprintf oc "{%a,\"Args\":[%a]}" inst_name "Plabel" p_label l
  | Pbuiltin (ef,args1,args2) -> ()
  | Pcfi_adjust _  (* Only debug relevant *)
  | Pcfi_rel_offset _ ->  () (* Only debug relevant *)

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
  and instr = List.filter (function Pbuiltin _| Pcfi_adjust _ | Pcfi_rel_offset _ -> false | _ -> true) f.fn_code in
  let c_section,l_section,j_section = match (atom_sections name) with [a;b;c] -> a,b,c | _ -> assert false in
  fprintf oc "{\"Fun Name\":%a,\n\"Fun Storage Class\":%a,\n\"Fun Alignment\":%a,\n\"Fun Section Code\":%a,\"Fun Section Literals\":%a,\"Fun Section Jumptable\":%a,\n\"Fun Inline\":%B,\n\"Fun Code\":%a}\n"
    p_atom name  p_storage static p_int_opt alignment
    p_section c_section p_section l_section p_section j_section inline
    (p_list p_instruction) instr

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
    (p_list p_init_data) v.gvar_init

let p_program oc prog =
  let prog_vars,prog_funs = List.fold_left (fun (vars,funs) (ident,def) ->
    match def with
    | Gfun (Internal f) -> vars,(ident,f)::funs
    | Gvar v -> (ident,v)::vars,funs
    | _ -> vars,funs) ([],[]) prog.prog_defs in
  fprintf oc "{\"Global Variables\":%a,\n\"Functions\":%a}"
    (p_list p_vardef) prog_vars
    (p_list p_fundef) prog_funs

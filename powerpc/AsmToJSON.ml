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
  match ic with
  | Padd (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Padd\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Paddc (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Paddc\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Padde (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Padde\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Paddi (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Paddi\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Paddic  (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Paddic\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Paddis  (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Paddis\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Paddze (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Paddze\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pallocframe (c,i) -> assert false(* Should not occur *)
  | Pand_ (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pand_\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pandc (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pandc\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pandi_ (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pandi_\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Pandis_ (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pandis_\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Pb l -> fprintf oc "{\"Instruction Name\":\"Pb\",\"Args\":[%a]}" p_label l
  | Pbctr s -> fprintf oc  "{\"Instruction Name\":\"Pbctr\",\"Args\":[]}"
  | Pbctrl s -> fprintf oc "{\"Instruction Name\":\"Pbctrl\",\"Args\":[]}"
  | Pbdnz l -> fprintf oc "{\"Instruction Name\":\"Pbdnz\",\"Args\":[%a]}" p_label l 
  | Pbf (c,l) -> fprintf oc "{\"Instruction Name\":\"Pbf\",\"Args\":[%a,%a]}" p_crbit c p_label l
  | Pbl (i,s) -> fprintf oc "{\"Instruction Name\":\"Pbl\",\"Args\":[%a]}"  p_atom_constant i
  | Pbs (i,s) -> fprintf oc "{\"Instruction Name\":\"Pbs\",\"Args\":[%a]}"  p_atom_constant i
  | Pblr -> fprintf oc "{\"Instruction Name\":\"Pblr\",\"Args\":[]}"
  | Pbt (cr,l) -> fprintf oc "{\"Instruction Name\":\"Pbt\",\"Args\":[%a,%a]}" p_crbit cr p_label l
  | Pbtbl (i,lb) -> fprintf oc "{\"Instruction Name\":\"Pbtl\",\"Args\":[%a%a]}" p_ireg i (p_list_cont p_label) lb
  | Pcmplw (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pcmplw\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pcmplwi (ir,c) -> fprintf oc "{\"Instruction Name\":\"Pcmplwi\",\"Args\":[%a,%a]}" p_ireg ir p_constant c
  | Pcmpw (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pcmpw\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pcmpwi (ir,c) -> fprintf oc "{\"Instruction Name\":\"Pcmpwi\",\"Args\":[%a,%a]}" p_ireg ir p_constant c 
  | Pcntlzw (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pcntlzw\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pcreqv (cr1,cr2,cr3) -> fprintf oc "{\"Instruction Name\":\"Pcreqv\",\"Args\":[%a,%a,%a]}" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pcror (cr1,cr2,cr3) -> fprintf oc "{\"Instruction Name\":\"Pcror\",\"Args\":[%a,%a,%a]}" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pcrxor (cr1,cr2,cr3) -> fprintf oc "{\"Instruction Name\":\"Pcrxor\",\"Args\":[%a,%a,%a]}" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pdcbf (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pdcbf\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pdcbi (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pdcbi\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pdcbt (n,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pdcbt\",\"Args\":[%a,%a,%a]}" p_int_constant n p_ireg ir1 p_ireg ir2
  | Pdcbtst (n,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pdcbtst\",\"Args\":[%a,%a,%a]}" p_int_constant n p_ireg ir1 p_ireg ir2
  | Pdcbtls (n,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pdcbtls\",\"Args\":[%a,%a,%a]}" p_int_constant n p_ireg ir1 p_ireg ir2
  | Pdcbz (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pdcbz\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pdivw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pdivw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pdivwu (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pdivwu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Peieio -> fprintf oc "{\"Instruction Name\":\"Peieio,\"Args\":[]}"
  | Peqv (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Peqv\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pextsb (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pextsb\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pextsh (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pextsh\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pfreeframe (c,i) -> assert false (* Should not occur *)
  | Pfabs (fr1,fr2) 
  | Pfabss (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfabs\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfadd (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfadd\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfadds (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfadds\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfcmpu (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfcmpu\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfcti (ir,fr) -> assert false (* Should not occur *)
  | Pfctiw (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfctiw\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfctiwz (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfctiwz\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfdiv (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfdiv\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfdivs (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfdivs\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfmake (fr,ir1,ir2) -> assert false (* Should not occur *)
  | Pfmr (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfmr\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfmul (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfmul\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfmuls(fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfmuls\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfneg (fr1,fr2)
  | Pfnegs (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfneg\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfrsp (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfrsp\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfxdp (fr1,fr2) -> assert false (* Should not occur *)
  | Pfsub (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfsub\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfsubs (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfsubs\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfmadd (fr1,fr2,fr3,fr4) -> fprintf oc "{\"Instruction Name\":\"Pfmadd\",\"Args\":[%a,%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pfmsub (fr1,fr2,fr3,fr4) -> fprintf oc "{\"Instruction Name\":\"Pfmsub\",\"Args\":[%a,%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pfnmadd (fr1,fr2,fr3,fr4) -> fprintf oc "{\"Instruction Name\":\"Pfmadd\",\"Args\":[%a,%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pfnmsub (fr1,fr2,fr3,fr4) -> fprintf oc "{\"Instruction Name\":\"Pfnmsub\",\"Args\":[%a,%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Pfsqrt (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfsqrt\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfrsqrte (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfsqrte\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfres (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfres\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfsel (fr1,fr2,fr3,fr4) -> fprintf oc "{\"Instruction Name\":\"Pfsel\",\"Args\":[%a,%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3 p_freg fr4
  | Picbi (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Picbi\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Picbtls (n,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Picbtls\",\"Args\":[%a,%a,%a]}" p_int_constant n p_ireg ir1 p_ireg ir2
  | Pisync -> fprintf oc "{\"Instruction Name\":\"Pisync\",\"Args\":[]}"
  | Plwsync -> fprintf oc "{\"Instruction Name\":\"Plwsync\",\"Args\":[]}"
  | Plbz (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plbz\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plbzx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plbzx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plfd (fr,c,ir)
  | Plfd_a (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Plfd\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Plfdx (fr,ir1,ir2)
  | Plfdx_a (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Plfdx\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Plfs (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Plfs\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Plfsx  (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Plfsx\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Plha (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plha\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plhax (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plhax\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plhbrx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plhbrx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plhz (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plhz\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plhzx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plhzx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plfi (fr,fc) -> fprintf oc "{\"Instruction Name\":\"Plfi\",\"Args\":[%a,%a]}" p_freg fr p_float64_constant fc
  | Plfis (fr,fc) -> fprintf oc "{\"Instruction Name\":\"Plfis\",\"Args\":[%a,%a]}" p_freg fr p_float32_constant fc
  | Plwz (ir1,ic,ir2) -> fprintf oc "{\"Instruction Name\":\"Plwz\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant ic p_ireg ir2
  | Plwz_a (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plwz\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plwzu (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plwzu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plwzx (ir1,ir2,ir3) 
  | Plwzx_a (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plwzx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plwarx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plwarx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plwbrx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plwbrx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmbar c -> fprintf oc "{\"Instruction Name\":\"Pmbar\",\"Args\":[%a]}" p_int_constant c
  | Pmfcr ir -> fprintf oc "{\"Instruction Name\":\"Pmfcr\",\"Args\":[%a]}" p_ireg ir
  | Pmfcrbit (ir,crb) -> assert false (* Should not occur *)
  | Pmflr ir -> fprintf oc "{\"Instruction Name\":\"Pmflr\",\"Args\":[%a]}" p_ireg ir
  | Pmr (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pmr\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pmtctr ir -> fprintf oc "{\"Instruction Name\":\"Pmtctr\",\"Args\":[%a]}" p_ireg ir
  | Pmtlr ir -> fprintf oc "{\"Instruction Name\":\"Pmtlr\",\"Args\":[%a]}" p_ireg ir
  | Pmfspr(ir, n) -> fprintf oc "{\"Instruction Name\":\"Pmfspr\",\"Args\":[%a,%a]}" p_ireg ir p_int_constant n
  | Pmtspr(n, ir) -> fprintf oc "{\"Instruction Name\":\"Pmtspr\",\"Args\":[%a,%a]}" p_int_constant n p_ireg ir
  | Pmulli (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pmulli\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Pmullw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pmullw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmulhw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pmulhw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmulhwu (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pmulhwu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pnand (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pnand\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pnor (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pnor\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Por (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Por\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Porc (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Porc\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pori (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pori\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Poris (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Poris\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Prlwinm (ir1,ir2,ic1,ic2) -> fprintf oc "{\"Instruction Name\":\"Prlwinm\",\"Args\":[%a,%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_int_constant ic1 p_int_constant ic2
  | Prlwimi  (ir1,ir2,ic1,ic2) -> fprintf oc "{\"Instruction Name\":\"Prlwimi\",\"Args\":[%a,%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_int_constant ic1 p_int_constant ic2
  | Pslw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pslw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psraw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psraw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psrawi  (ir1,ir2,ic) -> fprintf oc "{\"Instruction Name\":\"Psrawi\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_int_constant ic
  | Psrw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psrw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstb (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstb\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Pstbx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstbx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstfd (fr,c,ir)
  | Pstfd_a (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Pstfd\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Pstfdu (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Pstfdu\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Pstfdx (fr,ir1,ir2)
  | Pstfdx_a (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstfdx\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Pstfs (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Pstfs\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Pstfsx (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstfsx\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Psth (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Psth\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Psthx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psthx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psthbrx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psthbrx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstw (ir1,c,ir2)
  | Pstw_a (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Pstwu (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstwu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Pstwx (ir1,ir2,ir3)
  | Pstwx_a (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwux (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwux\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwbrx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwbrx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwcx_ (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwc_\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfc (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psubfc\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfe (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psubfe\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfze (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Psubfe\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Psubfic (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Psubfic\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Psync -> fprintf oc "{\"Instruction Name\":\"Psync\",\"Args\":[]}"
  | Ptrap -> fprintf oc "{\"Instruction Name\":\"Ptrap\",\"Args\":[]}"
  | Pxor (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pxor\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pxori (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pxori\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Pxoris (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pxoris\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Plabel l -> fprintf oc "{\"Instruction Name\":\"Plabel\",\"Args\":[%a]}" p_label l
  | Pbuiltin (ef,args1,args2) -> ()
(* FIXME *)
(*
      begin match ef with
      | EF_inline_asm (i,s,il) ->
          fprintf oc "{\"Instruction Name\":\"Inline_asm\",\"Args\":[%a%a%a%a]}" p_atom_constant i  (p_list_cont p_char_list) il
            (p_list_cont p_preg) args1  (p_list_cont p_preg) args2
      | _ -> (* Should all be folded away *)
          assert false
      end
*)
(* END FIXME *)
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
  | Section_user (s,w,e) -> fprintf oc "{\"Section Name\":%s,\"Writable\":%B,\"Executable\":%B}" s w e
  | Section_debug_info 
  | Section_debug_abbrev -> () (* There should be no info in the debug sections *)

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

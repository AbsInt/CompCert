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
open Camlcoq
open Printf

let p_ireg oc = function
  | GPR0 -> fprintf oc "{\"Register\":\"GPR0\"}"
  | GPR1 -> fprintf oc "{\"Register\":\"GPR1\"}"
  | GPR2 -> fprintf oc "{\"Register\":\"GPR2\"}"
  | GPR3 -> fprintf oc "{\"Register\":\"GPR3\"}"
  | GPR4 -> fprintf oc "{\"Register\":\"GPR4\"}"
  | GPR5 -> fprintf oc "{\"Register\":\"GPR5\"}"
  | GPR6 -> fprintf oc "{\"Register\":\"GPR6\"}"
  | GPR7 -> fprintf oc "{\"Register\":\"GPR7\"}"
  | GPR8 -> fprintf oc "{\"Register\":\"GPR8\"}"
  | GPR9 -> fprintf oc "{\"Register\":\"GPR9\"}"
  | GPR10 -> fprintf oc "{\"Register\":\"GPR10\"}"
  | GPR11 -> fprintf oc "{\"Register\":\"GPR11\"}"
  | GPR12 -> fprintf oc "{\"Register\":\"GPR12\"}"
  | GPR13 -> fprintf oc "{\"Register\":\"GPR13\"}"
  | GPR14 -> fprintf oc "{\"Register\":\"GPR14\"}"
  | GPR15 -> fprintf oc "{\"Register\":\"GPR15\"}"
  | GPR16 -> fprintf oc "{\"Register\":\"GPR16\"}"
  | GPR17 -> fprintf oc "{\"Register\":\"GPR17\"}"
  | GPR18 -> fprintf oc "{\"Register\":\"GPR18\"}"
  | GPR19 -> fprintf oc "{\"Register\":\"GPR19\"}"
  | GPR20 -> fprintf oc "{\"Register\":\"GPR20\"}"
  | GPR21 -> fprintf oc "{\"Register\":\"GPR21\"}"
  | GPR22 -> fprintf oc "{\"Register\":\"GPR22\"}"
  | GPR23 -> fprintf oc "{\"Register\":\"GPR23\"}"
  | GPR24 -> fprintf oc "{\"Register\":\"GPR24\"}"
  | GPR25 -> fprintf oc "{\"Register\":\"GPR25\"}"
  | GPR26 -> fprintf oc "{\"Register\":\"GPR26\"}"
  | GPR27 -> fprintf oc "{\"Register\":\"GPR27\"}"
  | GPR28 -> fprintf oc "{\"Register\":\"GPR28\"}"
  | GPR29 -> fprintf oc "{\"Register\":\"GPR29\"}"
  | GPR30 -> fprintf oc "{\"Register\":\"GPR30\"}"
  | GPR31 -> fprintf oc "{\"Register\":\"GPR31\"}"

let p_freg oc = function
  | FPR0 -> fprintf oc "{\"Register\":\"FPR0\"}"
  | FPR1 -> fprintf oc "{\"Register\":\"FPR1\"}"
  | FPR2 -> fprintf oc "{\"Register\":\"FPR2\"}"
  | FPR3 -> fprintf oc "{\"Register\":\"FPR3\"}"
  | FPR4 -> fprintf oc "{\"Register\":\"FPR4\"}"
  | FPR5 -> fprintf oc "{\"Register\":\"FPR5\"}"
  | FPR6 -> fprintf oc "{\"Register\":\"FPR6\"}"
  | FPR7 -> fprintf oc "{\"Register\":\"FPR7\"}"
  | FPR8 -> fprintf oc "{\"Register\":\"FPR8\"}"
  | FPR9 -> fprintf oc "{\"Register\":\"FPR9\"}"
  | FPR10 -> fprintf oc "{\"Register\":\"FPR10\"}"
  | FPR11 -> fprintf oc "{\"Register\":\"FPR11\"}"
  | FPR12 -> fprintf oc "{\"Register\":\"FPR12\"}"
  | FPR13 -> fprintf oc "{\"Register\":\"FPR13\"}"
  | FPR14 -> fprintf oc "{\"Register\":\"FPR14\"}"
  | FPR15 -> fprintf oc "{\"Register\":\"FPR15\"}"
  | FPR16 -> fprintf oc "{\"Register\":\"FPR16\"}"
  | FPR17 -> fprintf oc "{\"Register\":\"FPR17\"}"
  | FPR18 -> fprintf oc "{\"Register\":\"FPR18\"}"
  | FPR19 -> fprintf oc "{\"Register\":\"FPR19\"}"
  | FPR20 -> fprintf oc "{\"Register\":\"FPR20\"}"
  | FPR21 -> fprintf oc "{\"Register\":\"FPR21\"}"
  | FPR22 -> fprintf oc "{\"Register\":\"FPR22\"}"
  | FPR23 -> fprintf oc "{\"Register\":\"FPR23\"}"
  | FPR24 -> fprintf oc "{\"Register\":\"FPR24\"}"
  | FPR25 -> fprintf oc "{\"Register\":\"FPR25\"}"
  | FPR26 -> fprintf oc "{\"Register\":\"FPR26\"}"
  | FPR27 -> fprintf oc "{\"Register\":\"FPR27\"}"
  | FPR28 -> fprintf oc "{\"Register\":\"FPR28\"}"
  | FPR29 -> fprintf oc "{\"Register\":\"FPR29\"}"
  | FPR30 -> fprintf oc "{\"Register\":\"FPR30\"}"
  | FPR31 -> fprintf oc "{\"Register\":\"FPR31\"}"

let p_preg oc = function
  | IR ir -> p_ireg oc ir
  | FR fr -> p_freg oc fr
  | PC -> fprintf oc "{\"Register\":\"PC\"}"
  | LR -> fprintf oc "{\"Register\":\"LR\"}"
  | CTR -> fprintf oc "{\"Register\":\"CTR\"}"
  | CARRY -> fprintf oc "{\"Register\":\"CARRY\"}"
  | CR0_0 -> fprintf oc "{\"Register\":\"CR0_0\"}"
  | CR0_1 -> fprintf oc "{\"Register\":\"CR0_1\"}"
  | CR0_2 -> fprintf oc "{\"Register\":\"CR0_2\"}"
  | CR0_3 -> fprintf oc "{\"Register\":\"CR0_3\"}"
  | CR1_2 -> fprintf oc "{\"Register\":\"CR1_2\"}"

let p_atom oc a = fprintf oc "\"%s\"" (extern_atom a)

let p_int oc i = fprintf oc "%ld" (camlint_of_coqint i)
let p_int64 oc i = fprintf oc "%Ld" (camlint64_of_coqint i)
let p_float32 oc f = fprintf oc "%f" (camlfloat_of_coqfloat32 f)
let p_float64 oc f = fprintf oc "%f" (camlfloat_of_coqfloat f)
let p_z oc z = fprintf oc "%s" (Z.to_string z)


let p_constant oc  = function
  | Cint i -> fprintf oc "{\"Integer\":%a}" p_int i
  | Csymbol_low (i,c) -> fprintf oc "{\"Symbol_low\":[%a,%a]}" p_atom i p_int c
  | Csymbol_high (i,c) -> fprintf oc "{\"Symbol_high\":[%a,%a]}" p_atom i p_int c 
  | Csymbol_sda (i,c) -> fprintf oc "{\"Symbol_sda\":[%a,%a]}" p_atom i p_int c 
  | Csymbol_rel_low (i,c) -> fprintf oc "{\"Symbol_rel_low\":[%a,%a]}" p_atom i p_int c 
  | Csymbol_rel_high (i,c) -> fprintf oc "{\"Symbol_rel_high\":[%a,%a]}" p_atom i p_int c 

let p_crbit oc c = 
  let number = match c with
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3
  | CRbit_6 -> 6 in
  fprintf oc "{\"CRbit\":%d}" number


let p_label oc l = fprintf oc "{\"Label:\"%ld}" (P.to_int32 l)

let p_list elem oc l =
  match l with
  | [] -> fprintf oc "null"
  | hd::tail ->
      output_string oc "["; elem oc hd;List.iter (fprintf oc ",%a" elem) tail;output_string oc "]"

let p_list_cont elem oc l =
  match l with
  | [] -> ()
  | _ ->
      List.iter (fprintf oc ",%a" elem) l

let p_typ oc = function
    | Tint -> fprintf oc "\"Tint\""
    | Tfloat -> fprintf oc "\"Tfloat\""
    | Tlong -> fprintf oc "\"Tlong\""
    | Tsingle -> fprintf oc "\"Tsingle\""
    | Tany32 -> fprintf oc "\"Tany32\""
    | Tany64 -> fprintf oc "\"Tany64\""

let p_signature oc signature =
  let p_result oc = function
    | None -> fprintf oc "null"
    | Some e -> p_typ oc e in
  let p_calling_convention oc cc =
    fprintf oc "{\"Vararg\":%B,\"Structreg\":%B}" cc.cc_vararg cc.cc_structret
  in
  fprintf oc "{\"Sig_args\":%a,\"Sig_res\":%a,\"Sig_cc\":%a}"
    (p_list p_typ) signature.sig_args 
    p_result signature.sig_res
    p_calling_convention signature.sig_cc

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
  | Pallocframe (c,i) -> fprintf oc "{\"Instruction Name\":\"Pallocframe\",\"Args\":[%a,%a]}" p_z c p_int i
  | Pand_ (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pand_\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pandc (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pandc\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pandi_ (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pandi_\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Pandis_ (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pandis_\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Pb l -> fprintf oc "{\"Instruction Name\":\"Pb\",\"Args\":[%a]}" p_label l
  | Pbctr s ->  fprintf oc "{\"Instruction Name\":\"Pbctr\",\"Args\":[%a]}" p_signature s
  | Pbctrl s -> fprintf oc "{\"Instruction Name\":\"Pbctrl\",\"Args\":[%a]}" p_signature s
  | Pbdnz l -> fprintf oc "{\"Instruction Name\":\"Pbdnz\",\"Args\":[%a]}" p_label l 
  | Pbf (c,l) -> fprintf oc "{\"Instruction Name\":\"Pbf\",\"Args\":[%a,%a]}" p_crbit c p_label l
  | Pbl (i,s) -> fprintf oc "{\"Instruction Name\":\"Pbl\",\"Args\":[%a,%a]}"  p_atom i p_signature s
  | Pbs (i,s) -> fprintf oc "{\"Instruction Name\":\"Pbs\",\"Args\":[%a,%a]}"  p_atom i p_signature s
  | Pblr -> fprintf oc "{\"Instruction Name\":\"Pblr\",\"Args\":null}"
  | Pbt (cr,l) -> fprintf oc "{\"Instruction Name\":\"Pbt\",\"Args\":[%a,%a]}" p_crbit cr p_label l
  | Pbtbl (i,lb) -> fprintf oc "{\"Instruction Name\":\"Pbtl\",\"Args\":[%a,%a]}" p_ireg i (p_list p_label) lb
  | Pcmplw (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pcmplw\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pcmplwi (ir,c) -> fprintf oc "{\"Instruction Name\":\"Pcmplwi\",\"Args\":[%a,%a]}" p_ireg ir p_constant c
  | Pcmpw (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pcmpw\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pcmpwi (ir,c) -> fprintf oc "{\"Instruction Name\":\"Pcmpwi\",\"Args\":[%a,%a]}" p_ireg ir p_constant c 
  | Pcntlz (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pcntlz\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pcreqv (cr1,cr2,cr3) -> fprintf oc "{\"Instruction Name\":\"Pcreqv\",\"Args\":[%a,%a,%a]}" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pcror (cr1,cr2,cr3) -> fprintf oc "{\"Instruction Name\":\"Pcror\",\"Args\":[%a,%a,%a]}" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pcrxor (cr1,cr2,cr3) -> fprintf oc "{\"Instruction Name\":\"Pcrxor\",\"Args\":[%a,%a,%a]}" p_crbit cr1 p_crbit cr2 p_crbit cr3
  | Pdivw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pdivw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pdivwu (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pdivwu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Peieio -> fprintf oc "{\"Instruction Name\":\"Peieio,\"Args\":null}"
  | Peqv (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Peqv\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pextsb (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pextsb\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pextsh (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pextsh\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pfreeframe (c,i) -> fprintf oc "{\"Instruction Name\":\"Pfreeframe\",\"Args\":[%ld,%a]}" (Z.to_int32 c) p_int i
  | Pfabs (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfabs\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfabss (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfabss\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfadd (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfadd\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfadds (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfadds\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfcmpu (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfcmpu\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfcti (ir,fr) -> fprintf oc "{\"Instruction Name\":\"Pfcti\",\"Args\":[%a,%a]}" p_ireg ir p_freg fr
  | Pfctiw (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfctiw\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfctiwz (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfctiwz\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfdiv (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfdiv\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfdivs (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfdivs\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfmake (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pfmake\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Pfmr (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfmr\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfmul (fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfmul\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfmuls(fr1,fr2,fr3) -> fprintf oc "{\"Instruction Name\":\"Pfmuls\",\"Args\":[%a,%a,%a]}" p_freg fr1 p_freg fr2 p_freg fr3
  | Pfneg (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfneg\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfnegs (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfnegs\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfrsp (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfrsp\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
  | Pfxdp (fr1,fr2) -> fprintf oc "{\"Instruction Name\":\"Pfxdp\",\"Args\":[%a,%a]}" p_freg fr1 p_freg fr2
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
  | Pisync -> fprintf oc "{\"Instruction Name\":\"Pisync\",\"Args\":null}"
  | Plbz (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plbz\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plbzx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pblzx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plfd (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Plbz\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Plfdx (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Plfdx\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Plfd_a (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Plfd_a\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Plfdx_a (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Plfdx_a\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Plfs (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Plfs\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Plfsx  (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Plfsx\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Plha (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plha\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plhax (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plhax\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plhbrx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plhbrx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plhz (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plhz\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plhzx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plhzx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plfi (fr,fc) -> fprintf oc "{\"Instruction Name\":\"Plfi\",\"Args\":[%a,%a]}" p_freg fr p_float64 fc
  | Plfis (fr,fc) -> fprintf oc "{\"Instruction Name\":\"Plfis\",\"Args\":[%a,%a]}" p_freg fr p_float64 fc
  | Plwz (ir1,ic,ir2) -> fprintf oc "{\"Instruction Name\":\"Plwz\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant ic p_ireg ir2
  | Plwzu (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plwzu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plwzx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plwz\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plwz_a (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Plwz_a\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Plwzx_a (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plwzx_a\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plwarx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plwarx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Plwbrx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Plwbrx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmfcr ir -> fprintf oc "{\"Instruction Name\":\"Pmfcr\",\"Args\":[%a]}" p_ireg ir
  | Pmfcrbit (ir,crb) -> fprintf oc "{\"Instruction Name\":\"Pmfcrbit\",\"Args\":[%a,%a]}" p_ireg ir p_crbit crb
  | Pmflr ir -> fprintf oc "{\"Instruction Name\":\"Pmflr\",\"Args\":[%a]}" p_ireg ir
  | Pmr (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pmr\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Pmtctr ir -> fprintf oc "{\"Instruction Name\":\"Pmtctr\",\"Args\":[%a]}" p_ireg ir
  | Pmtlr ir -> fprintf oc "{\"Instruction Name\":\"Pmtlr\",\"Args\":[%a]}" p_ireg ir
  | Pmulli (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pmulli\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Pmullw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pmulw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmulhw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pmulhw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pmulhwu (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pmulhwu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pnand (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pnand\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pnor (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pnor\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Por (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Por\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Porc (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Porc\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pori (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pori\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Poris (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Poris\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Prlwinm (ir1,ir2,ic1,ic2) -> fprintf oc "{\"Instruction Name\":\"Prlwinm\",\"Args\":[%a,%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_int ic1 p_int ic2
  | Prlwimi  (ir1,ir2,ic1,ic2) -> fprintf oc "{\"Instruction Name\":\"Prlwimi\",\"Args\":[%a,%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_int ic1 p_int ic2
  | Pslw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pslw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psraw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psraw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psrawi  (ir1,ir2,ic) -> fprintf oc "{\"Instruction Name\":\"Psrawi\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_int ic
  | Psrw (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psrw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstb (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstb\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Pstbx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstbx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstfd (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Pstfd\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Pstfdu (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Pstdu\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Pstfdx (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Psrw\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Pstfd_a (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Pstfd_a\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Pstfdx_a (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstfdx_a\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Pstfs (fr,c,ir) -> fprintf oc "{\"Instruction Name\":\"Pstfs\",\"Args\":[%a,%a,%a]}" p_freg fr p_constant c p_ireg ir
  | Pstfsx (fr,ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstfsx\",\"Args\":[%a,%a,%a]}" p_freg fr p_ireg ir1 p_ireg ir2
  | Psth (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Psth\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Psthx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psthx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psthbrx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psthbrx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstw (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstw\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Pstwu (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstwu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Pstwx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwxu (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwxu\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstw_a (ir1,c,ir2) -> fprintf oc "{\"Instruction Name\":\"Pstw_a\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_constant c p_ireg ir2
  | Pstwx_a (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwx_a\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwbrx (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwbrx\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pstwcx_ (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pstwc_\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfc (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psubfc\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfe (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Psubfe\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Psubfze (ir1,ir2) -> fprintf oc "{\"Instruction Name\":\"Psubfe\",\"Args\":[%a,%a]}" p_ireg ir1 p_ireg ir2
  | Psubfic (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Psubfic\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Psync -> fprintf oc "{\"Instruction Name\":\"Psync\",\"Args\":null}"
  | Ptrap -> fprintf oc "{\"Instruction Name\":\"Ptrap\",\"Args\":null}"
  | Pxor (ir1,ir2,ir3) -> fprintf oc "{\"Instruction Name\":\"Pxor\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_ireg ir3
  | Pxori (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pxori\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Pxoris (ir1,ir2,c) -> fprintf oc "{\"Instruction Name\":\"Pxoris\",\"Args\":[%a,%a,%a]}" p_ireg ir1 p_ireg ir2 p_constant c
  | Plabel l -> fprintf oc "{\"Instruction Name\":\"Plabel\",\"Args\":[%a]}" p_label l
  | Pbuiltin (ef,args1,args2) ->
      begin match ef with
      | EF_inline_asm (i,s,il) ->
          fprintf oc "{\"Instruction Name\":\"Inline_asm\",\"Args\":[%a,%a%a%a%a]}" p_atom i p_signature s (p_list_cont p_atom) il
            (p_list_cont p_preg) args1  (p_list_cont p_preg) args2
      | _ -> (* Should all be folded away *)
          assert false
      end
  | Pannot _ -> () (* We do not check the annotations *)
  | Pcfi_adjust _ -> () (* Only debug relevant *)
  | Pcfi_rel_offset _ ->  () (* Only debug relevant *)

let p_fundef oc name = function
  | Internal f ->
      let instr = List.filter (function Pannot _ | Pcfi_adjust _ | Pcfi_rel_offset _ -> false | _ -> true) f.fn_code in
      fprintf oc "{\"Fun_name\":%a,\n\"Fun_sig\":%a,\n\"Fun_code\":%a}"
        p_atom name
        p_signature f.fn_sig (p_list p_instruction) instr
  | External _ ->() (* Is of no interest *)

let p_init_data oc = function
  | Init_int8 ic -> fprintf oc "{\"Init_int8\":%a}" p_int ic
  | Init_int16 ic -> fprintf oc "{\"Init_int16\":%a}" p_int ic
  | Init_int32 ic -> fprintf oc "{\"Init_int32\":%a}" p_int ic
  | Init_int64 lc -> fprintf oc "{\"Init_int64\":%a}" p_int64 lc
  | Init_float32 f -> fprintf oc "{\"Init_float32\":%a}" p_float32 f
  | Init_float64 f -> fprintf oc "{\"Init_float64\":%a}" p_float64 f
  | Init_space z -> fprintf oc "{\"Init_space\":%a}" p_z z
  | Init_addrof (p,i) -> fprintf oc "{\"Init_addrof\":[%a,%a]}" p_atom p p_int i

let p_prog_def oc (ident,def) =
  output_string oc "\n";
  match def with
  | Gfun f -> p_fundef oc ident f
  | Gvar v -> fprintf oc "{\"Var_name\":%a,\"Var_init\":%a,\"Var_readonly\":%B,\"Var_volatile\":%B}"
        p_atom ident (p_list p_init_data) v.gvar_init v.gvar_readonly v.gvar_volatile

let re_builtin = Str.regexp "__builtin_\\|__i64_\\|__compcert_"

let p_public oc p =
  let p = List.map extern_atom p in
  let p = List.filter (fun s -> 
    not (Str.string_match re_builtin s 0)) p in
  (p_list (fun oc s -> fprintf oc "\n\"%s\"" s)) oc p

let p_program oc prog =
  let prog_defs = List.filter (function _,Gfun (External _) -> false | _ -> true) prog.prog_defs in
  fprintf oc "{\"Prog_defs\":%a,\n\"Prog_public\":%a,\n\"Prog_main\":%a}"
    (p_list p_prog_def) prog_defs
    p_public prog.prog_public
    p_atom prog.prog_main

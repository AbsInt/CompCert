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

(* Simple functions to serialize RISC-V Asm to JSON *)

open Asm
open AST
open BinNums
open Camlcoq
open Json

module StringSet = Set.Make(String)

let mnemonic_names = StringSet.of_list
  [
  "Paddil"; "Paddiw"; "Paddl"; "Paddw"; "Pandil"; "Pandiw"; "Pandl"; "Pandw";
  "Pbeql"; "Pbeqw"; "Pbgel"; "Pbgeul"; "Pbgeuw"; "Pbgew"; "Pbltl"; "Pbltul";
  "Pbltuw"; "Pbltw"; "Pbnel"; "Pbnew"; "Pbtbl"; "Pdivl"; "Pdivul"; "Pdivuw";
  "Pdivw"; "Pfabsd"; "Pfabss"; "Pfaddd"; "Pfadds"; "Pfcvtdl"; "Pfcvtdlu";
  "Pfcvtds"; "Pfcvtdw"; "Pfcvtdwu"; "Pfcvtld"; "Pfcvtls"; "Pfcvtlud";
  "Pfcvtlus"; "Pfcvtsd"; "Pfcvtsl"; "Pfcvtslu"; "Pfcvtsw"; "Pfcvtswu";
  "Pfcvtwd"; "Pfcvtws"; "Pfcvtwud"; "Pfcvtwus"; "Pfdivd"; "Pfdivs"; "Pfence";
  "Pfeqd"; "Pfeqs"; "Pfld"; "Pfld_a"; "Pfled"; "Pfles"; "Pfls"; "Pfltd";
  "Pflts"; "Pfmaddd"; "Pfmadds"; "Pfmaxd"; "Pfmaxs"; "Pfmind"; "Pfmins";
  "Pfmsubd"; "Pfmsubs"; "Pfmuld"; "Pfmuls"; "Pfmv"; "Pfmvdx"; "Pfmvsx";
  "Pfmvxd"; "Pfmvxs"; "Pfnegd"; "Pfnegs"; "Pfnmaddd"; "Pfnmadds"; "Pfnmsubd";
  "Pfnmsubs"; "Pfsd"; "Pfsd_a"; "Pfsqrtd"; "Pfsqrts"; "Pfss"; "Pfsubd";
  "Pfsubs"; "Pj_l"; "Pj_r"; "Pj_s"; "Pjal_r"; "Pjal_s"; "Plabel"; "Plb";
  "Plbu"; "Pld"; "Pld_a"; "Plh"; "Plhu"; "Ploadfi"; "Ploadli"; "Ploadsi";
  "Ploadsymbol"; "Ploadsymbol_high"; "Pluil"; "Pluiw"; "Plw"; "Plw_a";
  "Pmulhl"; "Pmulhul"; "Pmulhuw"; "Pmulhw"; "Pmull"; "Pmulw"; "Pmv"; "Pnop";
  "Poril"; "Poriw"; "Porl"; "Porw"; "Preml"; "Premul"; "Premuw"; "Premw";
  "Psb"; "Psd"; "Psd_a"; "Psh"; "Psllil"; "Pslliw"; "Pslll"; "Psllw"; "Psltil";
  "Psltiul"; "Psltiuw"; "Psltiw"; "Psltl"; "Psltul"; "Psltuw"; "Psltw";
  "Psrail"; "Psraiw"; "Psral"; "Psraw"; "Psrlil"; "Psrliw"; "Psrll"; "Psrlw";
  "Psubl"; "Psubw"; "Psw"; "Psw_a"; "Pxoril"; "Pxoriw"; "Pxorl"; "Pxorw";
  ]

type instruction_arg =
  | ALabel of positive
  | Atom of positive
  | Float32 of Floats.float32
  | Float64 of Floats.float
  | Freg of freg
  | Id
  | Int of Integers.Int.int
  | Int64 of Integers.Int64.int
  | Ireg of ireg
  | Ireg0 of ireg0
  | Offset of offset
  | String of string
  | Symbol of ident * BinNums.coq_Z

let pp_reg pp reg =
  pp_jsingle_object pp "Register" pp_jstring reg

let pp_ireg pp reg =
  pp_reg pp (TargetPrinter.int_reg_name reg)

let pp_ireg0 pp reg =
  let rs = match reg with
  | X0 -> "x0"
  | X r -> TargetPrinter.int_reg_name r
  in
  pp_reg pp rs

let pp_freg pp reg =
  pp_reg pp (TargetPrinter.float_reg_name reg)

let pp_label pp l =
  pp_jsingle_object pp "ALabel" pp_jint32 (P.to_int32 l)

let pp_symbol pp (id, ofs) =
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Name" pp_atom id;
  pp_jmember pp "Offset" pp_z ofs;
  pp_jobject_end pp

let pp_offset pp ofs =
  match ofs with
  | Ofsimm(ofs) -> pp_jsingle_object pp "Integer" pp_int64 ofs
  | Ofslow(id, ofs) -> pp_jsingle_object pp "OffsetSymbolLow" pp_symbol (id, ofs)

let pp_arg pp = function
  | ALabel lbl -> pp_label pp lbl
  | Atom a -> pp_atom_constant pp a
  | Float32 f -> pp_float32_constant pp f
  | Float64 f  -> pp_float64_constant pp f
  | Freg fr -> pp_freg pp fr
  | Id -> pp_id_const pp ()
  | Int i
  | Int64 i -> pp_jsingle_object pp "Integer" pp_int64 i
  | Ireg ir -> pp_ireg pp ir
  | Ireg0 ir -> pp_ireg0 pp ir
  | Offset ofs -> pp_offset pp ofs
  | String s -> pp_jsingle_object pp "String" pp_jstring s
  | Symbol (id, ofs) -> pp_jsingle_object pp "Symbol" pp_symbol (id, ofs)

let pp_instructions pp ic =
  let ic = List.filter (fun s -> match s with
      | Pbuiltin (ef,args,_) ->
        begin match ef with
          | EF_inline_asm _ -> true
          | EF_annot  (kind,txt,targs) ->
            P.to_int kind = 2 && AisAnnot.json_ais_annot TargetPrinter.preg_annot "x2" (camlstring_of_coqstring txt) args <> []
          | _ -> false
        end
      | _ -> true) ic in

  let instruction pp n args =
    assert (StringSet.mem n mnemonic_names);
    pp_jobject_start pp;
    pp_jmember ~first:true pp "Instruction Name" pp_jstring n;
    pp_jmember pp "Args" (pp_jarray pp_arg) args;
    pp_jobject_end pp
  in

  let [@ocaml.warning "+4"] instruction pp = function
    | Pbuiltin (ef, args, _) ->
      begin match ef with
        | EF_inline_asm _ ->
          instruction pp "Pinlineasm" [Id];
          Diagnostics.(warning no_loc Inline_asm_sdump "inline assembler is not supported in sdump")
        | EF_annot (kind,txt, targs) ->

          begin match P.to_int kind with
          | 2 ->
            let annots = AisAnnot.json_ais_annot TargetPrinter.preg_annot "x2" (camlstring_of_coqstring txt) args in
            let annots = List.map (function
                | AisAnnot.String s -> String s
                | AisAnnot.Symbol s -> Atom s
                | AisAnnot.Label _ -> assert false (* should never happen *)
              ) annots in
            instruction pp "Pannot" annots
          | _ -> assert false
          end
        (* Builtins that are not exported to JSON *)
        | EF_annot_val _
        | EF_builtin _
        | EF_debug _
        | EF_external _
        | EF_free
        | EF_malloc
        | EF_memcpy _
        | EF_runtime _
        | EF_vload _
        | EF_vstore _ -> assert false
      end
    (* Expanded in Asmexpand *)
    | Pallocframe _
    | Pfreeframe _
    | Pseqw _
    | Psnew _
    | Pseql _
    | Psnel _
    | Pcvtl2w _
    | Pcvtw2l _ -> assert false
    (* RISC-V instructions *)
    | Paddil(rd, rs, imm) -> instruction pp "Paddil" [Ireg rd; Ireg0 rs; Int imm]
    | Paddiw(rd, rs, imm) -> instruction pp "Paddiw" [Ireg rd; Ireg0 rs; Int64 imm]
    | Paddl(rd, rs1, rs2) -> instruction pp "Paddl" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Paddw(rd, rs1, rs2) -> instruction pp "Paddw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pandil(rd, rs, imm) -> instruction pp "Pandil" [Ireg rd; Ireg0 rs; Int64 imm]
    | Pandiw(rd, rs, imm) -> instruction pp "Pandiw" [Ireg rd; Ireg0 rs; Int imm]
    | Pandl(rd, rs1, rs2) -> instruction pp "Pandl" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pandw(rd, rs1, rs2) -> instruction pp "Pandw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pbeql(rs1, rs2, l) -> instruction pp "Pbeql" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbeqw(rs1, rs2, l) -> instruction pp "Pbeqw" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbgel(rs1, rs2, l) -> instruction pp "Pbgel" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbgeul(rs1, rs2, l) -> instruction pp "Pbgeul" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbgeuw(rs1, rs2, l) -> instruction pp "Pbgeuw" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbgew(rs1, rs2, l) -> instruction pp "Pbgew" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbltl(rs1, rs2, l) -> instruction pp "Pbltl" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbltul(rs1, rs2, l) -> instruction pp "Pbltul" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbltuw(rs1, rs2, l) -> instruction pp "Pbltuw" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbltw(rs1, rs2, l) -> instruction pp "Pbltw" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbnel(rs1, rs2, l) -> instruction pp "Pbnel" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbnew(rs1, rs2, l) -> instruction pp "Pbnew" [Ireg0 rs1; Ireg0 rs2; ALabel l]
    | Pbtbl(r, tbl) -> instruction pp "Pbtbl" ((Ireg r)::(List.map (fun a -> ALabel a) tbl))
    | Pdivl(rd, rs1, rs2) -> instruction pp "Pdivl" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pdivul(rd, rs1, rs2) -> instruction pp "Pdivul" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pdivuw(rd, rs1, rs2) -> instruction pp "Pdivuw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pdivw(rd, rs1, rs2) -> instruction pp "Pdivw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pfabsd(rd, rs) -> instruction pp "Pfabsd" [Freg rd; Freg rs]
    | Pfabss(rd, rs) -> instruction pp "Pfabss" [Freg rd; Freg rs]
    | Pfaddd(rd, rs1, rs2) -> instruction pp "Pfaddd" [Freg rd; Freg rs1; Freg rs2]
    | Pfadds(rd, rs1, rs2) -> instruction pp "Pfadds" [Freg rd; Freg rs1; Freg rs2]
    | Pfcvtdl(rd, rs) -> instruction pp "Pfcvtdl" [Freg rd; Ireg0 rs]
    | Pfcvtdlu(rd, rs) -> instruction pp "Pfcvtdlu" [Freg rd; Ireg0 rs]
    | Pfcvtds(rd, rs) -> instruction pp "Pfcvtds" [Freg rd; Freg rs]
    | Pfcvtdw(rd, rs) -> instruction pp "Pfcvtdw" [Freg rd; Ireg0 rs]
    | Pfcvtdwu(rd, rs) -> instruction pp "Pfcvtdwu" [Freg rd; Ireg0 rs]
    | Pfcvtld(rd, rs) -> instruction pp "Pfcvtld" [Ireg rd; Freg rs]
    | Pfcvtls(rd, rs) -> instruction pp "Pfcvtls" [Ireg rd; Freg rs]
    | Pfcvtlud(rd, rs) -> instruction pp "Pfcvtlud" [Ireg rd; Freg rs]
    | Pfcvtlus(rd, rs) -> instruction pp "Pfcvtlus" [Ireg rd; Freg rs]
    | Pfcvtsd(rd, rs) -> instruction pp "Pfcvtsd" [Freg rd; Freg rs]
    | Pfcvtsl(rd, rs) -> instruction pp "Pfcvtsl" [Freg rd; Ireg0 rs]
    | Pfcvtslu(rd, rs) -> instruction pp "Pfcvtslu" [Freg rd; Ireg0 rs]
    | Pfcvtsw(rd, rs) -> instruction pp "Pfcvtsw" [Freg rd; Ireg0 rs]
    | Pfcvtswu(rd, rs) -> instruction pp "Pfcvtswu" [Freg rd; Ireg0 rs]
    | Pfcvtwd(rd, rs) -> instruction pp "Pfcvtwd" [Ireg rd; Freg rs]
    | Pfcvtws(rd, rs) -> instruction pp "Pfcvtws" [Ireg rd; Freg rs]
    | Pfcvtwud(rd, rs) -> instruction pp "Pfcvtwud" [Ireg rd; Freg rs]
    | Pfcvtwus(rd, rs) -> instruction pp "Pfcvtwus" [Ireg rd; Freg rs]
    | Pfdivd(rd, rs1, rs2) -> instruction pp "Pfdivd" [Freg rd; Freg rs1; Freg rs2]
    | Pfdivs(rd, rs1, rs2) -> instruction pp "Pfdivs" [Freg rd; Freg rs1; Freg rs2]
    | Pfence -> instruction pp "Pfence" []
    | Pfeqd(rd, rs1, rs2) -> instruction pp "Pfeqd" [Ireg rd; Freg rs1; Freg rs2]
    | Pfeqs(rd, rs1, rs2) -> instruction pp "Pfeqs" [Ireg rd; Freg rs1; Freg rs2]
    | Pfld(rd, ra, ofs) -> instruction pp "Pfld" [Freg rd; Ireg ra; Offset ofs]
    | Pfld_a(rd, ra, ofs) -> instruction pp "Pfld_a" [Freg rd; Ireg ra; Offset ofs]
    | Pfled(rd, rs1, rs2) -> instruction pp "Pfled" [Ireg rd; Freg rs1; Freg rs2]
    | Pfles(rd, rs1, rs2) -> instruction pp "Pfles" [Ireg rd; Freg rs1; Freg rs2]
    | Pfls(rd, ra, ofs) -> instruction pp "Pfls" [Freg rd; Ireg ra; Offset ofs]
    | Pfltd(rd, rs1, rs2) -> instruction pp "Pfltd" [Ireg rd; Freg rs1; Freg rs2]
    | Pflts(rd, rs1, rs2) -> instruction pp "Pflts" [Ireg rd; Freg rs1; Freg rs2]
    | Pfmaddd(rd, rs1, rs2, rs3) -> instruction pp "Pfmaddd" [Freg rd; Freg rs1; Freg rs2; Freg rs3]
    | Pfmadds(rd, rs1, rs2, rs3) -> instruction pp "Pfmadds" [Freg rd; Freg rs1; Freg rs2; Freg rs3]
    | Pfmaxd(rd, rs1, rs2) -> instruction pp "Pfmaxd" [Freg rd; Freg rs1; Freg rs2]
    | Pfmaxs(rd, rs1, rs2) -> instruction pp "Pfmaxs" [Freg rd; Freg rs1; Freg rs2]
    | Pfmind(rd, rs1, rs2) -> instruction pp "Pfmind" [Freg rd; Freg rs1; Freg rs2]
    | Pfmins(rd, rs1, rs2) -> instruction pp "Pfmins" [Freg rd; Freg rs1; Freg rs2]
    | Pfmsubd(rd, rs1, rs2, rs3) -> instruction pp "Pfmsubd" [Freg rd; Freg rs1; Freg rs2; Freg rs3]
    | Pfmsubs(rd, rs1, rs2, rs3) -> instruction pp "Pfmsubs" [Freg rd; Freg rs1; Freg rs2; Freg rs3]
    | Pfmuld(rd, rs1, rs2) -> instruction pp "Pfmuld" [Freg rd; Freg rs1; Freg rs2]
    | Pfmuls(rd, rs1, rs2) -> instruction pp "Pfmuls" [Freg rd; Freg rs1; Freg rs2]
    | Pfmv(rd, rs) -> instruction pp "Pfmv" [Freg rd; Freg rs]
    | Pfmvdx(rd, rs) -> instruction pp "Pfmvdx" [Freg rd; Ireg rs]
    | Pfmvsx(rd, rs) -> instruction pp "Pfmvsx" [Freg rd; Ireg rs]
    | Pfmvxd(rd, rs) -> instruction pp "Pfmvxd" [Ireg rd; Freg rs]
    | Pfmvxs(rd, rs) -> instruction pp "Pfmvxs" [Ireg rd; Freg rs]
    | Pfnegd(rd, rs) -> instruction pp "Pfnegd" [Freg rd; Freg rs]
    | Pfnegs(rd, rs) -> instruction pp "Pfnegs" [Freg rd; Freg rs]
    | Pfnmaddd(rd, rs1, rs2, rs3) -> instruction pp "Pfnmaddd" [Freg rd; Freg rs1; Freg rs2; Freg rs3]
    | Pfnmadds(rd, rs1, rs2, rs3) -> instruction pp "Pfnmadds" [Freg rd; Freg rs1; Freg rs2; Freg rs3]
    | Pfnmsubd(rd, rs1, rs2, rs3) -> instruction pp "Pfnmsubd" [Freg rd; Freg rs1; Freg rs2; Freg rs3]
    | Pfnmsubs(rd, rs1, rs2, rs3) -> instruction pp "Pfnmsubs" [Freg rd; Freg rs1; Freg rs2; Freg rs3]
    | Pfsd(rd, ra, ofs) -> instruction pp "Pfsd" [Freg rd; Ireg ra; Offset ofs]
    | Pfsd_a(rd, ra, ofs) -> instruction pp "Pfsd_a" [Freg rd; Ireg ra; Offset ofs]
    | Pfsqrtd(rd, rs) -> instruction pp "Pfsqrtd" [Freg rd; Freg rs]
    | Pfsqrts(rd, rs) -> instruction pp "Pfsqrts" [Freg rd; Freg rs]
    | Pfss(rd, ra, ofs) -> instruction pp "Pfss" [Freg rd; Ireg ra; Offset ofs]
    | Pfsubd(rd, rs1, rs2) -> instruction pp "Pfsubd" [Freg rd; Freg rs1; Freg rs2]
    | Pfsubs(rd, rs1, rs2) -> instruction pp "Pfsubs" [Freg rd; Freg rs1; Freg rs2]
    | Pj_l(l) -> instruction pp "Pj_l" [ALabel l]
    | Pj_r(r, sg) -> instruction pp "Pj_r" [Ireg r]
    | Pj_s(id, sg) -> instruction pp "Pj_s" [Atom id]
    | Pjal_r(r, sg) -> instruction pp "Pjal_r" [Ireg r]
    | Pjal_s(id, sg) -> instruction pp "Pjal_s" [Atom id]
    | Plabel l -> instruction pp "Plabel" [ALabel l]
    | Plb(rd, ra, ofs) -> instruction pp "Plb" [Ireg rd; Ireg ra; Offset ofs]
    | Plbu(rd, ra, ofs) -> instruction pp "Plbu" [Ireg rd; Ireg ra; Offset ofs]
    | Pld(rd, ra, ofs) -> instruction pp "Pld" [Ireg rd; Ireg ra; Offset ofs]
    | Pld_a(rd, ra, ofs) -> instruction pp "Pld_a" [Ireg rd; Ireg ra; Offset ofs]
    | Plh(rd, ra, ofs) -> instruction pp "Plh" [Ireg rd; Ireg ra; Offset ofs]
    | Plhu(rd, ra, ofs) -> instruction pp "Plhu" [Ireg rd; Ireg ra; Offset ofs]
    | Ploadfi(rd, f) -> instruction pp "Ploadfi" [Freg rd; Float64 f]
    | Ploadli(rd, i) -> instruction pp "Ploadli" [Ireg rd; Int64 i]
    | Ploadsi(rd, f) -> instruction pp "Ploadsi" [Freg rd; Float32 f]
    | Ploadsymbol(rd, id, ofs) -> instruction pp "Ploadsymbol" [Ireg rd; Symbol (id, ofs)]
    | Ploadsymbol_high(rd, id, ofs) -> instruction pp "Ploadsymbol_high" [Ireg rd; Symbol (id, ofs)]
    | Pluil(rd, imm) -> instruction pp "Pluil" [Ireg rd; Int64 imm]
    | Pluiw(rd, imm) -> instruction pp "Pluiw" [Ireg rd; Int imm]
    | Plw(rd, ra, ofs) -> instruction pp "Plw" [Ireg rd; Ireg ra; Offset ofs]
    | Plw_a(rd, ra, ofs) -> instruction pp "Plw_a" [Ireg rd; Ireg ra; Offset ofs]
    | Pmulhl(rd, rs1, rs2) -> instruction pp "Pmulhl" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pmulhul(rd, rs1, rs2) -> instruction pp "Pmulhul" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pmulhuw(rd, rs1, rs2) -> instruction pp "Pmulhuw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pmulhw(rd, rs1, rs2) -> instruction pp "Pmulhw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pmull(rd, rs1, rs2) -> instruction pp "Pmull" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pmulw(rd, rs1, rs2) -> instruction pp "Pmulw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pmv(rd, rs) -> instruction pp "Pmv" [Ireg rd; Ireg rs]
    | Pnop -> instruction pp "Pnop" []
    | Poril(rd, rs, imm) -> instruction pp "Poril" [Ireg rd; Ireg0 rs; Int64 imm]
    | Poriw(rd, rs, imm) -> instruction pp "Poriw" [Ireg rd; Ireg0 rs; Int imm]
    | Porl(rd, rs1, rs2) -> instruction pp "Porl" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Porw(rd, rs1, rs2) -> instruction pp "Porw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Preml(rd, rs1, rs2) -> instruction pp "Preml" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Premul(rd, rs1, rs2) -> instruction pp "Premul" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Premuw(rd, rs1, rs2) -> instruction pp "Premuw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Premw(rd, rs1, rs2) -> instruction pp "Premw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psb(rd, ra, ofs) -> instruction pp "Psb" [Ireg rd; Ireg ra; Offset ofs]
    | Psd(rd, ra, ofs) -> instruction pp "Psd" [Ireg rd; Ireg ra; Offset ofs]
    | Psd_a(rd, ra, ofs) -> instruction pp "Psd_a" [Ireg rd; Ireg ra; Offset ofs]
    | Psh(rs, ra, ofs) -> instruction pp "Psh" [Ireg rs; Ireg ra; Offset ofs]
    | Psllil(rd, rs, imm) -> instruction pp "Psllil" [Ireg rd; Ireg0 rs; Int imm]
    | Pslliw(rd, rs, imm) -> instruction pp "Pslliw" [Ireg rd; Ireg0 rs; Int imm]
    | Pslll(rd, rs1, rs2) -> instruction pp "Pslll" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psllw(rd, rs1, rs2) -> instruction pp "Psllw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psltil(rd, rs, imm) -> instruction pp "Psltil" [Ireg rd; Ireg0 rs; Int64 imm]
    | Psltiul(rd, rs, imm) -> instruction pp "Psltiul" [Ireg rd; Ireg0 rs; Int64 imm]
    | Psltiuw(rd, rs, imm) -> instruction pp "Psltiuw" [Ireg rd; Ireg0 rs; Int imm]
    | Psltiw(rd, rs, imm) -> instruction pp "Psltiw" [Ireg rd; Ireg0 rs; Int imm]
    | Psltl(rd, rs1, rs2) -> instruction pp "Psltl" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psltul(rd, rs1, rs2) -> instruction pp "Psltul" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psltuw(rd, rs1, rs2) -> instruction pp "Psltuw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psltw(rd, rs1, rs2) -> instruction pp "Psltw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psrail(rd, rs, imm) -> instruction pp "Psrail" [Ireg rd; Ireg0 rs; Int imm]
    | Psraiw(rd, rs, imm) -> instruction pp "Psraiw" [Ireg rd; Ireg0 rs; Int imm]
    | Psral(rd, rs1, rs2) -> instruction pp "Psral" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psraw(rd, rs1, rs2) -> instruction pp "Psraw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psrlil(rd, rs, imm) -> instruction pp "Psrlil" [Ireg rd; Ireg0 rs; Int imm]
    | Psrliw(rd, rs, imm) -> instruction pp "Psrliw" [Ireg rd; Ireg0 rs; Int imm]
    | Psrll(rd, rs1, rs2) -> instruction pp "Psrll" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psrlw(rd, rs1, rs2) -> instruction pp "Psrlw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psubl(rd, rs1, rs2) -> instruction pp "Psubl" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psubw(rd, rs1, rs2) -> instruction pp "Psubw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Psw(rs, ra, ofs) -> instruction pp "Psw" [Ireg rs; Ireg ra; Offset ofs]
    | Psw_a(rs, ra, ofs) -> instruction pp "Psw_a" [Ireg rs; Ireg ra; Offset ofs]
    | Pxoril(rd, rs, imm) -> instruction pp "Pxoril" [Ireg rd; Ireg0 rs; Int64 imm]
    | Pxoriw(rd, rs, imm) -> instruction pp "Pxoriw" [Ireg rd; Ireg0 rs; Int imm]
    | Pxorl(rd, rs1, rs2) -> instruction pp "Pxorl" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
    | Pxorw(rd, rs1, rs2) -> instruction pp "Pxorw" [Ireg rd; Ireg0 rs1; Ireg0 rs2]
  in
    pp_jarray instruction pp ic

let destination: string option ref = ref None

let sdump_folder = ref ""

let print_if prog sourcename =
  match !destination with
  | None -> ()
  | Some f ->
    let f = Filename.concat !sdump_folder f in
    let oc = open_out_bin f in
    JsonAST.pp_ast oc pp_instructions prog sourcename;
    close_out oc

let pp_mnemonics pp =
  JsonAST.pp_mnemonics pp (StringSet.elements mnemonic_names)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*          Michael Schmidt, AbsInt Angewandte Informatik GmbH         *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(* Simple functions to serialize arm Asm to JSON *)

open Asm
open AST
open BinNums
open Camlcoq
open Json

let mnemonic_names = [ "Padc"; "Padd"; "Padds"; "Pand";"Pannot"; "Pasr"; "Pb"; "Pbc"; "Pbic"; "Pblreg";
                       "Pblsymb"; "Pbne"; "Pbreg"; "Pbsymb"; "Pbtbl"; "Pclz"; "Pcmp"; "Pcmn"; "Pconstants"; "Pfcpy_iif";
                       "Pfcpy_fii"; "Pfcpy_fi"; "Pfcpy_sf"; "Pflid_lbl"; "Pflis_lbl"; "Pdmb"; "Pdsb"; "Peor"; "Pfabsd";
                       "Pfabss"; "Pfaddd"; "Pfadds"; "Pfcmpd"; "Pfcmps"; "Pfcmpzd"; "Pfcmpzs";
                       "Pfcpyd"; "Pfcpy_fs"; "Pfcpy_if";"Pfcvtds"; "Pfcvtsd"; "Pfdivd"; "Pfdivs"; "Pfldd";
                       "Pflid"; "Pflds"; "Pflid_imm"; "Pflis_imm"; "Pfmuld"; "Pfmuls"; "Pfnegd";
                       "Pfnegs"; "Pfsitod"; "Pfsitos"; "Pfsqrt"; "Pfstd";
                       "Pfsts"; "Pfsubd"; "Pfsubs"; "Pftosizd"; "Pftosizs"; "Pftouizd";
                       "Pftouizs"; "Pfuitod"; "Pfuitos"; "Pinlineasm"; "Pisb"; "Plabel"; "Pldr";
                       "Ploadsymbol_lbl"; "Pldr_p"; "Pldrb"; "Pldrb_p"; "Pldrh"; "Pldrh_p"; "Pldrsb";
                       "Pldrsh"; "Plsl"; "Plsr"; "Pmla"; "Pmov"; "Pmovite";
                       "Pmovt"; "Pmovw"; "Pmul"; "Pmvn";  "Ploadsymbol_imm"; "Pnop"; "Porr";
                       "Ppush"; "Prev"; "Prev16"; "Prsb"; "Prsbs"; "Prsc"; "Psbc"; "Psbfx"; "Psdiv"; "Psmull";
                       "Pstr"; "Pstr_p"; "Pstrb"; "Pstrb_p"; "Pstrh"; "Pstrh_p"; "Psub"; "Psubs"; "Pudiv";
                       "Pumull" ]

type instruction_arg =
  | ALabel of positive
  | Atom of positive
  | Data32 of Integers.Int.int
  | Data64 of Integers.Int64.int
  | DFreg of freg
  | Float32 of Floats.float32
  | Float64 of Floats.float
  | Id
  | Ireg of ireg
  | Long of Integers.Int.int
  | SFreg of freg
  | SPreg of sreg
  | Shift of shift_op
  | String of string
  | Symbol of ident * BinNums.coq_Z
  | Condition of string

let makedata (c : code_constant) : instruction_arg =
 match c with
 | Asm.Float32(_, f) -> Data32 (Floats.Float32.to_bits f)
 | Asm.Float64(_, f) -> Data64 (Floats.Float.to_bits f)
 | Asm.Symbol(_, id, ofs) -> Symbol(id, ofs)

let pp_reg pp reg =
  pp_jsingle_object pp "Register" pp_jstring reg

let pp_ireg pp reg =
  pp_reg pp (TargetPrinter.int_reg_name reg)

let pp_freg pp reg =
  pp_reg pp (TargetPrinter.float_reg_name reg)

let pp_single_freg pp reg =
  pp_reg pp (TargetPrinter.single_float_reg_name reg)

let pp_single_param_reg pp reg =
  pp_reg pp (TargetPrinter.single_param_reg_name reg)

let pp_shiftreg pp (r, op, n) =
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Register" pp_jstring (TargetPrinter.int_reg_name r);
  pp_jmember pp "Op" pp_jstring op;
  pp_jmember pp "Amount" pp_z n;
  pp_jobject_end pp

let pp_shiftop pp so =
  let (r, op, n) = match so with
    | SOimm n     -> (None, None, Some n)
    | SOreg r     -> (Some r, None, None)
    | SOlsl(r, n) -> (Some r, Some "lsl", Some n)
    | SOlsr(r, n) -> (Some r, Some "lsr", Some n)
    | SOasr(r, n) -> (Some r, Some "asr", Some n)
    | SOror(r, n) -> (Some r, Some "ror", Some n)
  in
  match (r, op, n) with
    | (None, None, Some n)      -> pp_jsingle_object pp "Integer" pp_int64 n
    | (Some r, None, None)      -> pp_ireg pp r
    | (Some r, Some op, Some n) -> pp_jsingle_object pp "ShiftedRegister" pp_shiftreg (r, op, n)
    | _ -> assert false

let pp_testcond pp bit =
  pp_jsingle_object pp "Condition" pp_jstring bit

let pp_label pp l =
  pp_jsingle_object pp "Label" pp_jint32 (P.to_int32 l)

let pp_symbol pp (id, ofs) =
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Name" pp_atom id;
  pp_jmember pp "Offset" pp_z ofs;
  pp_jobject_end pp


let pp_arg pp = function
  | ALabel lbl -> pp_label pp lbl
  | Atom a -> pp_atom_constant pp a
  | Data32 i -> pp_jsingle_object pp "Data32" pp_int i
  | Data64 i -> pp_jsingle_object pp "Data64" pp_int64 i
  | DFreg fr -> pp_freg pp fr
  | Float32 f -> pp_float32_constant pp f
  | Float64 f  -> pp_float64_constant pp f
  | Id ->  pp_id_const pp ()
  | Ireg ir -> pp_ireg pp ir
  | Long i ->  pp_jsingle_object pp "Integer" pp_int64 i
  | SFreg fr -> pp_single_freg pp fr
  | SPreg sr -> pp_single_param_reg pp sr
  | Shift so -> pp_shiftop pp so
  | String s -> pp_jsingle_object pp "String" pp_jstring s
  | Symbol (id, ofs) -> pp_jsingle_object pp "Symbol" pp_symbol (id, ofs)
  | Condition b -> pp_testcond pp b


let pp_instructions pp ic =
  let ic = List.filter (fun s -> match s with
      | Pbuiltin (ef,args,_) ->
        begin match ef with
          | EF_inline_asm _ -> true
          | EF_annot  (kind,txt,targs) ->
            P.to_int kind = 2 && AisAnnot.json_ais_annot TargetPrinter.preg_annot "r13" (camlstring_of_coqstring txt) args <> []
          | _ -> false
        end
      (* Only debug relevant *)
      | Pcfi_adjust _
      | Pcfi_rel_offset _ -> false
      | _ -> true) ic in

  let instruction pp n args =
    assert (List.mem n mnemonic_names);
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
            let annots = AisAnnot.json_ais_annot TargetPrinter.preg_annot "r13" (camlstring_of_coqstring txt) args in
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
    (* Stackframe, should not occur *)
    | Pallocframe _ -> assert false
    | Pfreeframe _  -> assert false
    (* Call Frame Information, only debug relevant and not exported *)
    | Pcfi_adjust _ -> assert false
    | Pcfi_rel_offset _ -> assert false
    (* Should be eliminated in constant expansion step *)
    | Pflis(r1, f) -> assert false
    | Ploadsymbol(r1, id, ofs) -> assert false
    (* ARM instructions *)
    | Padc(r1, r2, so) -> instruction pp "Padc" [Ireg r1; Ireg r2; Shift so]
    | Padd(r1, r2, so) -> instruction pp "Padd" [Ireg r1; Ireg r2; Shift so]
    | Padds(r1, r2, so) -> instruction pp "Padds" [Ireg r1; Ireg r2; Shift so]
    | Pand(r1, r2, so) -> instruction pp "Pand" [Ireg r1; Ireg r2; Shift so]
    | Pasr(r1, r2, r3) -> instruction pp "Pasr" [Ireg r1; Ireg r2; Ireg r3]
    | Pb(lbl) -> instruction pp "Pb" [ALabel lbl]
    | Pbc(bit, lbl) -> instruction pp "Pbc" [Condition (TargetPrinter.condition_name bit); ALabel lbl]
    | Pbic(r1, r2, so) -> instruction pp "Pbic" [Ireg r1; Ireg r2; Shift so]
    | Pblreg(r, sg) -> instruction pp "Pblreg" [Ireg r]
    | Pblsymb(id, sg) -> instruction pp "Pblsymb" [Atom id]
    | Pbne(lbl) -> instruction pp "Pbne" [ALabel lbl]
    | Pbreg(r, sg) -> instruction pp "Pbreg" [Ireg r]
    | Pbsymb(id, sg) -> instruction pp "Pbsymb" [Atom id]
    | Pbtbl(r, tbl) -> instruction pp "Pbtbl" ((Ireg r)::(List.map (fun a -> ALabel a) tbl))
    | Pclz(r1, r2) -> instruction pp "Pclz" [Ireg r1; Ireg r2]
    | Pcmp(r1,so) -> instruction pp "Pcmp" [Ireg r1; Shift so]
    | Pcmn(r1,so) -> instruction pp "Pcmn" [Ireg r1; Shift so]
    | Pdmb -> instruction pp "Pdmb" []
    | Pdsb -> instruction pp "Pdsb" []
    | Peor(r1, r2, so) -> instruction pp "Peor" [Ireg r1; Ireg r2; Shift so]
    | Pfabsd(r1, r2) -> instruction pp "Pfabsd" [DFreg r1; DFreg r2]
    | Pfabss(r1, r2) -> instruction pp "Pfabss" [SFreg r1; SFreg r2]
    | Pfaddd(r1, r2, r3) -> instruction pp "Pfaddd" [DFreg r1; DFreg r2; DFreg r3]
    | Pfadds(r1, r2, r3) -> instruction pp "Pfadds" [SFreg r1; SFreg r2; SFreg r3]
    | Pfcmpd(r1, r2) -> instruction pp "Pfcmpd" [DFreg r1; DFreg r2]
    | Pfcmps(r1, r2) -> instruction pp "Pfcmps" [SFreg r1; SFreg r2]
    | Pfcmpzd(r1) -> instruction pp "Pfcmpzd" [DFreg r1]
    | Pfcmpzs(r1) -> instruction pp "Pfcmpzs" [SFreg r1]
    | Pfcpyd(r1, r2) -> instruction pp "Pfcpyd" [DFreg r1; DFreg r2]
    | Pfcvtds(r1, r2) -> instruction pp "Pfcvtds" [DFreg r1; SFreg r2]
    | Pfcvtsd(r1, r2) -> instruction pp "Pfcvtsd" [SFreg r1; DFreg r2]
    | Pfdivd(r1, r2, r3) -> instruction pp "Pfdivd" [DFreg r1; DFreg r2; DFreg r3]
    | Pfdivs(r1, r2, r3) -> instruction pp "Pfdivs" [SFreg r1; SFreg r2; SFreg r3]
    | Pfldd(r1, r2, n) | Pfldd_a(r1, r2, n) -> instruction pp "Pfldd" [DFreg r1; Ireg r2; Long n]
    | Pflds(r1, r2, n) -> instruction pp "Pflds" [SFreg r1; Ireg r2; Long n]
    | Pflid(r1, f) -> instruction pp "Pflid" [DFreg r1; Float64 f]
    | Pfmuld(r1, r2, r3) -> instruction pp "Pfmuld" [DFreg r1; DFreg r2; DFreg r3]
    | Pfmuls(r1, r2, r3) -> instruction pp "Pfmuls" [SFreg r1; SFreg r2; SFreg r3]
    | Pfnegd(r1, r2) -> instruction pp "Pfnegd" [DFreg r1; DFreg r2]
    | Pfnegs(r1, r2) -> instruction pp "Pfnegs" [SFreg r1; SFreg r2]
    | Pfsitod(r1, r2) -> instruction pp "Pfsitod" [DFreg r1; Ireg r2]
    | Pfsitos(r1, r2) -> instruction pp "Pfsitos" [SFreg r1; Ireg r2]
    | Pfsqrt(r1, r2) -> instruction pp "Pfsqrt" [DFreg r1; DFreg r2]
    | Pfstd(r1, r2, n) | Pfstd_a(r1, r2, n) -> instruction pp "Pfstd" [DFreg r1; Ireg r2; Long n]
    | Pfsts(r1, r2, n) -> instruction pp "Pfsts" [SFreg r1; Ireg r2; Long n]
    | Pfsubd(r1, r2, r3) -> instruction pp "Pfsubd" [DFreg r1; DFreg r2; DFreg r3]
    | Pfsubs(r1, r2, r3) -> instruction pp "Pfsubs" [SFreg r1; SFreg r2; SFreg r3]
    | Pftosizd(r1, r2) -> instruction pp "Pftosizd" [Ireg r1; DFreg r2]
    | Pftosizs(r1, r2) -> instruction pp "Pftosizs" [Ireg r1; SFreg r2]
    | Pftouizd(r1, r2) -> instruction pp "Pftouizd" [Ireg r1; DFreg r2]
    | Pftouizs(r1, r2) -> instruction pp "Pftouizs" [Ireg r1; SFreg r2]
    | Pfuitod(r1, r2) -> instruction pp "Pfuitod" [DFreg r1; Ireg r2]
    | Pfuitos(r1, r2) -> instruction pp "Pfuitos" [SFreg r1; Ireg r2]
    | Pisb -> instruction pp "Pisb" []
    | Plabel l -> instruction pp "Plabel" [ALabel l]
    | Pldr(r1, r2, so) | Pldr_a(r1, r2, so) -> instruction pp "Pldr" [Ireg r1; Ireg r2; Shift so]
    | Pldr_p(r1, r2, so) -> instruction pp "Pldr_p" [Ireg r1; Ireg r2; Shift so]
    | Pldrb(r1, r2, so) -> instruction pp "Pldrb" [Ireg r1; Ireg r2; Shift so]
    | Pldrb_p(r1, r2, so) -> instruction pp "Pldrb_p" [Ireg r1; Ireg r2; Shift so]
    | Pldrh(r1, r2, so) -> instruction pp "Pldrh" [Ireg r1; Ireg r2; Shift so]
    | Pldrh_p(r1, r2, so) -> instruction pp "Pldrh_p" [Ireg r1; Ireg r2; Shift so]
    | Pldrsb(r1, r2, so) -> instruction pp "Pldrsb" [Ireg r1; Ireg r2; Shift so]
    | Pldrsh(r1, r2, so) -> instruction pp "Pldrsh" [Ireg r1; Ireg r2; Shift so]
    | Plsl(r1, r2, r3) -> instruction pp "Plsl" [Ireg r1; Ireg r2; Ireg r3]
    | Plsr(r1, r2, r3) -> instruction pp "Plsr" [Ireg r1; Ireg r2; Ireg r3]
    | Pmla(r1, r2, r3, r4) -> instruction pp "Pmla" [Ireg r1; Ireg r2; Ireg r3; Ireg r4]
    | Pmov(r1, so) -> instruction pp "Pmov" [Ireg r1; Shift so]
    | Pmovite(cond, r1, so1, so2) -> instruction pp "Pmovite" [Ireg r1; Condition (TargetPrinter.condition_name cond); Shift so1; Condition (TargetPrinter.neg_condition_name cond); Shift so2]
    | Pmovt(r1, n) -> instruction pp "Pmovt" [Ireg r1; Long n]
    | Pmovw(r1, n) -> instruction pp "Pmovw" [Ireg r1; Long n]
    | Pmul(r1, r2, r3) -> instruction pp "Pmul" [Ireg r1; Ireg r2; Ireg r3]
    | Pmvn(r1, so) -> instruction pp "Pmvn" [Ireg r1; Shift so]
    | Pnop -> instruction pp "Pnop" []
    | Porr(r1, r2, so) -> instruction pp "Porr" [Ireg r1; Ireg r2; Shift so]
    | Ppush(rl) -> instruction pp "Ppush" (List.map (fun r -> Ireg r) rl)
    | Prev(r1, r2) -> instruction pp "Prev" [Ireg r1; Ireg r2]
    | Prev16(r1, r2) -> instruction pp "Prev16" [Ireg r1; Ireg r2]
    | Prsb(r1, r2, so) -> instruction pp "Prsb" [Ireg r1; Ireg r2; Shift so]
    | Prsbs(r1, r2, so) -> instruction pp "Prsbs" [Ireg r1; Ireg r2; Shift so]
    | Prsc(r1, r2, so) -> instruction pp "Prsc" [Ireg r1; Ireg r2; Shift so]
    | Psbc(r1, r2, so) -> instruction pp "Psbc" [Ireg r1; Ireg r2; Shift so]
    | Psbfx(r1, r2, lsb, sz) -> instruction pp "Psbfx" [Ireg r1; Ireg r2; Long lsb; Long sz]
    | Psdiv -> instruction pp "Psdiv" [Ireg IR0; Ireg IR0; Ireg IR1]
    | Psmull(r1, r2, r3, r4) -> instruction pp "Psmull" [Ireg r1; Ireg r2; Ireg r3; Ireg r4]
    | Pstr(r1, r2, so) | Pstr_a(r1, r2, so) -> instruction pp "Pstr" [Ireg r1; Ireg r2; Shift so]
    | Pstr_p(r1, r2, so) -> instruction pp "Pstr_p" [Ireg r1; Ireg r2; Shift so]
    | Pstrb(r1, r2, so) -> instruction pp "Pstrb" [Ireg r1; Ireg r2; Shift so]
    | Pstrb_p(r1, r2, so) -> instruction pp "Pstrb_p" [Ireg r1; Ireg r2; Shift so]
    | Pstrh(r1, r2, so) -> instruction pp "Pstrh" [Ireg r1; Ireg r2; Shift so]
    | Pstrh_p(r1, r2, so) -> instruction pp "Pstrh_p" [Ireg r1; Ireg r2; Shift so]
    | Psub(r1, r2, so) -> instruction pp "Psub" [Ireg r1; Ireg r2; Shift so]
    | Psubs(r1, r2, so) -> instruction pp "Psubs" [Ireg r1; Ireg r2; Shift so]
    | Pudiv -> instruction pp "Pudiv" [Ireg IR0; Ireg IR0; Ireg IR1]
    | Pumull(r1, r2, r3, r4) -> instruction pp "Pumull" [Ireg r1; Ireg r2; Ireg r3; Ireg r4]
    (* Fixup instructions for calling conventions *)
    | Pfcpy_fs(r1, r2) -> instruction pp "Pfcpy_fs" [SFreg r1; SPreg r2]
    | Pfcpy_sf(r1, r2) -> instruction pp "Pfcpy_sf" [SPreg r1; SFreg r2]
    | Pfcpy_fii(r1, r2, r3) -> instruction pp "Pfcpy_fii" [DFreg r1; Ireg r2; Ireg r3]
    | Pfcpy_fi(r1, r2) -> instruction pp "Pfcpy_fi" [SFreg r1; Ireg r2]
    | Pfcpy_iif(r1, r2, r3) -> instruction pp "Pfcpy_iif" [Ireg r1; Ireg r2; DFreg r3]
    | Pfcpy_if (r1,r2) -> instruction pp "Pfcpy_if" [Ireg r1; SFreg r2]
    (* Pseudo instructions from constant expansion step *)
    | Pconstants consts -> instruction pp "Pconstants" (List.map makedata consts)
    | Ploadsymbol_imm (r1,id,ofs) -> instruction pp "Ploadsymbol_imm" [Ireg r1; Symbol (id,ofs)]
    | Pflid_lbl (r1,lbl,f) -> instruction pp "Pflid_lbl" [DFreg r1; ALabel lbl; Float64 f]
    | Pflis_lbl (r1,lbl,f) -> instruction pp "Pflis_lbl" [SFreg r1; ALabel lbl; Float32 f]
    | Pflid_imm (r1,f) -> instruction pp "Pflid_imm" [DFreg r1; Float64 f]
    | Pflis_imm (r1,f) -> instruction pp "Pflis_imm" [SFreg r1; Float32 f]
    | Ploadsymbol_lbl (r1,lbl,id,ofs) -> instruction pp "Ploadsymbol_lbl" [Ireg r1; ALabel lbl; Symbol (id,ofs)]
  in
    pp_jarray instruction pp ic

let destination : string option ref = ref None
let sdump_folder : string ref = ref ""

let print_if prog sourcename =
  match !destination with
  | None -> ()
  | Some f ->
    let f = Filename.concat !sdump_folder f in
    let oc = open_out_bin f in
    JsonAST.pp_ast (Format.formatter_of_out_channel oc) pp_instructions prog sourcename;
    close_out oc

let pp_mnemonics pp =
  JsonAST.pp_mnemonics pp mnemonic_names

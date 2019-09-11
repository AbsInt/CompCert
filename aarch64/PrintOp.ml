(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printing of operators, conditions, addressing modes *)

open Printf
open Camlcoq
open Integers
open Op

let comparison_name = function
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

let shift pp (s, a) =
  match s with
  | Slsl -> fprintf pp "<< %ld" (camlint_of_coqint a)
  | Slsr -> fprintf pp ">>u %ld" (camlint_of_coqint a)
  | Sasr -> fprintf pp ">>s %ld" (camlint_of_coqint a)
  | Sror -> fprintf pp "ror %ld" (camlint_of_coqint a)

let shiftl pp (s, a) =
  match s with
  | Slsl -> fprintf pp "<<l %ld" (camlint_of_coqint a)
  | Slsr -> fprintf pp ">>lu %ld" (camlint_of_coqint a)
  | Sasr -> fprintf pp ">>ls %ld" (camlint_of_coqint a)
  | Sror -> fprintf pp "rorl %ld" (camlint_of_coqint a)

let extend_name = function
  | Xsgn32 -> "sext"
  | Xuns32 -> "zext"

let print_condition reg pp = function
  | (Ccomp c, [r1;r2]) ->
      fprintf pp "%a %ss %a" reg r1 (comparison_name c) reg r2
  | (Ccompu c, [r1;r2]) ->
      fprintf pp "%a %su %a" reg r1 (comparison_name c) reg r2
  | (Ccompimm(c, n), [r1]) ->
      fprintf pp "%a %ss %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompuimm(c, n), [r1]) ->
      fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompshift(c, s, a), [r1;r2]) ->
      fprintf pp "%a %ss %a %a" reg r1 (comparison_name c) reg r2 shift (s, a)
  | (Ccompushift(c, s, a), [r1;r2]) ->
      fprintf pp "%a %su %a %a" reg r1 (comparison_name c) reg r2 shift (s, a)
  | (Cmaskzero n, [r1]) ->
      fprintf pp "%a & 0x%lx == 0" reg r1 (camlint_of_coqint n)
  | (Cmasknotzero n, [r1]) ->
      fprintf pp "%a & 0x%lx != 0" reg r1 (camlint_of_coqint n)
  | (Ccompl c, [r1;r2]) ->
      fprintf pp "%a %sls %a" reg r1 (comparison_name c) reg r2
  | (Ccomplu c, [r1;r2]) ->
      fprintf pp "%a %slu %a" reg r1 (comparison_name c) reg r2
  | (Ccomplimm(c, n), [r1]) ->
      fprintf pp "%a %sls %Ld" reg r1 (comparison_name c) (camlint64_of_coqint n)
  | (Ccompluimm(c, n), [r1]) ->
      fprintf pp "%a %slu %Ld" reg r1 (comparison_name c) (camlint64_of_coqint n)
  | (Ccomplshift(c, s, a), [r1;r2]) ->
      fprintf pp "%a %sls %a %a" reg r1 (comparison_name c) reg r2 shift (s, a)
  | (Ccomplushift(c, s, a), [r1;r2]) ->
      fprintf pp "%a %slu %a %a" reg r1 (comparison_name c) reg r2 shift (s, a)
  | (Cmasklzero n, [r1]) ->
      fprintf pp "%a &l 0x%Lx == 0" reg r1 (camlint64_of_coqint n)
  | (Cmasklnotzero n, [r1]) ->
      fprintf pp "%a &l 0x%Lx != 0" reg r1 (camlint64_of_coqint n)
  | (Ccompf c, [r1;r2]) ->
      fprintf pp "%a %sf %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompf c, [r1;r2]) ->
      fprintf pp "%a not(%sf) %a" reg r1 (comparison_name c) reg r2
  | (Ccompfzero c, [r1]) ->
      fprintf pp "%a %sf 0.0" reg r1 (comparison_name c)
  | (Cnotcompfzero c, [r1]) ->
      fprintf pp "%a not(%sf) 0.0" reg r1 (comparison_name c)
  | (Ccompfs c, [r1;r2]) ->
      fprintf pp "%a %sfs %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompfs c, [r1;r2]) ->
      fprintf pp "%a not(%sfs) %a" reg r1 (comparison_name c) reg r2
  | (Ccompfszero c, [r1]) ->
      fprintf pp "%a %sfs 0.0" reg r1 (comparison_name c)
  | (Cnotcompfszero c, [r1]) ->
      fprintf pp "%a not(%sfs) 0.0" reg r1 (comparison_name c)
  | _ ->
      fprintf pp "<bad condition>"

let print_operation reg pp = function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Olongconst n, [] -> fprintf pp "%LdL" (camlint64_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "%F" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "%Ff" (camlfloat_of_coqfloat32 n)
  | Oaddrsymbol(id, ofs), [] ->
      fprintf pp "\"%s\" + %Ld" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Oaddrstack ofs, [] ->
      fprintf pp "stack(%Ld)" (camlint64_of_ptrofs ofs)
(* 32-bit integer arithmetic *)
  | Oshift(s, a), [r1] -> fprintf pp "%a %a" reg r1 shift (s,a)
  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddshift(s, a), [r1;r2] -> fprintf pp "%a + %a %a" reg r1 reg r2 shift (s,a)
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Oneg, [r1] -> fprintf pp "- %a" reg r1
  | Onegshift(s, a), [r1] -> fprintf pp "- (%a %a)" reg r1 shift (s,a)
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Osubshift(s, a), [r1;r2] -> fprintf pp "%a - %a %a" reg r1 reg r2 shift (s,a)
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omuladd, [r1;r2;r3] -> fprintf pp "%a + %a * %a" reg r3 reg r1 reg r2
  | Omulsub, [r1;r2;r3] -> fprintf pp "%a - %a * %a" reg r3 reg r1 reg r2
  | Odiv, [r1;r2] -> fprintf pp "%a /s %a" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "%a /u %a" reg r1 reg r2
  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandshift(s, a), [r1;r2] -> fprintf pp "%a & %a %a" reg r1 reg r2 shift (s,a)
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorshift(s, a), [r1;r2] -> fprintf pp "%a | %a %a" reg r1 reg r2 shift (s,a)
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorshift(s, a), [r1;r2] -> fprintf pp "%a ^ %a %a" reg r1 reg r2 shift (s,a)
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)
  | Onot, [r1] -> fprintf pp "~ %a" reg r1
  | Onotshift(s, a), [r1] -> fprintf pp "~ (%a %a)" reg r1 shift (s,a)
  | Obic, [r1;r2] -> fprintf pp "%a & ~ %a" reg r1 reg r2
  | Obicshift(s, a), [r1;r2] -> fprintf pp "%a & ~ %a %a" reg r1 reg r2 shift (s,a)
  | Oorn, [r1;r2] -> fprintf pp "%a | ~ %a" reg r1 reg r2
  | Oornshift(s, a), [r1;r2] -> fprintf pp "%a | ~ %a %a" reg r1 reg r2 shift (s,a)
  | Oeqv, [r1;r2] -> fprintf pp "%a ^ ~ %a" reg r1 reg r2
  | Oeqvshift(s, a), [r1;r2] -> fprintf pp "%a ^ ~ %a %a" reg r1 reg r2 shift (s,a)
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
  | Ozext s, [r1] -> fprintf pp "zext(%d, %a)" (Z.to_int s) reg r1
  | Osext s, [r1] -> fprintf pp "sext(%d, %a)" (Z.to_int s) reg r1
  | Oshlzext(s, a), [r1] -> fprintf pp "zext(%d, %a) << %ld" (Z.to_int s) reg r1 (camlint_of_coqint a)
  | Oshlsext(s, a), [r1] -> fprintf pp "sext(%d, %a) << %ld" (Z.to_int s) reg r1 (camlint_of_coqint a)
  | Ozextshr(a, s), [r1] -> fprintf pp "zext(%d, %a >>u %ld)" (Z.to_int s) reg r1 (camlint_of_coqint a)
  | Osextshr(a, s), [r1] -> fprintf pp "sext(%d, %a >>s %ld)" (Z.to_int s) reg r1 (camlint_of_coqint a)
(* 64-bit integer arithmetic *)
  | Oshiftl(s, a), [r1] -> fprintf pp "%a %a" reg r1 shiftl (s,a)
  | Oextend(x, a), [r1] -> fprintf pp "%s(32, %a) <<l %ld" (extend_name x) reg r1 (camlint_of_coqint a)
  | Omakelong, [r1;r2] -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong, [r1] -> fprintf pp "highlong(%a)" reg r1
  | Oaddl, [r1;r2] -> fprintf pp "%a +l %a" reg r1 reg r2
  | Oaddlshift(s, a), [r1;r2] -> fprintf pp "%a +l %a %a" reg r1 reg r2 shiftl (s,a)
  | Oaddlext(x, a), [r1;r2] -> fprintf pp "%a +l %s(%a) << %ld" reg r1 (extend_name x) reg r2 (camlint_of_coqint a)
  | Oaddlimm n, [r1] -> fprintf pp "%a +l %Ld" reg r1 (camlint64_of_coqint n)
  | Onegl, [r1] -> fprintf pp "-l %a" reg r1
  | Oneglshift(s, a), [r1] -> fprintf pp "-l (%a %a)" reg r1 shiftl (s,a)
  | Osubl, [r1;r2] -> fprintf pp "%a -l %a" reg r1 reg r2
  | Osublext(x, a), [r1;r2] -> fprintf pp "%a +l %s(%a) << %ld" reg r1 (extend_name x) reg r2 (camlint_of_coqint a)
  | Osublshift(s, a), [r1;r2] -> fprintf pp "%a -l %a %a" reg r1 reg r2 shiftl (s,a)
  | Omull, [r1;r2] -> fprintf pp "%a *l %a" reg r1 reg r2
  | Omulladd, [r1;r2;r3] -> fprintf pp "%a +l %a *l %a" reg r3 reg r1 reg r2
  | Omullsub, [r1;r2;r3] -> fprintf pp "%a -l %a *l %a" reg r3 reg r1 reg r2
  | Omullhs, [r1;r2] -> fprintf pp "%a *hls %a" reg r1 reg r2
  | Omullhu, [r1;r2] -> fprintf pp "%a *hlu %a" reg r1 reg r2
  | Odivl, [r1;r2] -> fprintf pp "%a /ls %a" reg r1 reg r2
  | Odivlu, [r1;r2] -> fprintf pp "%a /lu %a" reg r1 reg r2
  | Oandl, [r1;r2] -> fprintf pp "%a &l %a" reg r1 reg r2
  | Oandlshift(s, a), [r1;r2] -> fprintf pp "%a &l %a %a" reg r1 reg r2 shiftl (s,a)
  | Oandlimm n, [r1] -> fprintf pp "%a &l %Ld" reg r1 (camlint64_of_coqint n)
  | Oorl, [r1;r2] -> fprintf pp "%a |l %a" reg r1 reg r2
  | Oorlshift(s, a), [r1;r2] -> fprintf pp "%a |l %a %a" reg r1 reg r2 shiftl (s,a)
  | Oorlimm n, [r1] ->  fprintf pp "%a |l %Ld" reg r1 (camlint64_of_coqint n)
  | Oxorl, [r1;r2] -> fprintf pp "%a ^l %a" reg r1 reg r2
  | Oxorlshift(s, a), [r1;r2] -> fprintf pp "%a ^l %a %a" reg r1 reg r2 shiftl (s,a)
  | Oxorlimm n, [r1] -> fprintf pp "%a ^l %Ld" reg r1 (camlint64_of_coqint n)
  | Onotl, [r1] -> fprintf pp "~l %a" reg r1
  | Onotlshift(s, a), [r1] -> fprintf pp "~l (%a %a)" reg r1 shiftl (s,a)
  | Obicl, [r1;r2] -> fprintf pp "%a &l ~l %a" reg r1 reg r2
  | Obiclshift(s, a), [r1;r2] -> fprintf pp "%a &l ~l %a %a" reg r1 reg r2 shiftl (s,a)
  | Oornl, [r1;r2] -> fprintf pp "%a |l ~l %a" reg r1 reg r2
  | Oornlshift(s, a), [r1;r2] -> fprintf pp "%a |l ~l %a %a" reg r1 reg r2 shiftl (s,a)
  | Oeqvl, [r1;r2] -> fprintf pp "%a ^l ~l %a" reg r1 reg r2
  | Oeqvlshift(s, a), [r1;r2] -> fprintf pp "%a ^l ~l %a %a" reg r1 reg r2 shift (s,a)
  | Oshll, [r1;r2] -> fprintf pp "%a <<l %a" reg r1 reg r2
  | Oshrl, [r1;r2] -> fprintf pp "%a >>ls %a" reg r1 reg r2
  | Oshrlu, [r1;r2] -> fprintf pp "%a >>lu %a" reg r1 reg r2
  | Oshrlximm n, [r1] -> fprintf pp "%a >>lx %ld" reg r1 (camlint_of_coqint n)
  | Ozextl s, [r1] -> fprintf pp "zextl(%d, %a)" (Z.to_int s) reg r1
  | Osextl s, [r1] -> fprintf pp "sextl(%d, %a)" (Z.to_int s) reg r1
  | Oshllzext(s, a), [r1] -> fprintf pp "zextl(%d, %a) <<l %ld" (Z.to_int s) reg r1 (camlint_of_coqint a)
  | Oshllsext(s, a), [r1] -> fprintf pp "sextl(%d, %a) <<l %ld" (Z.to_int s) reg r1 (camlint_of_coqint a)
  | Ozextshrl(a, s), [r1] -> fprintf pp "zextl(%d, %a >>lu %ld)" (Z.to_int s) reg r1 (camlint_of_coqint a)
  | Osextshrl(a, s), [r1] -> fprintf pp "sextl(%d, %a >>ls %ld)" (Z.to_int s) reg r1 (camlint_of_coqint a)
(* 64-bit floating-point arithmetic *)
  | Onegf, [r1] -> fprintf pp "negf(%a)" reg r1
  | Oabsf, [r1] -> fprintf pp "absf(%a)" reg r1
  | Oaddf, [r1;r2] -> fprintf pp "%a +f %a" reg r1 reg r2
  | Osubf, [r1;r2] -> fprintf pp "%a -f %a" reg r1 reg r2
  | Omulf, [r1;r2] -> fprintf pp "%a *f %a" reg r1 reg r2
  | Odivf, [r1;r2] -> fprintf pp "%a /f %a" reg r1 reg r2
(* 32-bit floating-point arithmetic *)
  | Onegfs, [r1] -> fprintf pp "negfs(%a)" reg r1
  | Oabsfs, [r1] -> fprintf pp "absfs(%a)" reg r1
  | Oaddfs, [r1;r2] -> fprintf pp "%a +fs %a" reg r1 reg r2
  | Osubfs, [r1;r2] -> fprintf pp "%a -fs %a" reg r1 reg r2
  | Omulfs, [r1;r2] -> fprintf pp "%a *fs %a" reg r1 reg r2
  | Odivfs, [r1;r2] -> fprintf pp "%a /fs %a" reg r1 reg r2
  | Osingleoffloat, [r1] -> fprintf pp "singleoffloat(%a)" reg r1
  | Ofloatofsingle, [r1] -> fprintf pp "floatofsingle(%a)" reg r1
(* Conversions between int and float *)
  | Ointoffloat, [r1] -> fprintf pp "intoffloat(%a)" reg r1
  | Ointuoffloat, [r1] -> fprintf pp "intuoffloat(%a)" reg r1
  | Ofloatofint, [r1] -> fprintf pp "floatofint(%a)" reg r1
  | Ofloatofintu, [r1] -> fprintf pp "floatofintu(%a)" reg r1
  | Olongoffloat, [r1] -> fprintf pp "longoffloat(%a)" reg r1
  | Olonguoffloat, [r1] -> fprintf pp "longuoffloat(%a)" reg r1
  | Ofloatoflong, [r1] -> fprintf pp "floatoflong(%a)" reg r1
  | Ofloatoflongu, [r1] -> fprintf pp "floatoflongu(%a)" reg r1
  | Ointofsingle, [r1] -> fprintf pp "intofsingle(%a)" reg r1
  | Ointuofsingle, [r1] -> fprintf pp "intuofsingle(%a)" reg r1
  | Osingleofint, [r1] -> fprintf pp "singleofint(%a)" reg r1
  | Osingleofintu, [r1] -> fprintf pp "singleofintu(%a)" reg r1
  | Olongofsingle, [r1] -> fprintf pp "longofsingle(%a)" reg r1
  | Olonguofsingle, [r1] -> fprintf pp "longuofsingle(%a)" reg r1
  | Osingleoflong, [r1] -> fprintf pp "singleoflong(%a)" reg r1
  | Osingleoflongu, [r1] -> fprintf pp "singleoflongu(%a)" reg r1
(* Boolean tests *)
  | Ocmp c, args -> print_condition reg pp (c, args)
  | Osel (c, ty), r1::r2::args ->
      fprintf pp "%a ?%s %a : %a"
         (print_condition reg) (c, args)
         (PrintAST.name_of_type ty) reg r1 reg r2
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %Ld" reg r1 (camlint64_of_coqint n)
  | Aindexed2, [r1; r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Aindexed2shift a, [r1; r2] -> fprintf pp "%a + %a << %ld" reg r1 reg r2 (camlint_of_coqint a)
  | Aindexed2ext(x, a), [r1; r2] -> fprintf pp "%a + %s(%a) << %ld" reg r1 (extend_name x) reg r2 (camlint_of_coqint a)
  | Aglobal(id, ofs), [] ->
      fprintf pp "\"%s\" + %Ld" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Ainstack ofs, [] -> fprintf pp "stack(%Ld)" (camlint64_of_ptrofs ofs)
  | _ -> fprintf pp "<bad addressing>"

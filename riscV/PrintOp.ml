(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
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

let print_condition reg pp = function
  | (Ccomp c, [r1;r2]) ->
      fprintf pp "%a %ss %a" reg r1 (comparison_name c) reg r2
  | (Ccompu c, [r1;r2]) ->
      fprintf pp "%a %su %a" reg r1 (comparison_name c) reg r2
  | (Ccompimm(c, n), [r1]) ->
      fprintf pp "%a %ss %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompuimm(c, n), [r1]) ->
      fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompf c, [r1;r2]) ->
      fprintf pp "%a %sf %a" reg r1 (comparison_name c) reg r2
  | (Ccompl c, [r1;r2]) ->
      fprintf pp "%a %sls %a" reg r1 (comparison_name c) reg r2
  | (Ccomplu c, [r1;r2]) ->
      fprintf pp "%a %slu %a" reg r1 (comparison_name c) reg r2
  | (Ccomplimm(c, n), [r1]) ->
      fprintf pp "%a %sls %Ld" reg r1 (comparison_name c) (camlint64_of_coqint n)
  | (Ccompluimm(c, n), [r1]) ->
      fprintf pp "%a %slu %Lu" reg r1 (comparison_name c) (camlint64_of_coqint n)
  | (Cnotcompf c, [r1;r2]) ->
      fprintf pp "%a not(%sf) %a" reg r1 (comparison_name c) reg r2
  | (Ccompfs c, [r1;r2]) ->
      fprintf pp "%a %sfs %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompfs c, [r1;r2]) ->
      fprintf pp "%a not(%sfs) %a" reg r1 (comparison_name c) reg r2
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
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Oneg, [r1] -> fprintf pp "-(%a)" reg r1
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulhs, [r1;r2] -> fprintf pp "%a *hs %a" reg r1 reg r2
  | Omulhu, [r1;r2] -> fprintf pp "%a *hu %a" reg r1 reg r2
  | Odiv, [r1;r2] -> fprintf pp "%a /s %a" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "%a /u %a" reg r1 reg r2
  | Omod, [r1;r2] -> fprintf pp "%a %%s %a" reg r1 reg r2
  | Omodu, [r1;r2] -> fprintf pp "%a %%u %a" reg r1 reg r2
  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshlimm n, [r1] -> fprintf pp "%a << %ld" reg r1 (camlint_of_coqint n)
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "%a >>s %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Oshruimm n, [r1] -> fprintf pp "%a >>u %ld" reg r1 (camlint_of_coqint n)
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)

  | Omakelong, [r1;r2] -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong, [r1] -> fprintf pp "highlong(%a)" reg r1
  | Ocast32signed, [r1] -> fprintf pp "long32signed(%a)" reg r1
  | Ocast32unsigned, [r1] -> fprintf pp "long32unsigned(%a)" reg r1
  | Oaddl, [r1;r2] -> fprintf pp "%a +l %a" reg r1 reg r2
  | Oaddlimm n, [r1] -> fprintf pp "%a +l %Ld" reg r1 (camlint64_of_coqint n)
  | Onegl, [r1] -> fprintf pp "-l (%a)" reg r1
  | Osubl, [r1;r2] -> fprintf pp "%a -l %a" reg r1 reg r2
  | Omull, [r1;r2] -> fprintf pp "%a *l %a" reg r1 reg r2
  | Omullhs, [r1;r2] -> fprintf pp "%a *lhs %a" reg r1 reg r2
  | Omullhu, [r1;r2] -> fprintf pp "%a *lhu %a" reg r1 reg r2
  | Odivl, [r1;r2] -> fprintf pp "%a /ls %a" reg r1 reg r2
  | Odivlu, [r1;r2] -> fprintf pp "%a /lu %a" reg r1 reg r2
  | Omodl, [r1;r2] -> fprintf pp "%a %%ls %a" reg r1 reg r2
  | Omodlu, [r1;r2] -> fprintf pp "%a %%lu %a" reg r1 reg r2
  | Oandl, [r1;r2] -> fprintf pp "%a &l %a" reg r1 reg r2
  | Oandlimm n, [r1] -> fprintf pp "%a &l %Ld" reg r1 (camlint64_of_coqint n)
  | Oorl, [r1;r2] -> fprintf pp "%a |l %a" reg r1 reg r2
  | Oorlimm n, [r1] ->  fprintf pp "%a |l %Ld" reg r1 (camlint64_of_coqint n)
  | Oxorl, [r1;r2] -> fprintf pp "%a ^l %a" reg r1 reg r2
  | Oxorlimm n, [r1] -> fprintf pp "%a ^l %Ld" reg r1 (camlint64_of_coqint n)
  | Oshll, [r1;r2] -> fprintf pp "%a <<l %a" reg r1 reg r2
  | Oshllimm n, [r1] -> fprintf pp "%a <<l %Ld" reg r1 (camlint64_of_coqint n)
  | Oshrl, [r1;r2] -> fprintf pp "%a >>ls %a" reg r1 reg r2
  | Oshrlimm n, [r1] -> fprintf pp "%a >>ls %ld" reg r1 (camlint_of_coqint n)
  | Oshrlu, [r1;r2] -> fprintf pp "%a >>lu %a" reg r1 reg r2
  | Oshrluimm n, [r1] -> fprintf pp "%a >>lu %ld" reg r1 (camlint_of_coqint n)
  | Oshrxlimm n, [r1] -> fprintf pp "%a >>lx %ld" reg r1 (camlint_of_coqint n)

  | Onegf, [r1] -> fprintf pp "negf(%a)" reg r1
  | Oabsf, [r1] -> fprintf pp "absf(%a)" reg r1
  | Oaddf, [r1;r2] -> fprintf pp "%a +f %a" reg r1 reg r2
  | Osubf, [r1;r2] -> fprintf pp "%a -f %a" reg r1 reg r2
  | Omulf, [r1;r2] -> fprintf pp "%a *f %a" reg r1 reg r2
  | Odivf, [r1;r2] -> fprintf pp "%a /f %a" reg r1 reg r2
  | Onegfs, [r1] -> fprintf pp "negfs(%a)" reg r1
  | Oabsfs, [r1] -> fprintf pp "absfs(%a)" reg r1
  | Oaddfs, [r1;r2] -> fprintf pp "%a +fs %a" reg r1 reg r2
  | Osubfs, [r1;r2] -> fprintf pp "%a -fs %a" reg r1 reg r2
  | Omulfs, [r1;r2] -> fprintf pp "%a *fs %a" reg r1 reg r2
  | Odivfs, [r1;r2] -> fprintf pp "%a /fs %a" reg r1 reg r2
  | Osingleoffloat, [r1] -> fprintf pp "singleoffloat(%a)" reg r1
  | Ofloatofsingle, [r1] -> fprintf pp "floatofsingle(%a)" reg r1
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
  | Ocmp c, args -> print_condition reg pp (c, args)
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %Ld" reg r1 (camlint64_of_ptrofs n)
  | Aglobal(id, ofs), [] ->
      fprintf pp "\"%s\" + %Ld" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Ainstack ofs, [] -> fprintf pp "stack(%Ld)" (camlint64_of_ptrofs ofs)
  | _ -> fprintf pp "<bad addressing>"

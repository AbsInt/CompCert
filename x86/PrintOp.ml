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
      fprintf pp "%a %su %lu" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompl c, [r1;r2]) ->
      fprintf pp "%a %sls %a" reg r1 (comparison_name c) reg r2
  | (Ccomplu c, [r1;r2]) ->
      fprintf pp "%a %slu %a" reg r1 (comparison_name c) reg r2
  | (Ccomplimm(c, n), [r1]) ->
      fprintf pp "%a %sls %Ld" reg r1 (comparison_name c) (camlint64_of_coqint n)
  | (Ccompluimm(c, n), [r1]) ->
      fprintf pp "%a %slu %Lu" reg r1 (comparison_name c) (camlint64_of_coqint n)
  | (Ccompf c, [r1;r2]) ->
      fprintf pp "%a %sf %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompf c, [r1;r2]) ->
      fprintf pp "%a not(%sf) %a" reg r1 (comparison_name c) reg r2
  | (Ccompfs c, [r1;r2]) ->
      fprintf pp "%a %sfs %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompfs c, [r1;r2]) ->
      fprintf pp "%a not(%sfs) %a" reg r1 (comparison_name c) reg r2
  | (Cmaskzero n, [r1]) ->
      fprintf pp "%a & 0x%lx == 0" reg r1 (camlint_of_coqint n)
  | (Cmasknotzero n, [r1]) ->
      fprintf pp "%a & 0x%lx != 0" reg r1 (camlint_of_coqint n)
  | _ ->
      fprintf pp "<bad condition>"

let print_addressing reg pp = function
  | Aindexed n, [r1] ->
      fprintf pp "%a + %s" reg r1 (Z.to_string n)
  | Aindexed2 n, [r1; r2] ->
      fprintf pp "%a + %a + %s" reg r1 reg r2 (Z.to_string n)
  | Ascaled(sc,n), [r1] ->
      fprintf pp "%a * %s + %s" reg r1 (Z.to_string sc) (Z.to_string n)
  | Aindexed2scaled(sc, n), [r1; r2] ->
      fprintf pp "%a + %a * %s + %s" reg r1 reg r2 (Z.to_string sc) (Z.to_string n)
  | Aglobal(id, ofs), [] -> fprintf pp "%s + %s" (extern_atom id) (Z.to_string ofs)
  | Abased(id, ofs), [r1] -> fprintf pp "%s + %s + %a" (extern_atom id) (Z.to_string ofs) reg r1
  | Abasedscaled(sc,id, ofs), [r1] -> fprintf pp "%s + %s + %a * %ld" (extern_atom id) (Z.to_string ofs) reg r1 (camlint_of_coqint sc)
  | Ainstack ofs, [] -> fprintf pp "stack(%s)" (Z.to_string ofs)
  | _ -> fprintf pp "<bad addressing>"

let print_operation reg pp = function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Olongconst n, [] -> fprintf pp "%LdL" (camlint64_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "%.15F" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "%.15Ff" (camlfloat_of_coqfloat32 n)
  | Oindirectsymbol id, [] -> fprintf pp "&%s" (extern_atom id)
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast8unsigned, [r1] -> fprintf pp "int8unsigned(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Ocast16unsigned, [r1] -> fprintf pp "int16unsigned(%a)" reg r1
  | Oneg, [r1] -> fprintf pp "(- %a)" reg r1
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulimm n, [r1] -> fprintf pp "%a * %ld" reg r1 (camlint_of_coqint n)
  | Omulhs, [r1;r2] -> fprintf pp "mulhs(%a,%a)" reg r1 reg r2
  | Omulhu, [r1;r2] -> fprintf pp "mulhu(%a,%a)" reg r1 reg r2
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
  | Onot, [r1] -> fprintf pp "not(%a)" reg r1
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshlimm n, [r1] -> fprintf pp "%a << %ld" reg r1 (camlint_of_coqint n)
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "%a >>s %ld" reg r1 (camlint_of_coqint n)
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Oshruimm n, [r1] -> fprintf pp "%a >>u %ld" reg r1 (camlint_of_coqint n)
  | Ororimm n, [r1] -> fprintf pp "%a ror %ld" reg r1 (camlint_of_coqint n)
  | Oshldimm n, [r1;r2] -> fprintf pp "(%a, %a) << %ld" reg r1 reg r2 (camlint_of_coqint n)
  | Olea addr, args -> print_addressing reg pp (addr, args); fprintf pp " (int)"
  | Omakelong, [r1;r2] -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong, [r1] -> fprintf pp "highlong(%a)" reg r1
  | Ocast32signed, [r1] -> fprintf pp "long32signed(%a)" reg r1
  | Ocast32unsigned, [r1] -> fprintf pp "long32unsigned(%a)" reg r1
  | Onegl, [r1] -> fprintf pp "(-l %a)" reg r1
  | Osubl, [r1;r2] -> fprintf pp "%a -l %a" reg r1 reg r2
  | Omull, [r1;r2] -> fprintf pp "%a *l %a" reg r1 reg r2
  | Omullimm n, [r1] -> fprintf pp "%a *l %Ld" reg r1 (camlint64_of_coqint n)
  | Omullhs, [r1;r2] -> fprintf pp "mullhs(%a,%a)" reg r1 reg r2
  | Omullhu, [r1;r2] -> fprintf pp "mullhu(%a,%a)" reg r1 reg r2
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
  | Onotl, [r1] -> fprintf pp "notl(%a)" reg r1
  | Oshll, [r1;r2] -> fprintf pp "%a <<l %a" reg r1 reg r2
  | Oshllimm n, [r1] -> fprintf pp "%a <<l %ld" reg r1 (camlint_of_coqint n)
  | Oshrl, [r1;r2] -> fprintf pp "%a >>ls %a" reg r1 reg r2
  | Oshrlimm n, [r1] -> fprintf pp "%a >>ls %ld" reg r1 (camlint_of_coqint n)
  | Oshrxlimm n, [r1] -> fprintf pp "%a >>lx %ld" reg r1 (camlint_of_coqint n)
  | Oshrlu, [r1;r2] -> fprintf pp "%a >>lu %a" reg r1 reg r2
  | Oshrluimm n, [r1] -> fprintf pp "%a >>lu %ld" reg r1 (camlint_of_coqint n)
  | Ororlimm n, [r1] -> fprintf pp "%a rorl %ld" reg r1 (camlint_of_coqint n)
  | Oleal addr, args -> print_addressing reg pp (addr, args); fprintf pp " (long)"
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
  | Ofloatofint, [r1] -> fprintf pp "floatofint(%a)" reg r1
  | Ointofsingle, [r1] -> fprintf pp "intofsingle(%a)" reg r1
  | Osingleofint, [r1] -> fprintf pp "singleofint(%a)" reg r1
  | Olongoffloat, [r1] -> fprintf pp "longoffloat(%a)" reg r1
  | Ofloatoflong, [r1] -> fprintf pp "floatoflong(%a)" reg r1
  | Olongofsingle, [r1] -> fprintf pp "longofsingle(%a)" reg r1
  | Osingleoflong, [r1] -> fprintf pp "singleoflong(%a)" reg r1
  | Ocmp c, args -> print_condition reg pp (c, args)
  | _ -> fprintf pp "<bad operator>"



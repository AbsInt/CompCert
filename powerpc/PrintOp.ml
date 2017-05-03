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
      fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompf c, [r1;r2]) ->
      fprintf pp "%a %sf %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompf c, [r1;r2]) ->
      fprintf pp "%a not(%sf) %a" reg r1 (comparison_name c) reg r2
  | (Cmaskzero n, [r1]) ->
      fprintf pp "%a & 0x%lx == 0" reg r1 (camlint_of_coqint n)
  | (Cmasknotzero n, [r1]) ->
      fprintf pp "%a & 0x%lx != 0" reg r1 (camlint_of_coqint n)
  | _ ->
      fprintf pp "<bad condition>"

let print_operation reg pp = function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "%.15F" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "%.15Ff" (camlfloat_of_coqfloat32 n)
  | Oaddrsymbol(id, ofs), [] ->
      fprintf pp "\"%s\" + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | Oaddrstack ofs, [] ->
      fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Oaddsymbol(id, ofs), [r1] ->
      fprintf pp "\"%s\" + %ld + %a" (extern_atom id) (camlint_of_coqint ofs) reg r1
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Osubimm n, [r1] -> fprintf pp "%ld - %a" (camlint_of_coqint n) reg r1
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulimm n, [r1] -> fprintf pp "%a * %ld" reg r1 (camlint_of_coqint n)
  | Odiv, [r1;r2] -> fprintf pp "%a /s %a" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "%a /u %a" reg r1 reg r2
  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)
  | Onot, [r1] -> fprintf pp "not(%a)" reg r1
  | Onand, [r1;r2] -> fprintf pp "not(%a & %a)" reg r1 reg r2
  | Onor, [r1;r2] -> fprintf pp "not(%a | %a)" reg r1 reg r2
  | Onxor, [r1;r2] -> fprintf pp "not(%a ^ %a)" reg r1 reg r2
  | Oandc, [r1;r2] -> fprintf pp "%a & not %a" reg r1 reg r2
  | Oorc, [r1;r2] -> fprintf pp "%a | not %a" reg r1 reg r2
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "%a >>s %ld" reg r1 (camlint_of_coqint n)
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Orolm(n,m), [r1] ->
      fprintf pp "(%a rol %ld) & 0x%lx"
              reg r1 (camlint_of_coqint n) (camlint_of_coqint m)
  | Oroli(n,m), [r1;r2] ->
      fprintf pp "(%a & ~0x%lx) | ((%a rol %ld) & 0x%lx)"
              reg r1 (camlint_of_coqint m)
              reg r2 (camlint_of_coqint n) (camlint_of_coqint m)
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
  | Ofloatofwords, [r1;r2] -> fprintf pp "floatofwords(%a,%a)" reg r1 reg r2
  | Omakelong, [r1;r2] -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong, [r1] -> fprintf pp "highlong(%a)" reg r1
  | Ocmp c, args -> print_condition reg pp (c, args)
  | Olongconst n, [] -> fprintf pp "%LdL" (camlint64_of_coqint n)
  | Ocast32signed, [r1] -> fprintf pp "int32signed(%a)" reg r1
  | Ocast32unsigned, [r1] -> fprintf pp "int32unsigned(%a)" reg r1
  | Oaddl, [r1;r2] -> fprintf pp "%a +l %a" reg r1 reg r2
  | Oaddlimm n, [r1] -> fprintf pp "%a +l %Ld" reg r1 (camlint64_of_coqint n)
  | Osubl, [r1;r2] -> fprintf pp "%a -l %a" reg r1 reg r2
  | Onegl, [r1] -> fprintf pp "-l %a" reg r1
  | Omull, [r1;r2] -> fprintf pp "%a *l %a" reg r1 reg r2
  | Odivl, [r1;r2] -> fprintf pp "%a /ls %a" reg r1 reg r2
  | Odivlu, [r1;r2] -> fprintf pp "%a /lu %a" reg r1 reg r2
  | Oandl, [r1;r2] -> fprintf pp "%a &l %a" reg r1 reg r2
  | Oandlimm n, [r1] -> fprintf pp "%a &l %Ld" reg r1 (camlint64_of_coqint n)
  | Oorl, [r1;r2] -> fprintf pp "%a |l %a" reg r1 reg r2
  | Oorlimm n, [r1] -> fprintf pp "%a |l %Ld" reg r1 (camlint64_of_coqint n)
  | Oxorl, [r1;r2] -> fprintf pp "%a ^l %a" reg r1 reg r2
  | Oxorlimm n, [r1] -> fprintf pp "%a ^l %Ld" reg r1 (camlint64_of_coqint n)
  | Onotl, [r1] -> fprintf pp "~l %a" reg r1
  | Oshll, [r1;r2] -> fprintf pp "%a <<l %a" reg r1 reg r2
  | Oshrl, [r1;r2] -> fprintf pp "%a >>ls %a" reg r1 reg r2
  | Oshrlimm n, [r1] -> fprintf pp "%a >>ls %ld" reg r1 (camlint_of_coqint n)
  | Oshrlu, [r1;r2] -> fprintf pp "%a >>lu %a" reg r1 reg r2
  | Orolml(n,m), [r1] ->
      fprintf pp "(%a rol %Ld) &l 0x%Lx"
              reg r1 (camlint64_of_coqint n) (camlint64_of_coqint m)
  | Olongoffloat, [r1] -> fprintf pp "longoffloat(%a)" reg r1
  | Ofloatoflong, [r1] -> fprintf pp "floatoflong(%a)" reg r1
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Aindexed2, [r1; r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Aglobal(id, ofs), [] -> fprintf pp "%s + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | Abased(id, ofs), [r1] -> fprintf pp "%s + %ld + %a" (extern_atom id) (camlint_of_coqint ofs) reg r1
  | Ainstack ofs, [] -> fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | _ -> fprintf pp "<bad addressing>"

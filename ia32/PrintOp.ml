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

open Format
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

let print_addressing reg pp = function
  | Aindexed n, [r1] ->
      fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Aindexed2 n, [r1; r2] ->
      fprintf pp "%a + %a + %ld" reg r1 reg r2 (camlint_of_coqint n)
  | Ascaled(sc,n), [r1] ->
      fprintf pp "%a * %ld + %ld" reg r1 (camlint_of_coqint sc) (camlint_of_coqint n)
  | Aindexed2scaled(sc, n), [r1; r2] ->
      fprintf pp "%a + %a * %ld + %ld" reg r1 reg r2 (camlint_of_coqint sc) (camlint_of_coqint n)
  | Aglobal(id, ofs), [] -> fprintf pp "%s + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | Abased(id, ofs), [r1] -> fprintf pp "%s + %ld + %a" (extern_atom id) (camlint_of_coqint ofs) reg r1
  | Abasedscaled(sc,id, ofs), [r1] -> fprintf pp "%s + %ld + %a * %ld" (extern_atom id) (camlint_of_coqint ofs) reg r1 (camlint_of_coqint sc)
  | Ainstack ofs, [] -> fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | _ -> fprintf pp "<bad addressing>"

let print_operation reg pp = function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "%F" (camlfloat_of_coqfloat n)
  | Oindirectsymbol id, [] -> fprintf pp "&%s" (extern_atom id)
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast8unsigned, [r1] -> fprintf pp "int8unsigned(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Ocast16unsigned, [r1] -> fprintf pp "int16unsigned(%a)" reg r1
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulimm n, [r1] -> fprintf pp "%a * %ld" reg r1 (camlint_of_coqint n)
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
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Oshruimm n, [r1] -> fprintf pp "%a >>u %ld" reg r1 (camlint_of_coqint n)
  | Ororimm n, [r1] -> fprintf pp "%a ror %ld" reg r1 (camlint_of_coqint n)
  | Oshldimm n, [r1;r2] -> fprintf pp "(%a, %a) << %ld" reg r1 reg r2 (camlint_of_coqint n)
  | Olea addr, args -> print_addressing reg pp (addr, args)
  | Onegf, [r1] -> fprintf pp "negf(%a)" reg r1
  | Oabsf, [r1] -> fprintf pp "absf(%a)" reg r1
  | Oaddf, [r1;r2] -> fprintf pp "%a +f %a" reg r1 reg r2
  | Osubf, [r1;r2] -> fprintf pp "%a -f %a" reg r1 reg r2
  | Omulf, [r1;r2] -> fprintf pp "%a *f %a" reg r1 reg r2
  | Odivf, [r1;r2] -> fprintf pp "%a /f %a" reg r1 reg r2
  | Osingleoffloat, [r1] -> fprintf pp "singleoffloat(%a)" reg r1
  | Ointoffloat, [r1] -> fprintf pp "intoffloat(%a)" reg r1
  | Ofloatofint, [r1] -> fprintf pp "floatofint(%a)" reg r1
  | Omakelong, [r1;r2] -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong, [r1] -> fprintf pp "highlong(%a)" reg r1
  | Ocmp c, args -> print_condition reg pp (c, args)
  | _ -> fprintf pp "<bad operator>"



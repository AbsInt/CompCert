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

let shift pp = function
  | Slsl a -> fprintf pp "<< %ld" (camlint_of_coqint a)
  | Slsr a -> fprintf pp ">>u %ld" (camlint_of_coqint a)
  | Sasr a -> fprintf pp ">>s %ld" (camlint_of_coqint a)
  | Sror a -> fprintf pp "ror %ld" (camlint_of_coqint a)

let print_condition reg pp = function
  | (Ccomp c, [r1;r2]) ->
      fprintf pp "%a %ss %a" reg r1 (comparison_name c) reg r2
  | (Ccompu c, [r1;r2]) ->
      fprintf pp "%a %su %a" reg r1 (comparison_name c) reg r2
  | (Ccompshift(c, s), [r1;r2]) ->
      fprintf pp "%a %ss %a %a" reg r1 (comparison_name c) reg r2 shift s
  | (Ccompushift(c, s), [r1;r2]) ->
      fprintf pp "%a %su %a %a" reg r1 (comparison_name c) reg r2 shift s
  | (Ccompimm(c, n), [r1]) ->
      fprintf pp "%a %ss %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompuimm(c, n), [r1]) ->
      fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
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
  | Ofloatconst n, [] -> fprintf pp "%.15F" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "%.15Ff" (camlfloat_of_coqfloat32 n)
  | Oaddrsymbol(id, ofs), [] ->
      fprintf pp "\"%s\" + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | Oaddrstack ofs, [] ->
      fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddshift s, [r1;r2] -> fprintf pp "%a + %a %a" reg r1 reg r2 shift s
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Osubshift s, [r1;r2] -> fprintf pp "%a - %a %a" reg r1 reg r2 shift s
  | Orsubshift s, [r1;r2] -> fprintf pp "%a %a - %a" reg r2 shift s reg r1
  | Orsubimm n, [r1] -> fprintf pp "%ld - %a" (camlint_of_coqint n) reg r1
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omla, [r1;r2;r3] -> fprintf pp "%a * %a + %a" reg r1 reg r2 reg r3
  | Odiv, [r1;r2] -> fprintf pp "%a /s %a" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "%a /u %a" reg r1 reg r2
  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandshift s, [r1;r2] -> fprintf pp "%a & %a %a" reg r1 reg r2 shift s
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorshift s, [r1;r2] -> fprintf pp "%a | %a %a" reg r1 reg r2 shift s
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorshift s, [r1;r2] -> fprintf pp "%a ^ %a %a" reg r1 reg r2 shift s
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)
  | Obic, [r1;r2] -> fprintf pp "%a & not %a" reg r1 reg r2
  | Obicshift s, [r1;r2] -> fprintf pp "%a & not(%a %a)" reg r1 reg r2 shift s
  | Onot, [r1] -> fprintf pp "not(%a)" reg r1
  | Onotshift s, [r1] -> fprintf pp "not(%a %a)" reg r1 shift s
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Oshift s, [r1] -> fprintf pp "%a %a" reg r1 shift s
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
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
  | Ointoffloat, [r1] -> fprintf pp "intoffloat(%a)" reg r1
  | Ointuoffloat, [r1] -> fprintf pp "intuoffloat(%a)" reg r1
  | Ofloatofint, [r1] -> fprintf pp "floatofint(%a)" reg r1
  | Ofloatofintu, [r1] -> fprintf pp "floatofintu(%a)" reg r1
  | Ofloatofsingle, [r1] -> fprintf pp "floatofsingle(%a)" reg r1
  | Ointofsingle, [r1] -> fprintf pp "intofsingle(%a)" reg r1
  | Ointuofsingle, [r1] -> fprintf pp "intuofsingle(%a)" reg r1
  | Osingleofint, [r1] -> fprintf pp "singleofint(%a)" reg r1
  | Osingleofintu, [r1] -> fprintf pp "singleofintu(%a)" reg r1
  | Omakelong, [r1;r2] -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong, [r1] -> fprintf pp "highlong(%a)" reg r1
  | Ocmp c, args -> print_condition reg pp (c, args)
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Aindexed2, [r1; r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Aindexed2shift s, [r1; r2] -> fprintf pp "%a + %a %a" reg r1 reg r2 shift s
  | Ainstack ofs, [] -> fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | _ -> fprintf pp "<bad addressing>"

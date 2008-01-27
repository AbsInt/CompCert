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

open Camlcoq
open Integers

let singleoffloat f =
  Int32.float_of_bits (Int32.bits_of_float f)

let intoffloat f =
  coqint_of_camlint (Int32.of_float f)

let floatofint i =
  Int32.to_float (camlint_of_coqint i)

let floatofintu i =
  Int64.to_float (Int64.logand (Int64.of_int32 (camlint_of_coqint i))
                               0xFFFFFFFFL)

let cmp c (x: float) (y: float) =
  match c with
  | Ceq -> x = y
  | Cne -> x <> y
  | Clt -> x < y
  | Cle -> x <= y
  | Cgt -> x > y
  | Cge -> x >= y

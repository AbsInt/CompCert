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

let singleoffloat f =
  Int32.float_of_bits (Int32.bits_of_float f)

let intoffloat f =
  coqint_of_camlint (Int32.of_float f)

let intuoffloat f =
  coqint_of_camlint (Int64.to_int32 (Int64.of_float f))

let floatofint i =
  Int32.to_float (camlint_of_coqint i)

let floatofintu i =
  Int64.to_float (Int64.logand (Int64.of_int32 (camlint_of_coqint i))
                               0xFFFFFFFFL)

let cmp c (x: float) (y: float) =
  match c with
  | Integers.Ceq -> x = y
  | Integers.Cne -> x <> y
  | Integers.Clt -> x < y
  | Integers.Cle -> x <= y
  | Integers.Cgt -> x > y
  | Integers.Cge -> x >= y

let bits_of_single f = coqint_of_camlint (Int32.bits_of_float f)
let single_of_bits f = Int32.float_of_bits (camlint_of_coqint f)

let bits_of_double f = coqint_of_camlint64 (Int64.bits_of_float f)
let double_of_bits f = Int64.float_of_bits (camlint64_of_coqint f)

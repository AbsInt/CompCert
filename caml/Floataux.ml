open Camlcoq

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
  | AST.Ceq -> x = y
  | AST.Cne -> x <> y
  | AST.Clt -> x < y
  | AST.Cle -> x <= y
  | AST.Cgt -> x > y
  | AST.Cge -> x >= y

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

(** Auxiliary functions on machine registers *)

open Machregs

let register_names = [
  ("AX", AX); ("BX", BX); ("CX", CX); ("DX", DX);
  ("SI", SI); ("DI", DI); ("BP", BP);
  ("XMM0", X0); ("XMM1", X1); ("XMM2", X2); ("XMM3", X3);
  ("XMM4", X4); ("XMM5", X5); ("XMM6", X6); ("XMM7", X7);
  ("ST0", FP0)
]

let name_of_register r =
  let rec rev_assoc = function
  | [] -> None
  | (a, b) :: rem -> if b = r then Some a else rev_assoc rem
  in rev_assoc register_names

let register_by_name s =
  try
    Some(List.assoc (String.uppercase s) register_names)
  with Not_found ->
    None

let can_reserve_register r =
  List.mem r Conventions1.int_callee_save_regs
  || List.mem r Conventions1.float_callee_save_regs


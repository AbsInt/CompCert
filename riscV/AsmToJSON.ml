(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

(* Simple functions to serialize RISC-V Asm to JSON *)

(* Dummy function *)
let destination: string option ref = ref None

let sdump_folder = ref ""

let print_if prog sourcename =
  ()

let pp_mnemonics pp = ()

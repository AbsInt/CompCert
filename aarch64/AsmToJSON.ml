(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Functions to serialize AArch64 Asm to JSON *)

(* Dummy function *)

let destination: string option ref = ref None

let sdump_folder = ref ""

let print_if prog sourcename =
  ()

let pp_mnemonics pp = ()

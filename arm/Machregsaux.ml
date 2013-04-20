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
  ("R0", R0);  ("R1", R1);  ("R2", R2);  ("R3", R3);
  ("R4", R4);  ("R5", R5);  ("R6", R6);  ("R7", R7);
  ("R8", R8);  ("R9", R9);  ("R10", R10); ("R11", R11);
  ("R12", R12);
  ("F0", F0);  ("F1", F1);  ("F2", F2); ("F3", F3);
  ("F4", F4);  ("F5", F5);  ("F6", F6); ("F7", F7);
  ("F8", F8);  ("F9", F9);  ("F10", F10); ("F11", F11);
  ("F12", F12);("F13", F13);("F14", F14); ("F15", F15)
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


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

open Camlcoq
open Machregs

let register_names : (mreg, string) Hashtbl.t = Hashtbl.create 31

let _ =
  List.iter
    (fun (s, r) -> Hashtbl.add register_names r (camlstring_of_coqstring s))
    Machregs.register_names

let is_scratch_register s =  s = "R14"  || s = "r14"

let name_of_register r =
  try Some (Hashtbl.find register_names r) with Not_found -> None

let register_by_name s =
  Machregs.register_by_name (coqstring_uppercase_ascii_of_camlstring s)

let can_reserve_register r =
  List.mem r Conventions1.int_callee_save_regs
  || List.mem r Conventions1.float_callee_save_regs

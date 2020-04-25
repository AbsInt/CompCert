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

(** Auxiliary functions on machine registers *)

open Camlcoq
open Machregs

let register_names : (mreg, string) Hashtbl.t = Hashtbl.create 31

let _ =
  List.iter
    (fun (s, r) -> Hashtbl.add register_names r (camlstring_of_coqstring s))
    Machregs.register_names

let is_scratch_register s =
  s = "X16" || s = "x16" || s = "X30" || s = "x30"


let name_of_register r =
  Hashtbl.find_opt register_names r

let register_by_name s =
  Machregs.register_by_name (coqstring_uppercase_ascii_of_camlstring s)

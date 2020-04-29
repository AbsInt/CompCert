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

let register_names : (Machregs.mreg, string) Hashtbl.t = Hashtbl.create 31

let _ =
  List.iter
    (fun (s, r) -> Hashtbl.add register_names r (Camlcoq.camlstring_of_coqstring s))
    Machregs.register_names

let name_of_register r =
  Hashtbl.find_opt register_names r

let register_by_name s =
  Machregs.register_by_name (Camlcoq.coqstring_uppercase_ascii_of_camlstring s)

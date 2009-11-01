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

(* Command-line flags *)

let prepro_options = ref ([]: string list)
let linker_options = ref ([]: string list)
let exe_name = ref "a.out"
let option_flonglong = ref false
let option_fmadd = ref false
let option_fsda = ref false
let option_dclight = ref false
let option_dasm = ref false
let option_E = ref false
let option_S = ref false
let option_c = ref false
let option_v = ref false

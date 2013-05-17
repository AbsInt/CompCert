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
let assembler_options = ref ([]: string list)
let option_flongdouble = ref false
let option_fstruct_return = ref false
let option_fbitfields = ref false
let option_fvararg_calls = ref true
let option_fpacked_structs = ref false
let option_fsse = ref true
let option_ffloatconstprop = ref 2
let option_ftailcalls = ref true
let option_falignfunctions = ref (None: int option)
let option_falignbranchtargets = ref 0
let option_faligncondbranchs = ref 0
let option_finline_asm = ref false
let option_dparse = ref false
let option_dcmedium = ref false
let option_dclight = ref false
let option_dcminor = ref false
let option_drtl = ref false
let option_dtailcall = ref false
let option_dinlining = ref false
let option_dconstprop = ref false
let option_dcse = ref false
let option_dalloc = ref false
let option_dalloctrace = ref false
let option_dmach = ref false
let option_dasm = ref false
let option_sdump = ref false
let option_g = ref false
let option_o = ref (None: string option)
let option_E = ref false
let option_S = ref false
let option_c = ref false
let option_v = ref false
let option_small_data = 
  ref (if Configuration.arch = "powerpc"
       && Configuration.variant = "eabi"
       && Configuration.system = "diab"
       then 8 else 0)
let option_small_const = ref (!option_small_data)

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
let option_fstruct_passing = ref false
let option_fbitfields = ref false
let option_fvararg_calls = ref true
let option_funprototyped = ref true
let option_fpacked_structs = ref false
let option_ffpu = ref true
let option_ffloatconstprop = ref 2
let option_ftailcalls = ref true
let option_fconstprop = ref true
let option_fcse = ref true
let option_fredundancy = ref true
let option_falignfunctions = ref (None: int option)
let option_falignbranchtargets = ref 0
let option_faligncondbranchs = ref 0
let option_finline_asm = ref false
let option_mthumb = ref (Configuration.model = "armv7m")
let option_Osize = ref false
let option_finline = ref true
let option_finline_functions_called_once = ref true
let option_dprepro = ref false
let option_dparse = ref false
let option_dcmedium = ref false
let option_dclight = ref false
let option_dcminor = ref false
let option_drtl = ref false
let option_dltl = ref false
let option_dalloctrace = ref false
let option_dmach = ref false
let option_dasm = ref false
let option_sdump = ref false
let option_g = ref false
let option_gdwarf = ref (if Configuration.system = "diab" then 2 else 3)
let option_gdepth = ref 3
let option_o = ref (None: string option)
let option_E = ref false
let option_S = ref false
let option_c = ref false
let option_v = ref false
let option_interp = ref false
let option_small_data =
  ref (if Configuration.arch = "powerpc"
       && Configuration.abi = "eabi"
       && Configuration.system = "diab"
       then 8 else 0)
let option_small_const = ref (!option_small_data)
let option_timings = ref false
let stdlib_path = ref Configuration.stdlib_path
let use_standard_headers =  ref Configuration.has_standard_headers

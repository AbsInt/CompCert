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
let option_funprototyped = ref true
let option_fpacked_structs = ref false
let option_ffpu = ref true
let option_ffloatconstprop = ref 2
let option_ftailcalls = ref true
let option_falignfunctions = ref (None: int option)
let option_falignbranchtargets = ref 0
let option_faligncondbranchs = ref 0
let option_finline_asm = ref false
let option_fthumb = ref false
let option_Osize = ref false
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
let option_o = ref (None: string option)
let option_E = ref false
let option_S = ref false
let option_c = ref false
let option_v = ref false
let option_interp = ref false
let option_small_data = 
  ref (if Configuration.arch = "powerpc"
       && Configuration.variant = "eabi"
       && Configuration.system = "diab"
       then 8 else 0)
let option_small_const = ref (!option_small_data)
let option_timings = ref false

(** Timing facility *)

let timers : (string * float) list ref = ref []

let add_to_timer name time =
  let rec add = function
  | [] -> [name, time]
  | (name1, time1 as nt1) :: rem ->
      if name1 = name then (name1, time1 +. time) :: rem else nt1 :: add rem
  in timers := add !timers

let time name fn arg =
  if not !option_timings then
    fn arg
  else begin
    let start = Sys.time() in
    try
      let res = fn arg in
      add_to_timer name (Sys.time() -. start);
      res
    with x ->
      add_to_timer name (Sys.time() -. start);
      raise x
  end

let time2 name fn arg1 arg2 = time name (fun () -> fn arg1 arg2) ()
let time3 name fn arg1 arg2 arg3 = time name (fun () -> fn arg1 arg2 arg3) ()

let time_coq name fn arg =
  if not !option_timings then
    fn arg
  else begin
    let start = Sys.time() in
    try
      let res = fn arg in
      add_to_timer (Camlcoq.camlstring_of_coqstring name) (Sys.time() -. start);
      res
    with x ->
      add_to_timer (Camlcoq.camlstring_of_coqstring name) (Sys.time() -. start);
      raise x
  end

let print_timers () =
  if !option_timings then
    List.iter
      (fun (name, time) -> Printf.printf "%7.2fs  %s\n" time name)
      !timers

let _ = at_exit print_timers

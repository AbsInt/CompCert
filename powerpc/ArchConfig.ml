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

(* Architecture dependend configuration types. *)

type cpus=
  | Generic
  | E5500

let cpu_of_string = function
  | "e5500" -> E5500
  | _ -> Generic (* Others are currently not supported *)

type model =
  | PPC32
  | PPC64

let model_config: model ref = ref PPC32

let set_model = function
  | "ppc32" -> model_config := PPC32
  | "ppc64" -> model_config := PPC64
  | s -> Printf.eprintf "Invalid model `%s' is not supported\n" s; exit 2

let get_model () = !model_config

let string_of_model () =
  match !model_config with
  | PPC32 -> ""
  | PPC64 -> "64"

let needs_thumb () = false

type abi =
  | Eabi
  | Gnu

let abi_config: abi ref = ref Eabi

let set_abi = function
  | "eabi" -> abi_config := Eabi
  | "gnu" -> abi_config := Gnu
  | s ->  Printf.eprintf "Invalid abi `%s' is not supported\n" s; exit 2

let get_abi () = !abi_config

type system =
  | Linux
  | Diab

let system_config: system ref = ref Linux

let set_system = function
  | "linux" -> system_config := Linux
  | "diab" -> system_config := Diab
  | s -> Printf.eprintf "Invald system `%s' is not supported\n" s; exit 2

let string_of_system () =
  match !system_config with
  | Linux -> "linux"
  | Diab -> "diab"

let get_system () = !system_config

let small_data () =
  match !abi_config,!system_config with
  | Eabi,Diab -> 8
  | _ -> 0

let debug_str _ = true

let diab_system () =
  match !system_config with
  | Diab -> true
  | Linux -> false

let macosx_system _ = false

let arch = "powerpc"

let target_string () =
  let abi =    match !abi_config with
    | Eabi -> "eabi"
    | Gnu -> "gnueabi"
  and system  =  match !system_config with
  | Linux -> "linux"
  | Diab -> "diab"
  and model = match !model_config with
  | PPC32 -> ""
  | PPC64 -> "64" in
  Printf.sprintf "%s%s-%s-%s" arch model system abi

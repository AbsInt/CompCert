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

let cpu_of_string = function
  | _ -> Generic (* Others are currently not supported *)

type model =
  | Armv6
  | Armv7a
  | Armv7r
  | Armv7m

let model_config: model ref = ref Armv7a

let set_model = function
  | "armv6" -> model_config := Armv6
  | "armv7a" -> model_config := Armv7a
  | "armv7r" -> model_config := Armv7r
  | "armv7m" -> model_config := Armv7m
  | s -> Printf.eprintf "Invalid model `%s' is not supported\n" s; exit 2

let get_model () = !model_config

let string_of_model () =
  match !model_config with
  | Armv6 -> "armv6"
  | Armv7a -> "armv7a"
  | Armv7r -> "armv7r"
  | Armv7m -> "armv7m"

let needs_thumb () =
  match !model_config with
  | Armv7m -> true
  | _ -> false

type abi =
  | Eabi
  | Eabihf

let abi_config: abi ref = ref Eabi

let set_abi = function
  | "eabi" -> abi_config := Eabi
  | "hardfloat" -> abi_config := Eabihf
  | s ->  Printf.eprintf "Invalid abi `%s' is not supported\n" s; exit 2

let get_abi () = !abi_config

let string_of_abi () =
  match !abi_config with
  | Eabi -> "eabi"
  | Eabihf -> "hardfloat"

let small_data () = 0

type system =
  | Linux

let system_config: system ref = ref Linux

let set_system = function
  | "linux" -> system_config := Linux
  | s -> Printf.eprintf "Invald system `%s' is not supported\n" s; exit 2

let get_system () = !system_config

let string_of_system () =
  match !system_config with
  | Linux -> "linux"

let debug_str system = true

let diab_system _ = false

let macosx_system _ = false

let arch = "arm"

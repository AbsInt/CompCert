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
  | SSE2

let model_config: model ref = ref SSE2

let set_model = function
  | "sse2" -> model_config := SSE2
  | s -> Printf.eprintf "Invalid model `%s' is not supported\n" s; exit 2

let get_model () = !model_config

let needs_thumb _ = false

type abi =
  | Standard

let abi_config: abi ref = ref Standard

let set_abi = function
  | "standard" -> abi_config := Standard
  | s ->  Printf.eprintf "Invalid abi `%s' is not supported\n" s; exit 2

let get_abi = !abi_config

let small_data () = 0

type system =
  | Linux
  | Bsd
  | Macosx
  | Cygwin

let system_config: system ref = ref Linux

let set_system = function
  | "linux" -> system_config := Linux
  | "bsd" -> system_config := Bsd
  | "cygwin" -> system_config := Cygwin
  | "macosx" -> system_config := Macosx
  | s -> Printf.eprintf "Invald system `%s' is not supported\n" s; exit 2

let get_system () = !system_config

let string_of_system () =
  match !system_config with
  | Linux -> "linux"
  | Bsd -> "bsd"
  | Cygwin -> "cygwin"
  | Macosx -> "macosx"

let debug_str () = !system_config <> Cygwin

let diab_system _ = false

let macosx_system () =
  match !system_config with
  | Macosx -> true
  | _ -> false

let arch = "ia32"

let target_string () =
  let abi =  match !abi_config with
  | Standard -> "gnu"
  and system  =  match !system_config with
  | Linux -> "linux"
  | Bsd -> "bsd"
  | Cygwin -> "cygwin"
  | Macosx -> "macosx"
  and model = match !model_config with
  | SSE2 -> "" in
  Printf.sprintf "%s%s-%s-%s" arch model system abi

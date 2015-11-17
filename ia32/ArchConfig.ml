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

let model_of_string = function
  | "sse2" -> SSE2
  | s -> Printf.eprintf "Invalid model `%s' is not supported\n" s; exit 2

let string_of_model = function
  | SSE2 -> "sse2"

let needs_thumb _ = false

type abi =
  | Standard


let abi_of_string = function
  | "standard" -> Standard
  | s ->  Printf.eprintf "Invalid abi `%s' is not supported\n" s; exit 2

let string_of_abi = function
  | Standard -> "standard"

let small_data _ _ = 0


type system =
  | Linux
  | Bsd
  | Macosx
  | Cygwin

let system_of_string = function
  | "linux" -> Linux
  | "bsd" -> Bsd
  | "cygwin" -> Cygwin
  | "macosx" -> Macosx
  | s -> Printf.eprintf "Invald system `%s' is not supported\n" s; exit 2

let string_of_system = function
  | Linux -> "linux"
  | Bsd -> "bsd"
  | Cygwin -> "cygwin"
  | Macosx -> "macosx"

let debug_str system = true

let diab_system _ = false

let macosx_system = function
  | Macosx -> true
  | _ -> false

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

let model_of_string = function
  | "armv6" -> Armv6
  | "armv7a" -> Armv7a
  | "armv7r" -> Armv7r
  | "armv7m" -> Armv7m
  | s -> Printf.eprintf "Invalid model `%s' is not supported\n" s; exit 2

let string_of_model = function
  | Armv6 -> "armv6"
  | Armv7a -> "armv7a"
  | Armv7r -> "armv7r"
  | Armv7m -> "armv7m"

let needs_thumb = function
  | Armv7m -> true
  | _ -> false

type abi =
  | Eabi
  | Eabihf

let abi_of_string = function
  | "eabi" -> Eabi
  | "hardfloat" -> Eabihf
  | s ->  Printf.eprintf "Invalid abi `%s' is not supported\n" s; exit 2

let string_of_abi = function
  | Eabi -> "eabi"
  | Eabihf -> "hardfloat"

let small_data _ _ = 0

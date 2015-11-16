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

let model_of_string = function
  | "ppc32" -> PPC32
  | "ppc64" -> PPC64
  | s -> Printf.eprintf "Invalid model `%s' is not supported\n" s; exit 2

let string_of_model = function
  | PPC32 -> "ppc32"
  | PPC64 -> "ppc64"

let needs_thumb _ = false

type abi =
  | Eabi
  | Gnu

let abi_of_string = function
  | "eabi" -> Eabi
  | "gnu" -> Gnu
  | s ->  Printf.eprintf "Invalid abi `%s' is not supported\n" s; exit 2

let string_of_abi = function
  | Eabi -> "eabi"
  | Gnu -> "gnu"

let small_data abi system =
  match abi,system with
  | Eabi,"diab" -> 8
  | _ -> 0

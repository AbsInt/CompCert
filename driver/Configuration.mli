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

val arch: string
  (** Target architecture *)

val model: string
  (** Sub-model for this architecture *)

val abi: string
  (** ABI to use *)

val is_big_endian: bool
  (** Endianness to use *)

val system: string
  (** Flavor of operating system that runs CompCert *)

val prepro: string list
  (** How to invoke the external preprocessor *)

val asm: string list
  (** How to invoke the external assembler *)

val linker: string list
  (** How to invoke the external linker *)

val asm_supports_cfi: bool
  (** True if the assembler supports Call Frame Information *)

val stdlib_path: string
  (** Path to CompCert's library *)

val has_runtime_lib: bool
  (** True if CompCert's library is available. *)

val has_standard_headers: bool
  (** True if CompCert's standard header files is available. *)


type struct_passing_style =
  | SP_ref_callee                       (* by reference, callee takes copy *)
  | SP_ref_caller                       (* by reference, caller takes copy *)
  | SP_split_args                       (* by value, as a sequence of ints *)

type struct_return_style =
  | SR_int1248      (* return by content if size is 1, 2, 4 or 8 bytes *)
  | SR_int1to4      (* return by content if size is <= 4 *)
  | SR_int1to8      (* return by content if size is <= 8 *)
  | SR_ref          (* always return by assignment to a reference
                       given as extra argument *)

val struct_passing_style: struct_passing_style
  (** Calling conventions to use for passing structs and unions as
      first-class values *)

val struct_return_style: struct_return_style
  (** Calling conventions to use for returning structs and unions as
      first-class values *)

type response_file_style =
  | Gnu         (* responsefiles in gnu compatible syntax *)
  | Diab        (* responsefiles in diab compatible syntax *)
  | Unsupported (* responsefiles are not supported *)

val response_file_style: response_file_style
  (** Style of supported responsefiles *)

val asm_supports_pipe: bool
  (** True if the assembler supports reading from stdin *)

val gnu_toolchain: bool
  (** Does the targeted system use the gnu toolchain *)

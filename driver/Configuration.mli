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

type response_file_style =
  | Gnu         (* responsefiles in gnu compatible syntax *)
  | Diab        (* responsefiles in diab compatible syntax *)
  | Unsupported (* responsefiles are not supported *)

val response_file_style: response_file_style
  (** Style of supported responsefiles *)

val gnu_toolchain: bool
  (** Does the targeted system use the gnu toolchain *)

val elf_target: bool
  (** Is the target binary format ELF? *)

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
val advanced_debug: bool
  (** True if advanced debug is implement for the Target *)


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

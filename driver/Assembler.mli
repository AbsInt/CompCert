(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*      Bernhard Schommer, AbsInt Angewandte Informatik GmbH           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

val assemble: string -> string -> unit
  (** From asm to object file *)

type assembler_handle
  (** Internal assembler handle type *)

val open_assembler_out : File.input_file -> out_channel * assembler_handle
  (** Open either a file or the assembler for assembling *)

val close_assembler_out :  out_channel -> assembler_handle -> string
  (** Either wait for the assembler to finish or close the file and call it *)

val assembler_actions: (Commandline.pattern * Commandline.action) list
  (** Commandline optins affecting the assembler *)

val assembler_help: string
  (** Commandline help description *)

val add_pipe: unit -> unit
  (** Add pipe option for the assembler *)

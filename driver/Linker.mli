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

val linker: string -> string list -> unit
  (** Link files into executbale *)

val linker_actions: (Commandline.pattern * Commandline.action) list
  (** Commandline optins affecting the assembler *)

val linker_help: string
  (** Commandline help description *)

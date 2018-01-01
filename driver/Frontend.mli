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

val dparse_destination: string option ref
  (** Destination file for parsed c file dump *)

val dcompcertc_destination: string option ref
  (** Destination file for CompCert C file dump *)

val preprocess: string -> string -> unit
  (** From C to preprocessed C *)

val parse_c_file: string -> string -> Csyntax.coq_function Ctypes.program
  (** From preprocessed C to Csyntax *)

val prepro_actions: (Commandline.pattern * Commandline.action) list
  (** Commandline optins affecting the frontend *)

val prepro_help: string
  (** Commandline help description *)

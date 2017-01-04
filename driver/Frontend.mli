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

val dcompcertc_destination: string option ref

val preprocess: string -> File.process_outfile option -> unit
  (** From C to preprocessed C *)

val parse_c_file: string -> in_channel -> Csyntax.coq_function Ctypes.program
  (** From preprocessed C to Csyntax *)

val prepro_actions: (Commandline.pattern * Commandline.action) list
  (** Commandline optins affecting the frontend *)

val prepro_help: string
  (** Commandline help description *)

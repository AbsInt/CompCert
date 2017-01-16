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

type prepro_handle
  (** Internal preprocessor handle type *)

val preprocess: File.input_file -> string -> unit
  (** From C to preprocessed C *)

val parse_c_file: string -> (in_channel * prepro_handle) -> Csyntax.coq_function Ctypes.program
  (** From preprocessed C to Csyntax *)

val prepro_actions: (Commandline.pattern * Commandline.action) list
  (** Commandline optins affecting the frontend *)

val prepro_help: string
  (** Commandline help description *)

val add_pipe: unit -> unit
  (** Add pipe option for the preprocessor *)

val open_prepro_in : File.input_file -> in_channel * prepro_handle
  (** Run or start the preprocessor and get an in_channel for its output *)

val close_prepro_in: in_channel -> prepro_handle -> unit
  (** Close the in_channel of the preprocessor optionally wait until it is finished *)

val open_preprocessed_file : File.input_file -> in_channel * prepro_handle
  (** Open a preproceesed file *)

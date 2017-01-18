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


val command: ?stdout:string -> string list -> int
    (** Execute the command with the given arguments and an optional file for
        the stdout. Returns the exit code. *)

val command_error: string -> int -> unit
   (** Generate an error message for the given command and exit code *)

val print_errorcodes: string -> Errors.errcode list -> 'a
   (** Printing of error messages *)

val explode_comma_option: string -> string list
   (** Split option at commas *)

val push_action: (File.input_file -> string) -> File.input_file -> unit
  (** Add an action to be performed after parsing the command line *)

val push_linker_arg: string -> unit
  (** Add a linker arguments *)

val perform_actions: unit -> string list
  (** Perform actions *)

type process_info
  (** Internal type for the create_process and waitpid wrappers *)

val waitpid: process_info -> int
  (** Wrapper around waitpid *)

val open_process_out : string list -> (process_info * out_channel) option
  (** Wrapper for a create_process based open_process_out implementation *)

val close_process_out : process_info -> out_channel -> int
  (** Corresponding close_process for open_process *)

val open_process_in : string list -> (process_info * in_channel) option
  (** Wrapper for a create_process based open_process_in implementation *)

val close_process_in : process_info -> in_channel -> int
  (** Corresponding close_process for open_process *)

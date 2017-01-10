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


val command: ?stdout:File.process_file -> ?stdin:Unix.file_descr -> string list -> int
    (** Execute the command with the given arguments and an optional file for
        the stdout. Returns the exit code. *)

val command_error: string -> int -> unit
   (** Generate an error message for the given command and exit code *)

val print_errorcodes: string -> Errors.errcode list -> 'a
   (** Printing of error messages *)

val gnu_system: bool
   (** Are the target tools gnu tools? *)

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

val create_process: Unix.file_descr-> Unix.file_descr -> string list -> process_info option
  (** Wrapper around create process *)

val waitpid: process_info -> int
  (** Wrapper around waitpid *)

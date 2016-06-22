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


val command: ?stdout:string  -> string list -> int
    (** Execute the command with the given arguments and an optional file for
        the stdout. Returns the exit code. *)

val command_error: string -> int -> unit
   (** Generate an error message for the given command and exit code *)

val safe_remove: string -> unit
   (** Remove the given file if it exists *)

val output_filename: ?final:bool -> string -> string -> string -> string
   (** Determine names for output files.  We use -o option if specified
       and if this is the final destination file (not a dump file).
       Otherwise, we generate a file in the current directory. *)

val output_filename_default: string -> string
   (** Return either the file specified by -o or the given file name *)

val ensure_inputfile_exists: string -> unit
   (** Test whether the given input file exists *)

val print_error:out_channel -> Errors.errcode list -> unit
   (** Printing of error messages *)

val gnu_option: string -> bool
   (** Set the options for gnu systems *)

val explode_comma_option: string -> string list
   (** Split option at commas *)

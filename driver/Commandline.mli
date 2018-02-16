(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Parsing of command-line flags and arguments *)

(* A command-line specification is a list of pairs (pattern, action).
   Command-line words are matched against the patterns, and the
   corresponding actions are invoked. *)

type pattern =
  | Exact of string             (** exactly this string *)
  | Prefix of string            (** any string starting with this prefix *)
  | Suffix of string            (** any string ending with this suffix *)
  | Regexp of Str.regexp        (** any string matching this anchored regexp *)

val _Regexp: string -> pattern  (** text of an [Str] regexp *)

type action =
  | Set of bool ref             (** set the given ref to true *)
  | Unset of bool ref           (** set the given ref to false *)
  | Self of (string -> unit)    (** call the function with the matched string *)
  | String of (string -> unit)  (** read next arg as a string, call function *)
  | Integer of (int -> unit)    (** read next arg as an int, call function *)
  | Ignore                      (** ignore the next arg *)
  | Unit of (unit -> unit)      (** call the function with unit as argument *)
(* Note on precedence: [Exact] patterns are tried first, then the other
   patterns are tried in the order in which they appear in the list. *)

exception CmdError of string
(** Raise by [parse_cmdline] when an error occured *)

val parse_cmdline: (pattern * action) list -> unit
(** [parse_cmdline actions] parses the commandline and performs all [actions].
    Raises [CmdError] if an error occurred.
*)

val longopt_int: string -> (int -> unit) -> pattern * action
(** [longopt_int key fn] generates a pattern and an action for
    options of the form [key=<n>] and calls [fn] with the integer argument
*)

val argv: string array ref
(** [argv] contains the complete command line after @-file expandsion *)

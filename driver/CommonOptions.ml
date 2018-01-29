(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Clflags
open Commandline

(* The version string for [tool_name] *)
let version_string tool_name=
  if Version.buildnr <> "" && Version.tag <> "" then
    Printf.sprintf "The CompCert %s, %s, Build: %s, Tag: %s\n" tool_name Version.version Version.buildnr Version.tag
  else
    Printf.sprintf "The CompCert %s, version %s\n" tool_name Version.version

(* Print the version string and exit the program *)
let print_version_and_exit tool_name () =
  Printf.printf "%s" (version_string tool_name); exit 0

let version_options tool_name =
  [ Exact "-version", Unit (print_version_and_exit tool_name);
    Exact "--version", Unit (print_version_and_exit tool_name);]

(* Language support options *)

let all_language_support_options = [
  option_fbitfields; option_flongdouble;
  option_fstruct_passing; option_fvararg_calls; option_funprototyped;
  option_fpacked_structs; option_finline_asm
]

let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref]
let set_all opts () = List.iter (fun r -> r := true) opts
let unset_all opts () = List.iter (fun r -> r := false) opts

let language_support_options =
  [ Exact "-fall", Unit (set_all all_language_support_options);
    Exact "-fnone", Unit (unset_all all_language_support_options);]
  @ f_opt "longdouble" option_flongdouble
  @ f_opt "struct-return" option_fstruct_passing
  @ f_opt "struct-passing" option_fstruct_passing
  @ f_opt "bitfields" option_fbitfields
  @ f_opt "vararg-calls" option_fvararg_calls
  @ f_opt "unprototyped" option_funprototyped
  @ f_opt "packed-structs" option_fpacked_structs
  @ f_opt "inline-asm" option_finline_asm

let language_support_help =
  {|Language support options (use -fno-<opt> to turn off -f<opt>) :
  -fbitfields    Emulate bit fields in structs [off]
  -flongdouble   Treat 'long double' as 'double' [off]
  -fstruct-passing  Support passing structs and unions by value as function
                    results or function arguments [off]
  -fstruct-return   Like -fstruct-passing (deprecated)
  -fvararg-calls Support calls to variable-argument functions [on]
  -funprototyped Support calls to old-style functions without prototypes [on]
  -fpacked-structs  Emulate packed structs [off]
  -finline-asm   Support inline 'asm' statements [off]
  -fall          Activate all language support options above
  -fnone         Turn off all language support options above
|}

(* General options *)

let general_help =
  {|General options:
  -stdlib <dir>  Set the path of the Compcert run-time library
  -v             Print external commands before invoking them
  -timings       Show the time spent in various compiler passes
  -version       Print the version string and exit
  -target <value> Generate code for the given target
  -conf <file>   Read configuration from file
  @<file>        Read command line options from <file>
|}

let general_options =
  [ Exact "-conf", Ignore; (* Ignore option since it is already handled *)
    Exact "-target", Ignore;(* Ignore option since it is already handled *)
    Exact "-v", Set option_v;
    Exact "-stdlib", String(fun s -> stdlib_path := s);
    Exact "-timings", Set option_timings;]

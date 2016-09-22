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

(* Management of errors and warnings *)

open Format
open Commandline

let error_fatal = ref false
let color_diagnostics =
  let term = try Sys.getenv "TERM" with Not_found -> "" in
  ref (Unix.isatty Unix.stderr && term <> "dumb" && term <>"")

let num_errors = ref 0
let num_warnings = ref 0

let reset () = num_errors := 0; num_warnings := 0

exception Abort

(* [fatal_error_raw] is identical to [fatal_error], except it uses [Printf]
   to print its message, as opposed to [Format], and does not automatically
   introduce indentation and a final dot into the message. This is useful
   for multi-line messages. *)

let fatal_error_raw fmt =
  incr num_errors;
  Printf.kfprintf
    (fun _ -> raise Abort)
    stderr
    (fmt ^^ "Fatal error; compilation aborted.\n%!")

type msg_class =
  | WarningMsg
  | ErrorMsg
  | FatalErrorMsg
  | SuppressedMsg

type warning_type =
  | Unnamed
  | Unknown_attribute
  | Zero_length_array
  | Celeven_extension
  | Gnu_empty_struct
  | Missing_declarations
  | Constant_conversion
  | Int_conversion
  | Varargs
  | Implicit_function_declaration
  | Pointer_type_mismatch
  | Compare_distinct_pointer_types
  | Implicit_int
  | Main_return_type
  | Invalid_noreturn
  | Return_type
  | Literal_range
  | Unknown_pragmas
  | CompCert_conformance

let active_warnings: warning_type list ref = ref [
  Unnamed;
  Unknown_attribute;
  Celeven_extension;
  Gnu_empty_struct;
  Missing_declarations;
  Constant_conversion;
  Int_conversion;
  Varargs;
  Implicit_function_declaration;
  Pointer_type_mismatch;
  Compare_distinct_pointer_types;
  Implicit_int;
  Main_return_type;
  Invalid_noreturn;
  Return_type;
  Literal_range;
]

let error_warnings: warning_type list ref = ref []

let string_of_warning = function
  | Unnamed -> ""
  | Unknown_attribute -> "unknown-attributes"
  | Zero_length_array -> "zero-length-array"
  | Celeven_extension -> "c11-extensions"
  | Gnu_empty_struct -> "gnu-empty-struct"
  | Missing_declarations -> "missing-declarations"
  | Constant_conversion -> "constant-conversion"
  | Int_conversion -> "int-conversion"
  | Varargs -> "varargs"
  | Implicit_function_declaration -> "implicit-function-declaration"
  | Pointer_type_mismatch -> "pointer-type-mismatch"
  | Compare_distinct_pointer_types -> "compare-distinct-pointer-types"
  | Implicit_int -> "implicit-int"
  | Main_return_type -> "main-return-type"
  | Invalid_noreturn -> "invalid-noreturn"
  | Return_type -> "return-type"
  | Literal_range -> "literal-range"
  | Unknown_pragmas -> "unknown-pragmas"
  | CompCert_conformance -> "compcert-conformance"

let activate_warning w () =
  if not (List.mem w !active_warnings) then
    active_warnings:=w::!active_warnings

let deactivate_warning w  () =
  active_warnings:=List.filter ((<>) w) !active_warnings;
  error_warnings:= List.filter ((<>) w) !error_warnings

let warning_as_error w ()=
  activate_warning w ();
  if not (List.mem w !error_warnings) then
    error_warnings := w::!error_warnings

let warning_not_as_error w () =
  error_warnings:= List.filter ((<>) w) !error_warnings

let wall () =
  active_warnings:=[
    Unnamed;
    Unknown_attribute;
    Zero_length_array;
    Celeven_extension;
    Gnu_empty_struct;
    Missing_declarations;
    Constant_conversion;
    Int_conversion;
    Varargs;
    Implicit_function_declaration;
    Pointer_type_mismatch;
    Compare_distinct_pointer_types;
    Implicit_int;
    Main_return_type;
    Invalid_noreturn;
    Return_type;
    Literal_range;
    Unknown_pragmas;
  ]

let werror () =
  error_warnings:=[
    Unnamed;
    Unknown_attribute;
    Zero_length_array;
    Celeven_extension;
    Gnu_empty_struct;
    Missing_declarations;
    Constant_conversion;
    Int_conversion;
    Varargs;
    Implicit_function_declaration;
    Pointer_type_mismatch;
    Compare_distinct_pointer_types;
    Implicit_int;
    Main_return_type;
    Invalid_noreturn;
    Return_type;
    Literal_range;
    Unknown_pragmas;
  ]


let key_of_warning w =
  match w with
  | Unnamed -> None
  | _ -> Some ("-W"^(string_of_warning w))

let key_add_werror = function
  | None -> Some ("-Werror")
  | Some s -> Some ("-Werror,"^s)

let classify_warning w =
  let key = key_of_warning w in
  if List.mem w !active_warnings then
    if List.mem w !error_warnings then
      let key = key_add_werror key in
      if !error_fatal then
        FatalErrorMsg,key
      else
        ErrorMsg,key
    else
      WarningMsg,key
  else
    SuppressedMsg,None

let cprintf fmt c =
  if  Unix.isatty Unix.stderr && !color_diagnostics then
    fprintf fmt c
  else
    ifprintf fmt c

let rsc fmt =
  cprintf fmt "\x1b[0m"

let bc fmt =
  cprintf fmt "\x1b[1m"

let rc fmt =
  cprintf fmt "\x1b[31;1m"

let mc fmt  =
  cprintf fmt "\x1b[35;1m"

let pp_key key fmt =
  let key = match key with
  | None -> ""
  | Some s -> " ["^s^"]" in
  fprintf fmt "%s%t@." key rsc

let pp_loc fmt (filename,lineno) =
  if filename <> "" then
    fprintf fmt "%t%s:%d:%t" bc filename lineno rsc

let error key loc fmt =
  incr num_errors;
  kfprintf (pp_key key)
    err_formatter ("%a %terror:%t %t" ^^ fmt) pp_loc loc rc rsc bc

let fatal_error key loc fmt =
  incr num_errors;
  kfprintf
    (fun fmt -> pp_key key fmt;raise Abort)
    err_formatter ("%a %terror:%t %t" ^^ fmt) pp_loc loc rc rsc bc

let warning loc ty fmt =
  let kind,key = classify_warning ty in
  match kind with
  | ErrorMsg ->
      error key loc fmt
  | FatalErrorMsg ->
      fatal_error key loc fmt
  | WarningMsg ->
      incr num_warnings;
      kfprintf (pp_key key)
        err_formatter ("%a %twarning:%t %t" ^^ fmt) pp_loc loc mc rsc bc
  | SuppressedMsg -> ifprintf err_formatter fmt

let error loc fmt =
  if !error_fatal then
    fatal_error None loc fmt
  else
    error None loc fmt

let fatal_error loc fmt =
  fatal_error None loc fmt

let check_errors () =
  if !num_errors > 0 then
    eprintf "@[<hov 0>%d error%s detected.@]@."
            !num_errors
            (if !num_errors = 1 then "" else "s");
  !num_errors > 0

let error_option w =
  let key = string_of_warning w in
  [Exact ("-W"^key), Unit (activate_warning w);
   Exact ("-Wno"^key), Unit (deactivate_warning w);
   Exact ("-Werror="^key), Unit ( warning_as_error w);
   Exact ("-Wno-error="^key), Unit ( warning_not_as_error w)]

let warning_options =
  error_option Unnamed @
  error_option Unknown_attribute @
  error_option Zero_length_array @
  error_option Celeven_extension @
  error_option Gnu_empty_struct @
  error_option Missing_declarations @
  error_option Constant_conversion @
  error_option Int_conversion @
  error_option Varargs @
  error_option Implicit_function_declaration @
  error_option Pointer_type_mismatch @
  error_option Compare_distinct_pointer_types @
  error_option Implicit_int @
  error_option Main_return_type @
  error_option Invalid_noreturn @
  error_option Return_type @
  error_option Literal_range @
  error_option Unknown_pragmas @
  [Exact ("-Wfatal-errors"), Set error_fatal;
   Exact ("-fdiagnostics-color"), Ignore; (* Either output supports it or no color *)
   Exact ("-fno-diagnostics-color"), Unset color_diagnostics;
   Exact ("-Werror"), Unit werror;
   Exact ("-Wall"), Unit wall;]

let warning_help = "Diagnostic options:\n\
\  -W<warning>        Enable the specific <warning>\n\
\  -Wno-<warning>     Disable the specific <warning>\n\
\  -Werror            Make all warnings into errors\n\
\  -Werror=<warning>  Turn <warning> into an error\n\
\  -Wno-error=<warning> Turn <warning> into a warning even if -Werror is\n\
                        specified\n\
\  -Wfatal-errors     Turn all errors into fatal errors aborting the compilation\n\
\  -fdiagnostics-color Turn on colored diagnostics\n\
\  -fno-diagnostics-color Turn of colored diagnostics\n"

let raise_on_errors () =
  if !num_errors > 0 then
    raise Abort

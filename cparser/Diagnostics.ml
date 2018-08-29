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

(* Should errors be treated as fatal *)
let error_fatal = ref false

(* Maximum number of errors, 0 means unlimited *)
let max_error = ref 0

(* Whether [-Woption] should be printed *)
let diagnostics_show_option = ref true

(* Test if color diagnostics are available by testing if stderr is a tty
   and if the environment varibale TERM is set
*)
let color_diagnostics =
  let term = try Sys.getenv "TERM" with Not_found -> "" in
  let activate = try
      (Unix.isatty Unix.stderr && term <> "dumb" && term <>"")
    with _ -> false in
  ref activate

let num_errors = ref 0
let num_warnings = ref 0


let error_limit_reached  () =
  let max_err = !max_error in
  max_err <> 0 && !num_errors >= max_err - 1

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
  | Inline_asm_sdump
  | Unused_variable
  | Unused_parameter
  | Wrong_ais_parameter
  | Unused_ais_parameter
  | Ignored_attributes
  | Extern_after_definition
  | Static_in_inline
  | Flexible_array_extensions
  | Tentative_incomplete_static
  | Reduced_alignment

(* List of active warnings *)
let active_warnings: warning_type list ref = ref [
  Unnamed;
  Unknown_attribute;
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
  Inline_asm_sdump;
  Wrong_ais_parameter;
  Unused_ais_parameter;
  Ignored_attributes;
  Extern_after_definition;
  Static_in_inline;
]

(* List of errors treated as warning *)
let error_warnings: warning_type list ref = ref []

(* Conversion from warning type to string *)
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
  | Inline_asm_sdump -> "inline-asm-sdump"
  | Unused_variable -> "unused-variable"
  | Unused_parameter -> "unused-parameter"
  | Wrong_ais_parameter -> "wrong-ais-parameter"
  | Unused_ais_parameter -> "unused-ais-parameter"
  | Ignored_attributes -> "ignored-attributes"
  | Extern_after_definition -> "extern-after-definition"
  | Static_in_inline -> "static-in-inline"
  | Flexible_array_extensions -> "flexible-array-extensions"
  | Tentative_incomplete_static -> "tentative-incomplete-static"
  | Reduced_alignment -> "reduced-alignment"

(* Activate the given warning *)
let activate_warning w () =
  if not (List.mem w !active_warnings) then
    active_warnings:=w::!active_warnings

(* Deactivate the given warning*)
let deactivate_warning w  () =
  active_warnings:=List.filter ((<>) w) !active_warnings;
  error_warnings:= List.filter ((<>) w) !error_warnings

(* Activate error for warning *)
let warning_as_error w ()=
  activate_warning w ();
  if not (List.mem w !error_warnings) then
    error_warnings := w::!error_warnings

(* Deactivate error for warning *)
let warning_not_as_error w () =
  error_warnings:= List.filter ((<>) w) !error_warnings

(* Activate all warnings *)
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
    CompCert_conformance;
    Inline_asm_sdump;
    Unused_variable;
    Unused_parameter;
    Wrong_ais_parameter;
    Ignored_attributes;
    Extern_after_definition;
    Static_in_inline;
    Flexible_array_extensions;
    Tentative_incomplete_static;
    Reduced_alignment;
  ]

let wnothing () =
  active_warnings :=[]

(* Make all warnings an error *)
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
    CompCert_conformance;
    Inline_asm_sdump;
    Unused_variable;
    Wrong_ais_parameter;
    Unused_ais_parameter;
    Ignored_attributes;
    Extern_after_definition;
    Static_in_inline;
    Flexible_array_extensions;
    Tentative_incomplete_static;
    Reduced_alignment;
  ]

(* Generate the warning key for the message *)
let key_of_warning w =
  match w with
  | Unnamed -> None
  | _ -> if !diagnostics_show_option then
      Some ("-W"^(string_of_warning w))
    else
      None

(* Add -Werror to the printed keys *)
let key_add_werror w =
  if !diagnostics_show_option then
    match w with
    | None -> Some ("-Werror")
    | Some s -> Some ("-Werror,"^s)
  else
    None

(* Lookup how to print the warning *)
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

(* Print color codes if color_diagnostics are enabled *)
let cprintf fmt c =
  if !color_diagnostics then
    fprintf fmt c
  else
    ifprintf fmt c

(* Reset color codes *)
let rsc fmt =
  cprintf fmt "\x1b[0m"

(* BOLD *)
let bc fmt =
  cprintf fmt "\x1b[1m"

(* RED *)
let rc fmt =
  cprintf fmt "\x1b[31;1m"

(* MAGENTA *)
let mc fmt  =
  cprintf fmt "\x1b[35;1m"

(* Print key (if available) and flush the formatter *)
let pp_key key fmt =
  let key = match key with
  | None -> ""
  | Some s -> " ["^s^"]" in
  fprintf fmt "%s%t@." key rsc

(* Different loc output formats *)
type loc_format =
  | Default
  | MSVC
  | Vi

let diagnostics_format : loc_format ref = ref Default

(* Parse the option string *)
let parse_loc_format s =
  let s = String.sub s 21 ((String.length s) - 21) in
  let loc_fmt = match s with
  | "ccomp" -> Default
  | "msvc" -> MSVC
  | "vi" -> Vi
  | s -> Printf.eprintf "Invalid value '%s' in '-fdiagnostics-format=%s'\n" s s; exit 2 in
  diagnostics_format := loc_fmt

(* Print the location or ccomp for the case of unknown loc *)
let pp_loc fmt (filename,lineno) =
  let lineno = if lineno = -10 then "" else
    match !diagnostics_format with
      | Default -> sprintf ":%d" lineno
      | MSVC -> sprintf "(%d)" lineno
      | Vi -> sprintf " +%d" lineno in
  if filename <> "" && filename <> "cabs loc unknown" then
    fprintf fmt "%t%s%s:%t " bc filename lineno rsc
  else
    fprintf fmt "%tccomp:%t " bc rsc

let error key loc fmt =
  incr num_errors;
  kfprintf (pp_key key)
    err_formatter ("%a%terror:%t %t" ^^ fmt) pp_loc loc rc rsc bc

let fatal_error key loc fmt =
  incr num_errors;
  kfprintf
    (fun fmt -> pp_key key fmt;raise Abort)
    err_formatter ("%a%terror:%t %t" ^^ fmt) pp_loc loc rc rsc bc

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
        err_formatter ("%a%twarning:%t %t" ^^ fmt) pp_loc loc mc rsc bc
  | SuppressedMsg -> ifprintf err_formatter fmt

let error loc fmt =
  if !error_fatal || error_limit_reached ()then
    fatal_error None loc fmt
  else
    error None loc fmt

let fatal_error loc fmt =
  fatal_error None loc fmt

let error_summary () =
 if !num_errors > 0 then begin
    eprintf "@[<hov 0>%d error%s detected.@]@."
            !num_errors
            (if !num_errors = 1 then "" else "s");
    num_errors := 0;
  end

let check_errors () =
  if !num_errors > 0 then begin
    eprintf "@[<hov 0>%d error%s detected.@]@."
            !num_errors
            (if !num_errors = 1 then "" else "s");
    num_errors := 0;
    raise Abort
  end


let error_option w =
  let key = string_of_warning w in
  [Exact ("-W"^key), Unit (activate_warning w);
   Exact ("-Wno-"^key), Unit (deactivate_warning w);
   Exact ("-Werror="^key), Unit (warning_as_error w);
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
  error_option CompCert_conformance @
  error_option Inline_asm_sdump @
  error_option Unused_variable @
  error_option Unused_parameter @
  error_option Wrong_ais_parameter @
  error_option Unused_ais_parameter @
  error_option Ignored_attributes @
  error_option Extern_after_definition @
  error_option Static_in_inline @
  error_option Flexible_array_extensions @
  error_option Tentative_incomplete_static @
  error_option Reduced_alignment @
  [Exact ("-Wfatal-errors"), Set error_fatal;
   Exact ("-fdiagnostics-color"), Ignore; (* Either output supports it or no color *)
   Exact ("-fno-diagnostics-color"), Unset color_diagnostics;
   Exact ("-Werror"), Unit werror;
   Exact ("-Wall"), Unit wall;
   Exact ("-w"), Unit wnothing;
   longopt_int ("-fmax-errors") ((:=) max_error);
   Exact("-fno-diagnostics-show-option"),Unset diagnostics_show_option;
   Exact("-fdiagnostics-show-option"),Set diagnostics_show_option;
   _Regexp("-fdiagnostics-format=\\(ccomp\\|msvc\\|vi\\)"),Self parse_loc_format;
  ]

let warning_help = {|Diagnostic options:
  -Wall              Enable all warnings
  -W<warning>        Enable the specific <warning>
  -Wno-<warning>     Disable the specific <warning>
  -Werror            Make all warnings into errors
  -Werror=<warning>  Turn <warning> into an error
  -Wno-error=<warning> Turn <warning> into a warning even if -Werror is
                       specified
  -Wfatal-errors     Turn all errors into fatal errors aborting the compilation
  -fdiagnostics-color Turn on colored diagnostics
  -fno-diagnostics-color Turn of colored diagnostics
  -fmax-errors=<n>   Maximum number of errors to report
  -fdiagnostics-show-option Print the option name with mappable diagnostics
  -fno-diagnostics-show-option Turn of printing of options with mappable
                               diagnostics
|}

let raise_on_errors () =
  if !num_errors > 0 then
    raise Abort

let crash exn =
  if Version.buildnr <> "" && Version.tag <> "" then begin
    let backtrace = Printexc.get_backtrace () in
    eprintf "%tThis is CompCert, %s, Build:%s, Tag:%s%t\n"
      bc Version.version Version.buildnr Version.tag rsc;
    eprintf "Backtrace (please include this in your support request):\n%s"
      backtrace;
    eprintf "%tUncaught exception: %s.\n\
\    Please report this problem to our support.\n\
\    Error occurred in Build: %s, Tag: %s.\n%t"
      rc (Printexc.to_string exn) Version.buildnr Version.tag rsc;
    exit 2
  end else begin
    let backtrace = Printexc.get_backtrace ()
    and exc = Printexc.to_string exn in
    eprintf "Fatal error: uncaught exception %s\n%s" exc backtrace;
    exit 2
  end

let no_loc = ("", -1)

let file_loc file = (file,-10)

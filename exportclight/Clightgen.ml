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

open Printf
open Commandline
open Clflags
open CommonOptions
open Driveraux
open Frontend
open Diagnostics

let tool_name = "Clight generator"

(* clightgen-specific options *)

let option_normalize = ref false

(* From CompCert C AST to Clight *)

let compile_c_ast sourcename csyntax ofile =
  let loc = file_loc sourcename in
  let clight =
    match SimplExpr.transl_program csyntax with
    | Errors.OK p ->
        begin match SimplLocals.transf_program p with
        | Errors.OK p' ->
            if !option_normalize
            then Clightnorm.norm_program p'
            else p'
        | Errors.Error msg ->
          fatal_error loc "%a" print_error  msg
        end
    | Errors.Error msg ->
      fatal_error loc "%a" print_error msg in
  (* Dump Clight in C syntax if requested *)
  if !option_dclight then begin
    let ofile = Filename.chop_suffix sourcename ".c" ^ ".light.c" in
    let oc = open_out ofile in
    PrintClight.print_program (Format.formatter_of_out_channel oc) clight;
    close_out oc
  end;
  (* Print Clight in Coq syntax *)
  let oc = open_out ofile in
  ExportClight.print_program (Format.formatter_of_out_channel oc)
                             clight sourcename !option_normalize;
  close_out oc

(* From C source to Clight *)

let compile_c_file sourcename ifile ofile =
  compile_c_ast sourcename (parse_c_file sourcename ifile) ofile

let output_filename sourcename suff =
  let prefixname = Filename.chop_suffix sourcename suff in
  output_filename_default (prefixname ^ ".v")

(* Processing of a .c file *)

let process_c_file sourcename =
  ensure_inputfile_exists sourcename;
  let ofile = output_filename sourcename ".c" in
  if !option_E then begin
    preprocess sourcename "-"
  end else begin
    let preproname = Driveraux.tmp_file ".i" in
    preprocess sourcename preproname;
    compile_c_file sourcename preproname ofile
  end

(* Processing of a .i file *)

let process_i_file sourcename =
  ensure_inputfile_exists sourcename;
  let ofile = output_filename sourcename ".i" in
  compile_c_file sourcename sourcename ofile

let usage_string =
  version_string tool_name^
{|Usage: clightgen [options] <source files>
Recognized source files:
  .c             C source file
  .i or .p       C source file that should not be preprocessed
Processing options:
  -normalize     Normalize the generated Clight code w.r.t. loads in expressions
  -E             Preprocess only, send result to standard output
  -o <file>      Generate output in <file>
|} ^
prepro_help ^
language_support_help ^
{|Tracing options:
  -dparse        Save C file after parsing and elaboration in <file>.parsed.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
|} ^
  general_help ^
  warning_help


let print_usage_and_exit () =
  printf "%s" usage_string; exit 0

let set_all opts () = List.iter (fun r -> r := true) opts
let unset_all opts () = List.iter (fun r -> r := false) opts

let actions : ((string -> unit) * string) list ref = ref []
let push_action fn arg =
  actions := (fn, arg) :: !actions

let perform_actions () =
  let rec perform = function
    | [] -> ()
    | (fn,arg) :: rem -> fn arg; perform rem
  in perform (List.rev !actions)

let num_input_files = ref 0

let cmdline_actions =
  [
(* Getting help *)
  Exact "-help", Unit print_usage_and_exit;
  Exact "--help", Unit print_usage_and_exit;]
  (* Getting version info *)
 @ version_options tool_name @
(* Processing options *)
 [ Exact "-E", Set option_E;
  Exact "-normalize", Set option_normalize;
  Exact "-o", String(fun s -> option_o := Some s);
  Prefix "-o", Self (fun s -> let s = String.sub s 2 ((String.length s) - 2) in
                              option_o := Some s);]
(* Preprocessing options *)
  @ prepro_actions @
(* Tracing options *)
 [ Exact "-dparse", Set option_dparse;
  Exact "-dc", Set option_dcmedium;
  Exact "-dclight", Set option_dclight;]
  @ general_options
(* Diagnostic options *)
  @ warning_options
  @ language_support_options @
(* Catch options that are not handled *)
  [Prefix "-", Self (fun s ->
     fatal_error no_loc "Unknown option `%s'" s);
(* File arguments *)
  Suffix ".c", Self (fun s ->
      incr num_input_files; push_action process_c_file s);
  Suffix ".i", Self (fun s ->
      incr num_input_files; push_action process_i_file s);
  Suffix ".p", Self (fun s ->
      incr num_input_files; push_action process_i_file s);
  ]

let _ =
  try
  Gc.set { (Gc.get()) with
              Gc.minor_heap_size = 524288; (* 512k *)
              Gc.major_heap_increment = 4194304 (* 4M *)
         };
  Printexc.record_backtrace true;
  Frontend.init ();
  parse_cmdline cmdline_actions;
  if !option_o <> None && !num_input_files >= 2 then
    fatal_error no_loc "Ambiguous '-o' option (multiple source files)";
  if !num_input_files = 0 then
    fatal_error no_loc "no input file";
  perform_actions ()
      with
  | Sys_error msg
  | CmdError msg -> error no_loc "%s" msg; exit 2
  | Abort -> exit 2
  | e -> crash e

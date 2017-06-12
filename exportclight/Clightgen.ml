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
open Driveraux
open Frontend

(* Location of the compatibility library *)

let stdlib_path = ref Configuration.stdlib_path

(* clightgen-specific options *)

let option_normalize = ref false

(* From CompCert C AST to Clight *)

let compile_c_ast sourcename csyntax ofile =
  let clight =
    match SimplExpr.transl_program csyntax with
    | Errors.OK p ->
        begin match SimplLocals.transf_program p with
        | Errors.OK p' ->
            if !option_normalize
            then Clightnorm.norm_program p'
            else p'
        | Errors.Error msg ->
            print_error stderr msg;
            exit 2
        end
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in
  (* Dump Clight in C syntax if requested *)
  if !option_dclight then begin
    let ofile = Filename.chop_suffix sourcename ".c" ^ ".light.c" in
    let oc = open_out ofile in
    PrintClight.print_program (Format.formatter_of_out_channel oc) clight;
    close_out oc
  end;
  (* Print Clight in Coq syntax *)
  let oc = open_out ofile in
  ExportClight.print_program (Format.formatter_of_out_channel oc) clight;
  close_out oc

(* From C source to Clight *)

let compile_c_file sourcename ifile ofile =
  compile_c_ast sourcename (parse_c_file sourcename ifile) ofile

(* Processing of a .c file *)

let process_c_file sourcename =
  let prefixname = Filename.chop_suffix sourcename ".c" in
  if !option_E then begin
    preprocess sourcename "-"
  end else begin
    let preproname = Filename.temp_file "compcert" ".i" in
    preprocess sourcename preproname;
    compile_c_file sourcename preproname (prefixname ^ ".v")
  end

let version_string =
  if Version.buildnr <> "" && Version.tag <> "" then
    sprintf "The CompCert Clight generator, %s, Build: %s, Tag: %s\n" Version.version Version.buildnr Version.tag
  else
    "The CompCert Clight generator, version "^ Version.version ^ "\n"

let usage_string =
  version_string ^
"Usage: clightgen [options] <source files>\n\
Recognized source files:\n\
\  .c             C source file\n\
Processing options:\n\
\  -normalize     Normalize the generated Clight code w.r.t. loads in expressions\n\
\  -E             Preprocess only, send result to standard output\n"^
prepro_help ^
"Language support options (use -fno-<opt> to turn off -f<opt>) :\n\
\  -fbitfields    Emulate bit fields in structs [off]\n\
\  -flongdouble   Treat 'long double' as 'double' [off]\n\
\  -fstruct-passing  Support passing structs and unions by value as function\n\
\                    results or function arguments [off]\n\
\  -fstruct-return   Like -fstruct-passing (deprecated)\n\
\  -fvararg-calls Emulate calls to variable-argument functions [on]\n\
\  -fpacked-structs  Emulate packed structs [off]\n\
\  -fall          Activate all language support options above\n\
\  -fnone         Turn off all language support options above\n\
Tracing options:\n\
\  -dparse        Save C file after parsing and elaboration in <file>.parsed.c\n\
\  -dc            Save generated Compcert C in <file>.compcert.c\n\
\  -dclight       Save generated Clight in <file>.light.c\n\
General options:\n\
\  -v             Print external commands before invoking them\n"

let print_usage_and_exit () =
  printf "%s" usage_string; exit 0

let print_version_and_exit () =
  printf "%s" version_string; exit 0

let language_support_options = [
  option_fbitfields; option_flongdouble;
  option_fstruct_passing; option_fvararg_calls; option_funprototyped;
  option_fpacked_structs; option_finline_asm
]

let set_all opts () = List.iter (fun r -> r := true) opts
let unset_all opts () = List.iter (fun r -> r := false) opts

let cmdline_actions =
  let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref] in
  [
(* Getting help *)
  Exact "-help", Unit print_usage_and_exit;
  Exact "--help", Unit print_usage_and_exit;
(* Getting version info *)
  Exact "-version", Unit print_version_and_exit;
  Exact "--version", Unit print_version_and_exit;
(* Processing options *)
  Exact "-E", Set option_E;
  Exact "-normalize", Set option_normalize]
(* Preprocessing options *)
  @ prepro_actions @
(* Language support options -- more below *)
  [Exact "-fall", Unit (set_all language_support_options);
  Exact "-fnone", Unit (unset_all language_support_options);
(* Tracing options *)
  Exact "-dparse", Set option_dparse;
  Exact "-dc", Set option_dcmedium;
  Exact "-dclight", Set option_dclight;
(* General options *)
  Exact "-v", Set option_v;
  Exact "-stdlib", String(fun s -> stdlib_path := s);
  ]
(* -f options: come in -f and -fno- variants *)
(* Language support options *)
  @ f_opt "longdouble" option_flongdouble
  @ f_opt "struct-return" option_fstruct_passing
  @ f_opt "struct-passing" option_fstruct_passing
  @ f_opt "bitfields" option_fbitfields
  @ f_opt "vararg-calls" option_fvararg_calls
  @ f_opt "unprototyped" option_funprototyped
  @ f_opt "packed-structs" option_fpacked_structs
  @ f_opt "inline-asm" option_finline_asm
  @ [
(* Catch options that are not handled *)
  Prefix "-", Self (fun s ->
      eprintf "Unknown option `%s'\n" s; exit 2);
(* File arguments *)
  Suffix ".c", Self (fun s -> process_c_file s);
  ]

let _ =
  Gc.set { (Gc.get()) with
              Gc.minor_heap_size = 524288; (* 512k *)
              Gc.major_heap_increment = 4194304 (* 4M *)
         };
  Printexc.record_backtrace true;
  Machine.config :=
    begin match Configuration.arch with
    | "powerpc" -> Machine.ppc_32_bigendian
    | "arm"     -> if Configuration.is_big_endian
                   then Machine.arm_bigendian
                   else Machine.arm_littleendian
    | "x86"     -> if Configuration.model = "64" then
                     Machine.x86_64
                   else
                     if Configuration.abi = "macosx"
                     then Machine.x86_32_macosx
                     else Machine.x86_32
    | _         -> assert false
    end;
  Builtins.set C2C.builtins;
  CPragmas.initialize();
  parse_cmdline cmdline_actions

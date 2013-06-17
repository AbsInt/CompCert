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
open Clflags

(* Location of the compatibility library *)

let stdlib_path = ref(
  try
    Sys.getenv "COMPCERT_LIBRARY"
  with Not_found ->
    Configuration.stdlib_path)

let command cmd =
  if !option_v then begin
    prerr_string "+ "; prerr_string cmd; prerr_endline ""
  end;
  Sys.command cmd

let quote_options opts =
  String.concat " " (List.rev_map Filename.quote opts)

let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()

(* Printing of error messages *)

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (Camlcoq.P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

(* From C to preprocessed C *)

let preprocess ifile ofile =
  let output =
    if ofile = "-" then "" else sprintf "> %s" ofile in
  let cmd =
    sprintf "%s -D__COMPCERT__ %s %s %s %s"
      Configuration.prepro
      (if Configuration.has_runtime_lib
       then sprintf "-I%s" !stdlib_path
       else "")
      (quote_options !prepro_options)
      ifile output in
  if command cmd <> 0 then begin
    if ofile <> "-" then safe_remove ofile;
    eprintf "Error during preprocessing.\n";
    exit 2
  end

(* From preprocessed C to Csyntax *)

let parse_c_file sourcename ifile =
  Sections.initialize();
  (* Simplification options *)
  let simplifs =
    "b" (* blocks: mandatory *)
  ^ (if !option_fstruct_return then "s" else "")
  ^ (if !option_fbitfields then "f" else "")
  ^ (if !option_fpacked_structs then "p" else "")
  in
  (* Parsing and production of a simplified C AST *)
  let ast =
    match Parse.preprocessed_file simplifs sourcename ifile with
    | None -> exit 2
    | Some p -> p in
  (* Remove preprocessed file (always a temp file) *)
  safe_remove ifile;
  (* Save C AST if requested *)
  if !option_dparse then begin
    let ofile = Filename.chop_suffix sourcename ".c" ^ ".parsed.c" in
    let oc = open_out ofile in
    Cprint.program (Format.formatter_of_out_channel oc) ast;
    close_out oc
  end;
  (* Conversion to Csyntax *)
  let csyntax =
    match C2C.convertProgram ast with
    | None -> exit 2
    | Some p -> p in
  flush stderr;
  (* Save CompCert C AST if requested *)
  if !option_dcmedium then begin
    let ofile = Filename.chop_suffix sourcename ".c" ^ ".compcert.c" in
    let oc = open_out ofile in
    PrintCsyntax.print_program (Format.formatter_of_out_channel oc) csyntax;
    close_out oc
  end;
  csyntax

(* From CompCert C AST to Clight *)

let compile_c_ast sourcename csyntax ofile =
  let clight =
    match SimplExpr.transl_program csyntax with
    | Errors.OK p ->
        begin match SimplLocals.transf_program p with
        | Errors.OK p' -> p'
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

(* Command-line parsing *)

let explode_comma_option s =
  match Str.split (Str.regexp ",") s with
  | [] -> assert false
  | hd :: tl -> tl

type action =
  | Set of bool ref
  | Unset of bool ref
  | Self of (string -> unit)
  | String of (string -> unit)
  | Integer of (int -> unit)

let rec find_action s = function
  | [] -> None
  | (re, act) :: rem ->
      if Str.string_match re s 0 then Some act else find_action s rem

let parse_cmdline spec usage =
  let acts = List.map (fun (pat, act) -> (Str.regexp pat, act)) spec in
  let error () =
    eprintf "%s" usage;
    exit 2 in
  let rec parse i =
    if i < Array.length Sys.argv then begin
      let s = Sys.argv.(i) in
      match find_action s acts with
      | None ->
          if s <> "-help" && s <> "--help" 
          then eprintf "Unknown argument `%s'\n" s;
          error ()
      | Some(Set r) ->
          r := true; parse (i+1)
      | Some(Unset r) ->
          r := false; parse (i+1)
      | Some(Self fn) ->
          fn s; parse (i+1)
      | Some(String fn) ->
          if i + 1 < Array.length Sys.argv then begin
            fn Sys.argv.(i+1); parse (i+2)
          end else begin
            eprintf "Option `%s' expects an argument\n" s; error()
          end
      | Some(Integer fn) ->
          if i + 1 < Array.length Sys.argv then begin
            let n =
              try
                int_of_string Sys.argv.(i+1)
              with Failure _ ->
                eprintf "Argument to option `%s' must be an integer\n" s;
                error()
            in
            fn n; parse (i+2)
          end else begin
            eprintf "Option `%s' expects an argument\n" s; error()
          end
    end
  in parse 1

let usage_string =
"The CompCert Clight generator
Usage: clightgen [options] <source files>
Recognized source files:
  .c             C source file
Processing options:
  -E             Preprocess only, send result to standard output
Preprocessing options:
  -I<dir>        Add <dir> to search path for #include files
  -D<symb>=<val> Define preprocessor symbol
  -U<symb>       Undefine preprocessor symbol
  -Wp,<opt>      Pass option <opt> to the preprocessor
Language support options (use -fno-<opt> to turn off -f<opt>) :
  -fbitfields    Emulate bit fields in structs [off]
  -flongdouble   Treat 'long double' as 'double' [off]
  -fstruct-return  Emulate returning structs and unions by value [off]
  -fvararg-calls Emulate calls to variable-argument functions [on]
  -fpacked-structs  Emulate packed structs [off]
  -fall          Activate all language support options above
  -fnone         Turn off all language support options above
Tracing options:
  -dparse        Save C file after parsing and elaboration in <file>.parse.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
General options:
  -v             Print external commands before invoking them
"

let language_support_options = [
  option_fbitfields; option_flongdouble;
  option_fstruct_return; option_fvararg_calls; option_fpacked_structs
]

let cmdline_actions =
  let f_opt name ref =
    ["-f" ^ name ^ "$", Set ref; "-fno-" ^ name ^ "$", Unset ref] in
  [
  "-I$", String(fun s -> prepro_options := s :: "-I" :: !prepro_options);
  "-D$", String(fun s -> prepro_options := s :: "-D" :: !prepro_options);
  "-U$", String(fun s -> prepro_options := s :: "-U" :: !prepro_options);
  "-[IDU].", Self(fun s -> prepro_options := s :: !prepro_options);
  "-dparse$", Set option_dparse;
  "-dc$", Set option_dcmedium;
  "-dclight$", Set option_dclight;
  "-E$", Set option_E;
  ".*\\.c$", Self (fun s -> process_c_file s);
  "-Wp,", Self (fun s ->
      prepro_options := List.rev_append (explode_comma_option s) !prepro_options);
  "-fall$", Self (fun _ ->
              List.iter (fun r -> r := true) language_support_options);
  "-fnone$", Self (fun _ ->
              List.iter (fun r -> r := false) language_support_options);
  ]
  @ f_opt "longdouble" option_flongdouble
  @ f_opt "struct-return" option_fstruct_return
  @ f_opt "bitfields" option_fbitfields
  @ f_opt "vararg-calls" option_fvararg_calls
  @ f_opt "packed-structs" option_fpacked_structs

let _ =
  Gc.set { (Gc.get()) with Gc.minor_heap_size = 524288 };
  Machine.config :=
    begin match Configuration.arch with
    | "powerpc" -> Machine.ppc_32_bigendian
    | "arm"     -> Machine.arm_littleendian
    | "ia32"    -> Machine.x86_32
    | _         -> assert false
    end;
  Builtins.set C2C.builtins_generic;
  CPragmas.initialize();
  parse_cmdline cmdline_actions usage_string

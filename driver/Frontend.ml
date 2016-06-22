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

open Clflags
open Commandline
open Driveraux
open Printf

(* Common frontend functions between clightgen and ccomp *)


(* From C to preprocessed C *)

let preprocess ifile ofile =
  let output =
    if ofile = "-" then None else Some ofile in
  let cmd = List.concat [
    Configuration.prepro;
    ["-D__COMPCERT__"];
    (if !Clflags.use_standard_headers
     then ["-I" ^ Filename.concat !Clflags.stdlib_path "include" ]
     else []);
    List.rev !prepro_options;
    [ifile]
  ] in
  let exc = command ?stdout:output cmd in
  if exc <> 0 then begin
    if ofile <> "-" then safe_remove ofile;
    command_error "preprocessor" exc;
    eprintf "Error during preprocessing.\n";
    exit 2
  end

(* From preprocessed C to Csyntax *)

let parse_c_file sourcename ifile =
  Debug.init_compile_unit sourcename;
  Sections.initialize();
  (* Simplification options *)
  let simplifs =
    "b" (* blocks: mandatory *)
  ^ (if !option_fstruct_passing then "s" else "")
  ^ (if !option_fbitfields then "f" else "")
  ^ (if !option_fpacked_structs then "p" else "")
  in
  (* Parsing and production of a simplified C AST *)
  let ast =
    match Parse.preprocessed_file simplifs sourcename ifile with
    | None -> exit 2
    | Some p -> p in
  (* Save C AST if requested *)
  if !option_dparse then begin
    let ofile = output_filename sourcename ".c" ".parsed.c" in
    let oc = open_out ofile in
    Cprint.program (Format.formatter_of_out_channel oc) ast;
    close_out oc
  end;
  (* Conversion to Csyntax *)
  let csyntax =
    match Timing.time "CompCert C generation" C2C.convertProgram ast with
    | None -> exit 2
    | Some p -> p in
  flush stderr;
  (* Save CompCert C AST if requested *)
  if !option_dcmedium then begin
    let ofile = output_filename sourcename ".c" ".compcert.c" in
    let oc = open_out ofile in
    PrintCsyntax.print_program (Format.formatter_of_out_channel oc) csyntax;
    close_out oc
  end;
  csyntax

(* Add gnu preprocessor list *)
let gnu_prepro_opt_key key s =
  if gnu_option s then
    prepro_options := s::key::!prepro_options

(* Add gnu preprocessor option *)
let gnu_prepro_opt s =
 if gnu_option s then
    prepro_options := s::!prepro_options

(* Add gnu preprocessor option s and the implict -E *)
let gnu_prepro_opt_e s =
  if gnu_option s then begin
    prepro_options := s :: !prepro_options;
    option_E := true
  end

let prepro_actions = [
  (* Preprocessing options *)
  Exact "-I", String(fun s -> prepro_options := s :: "-I" :: !prepro_options;
    assembler_options := s :: "-I" :: !assembler_options);
  Prefix "-I", Self(fun s -> prepro_options := s :: !prepro_options;
    assembler_options := s :: !assembler_options);
  Exact "-D", String(fun s -> prepro_options := s :: "-D" :: !prepro_options);
  Prefix "-D", Self(fun s -> prepro_options := s :: !prepro_options);
  Exact "-U", String(fun s -> prepro_options := s :: "-U" :: !prepro_options);
  Prefix "-U", Self(fun s -> prepro_options := s :: !prepro_options);
  Prefix "-Wp,", Self (fun s ->
    prepro_options := List.rev_append (explode_comma_option s) !prepro_options);
  Exact "-Xpreprocessor", String (fun s ->
    prepro_options := s :: !prepro_options);
  Exact "-include", String (fun s -> prepro_options := s :: "-include" :: !prepro_options);
  Exact "-M", Self gnu_prepro_opt_e;
  Exact "-MM", Self gnu_prepro_opt_e;
  Exact "-MF", String (gnu_prepro_opt_key "-MF");
  Exact "-MG", Self gnu_prepro_opt;
  Exact "-MP", Self gnu_prepro_opt;
  Exact "-MT", String (gnu_prepro_opt_key "-MT");
  Exact "-MQ", String (gnu_prepro_opt_key "-MQ");
  Exact "-nostdinc", Self (fun s -> gnu_prepro_opt s; use_standard_headers := false);
  Exact "-imacros", String (gnu_prepro_opt_key "-imacros");
  Exact "-idirafter", String (gnu_prepro_opt_key "-idirafter");
  Exact "-isystem", String (gnu_prepro_opt_key "-isystem");
  Exact "-iquote", String (gnu_prepro_opt_key "-iquore");
  Exact "-P", Self gnu_prepro_opt;
  Exact "-C", Self gnu_prepro_opt;
  Exact "-CC", Self gnu_prepro_opt;]

let prepro_help = "Preprocessing options:\n\
\  -I<dir>        Add <dir> to search path for #include files\n\
\  -include <file> Process <file> as if #include \"<file>\" appears at the first\n\
\                  line of the primary source file.\n\
\  -D<symb>=<val> Define preprocessor symbol\n\
\  -U<symb>       Undefine preprocessor symbol\n\
\  -Wp,<opt>      Pass option <opt> to the preprocessor\n\
\  -Xpreprocessor <opt> Pass option <opt> to the preprocessor\n\
\  -M             (GCC only) Ouput a rule suitable for make describing the\n\
\                 dependencies of the main source file\n\
\  -MM            (GCC only) Like -M but do not mention system header files\n\
\  -MF <file>     (GCC only) Specifies file <file> as output file for -M or -MM\n\
\  -MG            (GCC only) Assumes missing header files are generated for -M\n\
\  -MP            (GCC only) Add a phony target for each dependency other than\n\
\                 the main file\n\
\  -MT <target>   (GCC only) Change the target of the rule emitted by dependency\n\
\                 generation\n\
\  -MQ <target>   (GCC only) Like -MT but quotes <target>\n\
\  -nostdinc      (GCC only) Do not search the standard system directories for\n\
\                 header files\n\
\  -imacros <file> (GCC only) Like -include but throws output produced by\n\
\                  preprocessing of <file> away\n\
\  -idirafter <dir> (GCC only) Search <dir> for header files after all directories\n\
\                   specified with -I and the standard system directories\n\
\  -isystem <dir>  (GCC only) Search <dir> for header files after all directories\n\
\
\                  specified by -I but before the standard system directories\n\
\  -iquote <dir>   (GCC only) Like -isystem but only for headers included with\n\
\                   quotes\n\
\  -P              (GCC only) Do not generate linemarkers\n\
\  -C              (GCC only) Do not discard comments\n\
\  -CC             (GCC only) Do not discard comments, including during macro\n\
\                  expansion\n"

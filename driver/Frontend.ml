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

(* Common frontend functions between clightgen and ccomp *)

let predefined_macros =
  [
    "-D__COMPCERT__";
    "-U__STDC_IEC_559_COMPLEX__";
    "-D__STDC_NO_ATOMICS__";
    "-D__STDC_NO_COMPLEX__";
    "-D__STDC_NO_THREADS__";
    "-D__STDC_NO_VLA__"
  ]

(* From C to preprocessed C *)

let preprocess ifile ofile =
  Diagnostics.raise_on_errors ();
  let output =
    if ofile = "-" then None else Some ofile in
  let cmd = List.concat [
    Configuration.prepro;
    predefined_macros;
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
  let ast = Parse.preprocessed_file simplifs sourcename ifile in
  (* Save C AST if requested *)
  Cprint.print_if ast;
  (* Conversion to Csyntax *)
  let csyntax = Timing.time "CompCert C generation" C2C.convertProgram ast in
  (* Save CompCert C AST if requested *)
  PrintCsyntax.print_if csyntax;
  csyntax

let init () =
  Machine.config:=
    begin match Configuration.arch with
    | "powerpc" -> if Configuration.model = "e5500" || Configuration.model = "ppc64"
                   then if Configuration.abi = "linux" then Machine.ppc_32_r64_linux_bigendian
                   else if Configuration.gnu_toolchain then Machine.ppc_32_r64_bigendian
                   else Machine.ppc_32_r64_diab_bigendian
                   else if Configuration.abi = "linux" then Machine.ppc_32_linux_bigendian
                   else if Configuration.gnu_toolchain then Machine.ppc_32_bigendian
                   else Machine.ppc_32_diab_bigendian
    | "arm"     -> if Configuration.is_big_endian
                   then Machine.arm_bigendian
                   else Machine.arm_littleendian
    | "x86"     -> if Configuration.model = "64" then
                     Machine.x86_64
                   else
                     if Configuration.abi = "macosx"
                     then Machine.x86_32_macosx
                     else if Configuration.system = "bsd"
                     then Machine.x86_32_bsd
                     else Machine.x86_32
    | "riscV"   -> if Configuration.model = "64"
                   then Machine.rv64
                   else Machine.rv32
    | _         -> assert false
  end;
  Builtins.set C2C.builtins;
  Cutil.declare_attributes C2C.attributes;
  CPragmas.initialize()


(* Add gnu preprocessor list *)
let gnu_prepro_opt_key key s =
  prepro_options := s::key::!prepro_options

(* Add gnu preprocessor option *)
let gnu_prepro_opt s =
  prepro_options := s::!prepro_options

(* Add gnu preprocessor option s and the implict -E *)
let gnu_prepro_opt_e s =
  prepro_options := s :: !prepro_options;
  option_E := true

let gnu_prepro_actions = [
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
  Exact "-iquote", String (gnu_prepro_opt_key "-iquote");
  Exact "-P", Self gnu_prepro_opt;
  Exact "-C", Self gnu_prepro_opt;
  Exact "-CC", Self gnu_prepro_opt;]

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
  Exact "-include", String (fun s -> prepro_options := s :: "-include" :: !prepro_options);]
  @ (if Configuration.gnu_toolchain then gnu_prepro_actions else [])

let gnu_prepro_help =
{|  -M            Ouput a rule suitable for make describing the
                 dependencies of the main source file
  -MM            Like -M but do not mention system header files
  -MF <file>     Specifies file <file> as output file for -M or -MM
  -MG            Assumes missing header files are generated for -M
  -MP            Add a phony target for each dependency other than
                 the main file
  -MT <target>   Change the target of the rule emitted by dependency
                 generation
  -MQ <target>   Like -MT but quotes <target>
  -nostdinc      Do not search the standard system directories for
                 header files
  -imacros <file> Like -include but throws output produced by
                  preprocessing of <file> away
  -idirafter <dir> Search <dir> for header files after all directories
                   specified with -I and the standard system directories
  -isystem <dir>  Search <dir> for header files after all directories
                  specified by -I but before the standard system directories
  -iquote <dir>   Like -isystem but only for headers included with
                  quotes
  -P              Do not generate linemarkers
  -C              Do not discard comments
  -CC             Do not discard comments, including during macro
                  expansion
|}

let prepro_help = {|Preprocessing options:
  -I<dir>        Add <dir> to search path for #include files
  -include <file> Process <file> as if #include "<file>" appears at the first
                  line of the primary source file.
  -D<symb>=<val> Define preprocessor symbol
  -U<symb>       Undefine preprocessor symbol
  -Wp,<opt>      Pass option <opt> to the preprocessor
  -Xpreprocessor <opt> Pass option <opt> to the preprocessor
|}
  ^ (if Configuration.gnu_toolchain then gnu_prepro_help else "")

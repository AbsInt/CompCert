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

open Printf
open Commandline
open Clflags
open Timing
open Driveraux
open File
open Frontend
open Assembler
open Linker

let dump_options = ref false

(* Optional sdump suffix *)
let sdump_suffix = ref ".json"
let sdump_folder = ref ""

(* Dump Asm code in asm format for the validator *)

let jdump_magic_number = "CompCertJDUMP" ^ Version.version

let dump_jasm asm source_file =
  if !option_sdump then begin
    let sf = output_filename source_file !sdump_suffix in
    let destfile = Filename.concat !sdump_folder sf in
    let oc = open_out_bin destfile in
    fprintf oc "{\n\"Version\":\"%s\",\n\"System\":\"%s\"\n,\"Compilation Unit\":\"%s\",\n\"Asm Ast\":%a}"
      jdump_magic_number Configuration.system (File.input_name source_file) AsmToJSON.p_program asm;
    close_out oc
  end

let print_options source_file =
  if !dump_options then begin
    let oc = open_out_bin (output_filename source_file ".opt.json") in
    Optionsprinter.print oc !stdlib_path;
    close_out oc;
  end

(* From C source to asm *)

let compile_c_file  ifile (ic,prepro) =
  (* Prepare to dump Clight, RTL, etc, if requested *)
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename ifile ext)
      else None in
  set_dest dparse_destination option_dparse ".parsed.c";
  set_dest dcompcertc_destination option_dcmedium ".compcert.c";
  set_dest PrintClight.destination option_dclight ".light.c";
  set_dest PrintCminor.destination option_dcminor ".cm";
  set_dest PrintRTL.destination option_drtl ".rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dltl ".ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  let csyntax = parse_c_file (File.input_name ifile) (ic,prepro) in
  (* Convert to Asm *)
  match Compiler.apply_partial
          (Compiler.transf_c_program csyntax)
          Asmexpand.expand_program with
  | Errors.OK asm ->
    asm
  | Errors.Error msg ->
    print_errorcodes (File.input_name ifile) msg

let assemble_ast ?(sdump =true) asm source_file =
  if !option_S then begin
    let oc = open_out_bin (File.output_filename ~final:true source_file ".s") in
    PrintAsm.print_program oc asm;
    ""
  end else begin
    if sdump then dump_jasm asm source_file;
    let oc,handle = Assembler.open_assembler_out source_file in
    PrintAsm.print_program oc asm;
    let objname = Assembler.close_assembler_out oc handle in
    print_options source_file;
    objname
  end

(* From Cminor to asm *)

let compile_cminor_file ifile =
  (* Prepare to dump RTL, Mach, etc, if requested *)
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename ifile ext)
      else None in
  set_dest PrintRTL.destination option_drtl ".rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dltl ".ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  Sections.initialize();
  let ic = File.open_input_file ifile in
  let lb = Lexing.from_channel ic in
  (* Parse cminor *)
  let cm =
    try CMtypecheck.type_program (CMparser.prog CMlexer.token lb)
    with Parsing.Parse_error ->
           eprintf "File %s, character %d: Syntax error\n"
                   (File.input_name ifile) (Lexing.lexeme_start lb);
           exit 2
       | CMlexer.Error msg ->
           eprintf "File %s, character %d: %s\n"
                   (File.input_name ifile) (Lexing.lexeme_start lb) msg;
           exit 2
       | CMtypecheck.Error msg ->
           eprintf "File %s, type-checking error:\n%s"
                   (File.input_name ifile) msg;
           exit 2 in
  (* Convert to Asm *)
  match Compiler.apply_partial
          (Compiler.transf_cminor_program cm)
          Asmexpand.expand_program with
  | Errors.OK asm ->
    asm
  | Errors.Error msg -> print_errorcodes (File.input_name ifile) msg

(* From preprocessed c to object file or interpreter *)
let compile_prepro_file source_file (ic,prepro)=
  if !option_interp then begin
    Machine.config := Machine.compcert_interpreter !Machine.config;
    let csyntax = parse_c_file (File.input_name source_file) (ic,prepro) in
    Interp.execute csyntax;
    ""
  end else begin
    let asm = compile_c_file source_file (ic,prepro) in
    assemble_ast asm source_file
 end

(* Processing of a .c file *)

let process_c_file source_file =
  if !option_E then begin
    preprocess source_file (File.output_filename_default "-");
    ""
  end else begin
    let ic,prepro = open_prepro_in source_file in
    compile_prepro_file source_file (ic,prepro)
  end

(* Processing of a .i / .p file (preprocessed C) *)

let process_i_file source_file =
  compile_prepro_file source_file (open_preprocessed_file source_file)

(* Processing of a .cm file *)

let process_cminor_file source_file =
  let asm = compile_cminor_file source_file in
  assemble_ast ~sdump:false asm source_file

(* Processing of .S and .s files *)
let assemble_file source_file asm_file =
  if !option_S then
    ""
  else
    let objname = File.output_filename  ~final:!option_c source_file ".o"  in
    assemble asm_file objname;
    print_options source_file;
    objname

let process_s_file source_file =
  assemble_file source_file (File.input_name source_file)

let process_S_file source_file =
  if !option_E then begin
    preprocess source_file (File.output_filename_default "-");
    ""
  end else begin
    let asm_file = File.temp_file ".s" in
    preprocess source_file asm_file;
    assemble_file source_file  asm_file
  end

(* Processing of .h files *)

let process_h_file source_file =
  if !option_E then begin
    preprocess source_file (File.output_filename_default "-");
    ""
  end else begin
    eprintf "Error: input file %s ignored (not in -E mode)\n" (File.input_name source_file);
    exit 2
  end

let version_string =
  if Version.buildnr <> "" && Version.tag <> "" then
    sprintf "The CompCert C verified compiler, %s, Build: %s, Tag: %s\n" Version.version Version.buildnr Version.tag
  else
    "The CompCert C verified compiler, version "^ Version.version ^ "\n"

let target_help = if Configuration.arch = "arm" then
"Target processor options:\n\
\  -mthumb        Use Thumb2 instruction encoding\n\
\  -marm          Use classic ARM instruction encoding\n"
else
  ""

let usage_string =
  version_string ^
  "Usage: ccomp [options] <source files>\n\
Recognized source files:\n\
\  .c             C source file\n\
\  .i or .p       C source file that should not be preprocessed\n\
\  .cm            Cminor source file\n\
\  .s             Assembly file\n\
\  .S             Assembly file that must be preprocessed\n\
\  .o             Object file\n\
\  .a             Library file\n\
Processing options:\n\
\  -c             Compile to object file only (no linking), result in <file>.o\n\
\  -E             Preprocess only, send result to standard output\n\
\  -S             Compile to assembler only, save result in <file>.s\n\
\  -o <file>      Generate output in <file>\n" ^
  prepro_help ^
"Language support options (use -fno-<opt> to turn off -f<opt>) :\n\
\  -fbitfields    Emulate bit fields in structs [off]\n\
\  -flongdouble   Treat 'long double' as 'double' [off]\n\
\  -fstruct-passing  Support passing structs and unions by value as function\n\
\                    results or function arguments [off]\n\
\  -fstruct-return   Like -fstruct-passing (deprecated)\n\
\  -fvararg-calls Support calls to variable-argument functions [on]\n\
\  -funprototyped Support calls to old-style functions without prototypes [on]\n\
\  -fpacked-structs  Emulate packed structs [off]\n\
\  -finline-asm   Support inline 'asm' statements [off]\n\
\  -fall          Activate all language support options above\n\
\  -fnone         Turn off all language support options above\n" ^
 DebugInit.debugging_help ^
"Optimization options: (use -fno-<opt> to turn off -f<opt>)\n\
\  -O             Optimize the compiled code [on by default]\n\
\  -O0            Do not optimize the compiled code\n\
\  -O1 -O2 -O3    Synonymous for -O\n\
\  -Os            Optimize for code size in preference to code speed\n\
\  -ftailcalls    Optimize function calls in tail position [on]\n\
\  -fconst-prop   Perform global constant propagation  [on]\n\
\  -ffloat-const-prop <n>  Control constant propagation of floats\n\
\                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)\n\
\  -fcse          Perform common subexpression elimination [on]\n\
\  -fredundancy   Perform redundancy elimination [on]\n\
Code generation options: (use -fno-<opt> to turn off -f<opt>)\n\
\  -ffpu          Use FP registers for some integer operations [on]\n\
\  -fsmall-data <n>  Set maximal size <n> for allocation in small data area\n\
\  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area\n\
\  -falign-functions <n>  Set alignment (in bytes) of function entry points\n\
\  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets\n\
\  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches\n" ^
 target_help ^
 assembler_help ^
 linker_help ^
"Tracing options:\n\
\  -dprepro       Save C file after preprocessing in <file>.i\n\
\  -dparse        Save C file after parsing and elaboration in <file>.parsed.c\n\
\  -dc            Save generated Compcert C in <file>.compcert.c\n\
\  -dclight       Save generated Clight in <file>.light.c\n\
\  -dcminor       Save generated Cminor in <file>.cm\n\
\  -drtl          Save RTL at various optimization points in <file>.rtl.<n>\n\
\  -dltl          Save LTL after register allocation in <file>.ltl\n\
\  -dmach         Save generated Mach code in <file>.mach\n\
\  -dasm          Save generated assembly in <file>.s\n\
\  -dall          Save all generated intermediate files in <file>.<ext>\n\
\  -sdump         Save info for post-linking validation in <file>.json\n\
\  -doptions      Save the compiler configurations in <file>.opt.json\n\
General options:\n\
\  -stdlib <dir>  Set the path of the Compcert run-time library\n\
\  -v             Print external commands before invoking them\n\
\  -timings       Show the time spent in various compiler passes\n\
\  -version       Print the version string and exit\n\
\  -target <value> Generate code for the given target\n\
\  -conf <file>   Read configuration from file\n\
\  -pipe          Use pipes between commands, when possible\n\
\  @<file>        Read command line options from <file>\n" ^
  Cerrors.warning_help ^
"Interpreter mode:\n\
\  -interp        Execute given .c files using the reference interpreter\n\
\  -quiet         Suppress diagnostic messages for the interpreter\n\
\  -trace         Have the interpreter produce a detailed trace of reductions\n\
\  -random        Randomize execution order\n\
\  -all           Simulate all possible execution orders\n"

let print_usage_and_exit () =
  printf "%s" usage_string; exit 0

let print_version_and_exit () =
  printf "%s" version_string; exit 0

let enforce_buildnr nr =
  let build = int_of_string Version.buildnr in
  if nr != build then begin
    eprintf "Mismatching builds: This is CompCert build %d, but QSK requires build %d.\n\
Please use matching builds of QSK and CompCert.\n" build nr; exit 2
  end

let language_support_options = [
  option_fbitfields; option_flongdouble;
  option_fstruct_passing; option_fvararg_calls; option_funprototyped;
  option_fpacked_structs; option_finline_asm
]

let optimization_options = [
  option_ftailcalls; option_fconstprop; option_fcse; option_fredundancy
]

let set_all opts () = List.iter (fun r -> r := true) opts
let unset_all opts () = List.iter (fun r -> r := false) opts

let num_source_files = ref 0

let num_input_files = ref 0

let cmdline_actions =
  let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref] in
  [
(* Getting help *)
  Exact "-help", Unit print_usage_and_exit;
  Exact "--help", Unit print_usage_and_exit;
(* Getting version info *)
  Exact "-version", Unit print_version_and_exit;
  Exact "--version", Unit print_version_and_exit;] @
(* Enforcing CompCert build numbers for QSKs *)
  (if Version.buildnr <> "" then
    [ Exact "-qsk-enforce-build", Integer enforce_buildnr;
      Exact "--qsk-enforce-build", Integer enforce_buildnr; ]
   else []) @
(* Processing options *)
 [ Exact "-c", Set option_c;
  Exact "-E", Set option_E;
  Exact "-S", Set option_S;
  Exact "-o", String(fun s -> option_o := Some s);
  Prefix "-o", Self (fun s -> let s = String.sub s 2 ((String.length s) - 2) in
                              option_o := Some s);]
  (* Preprocessing options *)
    @ prepro_actions @
(* Language support options -- more below *)
 [ Exact "-fall", Unit (set_all language_support_options);
  Exact "-fnone", Unit (unset_all language_support_options);]
   (* Debugging options *)
    @ DebugInit.debugging_actions @
(* Code generation options -- more below *)
 [
  Exact "-O0", Unit (unset_all optimization_options);
  Exact "-O", Unit (set_all optimization_options);
  _Regexp "-O[123]$", Unit (set_all optimization_options);
  Exact "-Os", Set option_Osize;
  Exact "-fsmall-data", Integer(fun n -> option_small_data := n);
  Exact "-fsmall-const", Integer(fun n -> option_small_const := n);
  Exact "-ffloat-const-prop", Integer(fun n -> option_ffloatconstprop := n);
  Exact "-falign-functions", Integer(fun n -> option_falignfunctions := Some n);
  Exact "-falign-branch-targets", Integer(fun n -> option_falignbranchtargets := n);
  Exact "-falign-cond-branches", Integer(fun n -> option_faligncondbranchs := n);
(* Target processor options *)
  Exact "-conf", Ignore; (* Ignore option since it is already handled *)
  Exact "-target", Ignore;] @ (* Ignore option since it is already handled *)
  (if Configuration.arch = "arm" then
    [ Exact "-mthumb", Set option_mthumb;
      Exact "-marm", Unset option_mthumb; ]
  else []) @
(* Assembling options *)
  assembler_actions @
(* Linking options *)
  linker_actions @
(* Tracing options *)
 [ Exact "-dprepro", Set option_dprepro;
  Exact "-dparse", Set option_dparse;
  Exact "-dc", Set option_dcmedium;
  Exact "-dclight", Set option_dclight;
  Exact "-dcminor", Set option_dcminor;
  Exact "-drtl", Set option_drtl;
  Exact "-dltl", Set option_dltl;
  Exact "-dalloctrace", Set option_dalloctrace;
  Exact "-dmach", Set option_dmach;
  Exact "-dasm", Set option_dasm;
  Exact "-dall", Self (fun _ ->
    option_dprepro := true;
    option_dparse := true;
    option_dcmedium := true;
    option_dclight := true;
    option_dcminor := true;
    option_drtl := true;
    option_dalloctrace := true;
    option_dmach := true;
    option_dasm := true;
    dump_options:=true);
  Exact "-sdump", Set option_sdump;
  Exact "-sdump-suffix", String (fun s -> option_sdump := true; sdump_suffix:= s);
  Exact "-sdump-folder", String (fun s -> sdump_folder := s);
  Exact "-doptions", Set dump_options;
(* General options *)
  Exact "-v", Set option_v;
  Exact "-stdlib", String(fun s -> stdlib_path := s);
  Exact "-timings", Set option_timings;
  Exact "-pipe", Unit (fun () ->
       option_pipe := true;
       Frontend.add_pipe ();
       Assembler.add_pipe ());] @
(* Diagnostic options *)
  Cerrors.warning_options @
(* Interpreter mode *)
 [ Exact "-interp", Set option_interp;
  Exact "-quiet", Unit (fun () -> Interp.trace := 0);
  Exact "-trace", Unit (fun () -> Interp.trace := 2);
  Exact "-random", Unit (fun () -> Interp.mode := Interp.Random);
  Exact "-all", Unit (fun () -> Interp.mode := Interp.All)
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
(* Optimization options *)
  @ f_opt "tailcalls" option_ftailcalls
  @ f_opt "const-prop" option_fconstprop
  @ f_opt "cse" option_fcse
  @ f_opt "redundancy" option_fredundancy
(* Code generation options *)
  @ f_opt "fpu" option_ffpu
  @ f_opt "sse" option_ffpu (* backward compatibility *)
  @ [
(* Catch options that are not handled *)
  Prefix "-", Self (fun s ->
      eprintf "Unknown option `%s'\n" s; exit 2);
(* File arguments *)
  Suffix ".c", Self (fun s ->
      push_action process_c_file (File.new_input_file s ".c"); incr num_source_files; incr num_input_files);
  Suffix ".i", Self (fun s ->
      push_action process_i_file (File.new_input_file s ".i"); incr num_source_files; incr num_input_files);
  Suffix ".p", Self (fun s ->
      push_action process_i_file (File.new_input_file s ".p"); incr num_source_files; incr num_input_files);
  Suffix ".cm", Self (fun s ->
      push_action process_cminor_file (File.new_input_file s ".cm"); incr num_source_files; incr num_input_files);
  Suffix ".s", Self (fun s ->
      push_action process_s_file (File.new_input_file s ".s"); incr num_source_files; incr num_input_files);
  Suffix ".S", Self (fun s ->
      push_action process_S_file (File.new_input_file s ".S"); incr num_source_files; incr num_input_files);
  Suffix ".o", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".a", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .o.ext files and .so files are also object files *)
  _Regexp ".*\\.o\\.", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".so", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .h files can be preprocessed with -E *)
  Suffix ".h", Self (fun s ->
      push_action process_h_file (File.new_input_file s ".h"); incr num_source_files; incr num_input_files);
  ]

let _ =
  try
    Gc.set { (Gc.get()) with
                Gc.minor_heap_size = 524288; (* 512k *)
                Gc.major_heap_increment = 4194304 (* 4M *)
           };
    Printexc.record_backtrace true;
    Machine.config :=
      begin match Configuration.arch with
      | "powerpc" -> if Configuration.system = "linux"
                     then Machine.ppc_32_bigendian
                     else Machine.ppc_32_diab_bigendian
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
    parse_cmdline cmdline_actions;
    DebugInit.init (); (* Initialize the debug functions *)
    let nolink = !option_c || !option_S || !option_E || !option_interp in
    if nolink && !option_o <> None && !num_source_files >= 2 then begin
      eprintf "Ambiguous '-o' option (multiple source files)\n";
      exit 2
    end;
    if !num_input_files = 0 then
      begin
        eprintf "ccomp: error: no input file\n";
        exit 2
      end;
    let linker_args = time "Total compilation time" perform_actions () in
    if (not nolink) && linker_args <> [] then begin
      linker (output_filename_default "a.out") linker_args
    end;
   if  Cerrors.check_errors () then exit 2
  with Sys_error msg ->
    eprintf "I/O error: %s.\n" msg; exit 2

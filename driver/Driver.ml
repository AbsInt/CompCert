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
open Frontend
open Assembler
open Linker
open Json

(* Optional sdump suffix *)
let sdump_suffix = ref ".json"
let sdump_folder = ref ""

(* Dump Asm code in asm format for the validator *)

let jdump_magic_number = "CompCertJDUMP" ^ Version.version

let nolink () =
  !option_c || !option_S || !option_E || !option_interp

let dump_jasm asm sourcename destfile =
  let oc = open_out_bin destfile in
  let pp = Format.formatter_of_out_channel oc in
  let get_args () =
    let buf = Buffer.create 100 in
    Buffer.add_string buf Sys.executable_name;
    for i = 1 to (Array.length  !argv - 1) do
      Buffer.add_string buf " ";
      Buffer.add_string buf (Responsefile.gnu_quote  !argv.(i));
    done;
    Buffer.contents buf in
  let dump_compile_info pp () =
    pp_jobject_start pp;
    pp_jmember ~first:true pp "directory" pp_jstring (Sys.getcwd ());
    pp_jmember pp "command" pp_jstring (get_args ());
    pp_jmember pp "file" pp_jstring sourcename;
    pp_jobject_end pp in
  pp_jobject_start pp;
  pp_jmember ~first:true pp "Version" pp_jstring jdump_magic_number;
  pp_jmember pp "System" pp_jstring Configuration.system;
  pp_jmember pp "Compile Info" dump_compile_info ();
  pp_jmember pp "Compilation Unit" pp_jstring sourcename;
  pp_jmember pp "Asm Ast" AsmToJSON.pp_program asm;
  pp_jobject_end pp;
  Format.pp_print_flush pp ();
  close_out oc

let object_filename sourcename suff =
  if nolink () then
    output_filename ~final: !option_c sourcename suff ".o"
  else begin
    let tmpfile = Filename.temp_file "compcert" ".o" in
    at_exit (fun () -> safe_remove tmpfile);
    tmpfile
  end

(* From CompCert C AST to asm *)

let compile_c_ast sourcename csyntax ofile =
  (* Prepare to dump Clight, RTL, etc, if requested *)
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename sourcename ".c" ext)
                   else None in
  set_dest PrintClight.destination option_dclight ".light.c";
  set_dest PrintCminor.destination option_dcminor ".cm";
  set_dest PrintRTL.destination option_drtl ".rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dltl ".ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  (* Convert to Asm *)
  let asm =
    match Compiler.apply_partial
               (Compiler.transf_c_program csyntax)
               Asmexpand.expand_program with
    | Errors.OK asm ->
        asm
    | Errors.Error msg ->
        eprintf "%s: %a" sourcename print_error msg;
        exit 2 in
  (* Dump Asm in binary and JSON format *)
  if !option_sdump then begin
    let sf = output_filename sourcename ".c" !sdump_suffix in
    let csf = Filename.concat !sdump_folder sf in
    dump_jasm asm sourcename csf
  end;
  (* Print Asm in text form *)
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc

(* From C source to asm *)

let compile_c_file sourcename ifile ofile =
  let ast = parse_c_file sourcename ifile in
  compile_c_ast sourcename ast ofile


(* Processing of a .c file *)

let process_c_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = if !option_dprepro then
      output_filename sourcename ".c" ".i"
    else
      Filename.temp_file "compcert" ".i" in
    preprocess sourcename preproname;
    let name =
      if !option_interp then begin
        Machine.config := Machine.compcert_interpreter !Machine.config;
        let csyntax = parse_c_file sourcename preproname in
        if not !option_dprepro then
          safe_remove preproname;
       Interp.execute csyntax;
        ""
      end else if !option_S then begin
        compile_c_file sourcename preproname
          (output_filename ~final:true sourcename ".c" ".s");
        if not !option_dprepro then
          safe_remove preproname;
        ""
      end else begin
        let asmname =
          if !option_dasm
          then output_filename sourcename ".c" ".s"
          else Filename.temp_file "compcert" ".s" in
        compile_c_file sourcename preproname asmname;
        if not !option_dprepro then
          safe_remove preproname;
        let objname = object_filename sourcename ".c" in
        assemble asmname objname;
        if not !option_dasm then safe_remove asmname;
        objname
      end in
    name
  end

(* Processing of a .i / .p file (preprocessed C) *)

let process_i_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_interp then begin
    let csyntax = parse_c_file sourcename sourcename in
    Interp.execute csyntax;
    ""
  end else if !option_S then begin
    compile_c_file sourcename sourcename
      (output_filename ~final:true sourcename ".c" ".s");
    ""
  end else begin
    let asmname =
      if !option_dasm
      then output_filename sourcename ".c" ".s"
      else Filename.temp_file "compcert" ".s" in
    compile_c_file sourcename sourcename asmname;
    let objname = object_filename sourcename ".c" in
    assemble asmname objname;
    if not !option_dasm then safe_remove asmname;
    objname
  end


(* Processing of .S and .s files *)

let process_s_file sourcename =
  ensure_inputfile_exists sourcename;
  let objname = object_filename sourcename ".s" in
  assemble sourcename objname;
  objname

let process_S_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = Filename.temp_file "compcert" ".s" in
    preprocess sourcename preproname;
    let objname = object_filename sourcename ".S" in
    assemble preproname objname;
    safe_remove preproname;
    objname
  end

(* Processing of .h files *)

let process_h_file sourcename =
  if !option_E then begin
    ensure_inputfile_exists sourcename;
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    eprintf "Error: input file %s ignored (not in -E mode)\n" sourcename;
    exit 2
  end

let version_string =
  if Version.buildnr <> "" && Version.tag <> "" then
    sprintf "The CompCert C verified compiler, %s, Build: %s, Tag: %s\n" Version.version Version.buildnr Version.tag
  else
    "The CompCert C verified compiler, version "^ Version.version ^ "\n"

let target_help =
  if Configuration.arch = "arm" && Configuration.model <> "armv6" then
{|Target processor options:
  -mthumb        Use Thumb2 instruction encoding
  -marm          Use classic ARM instruction encoding
|}
else
  ""

let usage_string =
  version_string ^
  {|Usage: ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .i or .p       C source file that should not be preprocessed
  .s             Assembly file
  .S or .sx      Assembly file that must be preprocessed
  .o             Object file
  .a             Library file
Processing options:
  -c             Compile to object file only (no linking), result in <file>.o
  -E             Preprocess only, send result to standard output
  -S             Compile to assembler only, save result in <file>.s
  -o <file>      Generate output in <file>
|} ^
  prepro_help ^
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
|}^
 DebugInit.debugging_help ^
{|Optimization options: (use -fno-<opt> to turn off -f<opt>)
  -O             Optimize the compiled code [on by default]
  -O0            Do not optimize the compiled code
  -O1 -O2 -O3    Synonymous for -O
  -Os            Optimize for code size in preference to code speed
  -ftailcalls    Optimize function calls in tail position [on]
  -fconst-prop   Perform global constant propagation  [on]
  -ffloat-const-prop <n>  Control constant propagation of floats
                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)
  -fcse          Perform common subexpression elimination [on]
  -fredundancy   Perform redundancy elimination [on]
  -finline       Perform inlining of functions [on]
Code generation options: (use -fno-<opt> to turn off -f<opt>)
  -ffpu          Use FP registers for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
|} ^
 target_help ^
 assembler_help ^
 linker_help ^
{|Tracing options:
  -dprepro       Save C file after preprocessing in <file>.i
  -dparse        Save C file after parsing and elaboration in <file>.parsed.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save RTL at various optimization points in <file>.rtl.<n>
  -dltl          Save LTL after register allocation in <file>.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
  -dall          Save all generated intermediate files in <file>.<ext>
  -sdump         Save info for post-linking validation in <file>.json
General options:
  -stdlib <dir>  Set the path of the Compcert run-time library
  -v             Print external commands before invoking them
  -timings       Show the time spent in various compiler passes
  -version       Print the version string and exit
  -target <value> Generate code for the given target
  -conf <file>   Read configuration from file
  @<file>        Read command line options from <file>
|} ^
  Cerrors.warning_help ^
  {|Interpreter mode:
  -interp        Execute given .c files using the reference interpreter
  -quiet         Suppress diagnostic messages for the interpreter
  -trace         Have the interpreter produce a detailed trace of reductions
  -random        Randomize execution order
  -all           Simulate all possible execution orders
|}

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

let dump_mnemonics destfile =
  let oc = open_out_bin destfile in
  let pp = Format.formatter_of_out_channel oc in
  AsmToJSON.pp_mnemonics pp;
  Format.pp_print_flush pp ();
  close_out oc;
  exit 0

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
(* Enforcing CompCert build numbers for QSKs and mnemonics dump *)
  (if Version.buildnr <> "" then
    [ Exact "-qsk-enforce-build", Integer enforce_buildnr;
      Exact "--qsk-enforce-build", Integer enforce_buildnr;
      Exact "-dump-mnemonics", String  dump_mnemonics;
    ]
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
    if Configuration.model = "armv6" then
      [ Exact "-marm", Ignore ] (* Thumb needs ARMv6T2 or ARMv7 *)
    else
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
    option_dltl := true;
    option_dalloctrace := true;
    option_dmach := true;
    option_dasm := true);
  Exact "-sdump", Set option_sdump;
  Exact "-sdump-suffix", String (fun s -> option_sdump := true; sdump_suffix:= s);
  Exact "-sdump-folder", String (fun s -> sdump_folder := s);
(* General options *)
  Exact "-v", Set option_v;
  Exact "-stdlib", String(fun s -> stdlib_path := s);
  Exact "-timings", Set option_timings;] @
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
  @ f_opt "inline" option_finline
(* Code generation options *)
  @ f_opt "fpu" option_ffpu
  @ f_opt "sse" option_ffpu (* backward compatibility *)
  @ [
(* Catch options that are not handled *)
  Prefix "-", Self (fun s ->
      eprintf "Unknown option `%s'\n" s; exit 2);
(* File arguments *)
  Suffix ".c", Self (fun s ->
      push_action process_c_file s; incr num_source_files; incr num_input_files);
  Suffix ".i", Self (fun s ->
      push_action process_i_file s; incr num_source_files; incr num_input_files);
  Suffix ".p", Self (fun s ->
      push_action process_i_file s; incr num_source_files; incr num_input_files);
  Suffix ".s", Self (fun s ->
      push_action process_s_file s; incr num_source_files; incr num_input_files);
  Suffix ".S", Self (fun s ->
      push_action process_S_file s; incr num_source_files; incr num_input_files);
  Suffix ".sx", Self (fun s ->
      push_action process_S_file s; incr num_source_files; incr num_input_files);
  Suffix ".o", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".a", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .o.ext files and .so files are also object files *)
  _Regexp ".*\\.o\\.", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".so", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .h files can be preprocessed with -E *)
  Suffix ".h", Self (fun s ->
      push_action process_h_file s; incr num_source_files; incr num_input_files);
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
      | "riscV"   -> if Configuration.model = "64"
                     then Machine.rv64
                     else Machine.rv32
      | _         -> assert false
      end;
    Builtins.set C2C.builtins;
    Cutil.declare_attributes C2C.attributes;
    CPragmas.initialize();
    parse_cmdline cmdline_actions;
    DebugInit.init (); (* Initialize the debug functions *)
    if nolink () && !option_o <> None && !num_source_files >= 2 then begin
      eprintf "Ambiguous '-o' option (multiple source files)\n";
      exit 2
    end;
    if !num_input_files = 0 then
      begin
        eprintf "ccomp: error: no input file\n";
        exit 2
      end;
    let linker_args = time "Total compilation time" perform_actions () in
    if not (nolink ()) && linker_args <> [] then begin
      linker (output_filename_default "a.out") linker_args
    end;
   if  Cerrors.check_errors () then exit 2
  with Sys_error msg ->
    eprintf "I/O error: %s.\n" msg; exit 2
     | e ->
       Cerrors.crash e

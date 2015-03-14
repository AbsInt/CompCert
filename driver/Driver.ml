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
open Camlcoq
open Clflags
open Timing

(* Location of the compatibility library *)

let stdlib_path = ref Configuration.stdlib_path

let command cmd =
  if !option_v then begin
    prerr_string "+ "; prerr_string cmd; prerr_endline ""
  end;
  Sys.command cmd

let quote_options opts =
  String.concat " " (List.rev_map Filename.quote opts)

let quote_arguments args =
  String.concat " " (List.map Filename.quote args)

let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()

(* Printing of error messages *)

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

(* Determine names for output files.  We use -o option if specified
   and if this is the final destination file (not a dump file).
   Otherwise, we generate a file in the current directory. *)

let output_filename ?(final = false) source_file source_suffix output_suffix =
  match !option_o with
  | Some file when final -> file
  | _ -> 
    Filename.basename (Filename.chop_suffix source_file source_suffix)
    ^ output_suffix

(* A variant of [output_filename] where the default output name is fixed *)

let output_filename_default default_file =
  match !option_o with
  | Some file -> file
  | None -> default_file

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

(* Dump Asm code in binary format for the validator *)

let sdump_magic_number = "CompCertSDUMP" ^ Configuration.version

let dump_asm asm destfile =
  let oc = open_out_bin destfile in
  output_string oc sdump_magic_number;
  output_value oc asm;
  output_value oc Camlcoq.string_of_atom;
  output_value oc C2C.decl_atom;
  close_out oc

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
    match Compiler.transf_c_program csyntax with
    | Errors.OK asm ->
        Asmexpand.expand_program asm
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in
  (* Dump Asm in binary format *)  
  if !option_sdump then
    dump_asm asm (output_filename sourcename ".c" ".sdump");
  (* Print Asm in text form *)
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc

(* From C source to asm *)

let compile_c_file sourcename ifile ofile =
  compile_c_ast sourcename (parse_c_file sourcename ifile) ofile

(* From Cminor to asm *)

let compile_cminor_file ifile ofile =
  (* Prepare to dump RTL, Mach, etc, if requested *)
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename ifile ".cm" ext)
                   else None in
  set_dest PrintRTL.destination option_drtl ".rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dltl ".ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  Sections.initialize();
  let ic = open_in ifile in
  let lb = Lexing.from_channel ic in
  try
    match Compiler.transf_cminor_program
            (CMtypecheck.type_program
              (CMparser.prog CMlexer.token lb)) with
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2
    | Errors.OK p ->
        let oc = open_out ofile in
        PrintAsm.print_program oc p;
        close_out oc
  with Parsing.Parse_error ->
         eprintf "File %s, character %d: Syntax error\n"
                 ifile (Lexing.lexeme_start lb);
         exit 2
     | CMlexer.Error msg ->  
         eprintf "File %s, character %d: %s\n"
                 ifile (Lexing.lexeme_start lb) msg;
         exit 2
     | CMtypecheck.Error msg ->
         eprintf "File %s, type-checking error:\n%s"
                 ifile msg;
         exit 2

(* From asm to object file *)

let assemble ifile ofile =
  let cmd =
    sprintf "%s -o %s %s %s"
      Configuration.asm ofile (quote_options !assembler_options) ifile in
  let retcode = command cmd in
  if retcode <> 0 then begin
    safe_remove ofile;
    eprintf "Error during assembling.\n";
    exit 2
  end

(* Linking *)

let linker exe_name files =
  let cmd =
    sprintf "%s -o %s %s %s"
      Configuration.linker
      (Filename.quote exe_name)
      (quote_arguments files)
      (if Configuration.has_runtime_lib
       then sprintf "-L%s -lcompcert" !stdlib_path
       else "") in
  if command cmd <> 0 then exit 2

(* Processing of a .c file *)

let process_c_file sourcename =
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = Filename.temp_file "compcert" ".i" in
    preprocess sourcename preproname;
    if !option_interp then begin
      Machine.config := Machine.compcert_interpreter !Machine.config;
      let csyntax = parse_c_file sourcename preproname in
      safe_remove preproname;
      Interp.execute csyntax;
      ""
    end else if !option_S then begin
      compile_c_file sourcename preproname
                     (output_filename ~final:true sourcename ".c" ".s");
      safe_remove preproname;
      ""
    end else begin
      let asmname =
        if !option_dasm
        then output_filename sourcename ".c" ".s"
        else Filename.temp_file "compcert" ".s" in
      compile_c_file sourcename preproname asmname;
      safe_remove preproname;
      let objname = output_filename ~final: !option_c sourcename ".c" ".o" in
      assemble asmname objname;
      if not !option_dasm then safe_remove asmname;
      objname
    end
  end

(* Processing of a .i / .p file (preprocessed C) *)

let process_i_file sourcename =
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
    let objname = output_filename ~final: !option_c sourcename ".c" ".o" in
    assemble asmname objname;
    if not !option_dasm then safe_remove asmname;
    objname
  end

(* Processing of a .cm file *)

let process_cminor_file sourcename =
  if !option_S then begin
    compile_cminor_file sourcename
                        (output_filename ~final:true sourcename ".cm" ".s");
    ""
  end else begin
    let asmname =
      if !option_dasm
      then output_filename sourcename ".cm" ".s"
      else Filename.temp_file "compcert" ".s" in
    compile_cminor_file sourcename asmname;
    let objname = output_filename ~final: !option_c sourcename ".cm" ".o" in
    assemble asmname objname;
    if not !option_dasm then safe_remove asmname;
    objname
  end

(* Processing of .S and .s files *)

let process_s_file sourcename =
  let objname = output_filename ~final: !option_c sourcename ".s" ".o" in
  assemble sourcename objname;
  objname

let process_S_file sourcename =
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = Filename.temp_file "compcert" ".s" in
    preprocess sourcename preproname;
    let objname = output_filename ~final: !option_c sourcename ".S" ".o" in
    assemble preproname objname;
    safe_remove preproname;
    objname
  end

(* Processing of .h files *)

let process_h_file sourcename =
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    eprintf "Error: input file %s ignored (not in -E mode)\n" sourcename;
    exit 2
  end    

(* Record actions to be performed after parsing the command line *)

let actions : ((string -> string) * string) list ref = ref []

let push_action fn arg =
  actions := (fn, arg) :: !actions

let push_linker_arg arg =
  push_action (fun s -> s) arg

let perform_actions () =
  let rec perform = function
  | [] -> []
  | (fn, arg) :: rem -> let res = fn arg in res :: perform rem
  in perform (List.rev !actions)

(* Command-line parsing *)

let explode_comma_option s =
  match Str.split (Str.regexp ",") s with
  | [] -> assert false
  | hd :: tl -> tl

let usage_string =
"The CompCert C verified compiler, version " ^ Configuration.version ^ "
Usage: ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .i or .p       C source file that should not be preprocessed
  .cm            Cminor source file
  .s             Assembly file
  .S             Assembly file that must be preprocessed
  .o             Object file
  .a             Library file
Processing options:
  -c             Compile to object file only (no linking), result in <file>.o
  -E             Preprocess only, send result to standard output
  -S             Compile to assembler only, save result in <file>.s
  -o <file>      Generate output in <file>
Preprocessing options:
  -I<dir>        Add <dir> to search path for #include files
  -D<symb>=<val> Define preprocessor symbol
  -U<symb>       Undefine preprocessor symbol
  -Wp,<opt>      Pass option <opt> to the preprocessor
Language support options (use -fno-<opt> to turn off -f<opt>) :
  -fbitfields    Emulate bit fields in structs [off]
  -flongdouble   Treat 'long double' as 'double' [off]
  -fstruct-return  Emulate returning structs and unions by value [off]
  -fstruct-return=<convention>
                 Set the calling conventions used to return structs by value
  -fstruct-passing=<convention>
                 Set the calling conventions used to pass structs by value
  -fvararg-calls Support calls to variable-argument functions [on]
  -funprototyped Support calls to old-style functions without prototypes [on]
  -fpacked-structs  Emulate packed structs [off]
  -finline-asm   Support inline 'asm' statements [off]
  -fall          Activate all language support options above
  -fnone         Turn off all language support options above
Debugging options:
  -g             Generate debugging information
Optimization options: (use -fno-<opt> to turn off -f<opt>)
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
Code generation options: (use -fno-<opt> to turn off -f<opt>)
  -ffpu          Use FP registers for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
Target processor options:
  -mthumb        (ARM only) Use Thumb2 instruction encoding
  -marm          (ARM only) Use classic ARM instruction encoding
Assembling options:
  -Wa,<opt>      Pass option <opt> to the assembler
Linking options:
  -l<lib>        Link library <lib>
  -L<dir>        Add <dir> to search path for libraries
  -Wl,<opt>      Pass option <opt> to the linker
Tracing options:
  -dparse        Save C file after parsing and elaboration in <file>.parse.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save RTL at various optimization points in <file>.rtl.<n>
  -dltl          Save LTL after register allocation in <file>.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
  -sdump         Save info for post-linking validation in <file>.sdump
General options:
  -stdlib <dir>  Set the path of the Compcert run-time library
  -v             Print external commands before invoking them
  -timings       Show the time spent in various compiler passes
Interpreter mode:
  -interp        Execute given .c files using the reference interpreter
  -quiet         Suppress diagnostic messages for the interpreter
  -trace         Have the interpreter produce a detailed trace of reductions
  -random        Randomize execution order
  -all           Simulate all possible execution orders
"

let print_usage_and_exit _ =
  printf "%s" usage_string; exit 0

let language_support_options = [
  option_fbitfields; option_flongdouble;
  option_fstruct_return; option_fvararg_calls; option_funprototyped;
  option_fpacked_structs; option_finline_asm
]

let optimization_options = [
  option_ftailcalls; option_fconstprop; option_fcse; option_fredundancy
]

let set_all opts = List.iter (fun r -> r := true) opts
let unset_all opts = List.iter (fun r -> r := false) opts

let num_source_files = ref 0

let cmdline_actions =
  let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref] in
  [
(* Getting help *)
  Exact "-help", Self print_usage_and_exit;
  Exact "--help", Self print_usage_and_exit;
(* Processing options *)
  Exact "-c", Set option_c;
  Exact "-E", Set option_E;
  Exact "-S", Set option_S;
  Exact "-o", String(fun s -> option_o := Some s);
(* Preprocessing options *)
  Exact "-I", String(fun s -> prepro_options := s :: "-I" :: !prepro_options);
  Prefix "-I", Self(fun s -> prepro_options := s :: !prepro_options);
  Exact "-D", String(fun s -> prepro_options := s :: "-D" :: !prepro_options);
  Prefix "-D", Self(fun s -> prepro_options := s :: !prepro_options);
  Exact "-U", String(fun s -> prepro_options := s :: "-U" :: !prepro_options);
  Prefix "-U", Self(fun s -> prepro_options := s :: !prepro_options);
  Prefix "-Wp,", Self (fun s ->
    prepro_options := List.rev_append (explode_comma_option s) !prepro_options);
(* Language support options -- more below *)
  Exact "-fall", Self (fun _ -> set_all language_support_options);
  Exact "-fnone", Self (fun _ -> unset_all language_support_options);
(* Debugging options *)
  Exact "-g", Self (fun s -> option_g := true; push_linker_arg s);
(* Code generation options -- more below *)
  Exact "-O0", Self (fun _ -> unset_all optimization_options);
  Exact "-O", Self (fun _ -> set_all optimization_options);
  _Regexp "-O[123]$", Self (fun _ -> set_all optimization_options);
  Exact "-Os", Set option_Osize;
  Exact "-fsmall-data", Integer(fun n -> option_small_data := n);
  Exact "-fsmall-const", Integer(fun n -> option_small_const := n);
  Exact "-ffloat-const-prop", Integer(fun n -> option_ffloatconstprop := n);
  Exact "-falign-functions", Integer(fun n -> option_falignfunctions := Some n);
  Exact "-falign-branch-targets", Integer(fun n -> option_falignbranchtargets := n);
  Exact "-falign-cond-branches", Integer(fun n -> option_faligncondbranchs := n);
(* Target processor options *)
  Exact "-mthumb", Set option_mthumb;
  Exact "-marm", Unset option_mthumb;
(* Assembling options *)
  Prefix "-Wa,", Self (fun s -> assembler_options := s :: !assembler_options);
(* Linking options *)
  Prefix "-l", Self push_linker_arg;
  Prefix "-L", Self push_linker_arg;
  Prefix "-Wl,", Self push_linker_arg;
(* Tracing options *)
  Exact "-dparse", Set option_dparse;
  Exact "-dc", Set option_dcmedium;
  Exact "-dclight", Set option_dclight;
  Exact "-dcminor", Set option_dcminor;
  Exact "-drtl", Set option_drtl;
  Exact "-dltl", Set option_dltl;
  Exact "-dalloctrace", Set option_dalloctrace;
  Exact "-dmach", Set option_dmach;
  Exact "-dasm", Set option_dasm;
  Exact "-sdump", Set option_sdump;
(* General options *) 
  Exact "-v", Set option_v;
  Exact "-stdlib", String(fun s -> stdlib_path := s);
  Exact "-timings", Set option_timings;
(* Interpreter mode *)
  Exact "-interp", Set option_interp;
  Exact "-quiet", Self (fun _ -> Interp.trace := 0);
  Exact "-trace", Self (fun _ -> Interp.trace := 2);
  Exact "-random", Self (fun _ -> Interp.mode := Interp.Random);
  Exact "-all", Self (fun _ -> Interp.mode := Interp.All);
(* Special -f options *)
  Exact "-fstruct-passing=ref-callee",
    Self (fun _ -> option_fstruct_passing_style := Some Machine.SP_ref_callee);
  Exact "-fstruct-passing=ref-caller",
    Self (fun _ -> option_fstruct_return := true;
                   option_fstruct_passing_style := Some Machine.SP_ref_caller);
  Exact "-fstruct-passing=ints",
    Self (fun _ -> option_fstruct_return := true;
                   option_fstruct_passing_style := Some Machine.SP_split_args);
  Exact "-fstruct-return=ref",
    Self (fun _ -> option_fstruct_return := true;
                   option_fstruct_return_style := Some 0);
  Exact "-fstruct-return=int4",
    Self (fun _ -> option_fstruct_return := true;
                   option_fstruct_return_style := Some 4);
  Exact "-fstruct-return=int8",
    Self (fun _ -> option_fstruct_return := true;
                   option_fstruct_return_style := Some 8)
  ]
(* -f options: come in -f and -fno- variants *)
(* Language support options *)
  @ f_opt "longdouble" option_flongdouble
  @ f_opt "struct-return" option_fstruct_return
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
      push_action process_c_file s; incr num_source_files);
  Suffix ".i", Self (fun s ->
      push_action process_i_file s; incr num_source_files);
  Suffix ".p", Self (fun s ->
      push_action process_i_file s; incr num_source_files);
  Suffix ".cm", Self (fun s ->
      push_action process_cminor_file s; incr num_source_files);
  Suffix ".s", Self (fun s ->
      push_action process_s_file s; incr num_source_files);
  Suffix ".S", Self (fun s ->
      push_action process_S_file s; incr num_source_files);
  Suffix ".o", Self push_linker_arg;
  Suffix ".a", Self push_linker_arg;
  (* GCC compatibility: .o.ext files and .so files are also object files *)
  _Regexp ".*\\.o\\.", Self push_linker_arg;
  Suffix ".so", Self push_linker_arg;
  (* GCC compatibility: .h files can be preprocessed with -E *)
  Suffix ".h", Self (fun s ->
      push_action process_h_file s; incr num_source_files);
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
      | "powerpc" -> if Configuration.abi = "linux"
                     then Machine.ppc_32_bigendian_linux
                     else Machine.ppc_32_bigendian
      | "arm"     -> Machine.arm_littleendian
      | "ia32"    -> if Configuration.abi = "macosx"
                     then Machine.x86_32_macosx
                     else Machine.x86_32
      | _         -> assert false
      end;
    Builtins.set C2C.builtins;
    CPragmas.initialize();
    parse_cmdline cmdline_actions;
    let nolink = !option_c || !option_S || !option_E || !option_interp in
    if nolink && !option_o <> None && !num_source_files >= 2 then begin
      eprintf "Ambiguous '-o' option (multiple source files)\n";
      exit 2
    end;
    let linker_args = time "Total compilation time" perform_actions () in
    if (not nolink) && linker_args <> [] then begin
      linker (output_filename_default "a.out") linker_args
    end
  with Sys_error msg ->
    eprintf "I/O error: %s.\n" msg; exit 2

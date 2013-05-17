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
open Camlcoq
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
  | Some file when final -> option_o := None; file
  | _ -> 
    Filename.basename (Filename.chop_suffix source_file source_suffix)
    ^ output_suffix

(* A variant of [output_filename] where the default output name is fixed *)

let output_filename_default default_file =
  match !option_o with
  | Some file -> option_o := None; file
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
(*  ^ (if !option_flonglong then "l" else "") *)
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
    let ofile = output_filename sourcename ".c" ".parsed.c" in
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
  set_dest PrintRTL.destination_rtl option_drtl ".rtl";
  set_dest PrintRTL.destination_tailcall option_dtailcall ".tailcall.rtl";
  set_dest PrintRTL.destination_inlining option_dinlining ".inlining.rtl";
  set_dest PrintRTL.destination_constprop option_dconstprop ".constprop.rtl";
  set_dest PrintRTL.destination_cse option_dcse ".cse.rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dalloc ".alloc.ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  (* Convert to Asm *)
  let asm =
    match Compiler.transf_c_program csyntax with
    | Errors.OK x -> x
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in
  (* Dump Asm in binary format *)  
  if !option_sdump then
    dump_asm asm (output_filename sourcename ".c" ".sdump");
  (* Print Asm in text form *)
  let oc = open_out ofile in
  PrintAsm.print_program oc (Unusedglob.transf_program asm);
  close_out oc

(* From C source to asm *)

let compile_c_file sourcename ifile ofile =
  compile_c_ast sourcename (parse_c_file sourcename ifile) ofile

(* From Cminor to asm *)

let compile_cminor_file ifile ofile =
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
      (quote_options files)
      (if Configuration.has_runtime_lib
       then sprintf "-L%s -lcompcert" !stdlib_path
       else "") in
  if command cmd <> 0 then exit 2

(* Processing of a .c file *)

let option_interp = ref false

let process_c_file sourcename =
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = Filename.temp_file "compcert" ".i" in
    preprocess sourcename preproname;
    if !option_interp then begin
      let csyntax = parse_c_file sourcename preproname in
      Interp.execute csyntax;
      ""
    end else if !option_S then begin
      compile_c_file sourcename preproname
                     (output_filename ~final:true sourcename ".c" ".s");
      ""
    end else begin
      let asmname =
        if !option_dasm
        then output_filename sourcename ".c" ".s"
        else Filename.temp_file "compcert" ".s" in
      compile_c_file sourcename preproname asmname;
      let objname = output_filename ~final: !option_c sourcename ".c" ".o" in
      assemble asmname objname;
      if not !option_dasm then safe_remove asmname;
      objname
    end
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
    let objname = output_filename ~final: !option_c sourcename ".c" ".o" in
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
  let rec parse i =
    if i < Array.length Sys.argv then begin
      let s = Sys.argv.(i) in
      match find_action s acts with
      | None ->
          if s <> "-help" && s <> "--help" 
          then eprintf "Unknown argument `%s'\n" s
          else printf "%s" usage;
          exit 2
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
            eprintf "Option `%s' expects an argument\n" s; exit 2
          end
      | Some(Integer fn) ->
          if i + 1 < Array.length Sys.argv then begin
            let n =
              try
                int_of_string Sys.argv.(i+1)
              with Failure _ ->
                eprintf "Argument to option `%s' must be an integer\n" s;
                exit 2
            in
            fn n; parse (i+2)
          end else begin
            eprintf "Option `%s' expects an argument\n" s; exit 2
          end
    end
  in parse 1

let usage_string =
"The CompCert C verified compiler, version " ^ Configuration.version ^ "
Usage: ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .cm            Cminor source file
  .s             Assembly file
  .S             Assembly file, to be run through the preprocessor
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
  -fvararg-calls Emulate calls to variable-argument functions [on]
  -fpacked-structs  Emulate packed structs [off]
  -finline-asm   Support inline 'asm' statements [off]
  -fall          Activate all language support options above
  -fnone         Turn off all language support options above
Code generation options: (use -fno-<opt> to turn off -f<opt>) :
  -fsse          (IA32) Use SSE2 instructions for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -ffloat-const-prop <n>  Control constant propagation of floats
                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)
  -ftailcalls    Optimize function calls in tail position [on]
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
  -Wa,<opt>      Pass option <opt> to the assembler
Debugging options:
  -g             Generate debugging information
Linking options:
  -l<lib>        Link library <lib>
  -L<dir>        Add <dir> to search path for libraries
  -Wl,<opt>      Pass option <opt> to the linker
Tracing options:
  -dparse        Save C file after parsing and elaboration in <file>.parse.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save unoptimized generated RTL in <file>.rtl
  -dtailcall     Save RTL after tail call optimization in <file>.tailcall.rtl
  -dinlining     Save RTL after inlining optimization in <file>.inlining.rtl
  -dconstprop    Save RTL after constant propagation in <file>.constprop.rtl
  -dcse          Save RTL after CSE optimization in <file>.cse.rtl
  -dalloc        Save LTL after register allocation in <file>.alloc.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
  -sdump         Save info for post-linking validation in <file>.sdump
General options:
  -stdlib <dir>  Set the path of the Compcert run-time library
  -v             Print external commands before invoking them
Interpreter mode:
  -interp        Execute given .c files using the reference interpreter
  -quiet         Suppress diagnostic messages for the interpreter
  -trace         Have the interpreter produce a detailed trace of reductions
  -random        Randomize execution order
  -all           Simulate all possible execution orders
"

let language_support_options = [
  option_fbitfields; option_flongdouble;
  option_fstruct_return; option_fvararg_calls; option_fpacked_structs;
  option_finline_asm
]

let cmdline_actions =
  let f_opt name ref =
    ["-f" ^ name ^ "$", Set ref; "-fno-" ^ name ^ "$", Unset ref] in
  [
  "-I$", String(fun s -> prepro_options := s :: "-I" :: !prepro_options);
  "-D$", String(fun s -> prepro_options := s :: "-D" :: !prepro_options);
  "-U$", String(fun s -> prepro_options := s :: "-U" :: !prepro_options);
  "-[IDU].", Self(fun s -> prepro_options := s :: !prepro_options);
  "-[lL].", Self(fun s -> linker_options := s :: !linker_options);
  "-o$", String(fun s -> option_o := Some s);
  "-E$", Set option_E;
  "-S$", Set option_S;
  "-c$", Set option_c;
  "-v$", Set option_v;
  "-g$", Self (fun s ->
      option_g := true; linker_options := s :: !linker_options);
  "-stdlib$", String(fun s -> stdlib_path := s);
  "-dparse$", Set option_dparse;
  "-dc$", Set option_dcmedium;
  "-dclight$", Set option_dclight;
  "-dcminor", Set option_dcminor;
  "-drtl$", Set option_drtl;
  "-dtailcall$", Set option_dtailcall;
  "-dinlining$", Set option_dinlining;
  "-dconstprop$", Set option_dconstprop;
  "-dcse$", Set option_dcse;
  "-dalloc$", Set option_dalloc;
  "-dalloctrace$", Set option_dalloctrace;
  "-dmach$", Set option_dmach;
  "-dasm$", Set option_dasm;
  "-sdump$", Set option_sdump;
  "-interp$", Set option_interp;
  "-quiet$", Self (fun _ -> Interp.trace := 0);
  "-trace$", Self (fun _ -> Interp.trace := 2);
  "-random$", Self (fun _ -> Interp.mode := Interp.Random);
  "-all$", Self (fun _ -> Interp.mode := Interp.All);
  ".*\\.c$", Self (fun s ->
      let objfile = process_c_file s in
      linker_options := objfile :: !linker_options);
  ".*\\.cm$", Self (fun s ->
      let objfile = process_cminor_file s in
      linker_options := objfile :: !linker_options);
  ".*\\.s$", Self (fun s ->
      let objfile = process_s_file s in
      linker_options := objfile :: !linker_options);
  ".*\\.S$", Self (fun s ->
      let objfile = process_S_file s in
      linker_options := objfile :: !linker_options);
  ".*\\.[oa]$", Self (fun s ->
      linker_options := s :: !linker_options);
  "-Wp,", Self (fun s ->
      prepro_options := List.rev_append (explode_comma_option s) !prepro_options);
  "-Wa,", Self (fun s ->
      assembler_options := s :: !assembler_options);
  "-Wl,", Self (fun s ->
      linker_options := s :: !linker_options);
  "-fsmall-data$", Integer(fun n -> option_small_data := n);
  "-fsmall-const$", Integer(fun n -> option_small_const := n);
  "-ffloat-const-prop$", Integer(fun n -> option_ffloatconstprop := n);
  "-falign-functions$", Integer(fun n -> option_falignfunctions := Some n);
  "-falign-branch-targets", Integer(fun n -> option_falignbranchtargets := n);
  "-falign-cond-branches", Integer(fun n -> option_faligncondbranchs := n);
  "-fall$", Self (fun _ ->
              List.iter (fun r -> r := true) language_support_options);
  "-fnone$", Self (fun _ ->
              List.iter (fun r -> r := false) language_support_options);
  ]
  @ f_opt "tailcalls" option_ftailcalls
  @ f_opt "longdouble" option_flongdouble
  @ f_opt "struct-return" option_fstruct_return
  @ f_opt "bitfields" option_fbitfields
  @ f_opt "vararg-calls" option_fvararg_calls
  @ f_opt "packed-structs" option_fpacked_structs
  @ f_opt "inline-asm" option_finline_asm
  @ f_opt "sse" option_fsse

let _ =
  Gc.set { (Gc.get()) with Gc.minor_heap_size = 524288 };
  Machine.config :=
    begin match Configuration.arch with
    | "powerpc" -> Machine.ppc_32_bigendian
    | "arm"     -> Machine.arm_littleendian
    | "ia32"    -> Machine.x86_32
    | _         -> assert false
    end;
  Builtins.set C2C.builtins;
  CPragmas.initialize();
  parse_cmdline cmdline_actions usage_string;
  if !linker_options <> [] 
  && not (!option_c || !option_S || !option_E || !option_interp)
  then begin
    linker (output_filename_default "a.out") !linker_options
  end

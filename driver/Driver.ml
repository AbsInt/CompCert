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
open Clflags

(* Location of the standard library *)

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
  in
    List.iter print_one_error msg;
    output_char oc '\n'

(* For the CIL -> Csyntax translator:

  * The meaning of some type specifiers may depend on compiler options:
      the size of an int or the default signedness of char, for instance.

  * Those type conversions may be parameterized thanks to a functor.

  * Remark: [None] means that the type specifier is not supported
      (that is, an Unsupported exception will be raised if that type
      specifier is encountered in the program).
*)

module TypeSpecifierTranslator = struct
  
  open Cil
  open Csyntax
    
  (** Convert a Cil.ikind into an (intsize * signedness) option *)
  let convertIkind = function
    | IChar      -> Some (I8, Unsigned)
    | ISChar     -> Some (I8, Signed)
    | IUChar     -> Some (I8, Unsigned)
    | IInt       -> Some (I32, Signed)
    | IUInt      -> Some (I32, Unsigned)
    | IShort     -> Some (I16, Signed)
    | IUShort    -> Some (I16, Unsigned)
    | ILong      -> Some (I32, Signed)
    | IULong     -> Some (I32, Unsigned)
    | ILongLong  -> if !option_flonglong then Some (I32, Signed) else None
    | IULongLong -> if !option_flonglong then Some (I32, Unsigned) else None
	
  (** Convert a Cil.fkind into an floatsize option *)
  let convertFkind = function
    | FFloat      -> Some F32
    | FDouble     -> Some F64
    | FLongDouble -> if !option_flonglong then Some F64 else None
	
end

module Cil2CsyntaxTranslator = Cil2Csyntax.Make(TypeSpecifierTranslator)

(* From C to preprocessed C *)

let preprocess ifile ofile =
  let cmd =
    sprintf "%s -D__COMPCERT__ -I%s %s %s > %s"
      Configuration.prepro
      !stdlib_path
      (quote_options !prepro_options)
      ifile ofile in
  if command cmd <> 0 then begin
    safe_remove ofile;
    eprintf "Error during preprocessing.\n";
    exit 2
  end

(* From preprocessed C to asm *)

let compile_c_file sourcename ifile ofile =
  (* Parsing and production of a CIL.file *)
  let cil =
    try
      Frontc.parse ifile ()
    with
    | Frontc.ParseError msg ->
        eprintf "Error during parsing: %s\n" msg;
        exit 2
    | Errormsg.Error ->
        exit 2 in
  (* Remove preprocessed file (always a temp file) *)
  safe_remove ifile;
  (* Restore original source file name *)
  cil.Cil.fileName <- sourcename;
  (* Cleanup in the CIL.file *)
  Rmtmps.removeUnusedTemps ~isRoot:Rmtmps.isExportedRoot cil;
  (* Save CIL output if requested *)
  if !option_dcil then begin
    let ofile = Filename.chop_suffix sourcename ".c" ^ ".cil.c" in
    let oc = open_out ofile in
    Cil.dumpFile Cil.defaultCilPrinter oc ofile cil;
    close_out oc
  end;
  (* Conversion to Csyntax *)
  let csyntax =
    try
      Cil2CsyntaxTranslator.convertFile cil
    with
    | Cil2Csyntax.Error msg ->
        eprintf "%s\n" msg;
        exit 2
  in
  (* Save Csyntax if requested *)
  if !option_dclight then begin
    let ofile = Filename.chop_suffix sourcename ".c" ^ ".light.c" in
    let oc = open_out ofile in
    PrintCsyntax.print_program (Format.formatter_of_out_channel oc) csyntax;
    close_out oc
  end;
  (* Convert to Asm *)
  let ppc =
    match Compiler.transf_c_program csyntax with
    | Errors.OK x -> x
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in
  (* Save asm *)
  let oc = open_out ofile in
  PrintAsm.print_program oc ppc;
  close_out oc

(* From Cminor to asm *)

let compile_cminor_file ifile ofile =
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
    sprintf "%s -o %s %s"
      Configuration.asm ofile ifile in
  let retcode = command cmd in
  if not !option_dasm then safe_remove ifile;
  if retcode <> 0 then begin
    safe_remove ofile;
    eprintf "Error during assembling.\n";
    exit 2
  end

(* Linking *)

let linker exe_name files =
  let cmd =
    sprintf "%s -o %s %s -L%s -lcompcert"
      Configuration.linker
      (Filename.quote exe_name)
      (quote_options files)
      !stdlib_path in
  if command cmd <> 0 then exit 2

(* Processing of a .c file *)

let process_c_file sourcename =
  let prefixname = Filename.chop_suffix sourcename ".c" in
  if !option_E then begin
    preprocess sourcename (prefixname ^ ".i")
  end else begin
    let preproname = Filename.temp_file "compcert" ".i" in
    preprocess sourcename preproname;
    if !option_S then begin
      compile_c_file sourcename preproname (prefixname ^ ".s")
    end else begin
      let asmname =
        if !option_dasm
        then prefixname ^ ".s"
        else Filename.temp_file "compcert" ".s" in
      compile_c_file sourcename preproname asmname;
      assemble asmname (prefixname ^ ".o")
    end
  end;
  prefixname ^ ".o"

(* Processing of a .cm file *)

let process_cminor_file sourcename =
  let prefixname = Filename.chop_suffix sourcename ".cm" in
  if !option_S then begin
    compile_cminor_file sourcename (prefixname ^ ".s")
  end else begin
    let asmname =
      if !option_dasm
      then prefixname ^ ".s"
      else Filename.temp_file "compcert" ".s" in
    compile_cminor_file sourcename asmname;
    assemble asmname (prefixname ^ ".o")
  end;
  prefixname ^ ".o"

(* Command-line parsing *)

let usage_string =
"ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .cm            Cminor source file
  .o             Object file
  .a             Library file
Processing options:
  -E             Preprocess only, save result in <file>.i
  -S             Compile to assembler only, save result in <file>.s
  -c             Compile to object file only (no linking), result in <file>.o
Preprocessing options:
  -I<dir>        Add <dir> to search path for #include files
  -D<symb>=<val> Define preprocessor symbol
  -U<symb>       Undefine preprocessor symbol
Compilation options:
  -flonglong     Treat 'long long' as 'long' and 'long double' as 'double'
  -fmadd         Use fused multiply-add and multiply-sub instructions
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -dcil          Save CIL-processed source in <file>.cil.c
  -dclight       Save generated Clight in <file>.light.c
  -dasm          Save generated assembly in <file>.s
Linking options:
  -l<lib>        Link library <lib>
  -L<dir>        Add <dir> to search path for libraries
  -o <file>      Generate executable in <file> (default: a.out)
General options:
  -stdlib <dir>  Set the path of the Compcert run-time library
  -v             Print external commands before invoking them
"

type action =
  | Set of bool ref
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
    eprintf "Usage: %s" usage;
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

let cmdline_actions = [
  "-[IDU].", Self(fun s -> prepro_options := s :: !prepro_options);
  "-[lL].", Self(fun s -> linker_options := s :: !linker_options);
  "-o$", String(fun s -> exe_name := s);
  "-stdlib$", String(fun s -> stdlib_path := s);
  "-flonglong$", Set option_flonglong;
  "-fmadd$", Set option_fmadd;
  "-fsmall-data$", Integer(fun n -> option_small_data := n);
  "-fsmall-const$", Integer(fun n -> option_small_const := n);
  "-dcil$", Set option_dcil;
  "-dclight$", Set option_dclight;
  "-dasm$", Set option_dasm;
  "-E$", Set option_E;
  "-S$", Set option_S;
  "-c$", Set option_c;
  "-v$", Set option_v;
  ".*\\.c$", Self (fun s ->
      let objfile = process_c_file s in
      linker_options := objfile :: !linker_options);
  ".*\\.cm$", Self (fun s ->
      let objfile = process_cminor_file s in
      linker_options := objfile :: !linker_options);
  ".*\\.[oa]$", Self (fun s ->
      linker_options := s :: !linker_options)
]

let _ =
  Cil.initCIL();
  CPragmas.initialize();
  parse_cmdline cmdline_actions usage_string;
  if !linker_options <> [] 
  && not (!option_c || !option_S || !option_E)
  then begin
    linker !exe_name !linker_options
  end

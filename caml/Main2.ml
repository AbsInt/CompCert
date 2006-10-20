open Printf

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
    | ILongLong  -> (***Some (I32, Signed)***) None
    | IULongLong -> (***Some (I32, Unsigned)***) None
	
  (** Convert a Cil.fkind into an floatsize option *)
  let convertFkind = function
    | FFloat      -> Some F32
    | FDouble     -> Some F64
    | FLongDouble -> (***Some F64***) None
	
end

module Cil2CsyntaxTranslator = Cil2Csyntax.Make(TypeSpecifierTranslator)

let prepro_options = ref []
let save_csyntax = ref false

let preprocess file =
  let temp = Filename.temp_file "compcert" ".i" in
  let cmd =
    sprintf "gcc -arch ppc %s -D__COMPCERT__ -E %s > %s"
      (String.concat " " (List.rev !prepro_options))
      file
      temp in
  if Sys.command cmd = 0
  then temp
  else (eprintf "Error during preprocessing.\n"; exit 2)

let process_c_file sourcename =
  let targetname = Filename.chop_suffix sourcename ".c" in
  (* Preprocessing with cpp *)
  let preproname = preprocess sourcename in
  (* Parsing and production of a CIL.file *)
  let cil =
    try
      Frontc.parse preproname ()
    with
      Frontc.ParseError msg ->
        eprintf "Error during parsing: %s\n" msg;
        exit 2 in
  Sys.remove preproname;
  (* Restore source file name before preprocessing *)
  cil.Cil.fileName <- sourcename;
  (* Cleanup in the CIL.file *)
  Rmtmps.removeUnusedTemps ~isRoot:Rmtmps.isExportedRoot cil;
  (* Conversion to Csyntax *)
  let csyntax =
    try
      Cil2CsyntaxTranslator.convertFile cil
    with
    | Cil2CsyntaxTranslator.Unsupported msg ->
        eprintf "%s\n" msg;
        exit 2
    | Cil2CsyntaxTranslator.Internal_error msg ->
        eprintf "%s\nPlease report it.\n" msg;
        exit 2 in
  (* Save Csyntax if requested *)
  if !save_csyntax then begin
    let oc = open_out (targetname ^ ".light.c") in
    PrintCsyntax.print_program (Format.formatter_of_out_channel oc) csyntax;
    close_out oc
  end;
  (* Convert to PPC *)
  let ppc =
    match Main.transf_c_program csyntax with
    | Datatypes.Some x -> x
    | Datatypes.None ->
        eprintf "Error in translation Csyntax -> PPC\n";
        exit 2 in
  (* Save PPC asm *)
  let oc = open_out (targetname ^ ".s") in
  PrintPPC.print_program oc ppc;
  close_out oc

let process_cminor_file sourcename =
  let targetname = Filename.chop_suffix sourcename ".cm" ^ ".s" in
  let ic = open_in sourcename in
  let lb = Lexing.from_channel ic in
  try
    match Main.transf_cminor_program
            (CMtypecheck.type_program
              (CMparser.prog CMlexer.token lb)) with
    | Datatypes.None ->
        eprintf "Compiler failure\n";
        exit 2
    | Datatypes.Some p ->
        let oc = open_out targetname in
        PrintPPC.print_program oc p;
        close_out oc
  with Parsing.Parse_error ->
         eprintf "File %s, character %d: Syntax error\n"
                 sourcename (Lexing.lexeme_start lb);
         exit 2
     | CMlexer.Error msg ->  
         eprintf "File %s, character %d: %s\n"
                 sourcename (Lexing.lexeme_start lb) msg;
         exit 2
     | CMtypecheck.Error msg ->
         eprintf "File %s, type-checking error:\n%s"
                 sourcename msg;
         exit 2

(* Command-line parsing *)

let starts_with s1 s2 =
  String.length s1 >= String.length s2 &&
  String.sub s1 0 (String.length s2) = s2

let rec parse_cmdline i =
  if i < Array.length Sys.argv then begin
    let s = Sys.argv.(i) in
    if s = "-dump-c" then begin
      save_csyntax := true;
      parse_cmdline (i + 1)
    end else
    if starts_with s "-I" || starts_with s "-D" || starts_with s "-U"
    then begin
      prepro_options := s :: !prepro_options;
      parse_cmdline (i + 1)
    end else 
    if Filename.check_suffix s ".cm" then begin
      process_cminor_file s;
      parse_cmdline (i + 1)
    end else
    if Filename.check_suffix s ".c" then begin
      process_c_file s;
      parse_cmdline (i + 1)
    end else begin
      eprintf "Unknown argument `%s'\n" s;
      exit 2
    end
  end

let _ =
  parse_cmdline 1

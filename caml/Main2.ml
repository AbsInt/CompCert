open Printf
open Datatypes

let process_cminor_file sourcename =
  let targetname = Filename.chop_suffix sourcename ".cm" ^ ".s" in
  let ic = open_in sourcename in
  let lb = Lexing.from_channel ic in
  try
    match Main.transf_cminor_program
            (CMtypecheck.type_program
              (CMparser.prog CMlexer.token lb)) with
    | None ->
        eprintf "Compiler failure\n";
        exit 2
    | Some p ->
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

let process_file filename =
  if Filename.check_suffix filename ".cm" then
    process_cminor_file filename
  else
    raise (Arg.Bad ("unknown file type " ^ filename))

let _ =
  Arg.parse [] process_file
    "Usage: ccomp <options> <files>\nOptions are:"

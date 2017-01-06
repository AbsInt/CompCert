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

(* From asm to object file *)

let assemble source_file ifile =
  let ofile = File.output_filename  ~final:!option_c source_file ".o"
  and ifile_name,stdin = File.input_of_process_file ifile in
  let cmd = List.concat [
    Configuration.asm;
    ["-o"; ofile];
    List.rev !assembler_options;
    [ifile_name]
    ] in
  let exc = command ?stdin:stdin cmd in
  if exc <> 0 then begin
    File.safe_remove ofile;
    command_error "assembler" exc;
    exit 2
  end;
  ofile

let add_pipe () =
  if gnu_system then
     assembler_options :=  "-pipe"::"-xassembler" :: !assembler_options

let assembler_actions =
 [ Prefix "-Wa,", Self (fun s -> if gnu_system then
    assembler_options := s :: !assembler_options
  else
    assembler_options := List.rev_append (explode_comma_option s) !assembler_options);
  Exact "-Xassembler", String (fun s -> if gnu_system then
    assembler_options := s::"-Xassembler":: !assembler_options
  else
    assembler_options := s::!assembler_options );]

let assembler_help =
"Assembling options:\n\
\  -Wa,<opt>      Pass option <opt> to the assembler\n\
\  -Xassembler <opt> Pass <opt> as an option to the assembler\n"

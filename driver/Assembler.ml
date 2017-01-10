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

let assemble ifile ofile =
  let ifile_name,stdin = File.input_of_process_file ifile in
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
  end

let open_assembler_out source_file =
  let ofile = File.output_filename ~final:!option_c source_file ".o"  in
  let ifile,pid =
    if !option_dasm then
      File.file_process_file source_file ".s",None
    else if !option_pipe && Configuration.asm_supports_pipe then
      let process_file = File.pipe_process_file () in
      let ifile,stdin = File.in_descr_of_process_pipe process_file in
      let cmd = List.concat [
          Configuration.asm;
          ["-o"; ofile];
          List.rev !assembler_options;
          [ifile]
        ] in
      Unix.set_close_on_exec (File.out_descr_of_process_file process_file);
      let pid = create_process stdin Unix.stdout cmd in
      if pid = None then begin
        File.safe_remove ofile;
        command_error "assembler" (-1);
        exit 2
      end;
      process_file,pid
    else
      File.temp_process_file ".s",None in
  ofile,ifile,pid

let close_assembler_out file pid ofile =
  match pid with
  | Some pid ->
    let exc = Driveraux.waitpid pid in
    if exc <> 0 then begin
      File.safe_remove ofile;
      command_error "assembler" exc;
      exit 2 end
  | None ->
    assemble file ofile

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

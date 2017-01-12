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

let cmd ifile ofile =
  List.concat [
    Configuration.asm;
    ["-o"; ofile];
    List.rev !assembler_options;
    [ifile]
  ]

let assembler_error ofile exc =
  File.safe_remove ofile;
  command_error "assembler" exc;
  exit 2

let assemble ifile ofile =
  let cmd = cmd ifile ofile in
  let exc = command  cmd in
  if exc <> 0 then begin
    File.safe_remove ofile;
    command_error "assembler" exc;
    exit 2
  end

type assembler_handle =
  | File of string * string
  | Process of string * Driveraux.process_info

let open_assembler_out source_file =
  let ofile = File.output_filename ~final:!option_c source_file ".o"  in
  if !option_pipe && Configuration.asm_supports_pipe && not !option_dasm then
    let cmd = cmd "-" ofile in
    let pid = open_process_out cmd in
    match pid with
    | None -> assembler_error ofile (-1)
    | Some (pid,oc) -> oc,(Process (ofile,pid))
  else
    let ifile = if !option_dasm then
        File.output_filename source_file ".s"
      else
        File.temp_file ".s" in
    open_out_bin(ifile),File (ifile,ofile)

let close_assembler_out oc handle =
  match handle with
  | File (ifile,ofile) ->
    close_out oc;
    assemble ifile ofile;ofile
  | Process (ofile,pid) ->
    let exc = Driveraux.close_process_out pid oc in
    if exc <> 0 then begin
      File.safe_remove ofile;
      command_error "assembler" exc;
      exit 2 end;
    ofile

let add_pipe () =
  if Configuration.gnu_toolchain then
     assembler_options :=  "-pipe"::"-xassembler" :: !assembler_options

let assembler_actions =
 [ Prefix "-Wa,", Self (fun s -> if Configuration.gnu_toolchain then
    assembler_options := s :: !assembler_options
  else
    assembler_options := List.rev_append (explode_comma_option s) !assembler_options);
  Exact "-Xassembler", String (fun s -> if Configuration.gnu_toolchain then
    assembler_options := s::"-Xassembler":: !assembler_options
  else
    assembler_options := s::!assembler_options );]

let assembler_help =
"Assembling options:\n\
\  -Wa,<opt>      Pass option <opt> to the assembler\n\
\  -Xassembler <opt> Pass <opt> as an option to the assembler\n"

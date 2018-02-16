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
  Diagnostics.raise_on_errors ();
  let cmd = List.concat [
    Configuration.asm;
    ["-o"; ofile];
    List.rev !assembler_options;
    [ifile]
  ] in
  let exc = command cmd in
  if exc <> 0 then begin
    safe_remove ofile;
    command_error "assembler" exc
  end

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
{|Assembling options:
  -Wa,<opt>      Pass option <opt> to the assembler
  -Xassembler <opt> Pass <opt> as an option to the assembler
|}

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

open Printf
open Clflags

(* Invocation of external tools *)

let rec waitpid_no_intr pid =
  try Unix.waitpid [] pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_no_intr pid

let command ?stdout args =
  if !option_v then begin
    eprintf "+ %s" (String.concat " " args);
    begin match stdout with
    | None -> ()
    | Some f -> eprintf " > %s" f
    end;
    prerr_endline ""
  end;
  let argv = Array.of_list args in
  assert (Array.length argv > 0);
  try
    let fd_out =
      match stdout with
      | None -> Unix.stdout
      | Some f ->
          Unix.openfile f [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o666 in
    let pid =
      Unix.create_process argv.(0) argv Unix.stdin fd_out Unix.stderr in
    let (_, status) =
      waitpid_no_intr pid in
    if stdout <> None then Unix.close fd_out;
    match status with
    | Unix.WEXITED rc -> rc
    | Unix.WSIGNALED n | Unix.WSTOPPED n ->
        eprintf "Command '%s' killed on a signal.\n" argv.(0); -1
  with Unix.Unix_error(err, fn, param) ->
    eprintf "Error executing '%s': %s: %s %s\n"
            argv.(0) fn (Unix.error_message err) param;
    -1

let command_error n exc =
  eprintf "Error: %s command failed with exit code %d (use -v to see invocation)\n" n exc

let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()


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

(* All input files should exist *)

let ensure_inputfile_exists name =
  if not (Sys.file_exists name) then begin
    eprintf "error: no such file or directory: '%s'\n" name;
    exit 2
  end

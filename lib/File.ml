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


type input_file =
  {
    name : string;
    suffix: string;
  }

let new_input_file file suffix =
  if not (Sys.file_exists file) then begin
    eprintf "error: no such file or directory: '%s'\n" file;
    exit 2
  end;
  {
    name = file;
    suffix = suffix;
  }

let input_name file = file.name

let open_input_file file =
  open_in_bin file.name



(* Safe removal of files *)
let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()

(* Generate a temporary file with the given suffix that is removed on exit *)
let temp_file suffix =
  let file = Filename.temp_file "compcert" suffix in
  at_exit (fun () -> safe_remove file);
  file


(* Determine names for output files.  We use -o option if specified
   and if this is the final destination file (not a dump file).
   Otherwise, we generate a file in the current directory. *)
let output_filename ?(final = false) source_file output_suffix =
  match !option_o with
  | Some file when final -> file
  | _ ->
    Filename.basename (Filename.chop_suffix source_file.name source_file.suffix)
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

type process_file =
  | Pipe of Unix.file_descr * Unix.file_descr
  | Tmpfile of string
  | File of string


let temp_process_file ?(supports_pipe=true) suffix =
  if !option_pipe && supports_pipe then
    let ic,oc = Unix.pipe () in
    Pipe (ic,oc)
  else
    Tmpfile (temp_file suffix)

let file_process_file ?(final = false) source_file output_suffix =
  File (output_filename ~final:final source_file output_suffix)

let process_file_of_input_file f =
  File f.name

let in_channel_of_process_file = function
  | Pipe (ic,_) -> Unix.in_channel_of_descr ic
  | Tmpfile f
  | File f -> open_in_bin f

let input_of_process_file = function
  | Pipe (ic,_) -> "-",Some ic
  | Tmpfile f
  | File f -> f,None

let out_channel_of_process_file = function
  | Pipe (_,oc) -> Unix.out_channel_of_descr oc
  | Tmpfile f
  | File f -> open_out_bin f

let out_descr_of_process_file = function
  | Pipe (_,oc) -> oc
  | Tmpfile f
  | File f ->  Unix.openfile f [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o666

let safe_remove_process_file = function
  | Pipe _ -> ()
  | Tmpfile f
  | File f -> safe_remove f

let process_file_name = function
  | Pipe _ -> "pipe"
  | Tmpfile f
  | File f -> f

let process_file_default () =
  match !option_o with
  | Some file -> Some (File file)
  | None -> None

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

(* Create a new input file and ensure it's existence *)
let new_input_file file suffix =
  if not (Sys.file_exists file) then begin
    eprintf "error: no such file or directory: '%s'\n" file;
    exit 2
  end;
  {
    name = file;
    suffix = suffix;
  }

(* Get the name of the input file *)
let input_name file = file.name

(* Get the input channel from the input file *)
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

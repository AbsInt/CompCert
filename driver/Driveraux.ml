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

(* Safe removal of files *)
let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()

(* Invocation of external tools *)

let rec waitpid_no_intr pid =
  try Unix.waitpid [] pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_no_intr pid

let command stdout args =
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

let command ?stdout args =
  if !option_v then begin
    eprintf "+ %s" (String.concat " " args);
    begin match stdout with
    | None -> ()
    | Some f -> eprintf " > %s" f
    end;
    prerr_endline ""
  end;
  let resp = Sys.win32 && Configuration.response_file_style <> Configuration.Unsupported in
  if resp && List.fold_left (fun len arg -> len + String.length arg + 1) 0 args > 7000 then
    let quote,prefix = match Configuration.response_file_style with
    | Configuration.Unsupported -> assert false
    | Configuration.Gnu -> Responsefile.gnu_quote,"@"
    | Configuration.Diab -> Responsefile.diab_quote,"-@" in
    let file,oc = Filename.open_temp_file "compcert" "" in
    let cmd,args = match args with
    | cmd::args -> cmd,args
    | [] -> assert false (* Should never happen *) in
    List.iter (fun a -> Printf.fprintf oc "%s " (quote a)) args;
    close_out oc;
    let arg = prefix^file in
    let ret = command stdout [cmd;arg] in
    safe_remove file;
    ret
  else
    command stdout args

let command_error n exc =
  eprintf "Error: %s command failed with exit code %d (use -v to see invocation)\n" n exc


(* Determine names for output files.  We use -o option if specified
   and if this is the final destination file (not a dump file).
   Otherwise, we generate a file in the current directory. *)

let output_filename ?(final = false) source_file source_suffix output_suffix =
  match !option_o with
  | Some file when final -> file
  | _ ->
    Filename.basename (Filename.chop_suffix source_file source_suffix)
    ^ output_suffix

(* All input files should exist *)

let ensure_inputfile_exists name =
  if not (Sys.file_exists name) then begin
    eprintf "error: no such file or directory: '%s'\n" name;
    exit 2
  end
(* Printing of error messages *)

let print_errorcodes file msg =
  let print_one_error oc = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (Camlcoq.P.to_int32 i)
  in
  eprintf "%s: %a\n" file (fun oc msg -> List.iter (print_one_error oc) msg) msg;
  exit 2

(* Command-line parsing *)
let explode_comma_option s =
  match Str.split (Str.regexp ",") s with
  | [] -> assert false
  | _ :: tl -> tl

(* Record actions to be performed after parsing the command line *)
type action =
  | File_action of ((string -> string) * string)
  | Linker_action of string

let actions : action list ref = ref []

let push_action fn arg =
  actions := File_action(fn, arg) :: !actions

let push_linker_arg arg =
  actions := Linker_action arg :: !actions

let perform_actions () =
  let rec perform = function
  | [] -> []
  | act :: rem -> let res = action act in res :: perform rem
  and action = function
    | File_action (f,s) -> f s
    | Linker_action s -> s
  in perform (List.rev !actions)

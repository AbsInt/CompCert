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


let response_file args =
  let resp = Sys.win32 && Configuration.response_file_style <> Configuration.Unsupported in
  if resp && List.fold_left (fun len arg -> len + String.length arg + 1) 0 args > 7000 then
    let quote,prefix = match Configuration.response_file_style with
      | Configuration.Unsupported -> assert false
      | Configuration.Gnu -> Responsefile.gnu_quote,"@"
      | Configuration.Diab -> Responsefile.diab_quote,"-@" in
    let file = File.temp_file "" in
    let oc = open_out_bin file in
    let cmd,args = match args with
      | cmd::args -> cmd,args
      | [] -> assert false (* Should never happen *) in
    List.iter (fun a -> Printf.fprintf oc "%s " (quote a)) args;
    close_out oc;
    [|cmd;prefix^file|]
  else
    Array.of_list args

let print_error proc err fn param =
  eprintf "Error executing '%s': %s: %s %s"
    proc fn (Unix.error_message err) param;
  prerr_endline ""

type process_info = (int * string)

let waitpid (pid,proc) =
  try
    let (_, status) =
      waitpid_no_intr pid in
    match status with
    | Unix.WEXITED rc ->
      rc
    | Unix.WSIGNALED n | Unix.WSTOPPED n ->
      eprintf "Command '%s' killed on a signal.\n" proc; -1
  with Unix.Unix_error (err,fn,param) ->
    print_error proc err fn param;
    -1

let create_process fd_in fd_out args =
  let argv = response_file args in
  assert (Array.length argv > 0);
  let pid = Unix.create_process argv.(0) argv fd_in fd_out Unix.stderr in
  (pid,argv.(0))


let open_process_out args =
  if !option_v then begin
    eprintf "+ %s" (String.concat " " args);
    prerr_endline ""
  end;
  try
    let fd_in,fd_out = Unix.pipe () in
    Unix.set_close_on_exec fd_out;
    let proc = create_process fd_in Unix.stdout args in
    Unix.close fd_in;
    Some (proc,Unix.out_channel_of_descr fd_out)
  with Unix.Unix_error (err,fn,param) ->
    print_error (List.hd args) err fn param;
    None

let close_process_out proc oc =
  close_out_noerr oc;
  let rc = waitpid proc in
  rc

let open_process_in args =
  if !option_v then begin
    eprintf "+ %s" (String.concat " " args);
    prerr_endline ""
  end;
  try
    let fd_in,fd_out = Unix.pipe () in
    Unix.set_close_on_exec fd_in;
    let proc = create_process Unix.stdin fd_out args in
    Unix.close fd_out;
    Some (proc,Unix.in_channel_of_descr fd_in)
  with Unix.Unix_error (err,fn,param) ->
    print_error (List.hd args) err fn param;
    None

let close_process_in proc ic =
  let rc = waitpid proc in
  close_in_noerr ic;
  rc

let command ?stdout args =
  if !option_v then begin
    eprintf "+ %s" (String.concat " " args);
    begin match stdout with
    | None -> ()
    | Some f -> eprintf " > %s" f
    end;
    prerr_endline ""
  end;
  let fd_out =
    match stdout with
    | None -> Unix.stdout
    | Some f -> Unix.openfile f [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o666 in
  try
    let pid = create_process Unix.stdin fd_out args in
    let rc = waitpid pid in
    if stdout <> None then Unix.close fd_out;
    rc
  with Unix.Unix_error (err,fn,param) ->
    print_error (List.hd args) err fn param;
    -1

let command_error n exc =
  eprintf "Error: %s command failed with exit code %d (use -v to see invocation)\n" n exc

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
  | File_action of ((File.input_file -> string) * File.input_file)
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

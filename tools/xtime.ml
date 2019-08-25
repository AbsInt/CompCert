(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Timing the execution of a command, with more options than the
   standard Unix "time" utility. *)

open Printf

let outfile = ref ""
let errfile = ref ""
let command_name = ref ""
let num_runs = ref 1
let min_runs = ref 0
let min_time = ref 0.0
let print_sys = ref false

let error fmt =
  eprintf "Error: "; kfprintf (fun _ -> exit 2) stderr fmt

let open_file out dfl =
  if out = ""
  then dfl
  else Unix.(openfile out [O_WRONLY; O_CREAT; O_TRUNC] 0o666)

let close_file out fd =
  if out <> "" then Unix.close fd
  
let run1 (cmd, args) =
  let fd_out = open_file !outfile Unix.stdout in
  let fd_err = open_file !errfile Unix.stderr in
  let pid =
    Unix.create_process cmd (Array.of_list (cmd :: args))
                        Unix.stdin fd_out fd_err in
  close_file !outfile fd_out;
  close_file !errfile fd_err;
  let (_, st) = Unix.waitpid [] pid in
  match st with
  | Unix.WEXITED 127 -> error "cannot execute '%s'\n" cmd
  | Unix.WSIGNALED signo -> error "terminated by signal %d\n" signo
  | _ -> ()

let run (cmd, arg) =
  let rec repeat n =
    run1 (cmd, arg);
    if (!min_time > 0.0 && Unix.((times()).tms_cutime) < !min_time)
    || (!min_runs > 0 && n < !min_runs)
    || n < !num_runs
    then repeat (n + 1)
    else n in
  let n = repeat 1 in
  let ts = Unix.times() in
  let cmdname = if !command_name <> "" then !command_name else cmd in
  if !print_sys then
    Printf.printf "%.3f usr + %.3f sys %s\n"
                  (ts.Unix.tms_cutime /. float n)
                  (ts.Unix.tms_cstime /. float n)
                  cmdname
  else
    Printf.printf "%.3f %s\n"
                  (ts.Unix.tms_cutime /. float n)
                  cmdname

let _ =
  let cmd_and_args = ref [] in
  Arg.parse [
    "-o", Arg.Set_string outfile,
      " <file>  Redirect standard output of command to <file>";
    "-e", Arg.Set_string outfile,
      " <file>  Redirect standard error of command to <file>";
    "-name", Arg.Set_string command_name,
      " <name>  Name of command to report along with the time";
    "-repeat", Arg.Int (fun n -> num_runs := n),
      " <N>  Run the command N times";
    "-mintime", Arg.Float (fun f -> min_time := f),
      " <T>  Repeatedly run the command for a total duration of at least T seconds";
    "-minruns", Arg.Int (fun n -> num_runs := n),
      " <N>  Run the command at least N times (to be used in conjunction with -mintime)";
    "-sys", Arg.Set print_sys,
      "  Print system time (spent in the OS) in addition to user time (spent in the command)";
    "--", Arg.Rest (fun s -> cmd_and_args := s :: !cmd_and_args),
      " <executable> <arguments>   Specify the executable to time, with its arguments"
  ]
  (fun s -> raise (Arg.Bad (sprintf "Don't know what to do with '%s'" s)))
  "Usage: xtime [options] -- <executable> [arguments].\n\nOptions are:";
  match List.rev !cmd_and_args with
  | [] ->
      error "No command to execute\n"
  | cmd :: args ->
      Unix.handle_unix_error run (cmd, args)

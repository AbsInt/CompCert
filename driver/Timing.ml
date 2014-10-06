(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Clflags

(** Timing facility *)

let timers : (string * float) list ref = ref []

let add_to_timer name time =
  let rec add = function
  | [] -> [name, time]
  | (name1, time1 as nt1) :: rem ->
      if name1 = name then (name1, time1 +. time) :: rem else nt1 :: add rem
  in timers := add !timers

let time name fn arg =
  if not !option_timings then
    fn arg
  else begin
    let start = Sys.time() in
    try
      let res = fn arg in
      add_to_timer name (Sys.time() -. start);
      res
    with x ->
      add_to_timer name (Sys.time() -. start);
      raise x
  end

let time2 name fn arg1 arg2 = time name (fun () -> fn arg1 arg2) ()
let time3 name fn arg1 arg2 arg3 = time name (fun () -> fn arg1 arg2 arg3) ()

let time_coq name fn arg =
  if not !option_timings then
    fn arg
  else begin
    let start = Sys.time() in
    try
      let res = fn arg in
      add_to_timer (Camlcoq.camlstring_of_coqstring name) (Sys.time() -. start);
      res
    with x ->
      add_to_timer (Camlcoq.camlstring_of_coqstring name) (Sys.time() -. start);
      raise x
  end

let print_timers () =
  if !option_timings then
    List.iter
      (fun (name, time) -> Printf.printf "%7.2fs  %s\n" time name)
      !timers

let _ = at_exit print_timers

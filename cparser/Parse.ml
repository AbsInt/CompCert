(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(* Entry point for the library: parse, elaborate, and transform *)

module CharSet = Set.Make(struct type t = char let compare = compare end)

let transform_program t p =
  let run_pass pass flag p =
    if CharSet.mem flag t then begin
      let p = pass p in
      Diagnostics.check_errors ();
      p
    end else
      p
  in
    p
    |> run_pass Unblock.program 'b'
    |> run_pass PackedStructs.program 'p'
    |> run_pass StructPassing.program 's'
    |> Rename.program

let parse_transformations s =
  let t = ref CharSet.empty in
  let set s = String.iter (fun c -> t := CharSet.add c !t) s in
  String.iter
    (function 'b' -> set "b"
            | 's' -> set "s"
            | 'p' -> set "bp"
            |  _  -> ())
    s;
  !t

let read_file sourcefile =
  let ic = open_in_bin sourcefile in
  let n = in_channel_length ic in
  let text = really_input_string ic n in
  close_in ic;
  text

let parse_string name text =
  let log_fuel = Camlcoq.Nat.of_int 50 in
  match
    Parser.translation_unit_file log_fuel (Lexer.tokens_stream name text)
  with
  | Parser.MenhirLibParser.Inter.Parsed_pr (ast, _ ) ->
      (ast: Cabs.definition list)
  | _ -> (* Fail_pr or Fail_pr_full or Timeout_pr, depending
            on the version of Menhir.
            Fail_pr{,_full} means that there's an inconsistency
            between the pre-parser and the parser.
            Timeout_pr means that we ran for 2^50 steps. *)
      Diagnostics.fatal_error Diagnostics.no_loc "internal error while parsing"

let preprocessed_file transfs name sourcefile =
  Diagnostics.reset();
  let check_errors x =
    Diagnostics.check_errors(); x in
  (* Reading the whole file at once may seem costly, but seems to be
     the simplest / most robust way of accessing the text underlying
     a range of positions. This is used when printing an error message.
     Plus, I note that reading the whole file into memory leads to a
     speed increase: "make -C test" speeds up by 3 seconds out of 40
     on my machine. *)
  read_file sourcefile
  |> Timing.time2 "Parsing" parse_string name
  |> Timing.time "Elaboration" Elab.elab_file
  |> check_errors
  |> Timing.time2 "Emulations" transform_program (parse_transformations transfs)
  |> check_errors

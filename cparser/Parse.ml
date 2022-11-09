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

let transform_program ~unblock ~switch_norm ~struct_passing ~packed_structs p =
  let run_pass pass p =
    let p' = pass p in Diagnostics.check_errors (); p' in
  let run_opt_pass pass flag p =
    if flag then run_pass pass p else p
  and run_opt_pass3 pass flag p =
    match flag with
    | `Off -> p
    | `Partial -> run_pass (pass false) p
    | `Full -> run_pass (pass true) p in
  let unblock = unblock || switch_norm <> `Off || packed_structs in
  p
  |> run_opt_pass Unblock.program unblock
  |> run_opt_pass3 SwitchNorm.program switch_norm
  |> run_opt_pass PackedStructs.program packed_structs
  |> run_opt_pass StructPassing.program struct_passing
  |> Rename.program

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

let preprocessed_file ?(unblock = false)
                      ?(switch_norm = `Off)
                      ?(struct_passing = false)
                      ?(packed_structs = false)
                      name sourcefile =
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
  |> Timing.time "Emulations"
      (transform_program ~unblock ~switch_norm ~struct_passing ~packed_structs)
  |> check_errors

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

(* Entry point for the library: parse, elaborate, and transform *)

module CharSet = Set.Make(struct type t = char let compare = compare end)

let transform_program t p name =
  let run_pass pass flag p = if CharSet.mem flag t then pass p else p in
  let p1 = (run_pass StructPassing.program 's'
  (run_pass PackedStructs.program 'p'
  (run_pass Unblock.program 'b'
  (run_pass Bitfields.program 'f'
     p)))) in
  Rename.program p1

let parse_transformations s =
  let t = ref CharSet.empty in
  let set s = String.iter (fun c -> t := CharSet.add c !t) s in
  String.iter
    (function 'b' -> set "b"
            | 's' -> set "s"
            | 'f' -> set "bf"
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

let preprocessed_file transfs name sourcefile =
  Diagnostics.reset();
  (* Reading the whole file at once may seem costly, but seems to be
     the simplest / most robust way of accessing the text underlying
     a range of positions. This is used when printing an error message.
     Plus, I note that reading the whole file into memory leads to a
     speed increase: "make -C test" speeds up by 3 seconds out of 40
     on my machine. *)
  let text = read_file sourcefile in
  let p =
      let t = parse_transformations transfs in
      let rec inf = Datatypes.S inf in
      let ast : Cabs.definition list =
        Obj.magic
          (match Timing.time "Parsing"
              (* The call to Lexer.tokens_stream results in the pre
                 parsing of the entire file. This is non-negligeabe,
                 so we cannot use Timing.time2 *)
              (fun () ->
                Parser.translation_unit_file inf (Lexer.tokens_stream name text)) ()
           with
             | Parser.Parser.Inter.Fail_pr ->
                 (* Theoretically impossible : implies inconsistencies
                    between grammars. *)
               Diagnostics.fatal_error Diagnostics.no_loc "internal error while parsing"
             | Parser.Parser.Inter.Timeout_pr -> assert false
             | Parser.Parser.Inter.Parsed_pr (ast, _ ) -> ast) in
      let p1 = Timing.time "Elaboration" Elab.elab_file ast in
      Diagnostics.check_errors ();
      Timing.time2 "Emulations" transform_program t p1 name in
  Diagnostics.check_errors();
  p

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
  let p1 = (run_pass StructReturn.program 's'
  (run_pass PackedStructs.program 'p'
  (run_pass Unblock.program 'b'
  (run_pass Bitfields.program 'f'
  p)))) in
  let debug = 
    if !Clflags.option_g && Configuration.advanced_debug then
      Some (CtoDwarf.program_to_dwarf p p1 name)
    else
      None in
  (Rename.program p1 (Filename.chop_suffix name ".c")),debug

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

let preprocessed_file transfs name sourcefile =
  Cerrors.reset();
  let ic = open_in sourcefile in
  let p,d =
    try
      let t = parse_transformations transfs in
      let lb = Lexer.init name ic in
      let rec inf = Datatypes.S inf in
      let ast : Cabs.definition list =
        Obj.magic
          (match Timing.time2 "Parsing"
                 Parser.translation_unit_file inf (Lexer.tokens_stream lb) with
             | Parser.Parser.Inter.Fail_pr ->
                 (* Theoretically impossible : implies inconsistencies
                    between grammars. *)
                 Cerrors.fatal_error "Internal error while parsing"
             | Parser.Parser.Inter.Timeout_pr -> assert false
             | Parser.Parser.Inter.Parsed_pr (ast, _ ) -> ast) in
      let p1 = Timing.time "Elaboration" Elab.elab_file ast in
      Timing.time2 "Emulations" transform_program t p1 name
    with
    | Cerrors.Abort ->
        [],None in
  close_in ic;
  if Cerrors.check_errors() then None,None else Some p,d

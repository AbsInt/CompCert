(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*        Bernhard Schommer, AbsInt Angewandte Informatik GmbH         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)


{
(* To accumulate the characters in a word or quoted string *)
let buf = Buffer.create 32

(* Add the current contents of buf to the list of words seen so far,
   taking care not to add empty strings unless warranted (e.g. quoted) *)
let stash inword words =
  if inword then begin
    let w = Buffer.contents buf in
    Buffer.clear buf;
    w :: words
  end else
    words

}

let whitespace = [' ' '\t' '\012' '\r' '\n']

let backslashes_even = "\\\\"*        (* an even number of backslashes *)
let backslashes_odd  = "\\\\"* '\\'   (* an odd number of backslashes *)

(* GNU-style quoting *)
(* "Options in file are separated by whitespace.  A whitespace
    character may be included in an option by surrounding the entire
    option in either single or double quotes.  Any character (including
    a backslash) may be included by prefixing the character to be
    included with a backslash.  The file may itself contain additional
    @file options; any such options will be processed recursively." *)

rule gnu_unquoted inword words = parse
  | eof           { List.rev (stash inword words) }
  | whitespace+   { gnu_unquoted false (stash inword words) lexbuf }
  | '\''          { gnu_single_quote lexbuf; gnu_unquoted true words lexbuf }
  | '\"'          { gnu_double_quote lexbuf; gnu_unquoted true words lexbuf }
  | ""            { gnu_one_char lexbuf; gnu_unquoted true words lexbuf }

and gnu_one_char = parse
  | '\\' (_ as c) { Buffer.add_char buf c }
  | _ as c        { Buffer.add_char buf c }

and gnu_single_quote = parse
  | eof           { () (* tolerance *) }
  | '\''          { () }
  | ""            { gnu_one_char lexbuf; gnu_single_quote lexbuf }

and gnu_double_quote = parse
  | eof           { () (* tolerance *) }
  | '\"'          { () }
  | ""            { gnu_one_char lexbuf; gnu_double_quote lexbuf }

{

let re_responsefile = Str.regexp "@\\(.*\\)$"

exception Error of string

let expandargv argv =
  let rec expand_arg seen arg k =
    if not (Str.string_match re_responsefile arg 0) then
      arg :: k
    else begin
      let filename = Str.matched_group 1 arg in
      if List.mem filename seen then
        raise (Error ("cycle in response files: " ^ filename));
      let ic = open_in filename in
      let words = gnu_unquoted false [] (Lexing.from_channel ic) in
      close_in ic;
      expand_args (filename :: seen) words k
    end
  and expand_args seen args k =
    match args with
    | [] -> k
    | a1 :: al -> expand_args seen al (expand_arg seen a1 k)
  in
  let args = Array.to_list argv in
   Array.of_list (List.rev (expand_args [] args []))

(* This function reimplements quoting of writeargv from libiberty *)
let gnu_quote arg =
  let len = String.length arg in
  let buf = Buffer.create len in
  String.iter (fun c -> begin match c with
    | ' ' | '\t' | '\r' | '\n' | '\\' | '\'' | '"' ->
        Buffer.add_char buf '\\'
    | _ -> () end;
    Buffer.add_char buf c) arg;
  Buffer.contents buf

let re_quote = Str.regexp ".*[ \t\n\r\"]"

let diab_quote arg =
  let buf = Buffer.create ((String.length arg) + 8) in
  let doublequote = Str.string_match re_quote arg 0 in
  if doublequote then begin
    Buffer.add_char buf '"';
    String.iter (fun c ->
      if c = '"' then Buffer.add_char buf '\\';
      Buffer.add_char buf c) arg;
    if doublequote then Buffer.add_char buf '"';
    Buffer.contents buf
  end else
    arg
}

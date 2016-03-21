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

(* Parse a string as a list of tokens *)

let identstart = [ '0'-'9' 'A'-'Z' 'a'-'z' '$' '_' ]
let identcont  = [ '0'-'9' 'A'-'Z' 'a'-'z' '$' '_' '-' '.' ]

rule tokenize acc = parse
  | eof                 { List.rev acc }
  | [' ' '\t' '\n' '\r'] +   { tokenize acc lexbuf }
  | "\""                { tok_dquote acc (Buffer.create 16) lexbuf }
  | "'"                 { tok_squote acc (Buffer.create 16) lexbuf }
  | (identstart identcont*) as s
                        { tokenize (s :: acc) lexbuf }
  | _ as c              { tokenize (String.make 1 c :: acc) lexbuf }

and tok_dquote acc buf = parse
  | "\"" | eof          { tokenize (Buffer.contents buf :: acc) lexbuf }
  | "\\t"               { Buffer.add_char buf '\t'; tok_dquote acc buf lexbuf }
  | "\\n"               { Buffer.add_char buf '\n'; tok_dquote acc buf lexbuf }
  | "\\r"               { Buffer.add_char buf '\r'; tok_dquote acc buf lexbuf }
  | "\\" ([ '\\' '\"' ] as c)
                        { Buffer.add_char buf c; tok_dquote acc buf lexbuf }
  | _ as c              { Buffer.add_char buf c; tok_dquote acc buf lexbuf }

and tok_squote acc buf = parse
  | "\'" | eof          { tokenize (Buffer.contents buf :: acc) lexbuf }
  | _ as c              { Buffer.add_char buf c; tok_squote acc buf lexbuf }

{
let string s =
  tokenize [] (Lexing.from_string s)
}

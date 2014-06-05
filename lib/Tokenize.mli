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

val string: string -> string list
  (** [Tokenize.string s] decomposes [s] into a list of tokens.
      Whitespace separates tokens.  The following substrings
      constitute tokens:
    - A string enclosed in double quotes.  Within the string,
      the escape sequences '\t' '\n' '\"' and '\\' are recognized.
      The token value is the contents of the string without the
      enclosing double quotes.
    - A string enclosed in single quotes.  No escape sequences are
      recognized.  The token value is the contents of the string without the
      enclosing single quotes.
    - A sequence of letters, digits, or the [_], [$], [-] and [.]
      characters.  [-] and [.] cannot appear as the first character.
    - Any other non-whitespace character is treated as a separate token
      of length 1.
  *)

(* $Id: CMlexer.mli,v 1.1 2005/01/21 13:11:07 xleroy Exp $ *)

val token: Lexing.lexbuf -> CMparser.token
exception Error of string

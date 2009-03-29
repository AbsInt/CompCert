(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
(* A simple lexical analyzer for constructing CIL based on format strings *)
{
open Formatparse
exception Eof
exception InternalError of string
module H = Hashtbl
module E = Errormsg
(*
** Keyword hashtable
*)
let keywords = H.create 211

(*
** Useful primitives
*)
let scan_ident id = 
  try H.find keywords id
  with Not_found -> IDENT id  (* default to variable name *)

(*
** Buffer processor
*)
 

let init ~(prog: string) : Lexing.lexbuf =
  H.clear keywords;
  Lexerhack.currentPattern := prog;
  List.iter 
    (fun (key, token) -> H.add keywords key token)
    [ ("const", CONST); ("__const", CONST); ("__const__", CONST);
      ("static", STATIC);
      ("extern", EXTERN);
      ("long", LONG);
      ("short", SHORT);
      ("signed", SIGNED);
      ("unsigned", UNSIGNED);
      ("volatile", VOLATILE);
      ("char", CHAR);
      ("int", INT);
      ("float", FLOAT);
      ("double", DOUBLE);
      ("void", VOID);
      ("enum", ENUM);
      ("struct", STRUCT);
      ("typedef", TYPEDEF);
      ("union", UNION);
      ("break", BREAK);
      ("continue", CONTINUE);
      ("goto", GOTO); 
      ("return", RETURN);
      ("switch", SWITCH);
      ("case", CASE); 
      ("default", DEFAULT);
      ("while", WHILE);  
      ("do", DO);  
      ("for", FOR);
      ("if", IF);
      ("else", ELSE);
      ("__attribute__", ATTRIBUTE); ("__attribute", ATTRIBUTE);
      ("__int64", INT64);
      ("__builtin_va_arg", BUILTIN_VA_ARG);
    ];
  E.startParsingFromString prog

let finish () = 
  E.finishParsing ()

(*** Error handling ***)
let error msg =
  E.parse_error msg 


(*** escape character management ***)
let scan_escape str =
  match str with
    "n" -> "\n"
  | "r" -> "\r"
  | "t" -> "\t"
  | "b" -> "\b"
  | "f" -> "\012"  (* ASCII code 12 *)
  | "v" -> "\011"  (* ASCII code 11 *)
  | "a" -> "\007"  (* ASCII code 7 *)
  | "e" -> "\027"  (* ASCII code 27. This is a GCC extension *)
  | _ -> str

let get_value chr =
  match chr with
    '0'..'9' -> (Char.code chr) - (Char.code '0')
  | 'a'..'z' -> (Char.code chr) - (Char.code 'a') + 10
  | 'A'..'Z' -> (Char.code chr) - (Char.code 'A') + 10
  | _ -> 0
let scan_hex_escape str =
  String.make 1 (Char.chr (
		 (get_value (String.get str 0)) * 16
		   + (get_value (String.get str 1))
	           ))
let scan_oct_escape str =
  (* weimer: wide-character constants like L'\400' may be bigger than
   * 256 (in fact, may be up to 511), so Char.chr cannot be used directly *)
  let the_value = (get_value (String.get str 0)) * 64
		   + (get_value (String.get str 1)) * 8
		   + (get_value (String.get str 2)) in
  if the_value < 256 then String.make 1 (Char.chr the_value )
  else (String.make 1 (Char.chr (the_value / 256))) ^
       (String.make 1 (Char.chr (the_value mod 256)))

(* ISO standard locale-specific function to convert a wide character
 * into a sequence of normal characters. Here we work on strings. 
 * We convert L"Hi" to "H\000i\000" *)
let wbtowc wstr =
  let len = String.length wstr in 
  let dest = String.make (len * 2) '\000' in 
  for i = 0 to len-1 do 
    dest.[i*2] <- wstr.[i] ;
  done ;
  dest

(* This function converst the "Hi" in L"Hi" to { L'H', L'i', L'\0' } *)
let wstr_to_warray wstr =
  let len = String.length wstr in
  let res = ref "{ " in
  for i = 0 to len-1 do
    res := !res ^ (Printf.sprintf "L'%c', " wstr.[i])
  done ;
  res := !res ^ "}" ;
  !res

let getArgName (l: Lexing.lexbuf) (prefixlen: int) =
  let lexeme = Lexing.lexeme l in
  let ll = String.length lexeme in
  if  ll > prefixlen then 
    String.sub lexeme (prefixlen + 1) (ll - prefixlen - 1)
  else
    ""
}

let decdigit = ['0'-'9']
let octdigit = ['0'-'7']
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F']
let letter = ['a'- 'z' 'A'-'Z']

let floatsuffix = ['f' 'F' 'l' 'L']

let usuffix = ['u' 'U']
let lsuffix = "l"|"L"|"ll"|"LL"
let intsuffix = lsuffix | usuffix | usuffix lsuffix | lsuffix usuffix

let intnum = decdigit+ intsuffix?
let octnum = '0' octdigit+ intsuffix?
let hexnum = '0' ['x' 'X'] hexdigit+ intsuffix?

let exponent = ['e' 'E']['+' '-']? decdigit+
let fraction  = '.' decdigit+
let floatraw = (intnum? fraction)
			|(intnum exponent)
			|(intnum? fraction exponent)
			|(intnum '.') 
                        |(intnum '.' exponent) 
let floatnum = floatraw floatsuffix?

let ident = (letter|'_')(letter|decdigit|'_')* 
let attribident = (letter|'_')(letter|decdigit|'_'|':')
let blank = [' ' '\t' '\012' '\r']
let escape = '\\' _
let hex_escape = '\\' ['x' 'X'] hexdigit hexdigit
let oct_escape = '\\' octdigit  octdigit octdigit


(* The arguments are of the form %l:foo *)
let argname = ':' ident

rule initial =
	parse 	blank			{ initial lexbuf}
|               "/*"			{ let _ = comment lexbuf in 
                                          initial lexbuf}
|               "//"                    { endline lexbuf }
|               "\n"                    { E.newline (); initial lexbuf}
|		floatnum		{CST_FLOAT (Lexing.lexeme lexbuf)}
|		hexnum			{CST_INT (Lexing.lexeme lexbuf)}
|		octnum			{CST_INT (Lexing.lexeme lexbuf)}
|		intnum			{CST_INT (Lexing.lexeme lexbuf)}

|             "<<="                   {INF_INF_EQ}
|             ">>="                   {SUP_SUP_EQ}
|             "*="                    {STAR_EQ}
|             "/="                    {SLASH_EQ}
|             "&="                    {AND_EQ}
|             "|="                    {PIPE_EQ}
|             "^="                    {CIRC_EQ}
|             "%="                    {PERCENT_EQ}


|		"..."			{ELLIPSIS}
|		"-="			{MINUS_EQ}
|		"+="			{PLUS_EQ}
|		"*="			{STAR_EQ}
|		"<<"			{INF_INF}
|		">>"			{SUP_SUP}
| 		"=="			{EQ_EQ}
| 		"!="			{EXCLAM_EQ}
|		"<="			{INF_EQ}
|		">="			{SUP_EQ}
|		"="			{EQ}
|		"<"			{INF}
|		">"			{SUP}
|		"++"			{PLUS_PLUS}
|		"--"			{MINUS_MINUS}
|		"->"			{ARROW}
|		'+'			{PLUS}
|		'-'			{MINUS}
|		'*'			{STAR}
|		'/'			{SLASH}
|		'!'			{EXCLAM}
|		'&'			{AND}
|		'|'			{PIPE}
|		'^'			{CIRC}
|		'~'			{TILDE}
|		'['			{LBRACKET}
|		']'			{RBRACKET}
|		'{'			{LBRACE}
|		'}'			{RBRACE}
|		'('			{LPAREN}
|		')'			{RPAREN}
|		';'			{SEMICOLON}
|		','			{COMMA}
|		'.'			{DOT}
|               ':'                     {COLON}
|               '?'                     {QUEST}
|		"sizeof"		{SIZEOF}

|               "%eo" argname           {ARG_eo (getArgName lexbuf 3) }
|               "%e"  argname           {ARG_e  (getArgName lexbuf 2) }
|               "%E"  argname           {ARG_E  (getArgName lexbuf 2) }
|               "%u"  argname           {ARG_u  (getArgName lexbuf 2) }
|               "%b"  argname           {ARG_b  (getArgName lexbuf 2) }
|               "%t"  argname           {ARG_t  (getArgName lexbuf 2) }
|               "%d"  argname           {ARG_d  (getArgName lexbuf 2) }
|               "%lo" argname           {ARG_lo (getArgName lexbuf 3) }
|               "%l"  argname           {ARG_l  (getArgName lexbuf 2) }
|               "%i"  argname           {ARG_i  (getArgName lexbuf 2) }
|               "%I"  argname           {ARG_I  (getArgName lexbuf 2) }
|               "%o"  argname           {ARG_o  (getArgName lexbuf 2) }
|               "%va" argname           {ARG_va (getArgName lexbuf 3) }
|               "%v"  argname           {ARG_v  (getArgName lexbuf 2) }
|               "%k"  argname           {ARG_k  (getArgName lexbuf 2) }
|               "%f"  argname           {ARG_f  (getArgName lexbuf 2) }
|               "%F"  argname           {ARG_F  (getArgName lexbuf 2) }
|               "%p"  argname           {ARG_p  (getArgName lexbuf 2) }
|               "%P"  argname           {ARG_P  (getArgName lexbuf 2) }
|               "%s"  argname           {ARG_s  (getArgName lexbuf 2) }
|               "%S"  argname           {ARG_S  (getArgName lexbuf 2) }
|               "%g"  argname           {ARG_g  (getArgName lexbuf 2) }
|               "%A"  argname           {ARG_A  (getArgName lexbuf 2) }
|               "%c"  argname           {ARG_c  (getArgName lexbuf 2) } 

|		'%'			{PERCENT}
|		ident			{scan_ident (Lexing.lexeme lexbuf)}
|		eof			{EOF}
|		_			{E.parse_error 
                                           "Formatlex: Invalid symbol"
                                        }

and comment =
    parse 	
      "*/"			        { () }
|     '\n'                              { E.newline (); comment lexbuf }
| 		_ 			{ comment lexbuf }


and endline = parse 
        '\n' 			{ E.newline (); initial lexbuf}
|	_			{ endline lexbuf}

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

{
open BinNums
open Camlcoq
open CMparser
exception Error of string
}

let blank = [' ' '\009' '\012' '\010' '\013']
let floatlit = 
 ("-"? (['0'-'9'] ['0'-'9' '_']* 
  ('.' ['0'-'9' '_']* )?
  (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)? )) | "inf" | "nan"
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '_' '$' '0'-'9']*
let qident = '\'' [ ^ '\'' ]+ '\''
let temp = "$" ['1'-'9'] ['0'-'9']*
let intlit = "-"? ( ['0'-'9']+ | "0x" ['0'-'9' 'a'-'f' 'A'-'F']+
                               | "0o" ['0'-'7']+ | "0b" ['0'-'1']+ )
let stringlit = "\"" [ ^ '"' ] * '"'

rule token = parse
  | blank +      { token lexbuf }
  | "/*"         { comment lexbuf; token lexbuf }
  | "absf" { ABSF }
  | "&" { AMPERSAND }
  | "!"    { BANG }
  | "!="    { BANGEQUAL }
  | "!=f"    { BANGEQUALF }
  | "!=u"    { BANGEQUALU }
  | "|"     { BAR }
  | "builtin" { BUILTIN }
  | "^"     { CARET }
  | "case"  { CASE }
  | ":"    { COLON }
  | ","    { COMMA }
  | "default" { DEFAULT }
  | "else"    { ELSE }
  | "="    { EQUAL }
  | "=="    { EQUALEQUAL }
  | "==f"    { EQUALEQUALF }
  | "==u"    { EQUALEQUALU }
  | "exit"    { EXIT }
  | "extern"    { EXTERN }
  | "float"    { FLOAT }
  | "float32"    { FLOAT32 }
  | "float64"    { FLOAT64 }
  | "floatofint"    { FLOATOFINT }
  | "floatofintu"    { FLOATOFINTU }
  | "goto"  { GOTO } 
  | ">"    { GREATER }
  | ">f"    { GREATERF }
  | ">u"    { GREATERU }
  | ">="    { GREATEREQUAL }
  | ">=f"    { GREATEREQUALF }
  | ">=u"    { GREATEREQUALU }
  | ">>"    { GREATERGREATER }
  | ">>u"    { GREATERGREATERU }
  | "if"    { IF }
  | "in"    { IN }
  | "inline" { INLINE }
  | "int"    { INT }
  | "int16"    { INT16 }
  | "int16s"    { INT16S }
  | "int16u"    { INT16U }
  | "int32"    { INT32 }
  | "int8"    { INT8 }
  | "int8s"    { INT8S }
  | "int8u"    { INT8U }
  | "intoffloat"    { INTOFFLOAT }
  | "intuoffloat"    { INTUOFFLOAT }
  | "{"    { LBRACE }
  | "{{"    { LBRACELBRACE }
  | "["    { LBRACKET }
  | "<"    { LESS }
  | "<u"    { LESSU }
  | "<f"    { LESSF }
  | "<="    { LESSEQUAL }
  | "<=u"    { LESSEQUALU }
  | "<=f"    { LESSEQUALF }
  | "<<"    { LESSLESS }
  | "let"     { LET }
  | "loop"    { LOOP }
  | "("    { LPAREN }
  | "match" { MATCH }
  | "-"    { MINUS }
  | "->"    { MINUSGREATER }
  | "-f"    { MINUSF }
  | "%"    { PERCENT }
  | "%u"    { PERCENTU }
  | "+"    { PLUS }
  | "+f"    { PLUSF }
  | "}"    { RBRACE }
  | "}}"    { RBRACERBRACE }
  | "]"    { RBRACKET }
  | "readonly" { READONLY }
  | "return"    { RETURN }
  | ")"    { RPAREN }
  | ";"    { SEMICOLON }
  | "/"    { SLASH }
  | "/f"    { SLASHF }
  | "/u"    { SLASHU }
  | "stack"    { STACK }
  | "*" { STAR }
  | "*f"    { STARF }
  | "switch"    { SWITCH }
  | "tailcall"  { TAILCALL }
  | "~"    { TILDE }
  | "var"    { VAR }
  | "void"    { VOID }
  | "volatile" { VOLATILE }
  | "while" { WHILE }

  | intlit    { INTLIT(Int32.of_string(Lexing.lexeme lexbuf)) }
  | floatlit     { FLOATLIT(float_of_string(Lexing.lexeme lexbuf)) }
  | stringlit { let s = Lexing.lexeme lexbuf in
                STRINGLIT(String.sub s 1 (String.length s - 2)) }
  | ident | temp  { IDENT(Lexing.lexeme lexbuf) }
  | qident    { let s = Lexing.lexeme lexbuf in
                IDENT(String.sub s 1 (String.length s - 2)) }
  | eof      { EOF }
  | _        { raise(Error("illegal character `" ^ Char.escaped (Lexing.lexeme_char lexbuf 0) ^ "'")) }

and comment = parse
    "*/"     { () }
  | eof      { raise(Error "unterminated comment") }
  | _        { comment lexbuf }

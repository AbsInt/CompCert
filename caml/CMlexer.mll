(* $Id: CMlexer.mll,v 1.3 2005/03/21 15:53:00 xleroy Exp $ *)

{
open Camlcoq
open CMparser
exception Error of string
}

let blank = [' ' '\009' '\012' '\010' '\013']
let floatlit = 
  ['0'-'9'] ['0'-'9' '_']* 
  ('.' ['0'-'9' '_']* )?
  (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)?
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '_' '0'-'9']*
let intlit = "-"? ( ['0'-'9']+ | "0x" ['0'-'9' 'a'-'f' 'A'-'F']+
                               | "0o" ['0'-'7']+ | "0b" ['0'-'1']+ )
let stringlit = "\"" [ ^ '"' ] * '"'

rule token = parse
  | blank +      { token lexbuf }
  | "/*"         { comment lexbuf; token lexbuf }
  | "absf" { ABSF }
  | "alloc" { ALLOC }
  | "&" { AMPERSAND }
  | "&&" { AMPERSANDAMPERSAND }
  | "!"    { BANG }
  | "!="    { BANGEQUAL }
  | "!=f"    { BANGEQUALF }
  | "!=u"    { BANGEQUALU }
  | "|"     { BAR }
  | "||"    { BARBAR }
  | "^"     { CARET }
  | "case"  { CASE }
  | ":"    { COLON }
  | ","    { COMMA }
  | "default" { DEFAULT }
  | "$"    { DOLLAR }
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
  | "int"    { INT }
  | "int16s"    { INT16S }
  | "int16u"    { INT16U }
  | "int32"    { INT32 }
  | "int8s"    { INT8S }
  | "int8u"    { INT8U }
  | "intoffloat"    { INTOFFLOAT }
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
  | "?"    { QUESTION }
  | "}"    { RBRACE }
  | "}}"    { RBRACERBRACE }
  | "]"    { RBRACKET }
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
  | "~"    { TILDE }
  | "var"    { VAR }
  | "void"    { VOID }

  | intlit    { INTLIT(Int32.of_string(Lexing.lexeme lexbuf)) }
  | floatlit     { FLOATLIT(float_of_string(Lexing.lexeme lexbuf)) }
  | stringlit { let s = Lexing.lexeme lexbuf in
                STRINGLIT(intern_string(String.sub s 1 (String.length s - 2))) }
  | ident    { IDENT(intern_string(Lexing.lexeme lexbuf)) }
  | eof      { EOF }
  | _        { raise(Error("illegal character `" ^ Char.escaped (Lexing.lexeme_char lexbuf 0) ^ "'")) }

and comment = parse
    "*/"     { () }
  | eof      { raise(Error "unterminated comment") }
  | _        { comment lexbuf }

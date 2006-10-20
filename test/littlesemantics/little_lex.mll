{
open Little_syntax;;
}
rule token = parse
    [ ' ' '\t' '\n' ] {token lexbuf}
  | "variables" {T_VARIABLES}
  | "in" {T_IN}
  | "end" {T_END}
  | "while" {T_WHILE}
  | "do" {T_DO}
  | "done" {T_DONE}
  | ">" {T_GT}
  | ":=" {T_ASSIGN}
  | "+" {T_PLUS}
  | ";" {T_SCOLUMN}
  | "(" {T_OPEN}
  | ")" {T_CLOSE}
  | "{" {T_OPEN_B}
  | "}" {T_CLOSE_B}
  | "skip" {T_SKIP}
  | "-"?['0'-'9']+ {NUM(int_of_string (Lexing.lexeme lexbuf))}
  | ['a'-'z''A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* 
    {ID(Lexing.lexeme lexbuf)}

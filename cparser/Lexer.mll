(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
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
open Lexing
open Pre_parser
open Pre_parser_aux
open Cabshelper
open Camlcoq

module SMap = Map.Make(String)

let contexts : string list list ref = ref []
let lexicon : (string, Cabs.cabsloc -> token) Hashtbl.t = Hashtbl.create 0

let init filename channel : Lexing.lexbuf =
  assert (!contexts = []);
  Hashtbl.clear lexicon;
  List.iter
    (fun (key, builder) -> Hashtbl.add lexicon key builder)
    [ ("auto", fun loc -> AUTO loc);
      ("break", fun loc -> BREAK loc);
      ("case", fun loc -> CASE loc);
      ("char", fun loc -> CHAR loc);
      ("const", fun loc -> CONST loc);
      ("continue", fun loc -> CONTINUE loc);
      ("default", fun loc -> DEFAULT loc);
      ("do", fun loc -> DO loc);
      ("double", fun loc -> DOUBLE loc);
      ("else", fun loc -> ELSE loc);
      ("enum", fun loc -> ENUM loc);
      ("extern", fun loc -> EXTERN loc);
      ("float", fun loc -> FLOAT loc);
      ("for", fun loc -> FOR loc);
      ("goto", fun loc -> GOTO loc);
      ("if", fun loc -> IF loc);
      ("inline", fun loc -> INLINE loc);
      ("int", fun loc -> INT loc);
      ("long", fun loc -> LONG loc);
      ("register", fun loc -> REGISTER loc);
      ("restrict", fun loc -> RESTRICT loc);
      ("return", fun loc -> RETURN loc);
      ("short", fun loc -> SHORT loc);
      ("signed", fun loc -> SIGNED loc);
      ("sizeof", fun loc -> SIZEOF loc);
      ("static", fun loc -> STATIC loc);
      ("struct", fun loc -> STRUCT loc);
      ("switch", fun loc -> SWITCH loc);
      ("typedef", fun loc -> TYPEDEF loc);
      ("union", fun loc -> UNION loc);
      ("unsigned", fun loc -> UNSIGNED loc);
      ("void", fun loc -> VOID loc);
      ("volatile", fun loc -> VOLATILE loc);
      ("while", fun loc -> WHILE loc);
      ("_Alignas", fun loc -> ALIGNAS loc);
      ("_Alignof", fun loc -> ALIGNOF loc);
      ("__alignof", fun loc -> ALIGNOF loc);
      ("__alignof__", fun loc -> ALIGNOF loc);
      ("__attribute", fun loc -> ATTRIBUTE loc);
      ("__attribute__", fun loc -> ATTRIBUTE loc);
      ("_Bool", fun loc -> UNDERSCORE_BOOL loc);
      ("__builtin_va_arg", fun loc -> BUILTIN_VA_ARG loc);
      ("__packed__", fun loc -> PACKED loc);
      ("__asm__", fun loc -> ASM loc);
      ("__asm", fun loc -> ASM loc);
      ("asm", fun loc -> ASM loc);
    ];

  push_context := begin fun () -> contexts := []::!contexts end;
  pop_context := begin fun () ->
    match !contexts with
      | [] -> assert false
      | t::q -> List.iter (Hashtbl.remove lexicon) t;
                contexts := q
  end;

 declare_varname := begin fun id ->
   if Hashtbl.mem lexicon id then begin
     Hashtbl.add lexicon id (fun loc -> VAR_NAME (id, ref VarId, loc));
     match !contexts with
       | [] -> ()
       | t::q -> contexts := (id::t)::q
     end
  end;

  declare_typename := begin fun id ->
    Hashtbl.add lexicon id (fun loc -> TYPEDEF_NAME (id, ref TypedefId, loc));
    match !contexts with
      | [] -> ()
      | t::q -> contexts := (id::t)::q
  end;

  !declare_typename "__builtin_va_list";

  let lb = Lexing.from_channel channel in
  lb.lex_curr_p <-
    {lb.lex_curr_p with pos_fname = filename; pos_lnum = 1};
  lb

let currentLoc =
  let nextident = ref 0 in
  let getident () =
    nextident := !nextident + 1;
    !nextident
  in
  fun lb ->
    let p = Lexing.lexeme_start_p lb in
    Cabs.({ lineno   = p.Lexing.pos_lnum;
            filename = p.Lexing.pos_fname;
            byteno   = p.Lexing.pos_cnum;
            ident    = getident ();})

}

(* Identifiers *)
let digit = ['0'-'9']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let nondigit = ['_' 'a'-'z' 'A'-'Z']

let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit
let universal_character_name =
    "\\u" hex_quad
  | "\\U" hex_quad hex_quad

let identifier_nondigit =
    nondigit
(*| universal_character_name*)
  | '$'

let identifier = identifier_nondigit (identifier_nondigit|digit)*

(* Whitespaces *)
let whitespace_char_no_newline = [' ' '\t' '\012' '\r']

(* Integer constants *)
let nonzero_digit = ['1'-'9']
let decimal_constant = nonzero_digit digit*

let octal_digit = ['0'-'7']
let octal_constant = '0' octal_digit*

let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_constant =
  hexadecimal_prefix hexadecimal_digit+

let unsigned_suffix = ['u' 'U']
let long_suffix = ['l' 'L']
let long_long_suffix = "ll" | "LL"
let integer_suffix =
    unsigned_suffix long_suffix?
  | unsigned_suffix long_long_suffix
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?

let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?

(* Floating constants *)
let sign = ['-' '+']
let digit_sequence = digit+
let floating_suffix = ['f' 'l' 'F' 'L'] as suffix

let fractional_constant =
    (digit_sequence as intpart)? '.' (digit_sequence as frac)
  | (digit_sequence as intpart) '.'
let exponent_part =
    'e' ((sign? digit_sequence) as expo)
  | 'E' ((sign? digit_sequence) as expo)
let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | (digit_sequence as intpart) exponent_part floating_suffix?

let hexadecimal_digit_sequence = hexadecimal_digit+
let hexadecimal_fractional_constant =
    (hexadecimal_digit_sequence as intpart)? '.' (hexadecimal_digit_sequence as frac)
  | (hexadecimal_digit_sequence as intpart) '.'
let binary_exponent_part =
    'p' ((sign? digit_sequence) as expo)
  | 'P' ((sign? digit_sequence) as expo)
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
        binary_exponent_part floating_suffix?
  | hexadecimal_prefix (hexadecimal_digit_sequence as intpart)
        binary_exponent_part floating_suffix?

(* Charater constants *)
let simple_escape_sequence =
    "\\'" | "\\\"" | "\\?" | "\\\\" | "\\a" | "\\b" | "\\f" | "\\n"
  | "\\r" | "\\t" | "\\v"
let octal_escape_sequence =
    '\\' octal_digit
  | '\\' octal_digit octal_digit
  | '\\' octal_digit octal_digit octal_digit
let hexadecimal_escape_sequence = "\\x" hexadecimal_digit+
let escape_sequence =
    simple_escape_sequence
  | octal_escape_sequence
  | hexadecimal_escape_sequence
  | universal_character_name
let c_char =
    [^ '\'' '\\' '\n']
  | escape_sequence
let c_char_sequence = c_char+
let character_constant =
    "'" c_char_sequence "'"
  | "L'" c_char_sequence "'"

(* String literals *)
let s_char =
    [^ '"' '\\' '\n']
  | escape_sequence
let s_char_sequence = s_char+
let string_literal =
    '"' s_char_sequence? '"'
  | 'L' '"' s_char_sequence? '"'

(* We assume comments are removed by the preprocessor. *)
rule initial = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline    { initial lexbuf }
  | integer_constant as s         { CONSTANT (Cabs.CONST_INT s, currentLoc lexbuf) }
  | decimal_floating_constant     { CONSTANT (Cabs.CONST_FLOAT
                                      {Cabs.isHex_FI = false;
                                       Cabs.integer_FI = intpart;
                                       Cabs.fraction_FI = frac;
                                       Cabs.exponent_FI = expo;
                                       Cabs.suffix_FI =
                                         match suffix with
                                         | None -> None
                                         | Some c -> Some (String.make 1 c) },
                                      currentLoc lexbuf)}
  | hexadecimal_floating_constant { CONSTANT (Cabs.CONST_FLOAT
                                      {Cabs.isHex_FI = true;
                                       Cabs.integer_FI = intpart;
                                       Cabs.fraction_FI = frac;
                                       Cabs.exponent_FI = Some expo;
                                       Cabs.suffix_FI =
                                         match suffix with
                                           | None -> None
                                           | Some c -> Some (String.make 1 c) },
                                      currentLoc lexbuf)}
  | character_constant as s       { CONSTANT (Cabs.CONST_CHAR s, currentLoc lexbuf) }
  | string_literal as s           { STRING_LITERAL (s, currentLoc lexbuf) }
  | "..."                         { ELLIPSIS(currentLoc lexbuf) }
  | "+="                          { ADD_ASSIGN(currentLoc lexbuf) }
  | "-="                          { SUB_ASSIGN(currentLoc lexbuf) }
  | "*="                          { MUL_ASSIGN(currentLoc lexbuf) }
  | "/="                          { DIV_ASSIGN(currentLoc lexbuf) }
  | "%="                          { MOD_ASSIGN(currentLoc lexbuf) }
  | "|="                          { OR_ASSIGN(currentLoc lexbuf) }
  | "&="                          { AND_ASSIGN(currentLoc lexbuf) }
  | "^="                          { XOR_ASSIGN(currentLoc lexbuf) }
  | "<<="                         { LEFT_ASSIGN(currentLoc lexbuf) }
  | ">>="                         { RIGHT_ASSIGN(currentLoc lexbuf) }
  | "<<"                          { LEFT(currentLoc lexbuf) }
  | ">>"                          { RIGHT(currentLoc lexbuf) }
  | "=="                          { EQEQ(currentLoc lexbuf) }
  | "!="                          { NEQ(currentLoc lexbuf) }
  | "<="                          { LEQ(currentLoc lexbuf) }
  | ">="                          { GEQ(currentLoc lexbuf) }
  | "="                           { EQ(currentLoc lexbuf) }
  | "<"                           { LT(currentLoc lexbuf) }
  | ">"                           { GT(currentLoc lexbuf) }
  | "++"                          { INC(currentLoc lexbuf) }
  | "--"                          { DEC(currentLoc lexbuf) }
  | "->"                          { PTR(currentLoc lexbuf) }
  | "+"                           { PLUS(currentLoc lexbuf) }
  | "-"                           { MINUS(currentLoc lexbuf) }
  | "*"                           { STAR(currentLoc lexbuf) }
  | "/"                           { SLASH(currentLoc lexbuf) }
  | "%"                           { PERCENT(currentLoc lexbuf) }
  | "!"                           { BANG(currentLoc lexbuf) }
  | "&&"                          { ANDAND(currentLoc lexbuf) }
  | "||"                          { BARBAR(currentLoc lexbuf) }
  | "&"                           { AND(currentLoc lexbuf) }
  | "|"                           { BAR(currentLoc lexbuf) }
  | "^"                           { HAT(currentLoc lexbuf) }
  | "?"                           { QUESTION(currentLoc lexbuf) }
  | ":"                           { COLON(currentLoc lexbuf) }
  | "~"                           { TILDE(currentLoc lexbuf) }
  | "{"|"<%"                      { LBRACE(currentLoc lexbuf) }
  | "}"|"%>"                      { RBRACE(currentLoc lexbuf) }
  | "["|"<:"                      { LBRACK(currentLoc lexbuf) }
  | "]"|":>"                      { RBRACK(currentLoc lexbuf) }
  | "("                           { LPAREN(currentLoc lexbuf) }
  | ")"                           { RPAREN(currentLoc lexbuf) }
  | ";"                           { SEMICOLON(currentLoc lexbuf) }
  | ","                           { COMMA(currentLoc lexbuf) }
  | "."                           { DOT(currentLoc lexbuf) }
  | identifier as id              {
        try Hashtbl.find lexicon id (currentLoc lexbuf)
        with Not_found -> VAR_NAME (id, ref VarId, currentLoc lexbuf) }
  | eof                           { EOF }
  | _ as c                        {
      Cerrors.fatal_error "%s:%d Error:@ invalid symbol %C"
        lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum c }

and initial_linebegin = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline    { initial_linebegin lexbuf }
  | '#'                           { hash lexbuf }
  | ""                            { initial lexbuf }

(* We assume gcc -E syntax but try to tolerate variations. *)
and hash = parse
  | whitespace_char_no_newline +
    (decimal_constant as n)
    whitespace_char_no_newline *
    "\"" ([^ '\n' '\"']* as file) "\""
    [^ '\n']* '\n'
      { let n =
          try int_of_string n
          with Failure "int_of_string" ->
            Cerrors.warning "%s:%d Warning:@ invalid line number"
              lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum;
            lexbuf.lex_curr_p.pos_lnum
        in
        lexbuf.lex_curr_p <- {
          lexbuf.lex_curr_p with
            pos_fname = file;
            pos_lnum = n;
            pos_bol = lexbuf.lex_curr_p.pos_cnum
        };
        initial_linebegin lexbuf }
  | whitespace_char_no_newline *
    "pragma"
    whitespace_char_no_newline +
    ([^ '\n']* as s) '\n'
      { new_line lexbuf; PRAGMA (s, currentLoc lexbuf) }
  | [^ '\n']* '\n'
      { Cerrors.warning "%s:%d Warning:@ unrecognized '#' line"
          lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum;
        new_line lexbuf; initial_linebegin lexbuf }
  | [^ '\n']* eof
      { Cerrors.fatal_error "%s:%d Error:@ unexpected end of file"
          lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum }
  | _ as c
      { Cerrors.fatal_error "%s:%d Error:@ invalid symbol %C"
          lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum c }

{
  open Streams
  open Specif
  open Parser
  open Aut.GramDefs

  let tokens_stream lexbuf : token coq_Stream =
    let tokens = Queue.create () in
    let lexer_wraper lexbuf : Pre_parser.token =
      let res =
        if lexbuf.lex_curr_p.pos_cnum = lexbuf.lex_curr_p.pos_bol then
          initial_linebegin lexbuf
        else
          initial lexbuf
      in
      Queue.push res tokens;
      res
    in
    Pre_parser.translation_unit_file lexer_wraper lexbuf;
    assert (!contexts = []);
    let rec compute_token_stream () =
      let loop t v =
        Cons (Coq_existT (t, Obj.magic v), Lazy.from_fun compute_token_stream)
      in
      match Queue.pop tokens with
      | ADD_ASSIGN loc -> loop ADD_ASSIGN't loc
      | AND loc -> loop AND't loc
      | ANDAND loc -> loop ANDAND't loc
      | AND_ASSIGN loc -> loop AND_ASSIGN't loc
      | AUTO loc -> loop AUTO't loc
      | BANG loc -> loop BANG't loc
      | BAR loc -> loop BAR't loc
      | BARBAR loc -> loop BARBAR't loc
      | UNDERSCORE_BOOL loc -> loop UNDERSCORE_BOOL't loc
      | BREAK loc -> loop BREAK't loc
      | BUILTIN_VA_ARG loc -> loop BUILTIN_VA_ARG't loc
      | CASE loc -> loop CASE't loc
      | CHAR loc -> loop CHAR't loc
      | COLON loc -> loop COLON't loc
      | COMMA loc -> loop COMMA't loc
      | CONST loc -> loop CONST't loc
      | CONSTANT (cst, loc) -> loop CONSTANT't (cst, loc)
      | CONTINUE loc -> loop CONTINUE't loc
      | DEC loc -> loop DEC't loc
      | DEFAULT loc -> loop DEFAULT't loc
      | DIV_ASSIGN loc -> loop DIV_ASSIGN't loc
      | DO loc -> loop DO't loc
      | DOT loc -> loop DOT't loc
      | DOUBLE loc -> loop DOUBLE't loc
      | ELLIPSIS loc -> loop ELLIPSIS't loc
      | ELSE loc -> loop ELSE't loc
      | ENUM loc -> loop ENUM't loc
      | EOF -> loop EOF't ()
      | EQ loc -> loop EQ't loc
      | EQEQ loc -> loop EQEQ't loc
      | EXTERN loc -> loop EXTERN't loc
      | FLOAT loc -> loop FLOAT't loc
      | FOR loc -> loop FOR't loc
      | GEQ loc -> loop GEQ't loc
      | GOTO loc -> loop GOTO't loc
      | GT loc -> loop GT't loc
      | HAT loc -> loop HAT't loc
      | IF loc -> loop IF't loc
      | INC loc -> loop INC't loc
      | INLINE loc -> loop INLINE't loc
      | INT loc -> loop INT't loc
      | LBRACE loc -> loop LBRACE't loc
      | LBRACK loc -> loop LBRACK't loc
      | LEFT loc -> loop LEFT't loc
      | LEFT_ASSIGN loc -> loop LEFT_ASSIGN't loc
      | LEQ loc -> loop LEQ't loc
      | LONG loc -> loop LONG't loc
      | LPAREN loc -> loop LPAREN't loc
      | LT loc -> loop LT't loc
      | MINUS loc -> loop MINUS't loc
      | MOD_ASSIGN loc -> loop MOD_ASSIGN't loc
      | MUL_ASSIGN loc -> loop MUL_ASSIGN't loc
      | NEQ loc -> loop NEQ't loc
      | OR_ASSIGN loc -> loop OR_ASSIGN't loc
      | PACKED loc -> loop PACKED't loc
      | PERCENT loc -> loop PERCENT't loc
      | PLUS loc -> loop PLUS't loc
      | PTR loc -> loop PTR't loc
      | QUESTION loc -> loop QUESTION't loc
      | RBRACE loc -> loop RBRACE't loc
      | RBRACK loc -> loop RBRACK't loc
      | REGISTER loc -> loop REGISTER't loc
      | RESTRICT loc -> loop RESTRICT't loc
      | RETURN loc -> loop RETURN't loc
      | RIGHT loc -> loop RIGHT't loc
      | RIGHT_ASSIGN loc -> loop RIGHT_ASSIGN't loc
      | RPAREN loc -> loop RPAREN't loc
      | SEMICOLON loc -> loop SEMICOLON't loc
      | SHORT loc -> loop SHORT't loc
      | SIGNED loc -> loop SIGNED't loc
      | SIZEOF loc -> loop SIZEOF't loc
      | SLASH loc -> loop SLASH't loc
      | STAR loc -> loop STAR't loc
      | STATIC loc -> loop STATIC't loc
      | STRING_LITERAL (str, loc) ->
          let buf = Buffer.create (String.length str) in
          Buffer.add_string buf str;
          (* Merge consecutive string literals *)
          let rec doConcat () =
            try
              match Queue.peek tokens with
              | STRING_LITERAL (str, loc) ->
                  ignore (Queue.pop tokens);
                  Buffer.add_string buf str;
                  doConcat ()
              | _ -> ()
            with Queue.Empty -> ()
          in
          doConcat ();
          loop CONSTANT't (Cabs.CONST_STRING (Buffer.contents buf), loc)
      | STRUCT loc -> loop STRUCT't loc
      | SUB_ASSIGN loc -> loop SUB_ASSIGN't loc
      | SWITCH loc -> loop SWITCH't loc
      | TILDE loc -> loop TILDE't loc
      | TYPEDEF loc -> loop TYPEDEF't loc
      | TYPEDEF_NAME (id, typ, loc)
      | VAR_NAME (id, typ, loc) ->
          let terminal = match !typ with
            | VarId -> VAR_NAME't
            | TypedefId -> TYPEDEF_NAME't
            | OtherId -> OTHER_NAME't
          in
          loop terminal (id, loc)
      | UNION loc -> loop UNION't loc
      | UNSIGNED loc -> loop UNSIGNED't loc
      | VOID loc -> loop VOID't loc
      | VOLATILE loc -> loop VOLATILE't loc
      | WHILE loc -> loop WHILE't loc
      | XOR_ASSIGN loc -> loop XOR_ASSIGN't loc
      | ALIGNAS loc -> loop ALIGNAS't loc
      | ALIGNOF loc -> loop ALIGNOF't loc
      | ATTRIBUTE loc -> loop ATTRIBUTE't loc
      | ASM loc -> loop ASM't loc
      | PRAGMA (s, loc) -> loop PRAGMA't (s, loc)
    in
    Lazy.from_fun compute_token_stream

}

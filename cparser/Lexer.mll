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

module SSet = Set.Make(String)

let lexicon : (string, Cabs.cabsloc -> token) Hashtbl.t = Hashtbl.create 17
let ignored_keywords : SSet.t ref = ref SSet.empty

let () =
  List.iter (fun (key, builder) -> Hashtbl.add lexicon key builder)
    [ ("_Alignas", fun loc -> ALIGNAS loc);
      ("_Alignof", fun loc -> ALIGNOF loc);
      ("_Bool", fun loc -> UNDERSCORE_BOOL loc);
      ("__alignof", fun loc -> ALIGNOF loc);
      ("__alignof__", fun loc -> ALIGNOF loc);
      ("__asm", fun loc -> ASM loc);
      ("__asm__", fun loc -> ASM loc);
      ("__attribute", fun loc -> ATTRIBUTE loc);
      ("__attribute__", fun loc -> ATTRIBUTE loc);
      ("__builtin_va_arg", fun loc -> BUILTIN_VA_ARG loc);
      ("__builtin_offsetof", fun loc -> BUILTIN_OFFSETOF loc);
      ("__const", fun loc -> CONST loc);
      ("__const__", fun loc -> CONST loc);
      ("__inline", fun loc -> INLINE loc);
      ("__inline__", fun loc -> INLINE loc);
      ("__packed__", fun loc -> PACKED loc);
      ("__restrict", fun loc -> RESTRICT loc);
      ("__restrict__", fun loc -> RESTRICT loc);
      ("__signed", fun loc -> SIGNED loc);
      ("__signed__", fun loc -> SIGNED loc);
      ("__volatile", fun loc -> VOLATILE loc);
      ("__volatile__", fun loc -> VOLATILE loc);
      ("asm", fun loc -> ASM loc);
      ("auto", fun loc -> AUTO loc);
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
      ("_Noreturn", fun loc -> NORETURN loc);
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
      ("while", fun loc -> WHILE loc)];
  if Configuration.system <> "diab" then
    (* We can ignore the __extension__ GCC keyword. *)
    ignored_keywords := SSet.add "__extension__" !ignored_keywords

let init_ctx = SSet.singleton "__builtin_va_list"
let types_context : SSet.t ref = ref init_ctx

let _ =
  (* See comments in pre_parser_aux.ml *)
  save_context := begin fun () ->
    let save = !types_context in
    fun () -> types_context := save
  end;

  declare_varname := begin fun id ->
    types_context := SSet.remove id !types_context
  end;

  declare_typename := begin fun id ->
    types_context := SSet.add id !types_context
  end

let init filename channel : Lexing.lexbuf =
  let lb = Lexing.from_channel channel in
  lb.lex_curr_p <- {lb.lex_curr_p with pos_fname = filename; pos_lnum = 1};
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

(* Error reporting *)

let fatal_error lb fmt =
  Diagnostics.fatal_error
    (lb.lex_curr_p.pos_fname,lb.lex_curr_p.pos_lnum) fmt

let error lb fmt =
  Diagnostics.error
    (lb.lex_curr_p.pos_fname,lb.lex_curr_p.pos_lnum) fmt

let warning lb fmt =
  Diagnostics.warning
      (lb.lex_curr_p.pos_fname,lb.lex_curr_p.pos_lnum) Diagnostics.Unnamed fmt

(* Simple character escapes *)

let convert_escape = function
  | 'a' -> 7L  (* bell *)
  | 'b' -> 8L  (* backspace  *)
  | 'e' -> 27L (* escape (GCC extension) *)
  | 'f' -> 12L (* form feed *)
  | 'n' -> 10L (* new line *)
  | 'r' -> 13L (* carriage return *)
  | 't' -> 9L  (* horizontal tab *)
  | 'v' -> 11L (* vertical tab *)
  | c   -> Int64.of_int (Char.code c)
}

(* Identifiers *)
let digit = ['0'-'9']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let nondigit = ['_' 'a'-'z' 'A'-'Z']

let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit
let universal_character_name =
    "\\u" (hex_quad as n)
  | "\\U" (hex_quad hex_quad as n)

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

(* Preprocessing numbers *)
let preprocessing_number =
  '.'? ['0'-'9']
  (['0'-'9' 'A'-'Z' 'a'-'z' '_' '.'] | ['e' 'E' 'p' 'P']['+' '-'])*

(* Character and string constants *)
let simple_escape_sequence =
  '\\' ( ['\''  '\"'  '?'  '\\'  'a'  'b'  'e'  'f'  'n'  'r'  't'  'v'] as c)
let octal_escape_sequence =
  '\\' ((octal_digit
         | octal_digit octal_digit
         | octal_digit octal_digit octal_digit) as n)
let hexadecimal_escape_sequence = "\\x" (hexadecimal_digit+ as n)
let escape_sequence =
    simple_escape_sequence
  | octal_escape_sequence
  | hexadecimal_escape_sequence
  | universal_character_name

rule initial = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline +  { initial lexbuf }
  | "/*"                          { multiline_comment lexbuf; initial lexbuf }
  | "//"                          { singleline_comment lexbuf; initial lexbuf }
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
                                      currentLoc lexbuf) }
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
  | preprocessing_number as s     { error lexbuf "invalid numerical constant '%s'@ These characters form a preprocessor number, but not a constant" s;
                                    CONSTANT (Cabs.CONST_INT "0", currentLoc lexbuf) }
  | "'"                           { let l = char_literal lexbuf.lex_start_p [] lexbuf in
                                    CONSTANT (Cabs.CONST_CHAR(false, l),
                                              currentLoc lexbuf) }
  | "L'"                          { let l = char_literal lexbuf.lex_start_p [] lexbuf in
                                    CONSTANT (Cabs.CONST_CHAR(true, l),
                                              currentLoc lexbuf) }
  | "\""                          { let l = string_literal lexbuf.lex_start_p [] lexbuf in
                                    STRING_LITERAL(false, l, currentLoc lexbuf) }
  | "L\""                         { let l = string_literal lexbuf.lex_start_p [] lexbuf in
                                    STRING_LITERAL(true, l, currentLoc lexbuf) }
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
    if SSet.mem id !ignored_keywords then
      initial lexbuf
    else
      try Hashtbl.find lexicon id (currentLoc lexbuf)
      with Not_found -> PRE_NAME id }
  | eof                           { EOF }
  | _ as c                        { fatal_error lexbuf "invalid symbol %C" c }

and initial_linebegin = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline    { initial_linebegin lexbuf }
  | '#'                           { hash lexbuf }
  | ""                            { initial lexbuf }

and char = parse
  | universal_character_name
      { try
          Int64.of_string ("0x" ^ n)
        with Failure _ ->
          error lexbuf "overflow in universal character name";
          0L
      }
  | hexadecimal_escape_sequence
      { try
          Int64.of_string ("0x" ^ n)
        with Failure _ ->
          error lexbuf "overflow in hexadecimal escape sequence";
          0L
      }
  | octal_escape_sequence
      { Int64.of_string  ("0o" ^ n) }
  | simple_escape_sequence
      { convert_escape c }
  | '\\' (_ as c)
      { error lexbuf "incorrect escape sequence '\\%c'" c;
        Int64.of_int (Char.code c) }
  | _ as c
      { Int64.of_int (Char.code c) }

and char_literal startp accu = parse
  | '\''       { lexbuf.lex_start_p <- startp;
                 List.rev accu }
  | '\n' | eof { fatal_error lexbuf "missing terminating \"'\" character" }
  | ""         { let c = char lexbuf in char_literal startp (c :: accu) lexbuf }

and string_literal startp accu = parse
  | '\"'       { lexbuf.lex_start_p <- startp;
                 List.rev accu }
  | '\n' | eof { fatal_error lexbuf "missing terminating '\"' character" }
  | ""         { let c = char lexbuf in string_literal startp (c :: accu) lexbuf }

(* We assume gcc -E syntax but try to tolerate variations. *)
and hash = parse
  | whitespace_char_no_newline +
    (decimal_constant as n)
    whitespace_char_no_newline *
    "\"" ([^ '\n' '\"']* as file) "\""
    [^ '\n']* '\n'
      { let n =
          try
            int_of_string n
          with Failure _ ->
            warning lexbuf "invalid line number"; lexbuf.lex_curr_p.pos_lnum
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
      { warning lexbuf "unrecognized '#' line";
        new_line lexbuf; initial_linebegin lexbuf }
  | [^ '\n']* eof
      { fatal_error lexbuf "unexpected end of file" }
  | _ as c
      { fatal_error lexbuf "invalid symbol %C" c }

(* Multi-line comment terminated by "*/" *)
and multiline_comment = parse
  | "*/"   { () }
  | eof    { error lexbuf "unterminated comment" }
  | '\n'   { new_line lexbuf; multiline_comment lexbuf }
  | _      { multiline_comment lexbuf }

(* Single-line comment terminated by a newline *)
and singleline_comment = parse
  | '\n'   { new_line lexbuf }
  | eof    { () }
  | _      { singleline_comment lexbuf }

{
  open Streams
  open Specif
  open Parser
  open !Aut.GramDefs

  (* This is the main entry point to the lexer. *)

  let lexer : lexbuf -> Pre_parser.token =
    fun lexbuf ->
      if lexbuf.lex_curr_p.pos_cnum = lexbuf.lex_curr_p.pos_bol then
        initial_linebegin lexbuf
      else
        initial lexbuf

  (* [lexer tokens buffer] is a new lexer, which wraps [lexer], and also: 1-
     records the token stream into the FIFO queue [tokens] and 2- records the
     start and end positions of the last two tokens in the two-place buffer
     [buffer] and 3- duplicates identifier tokens into PRE_NAME and
     VAR/TYPE_NAME. *)

  let lexer tokens buffer : lexbuf -> Pre_parser.token =
    let curr_id = ref None in
    types_context := init_ctx;
    fun lexbuf ->
      match !curr_id with
      | Some id ->
        curr_id := None;
        let loc = currentLoc lexbuf in
        let token =
          if SSet.mem id !types_context then TYPEDEF_NAME (id, ref TypedefId, loc)
          else VAR_NAME (id, ref VarId, loc)
        in
        Queue.push token tokens;
        token
      | None ->
        let token = lexer lexbuf in
        begin match token with
        | PRE_NAME id -> curr_id := Some id
        | _ -> Queue.push token tokens
        end;
        let startp = lexbuf.lex_start_p
        and endp = lexbuf.lex_curr_p in
        buffer := ErrorReports.update !buffer (startp, endp);
        token

  (* [invoke_pre_parser] is in charge of calling the pre_parser. It uses
     the incremental API, which allows us to do our own error handling. *)

  let invoke_pre_parser filename text lexer buffer =
    let lexbuf = Lexing.from_string text in
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filename; pos_lnum = 1};
    let module I = Pre_parser.MenhirInterpreter in
    let checkpoint = Pre_parser.Incremental.translation_unit_file lexbuf.lex_curr_p
    and supplier = I.lexer_lexbuf_to_supplier lexer lexbuf
    and succeed () = ()
    and fail checkpoint =
      Diagnostics.fatal_error_raw "%s" (ErrorReports.report text !buffer checkpoint)
    in
    I.loop_handle succeed fail supplier checkpoint

  (* [tokens_stream filename text] runs the pre_parser and produces a stream
     of (appropriately classified) tokens. *)

  let tokens_stream filename text : token coq_Stream =
    let tokens = Queue.create () in
    let buffer = ref ErrorReports.Zero in
    invoke_pre_parser filename text (lexer tokens buffer) buffer;
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
      | BUILTIN_OFFSETOF loc -> loop BUILTIN_OFFSETOF't loc
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
      | NORETURN loc -> loop NORETURN't loc
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
      | STRING_LITERAL (wide, str, loc) ->
          (* Merge consecutive string literals *)
          let rec doConcat wide str =
            try
              match Queue.peek tokens with
              | STRING_LITERAL (wide', str', loc) ->
                  ignore (Queue.pop tokens);
                  let (wide'', str'') = doConcat wide' str' in
                  if str'' <> []
                  then (wide || wide'', str @ str'')
                  else (wide, str)
              | _ ->
                  (wide, str)
            with Queue.Empty -> (wide, str) in
          let (wide', str') = doConcat wide str in
          loop STRING_LITERAL't ((wide', str'), loc)
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
      | PRE_NAME _ -> assert false
    in
    Lazy.from_fun compute_token_stream

}


try 
  Little_syntax.main Little_lex.token (Lexing.from_channel stdin)
with Parsing.Parse_error -> print_string("parsing_error\n");;

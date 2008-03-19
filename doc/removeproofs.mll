rule process inproof oc = parse
  | "<span class=\"keyword\">Proof</span>" ' '* '.'
      { process true oc lexbuf }
  | "<span class=\"keyword\">" ("Qed" | "Defined") "</span>" ' '* '.'
      { process false oc lexbuf }
  | "<a class=\"idref\" href=\"" 
    [^ '"'] + '#' '"' [^ '\n' '>']* '"' '"' '>'
    ([^ '<' '\n']+ as ident)
    "</a>"
      { if not inproof then output_string oc ident;
        process inproof oc lexbuf }
  | _
      { if not inproof then output_char oc (Lexing.lexeme_char lexbuf 0);
        process inproof oc lexbuf }
  | eof
      { () }

{

let process_file name =
  let ic = open_in name in
  Sys.remove name;
  let oc = open_out name in
  process false oc (Lexing.from_channel ic);
  close_out oc;
  close_in ic

let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    process_file Sys.argv.(i)
  done
}


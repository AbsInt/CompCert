open Printf

(* Module to parse config file to output in ocaml format *)

let translate_file f = 
  let ic = open_in f in 
  try 
    while true do 
      let l = input_line ic in 
      (* allow for empty lines and comments *)
      if not (l = "" || String.starts_with ~prefix:"#" l) then begin 
        let r = Str.regexp {|\([^=]*\)=\(.*\)|} in 
        (* line does not match *)
        if not (Str.string_match r l 0) then 
          (* insert line as comment *)
          printf "(* %s *)\n" l 
        else 
          (* identifier must be "clean" identifier according to variable identifier definition *)
          let identifier = String.lowercase_ascii (Str.matched_group 1 l) in
          let value = Str.matched_group 2 l in 
          let value_escaped_backslash = Str.global_replace (Str.regexp {|\\|}) {|\\\\|} value in 
          let value_escaped = Str.global_replace (Str.regexp {|"|}) {|\\"|} value_escaped_backslash in 
          printf "let %s = \"%s\"\n" identifier value_escaped
      end
    done
  with End_of_file -> 
    close_in ic

(* Entrypoint -> read first arg of input, should be Config Format (VERSION, Makefile.config,...) file *)
let _ = 
  if Array.length Sys.argv = 2 then 
    translate_file Sys.argv.(1)
  else 
    invalid_arg "expected only one file name argument"
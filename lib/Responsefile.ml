(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*        Bernhard Schommer, AbsInt Angewandte Informatik GmbH         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)


let rec singlequote ic buf =
  match input_char ic with
  | exception End_of_file -> ()
  | '\'' -> ()
  | c -> Buffer.add_char buf c; singlequote ic buf

let doublequote ic buf =
  let rec aux buf =
    match input_char ic with
    | exception End_of_file -> (* Backslash-newline is ignored. *)
        ()
    | '\"' ->
        ()
    | '\\' ->
        begin match input_char ic with
        | exception End_of_file ->    (* tolerance *)
            Buffer.add_char buf '\\'
        | '\n' ->
            aux buf
        | ('\\' | '\"') as c ->
            Buffer.add_char buf c; aux buf
        | c ->
            Buffer.add_char buf '\\'; Buffer.add_char buf c; aux buf
        end
    | c ->
        Buffer.add_char buf c; aux buf in
  aux buf

let doublequote_win ic buf =
  let rec aux_win buf n =
    match input_char ic with
    | exception End_of_file ->   (* tolerance *)
        add_backslashes n
    | '\\' ->
        aux_win buf (n+1)
    | '\"' ->
      if n land 1 = 1 then begin
        add_backslashes (n/2); Buffer.add_char buf '\"';
          aux_win buf 0
      end else begin
        add_backslashes n
      end
    | '\n' ->
        if n >= 1 then add_backslashes (n-1) else Buffer.add_char buf '\n';
        aux_win buf 0
    | c ->
        add_backslashes n; Buffer.add_char buf c; aux_win buf 0
    and add_backslashes n =
      for _i = 1 to n do Buffer.add_char buf '\\' done in
    aux_win buf 0

let doublequote = if Sys.win32 then doublequote_win else doublequote

let is_add_file file =
  String.length file > 1 && String.get file 0 = '@'

let cut_add file =
  String.sub file 1 (String.length file - 1)

let readwords file =
  let visited = ref [] in
  let rec aux file =
    if Sys.file_exists file then begin
      if List.mem file !visited then
        raise (Arg.Bad "Circular includes in response files");
      visited := file :: !visited;
      let ic = open_in_bin file in
      let buf = Buffer.create 32 in
      let words = ref [] in
      let stash inw =
        if inw then begin
          let word = Buffer.contents buf in
          if is_add_file word then
            words := (aux (cut_add word))@ !words
          else
            words := Buffer.contents buf :: !words;
          Buffer.clear buf
        end in
      let rec unquoted inw =
        match input_char ic with
        | exception End_of_file ->
            stash inw
        | ' ' | '\t' | '\r' | '\n' ->
            stash inw; unquoted false
        | '\\' ->
            begin match input_char ic with
            | exception End_of_file ->    (* tolerance; treat like \newline *)
                unquoted inw
            | '\n' ->
              unquoted inw
            | c ->
                Buffer.add_char buf c; unquoted true
            end
        | '\'' ->
            singlequote ic buf; unquoted true
        | '\"' ->
            doublequote ic buf;
            unquoted true
        | c ->
            Buffer.add_char buf c; unquoted true in
      unquoted false;
      close_in ic;
      !words
    end else [file] in
  List.rev (aux file)

let expand_responsefiles args =
  let acc = ref [] in
  for i = (Array.length args - 1) downto 0 do
    let file = args.(i) in
    if is_add_file file then
      acc := readwords (cut_add file) @ !acc
    else
      acc := file::!acc
  done;
  Array.of_list !acc

let write_responsefile oc args start =
  let whitespace = Str.regexp "[ \t\r\n]" in
  let quote arg =
    if Str.string_match whitespace arg 0 then
      Filename.quote arg (* We need to quote arguments containing whitespaces *)
    else
      arg in
  let first = ref true in
  let sep oc = if !first then
    first := false
  else
    output_string oc " " in
  for i = start to (Array.length args -1) do
    Printf.fprintf oc "%t%s" sep (quote args.(i))
  done

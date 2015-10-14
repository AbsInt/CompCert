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

(* Preprocessor for .vp files *)

open Printf

(* Error reporting *)

let error file line msg =
  eprintf "%s:%d: Error: %s\n" file line msg;
  exit 2

(* Replace newlines with spaces *)

let oneline s =
  String.map (function '\n' -> ' ' | c -> c) s

(* Trim leading and terminating spaces, and compress multiple spaces *)

let re_trim_1 = Str.regexp "^[ \t]+\\|[ \t]+$"
let re_trim_2 = Str.regexp "  +"

let trim s =
  Str.global_replace re_trim_2 " " (Str.global_replace re_trim_1 "" s)

(* A nicer interface to Str.match_string, with automatic trimming *)

let str_match n re s =
  if not (Str.string_match re s 0) then [||] else begin
    let res = Array.make (n+1) "" in
    for i = 1 to n do res.(i) <- Str.matched_group i s done;
    for i = 1 to n do res.(i) <- trim res.(i) done;
    res
  end

(* List all occurrences of the given regexp in the given string *)

let str_grep re s =
  let rec occs pos =
    try
      let pos1 = Str.search_forward re s pos in
      let pos2 = Str.match_end() in
      String.sub s pos1 (pos2 - pos1) :: occs pos2
    with Not_found ->
      []
  in occs 0

(* Auxiliary transformations *)

let re_comma = Str.regexp ", *"

let remove_commas args = Str.global_replace re_comma " " args

(*  "x, y, z"  ->  "x as zz1, y as zz2, z as zz3" *)

let re_arg = Str.regexp "\\([a-z][a-z0-9_]*\\)"

let match_args args =
  let n = ref 0 in
  let subst s =
    incr n; sprintf "%s as zz%d" (Str.matched_group 1 s) !n in
  Str.global_substitute re_arg subst args

(* "x, y, z" -> "zz1 zz2 zz3" *)

let match_temps args =
  let n = ref 0 in
  let subst s =
    incr n; sprintf "zz%d" !n in
  Str.global_substitute re_arg subst (remove_commas args)

(*  "foo, bar, gee" -> "(foo) (bar) (gee)" *)

let parenpats p =
  "(" ^ Str.global_replace re_comma ") (" p ^ ")"

(* Extract the bound variables in a pattern.  Heuristic: any identifier
   that starts with a lowercase letter and is not "nil". *)

let re_ident = Str.regexp "\\([A-Za-z][A-Za-z0-9_]*\\)"

let boundvarspat p =
  String.concat " "
   (List.filter
      (fun id -> id <> "nil" && Str.string_match re_arg id 0)
      (str_grep re_ident p))

(* Given a match argument "id1, id2, id3"
   and a parameter list "(id0: ty0) (id1: ty1) (id2: ty2) (id3: ty3)"
   produce "(id1: ty1) (id2: ty2) (id3: ty3)". *)

let re_param = Str.regexp "(\\([A-Za-z][A-Za-z0-9_]*\\):[^)]*) *"

let matched_params params args =
  let arglist = Str.split re_comma args in
  let filter_param s =
    if List.mem (Str.matched_group 1 s) arglist
    then Str.matched_string s
    else "" in
  Str.global_substitute re_param filter_param params

(* Translation of a "Nondetfunction" *)

let re_nd = Str.regexp(
  "Nondetfunction +\\([a-z][a-z0-9_]*\\) +\\(.+\\):="    (* name, params *)
^ "\\(.*\\)"                                             (* prefix code *)
^ "\\bmatch\\b\\(.*\\)\\bwith\\b"                        (* match arguments *)
^ "\\(.*\\)\\bend\\."                                    (* match cases *)
)

let re_split_cases = Str.regexp "|"

let re_case = Str.regexp "\\(.*\\)=>\\(.*\\)"

let re_default_pat = Str.regexp "[ _,]*$"

let transl_ndfun filename lineno s =
  (* Decompose as follows:
        Nondetfunction <name> <parenthesized parameters> :=
          <prefix>
          match <args> with
            <cases>
          end. *)
  let res = str_match 5 re_nd (oneline s) in
  if Array.length res = 0 then
    error filename lineno "ill-formed 'Nondetfunction'";
  let name = res.(1)
  and params = res.(2)
  and prefix = res.(3)
  and args = res.(4)
  and cases = res.(5) in
  let mparams = matched_params params args in
(***
  printf "name = '%s'\n" name;
  printf "params = '%s'\n" params;
  printf "prefix = '%s'\n" prefix;
  printf "args = '%s'\n" args;
  printf "cases = '%s'\n" cases;
***)
  let a = Buffer.create 2048      (* inductive declaration *)
  and b = Buffer.create 2048      (* matching function *)
  and c = Buffer.create 2048 in   (* computational function *)

  (* Beginning of code *)
  bprintf a "Inductive %s_cases: forall %s, Type :=\n" name mparams;
  bprintf b "Definition %s_match %s :=\n" name mparams;
  bprintf b "  match %s return %s_cases %s with\n"
     (match_args args) name (match_temps args);
  bprintf c "Definition %s %s :=\n" name params;
  bprintf c " %s match %s_match %s with\n" prefix name (remove_commas args);

  (* Adding each case *)
  let numcase = ref 0 in
  let transl_case s =
    let res = str_match 2 re_case s in
    if Array.length res = 0 then
      error filename lineno ("ill-formed case: " ^ s);
    let patlist = res.(1) and rhs = res.(2) in
    let bv = boundvarspat patlist in
    if not (Str.string_match re_default_pat patlist 0) then begin
      incr numcase;
      bprintf a "  | %s_case%d: forall %s, %s_cases %s\n"
          name !numcase bv name (parenpats patlist);
      bprintf b "  | %s => %s_case%d %s\n" patlist name !numcase bv;
      bprintf c "  | %s_case%d %s => (* %s *) \n" name !numcase bv patlist;
      bprintf c "      %s\n" rhs
    end else begin
      let bv = remove_commas args in
      bprintf a "  | %s_default: forall %s, %s_cases %s.\n\n"
         name mparams name bv;
      bprintf b "  | %s => %s_default %s\n" args name bv;
      bprintf b "  end.\n\n";
      bprintf c "  | %s_default %s =>\n" name bv;
      bprintf c "      %s\n" rhs;
      bprintf c "  end.\n\n"
    end
  in List.iter transl_case (Str.split re_split_cases cases);

  (* Generate the output *)
  printf "(** Original definition:\n<<\n%s>>\n*)\n\n" s;
  Buffer.output_buffer stdout a;
  Buffer.output_buffer stdout b;
  Buffer.output_buffer stdout c

(* Main loop: translate "Nondetfunction ... end." fragments in the given
  file.  Copy the rest to standard output. *)

let re_begin_nd_fun = Str.regexp "Nondetfunction\\b"
let re_end_nd_fun = Str.regexp ".*\\bend\\."

let transl_file f =
  let ic = open_in f in
  let b = Buffer.create 2048 in
  let in_nd = ref false in
  let line_no = ref 0 in
  let line_start = ref 0 in
  try
    while true do
      incr line_no;
      let l = input_line ic in
      if !in_nd then begin
        Buffer.add_string b l;
        Buffer.add_char b '\n';
        if Str.string_match re_end_nd_fun l 0 then begin
          transl_ndfun f !line_start (Buffer.contents b);
          Buffer.clear b;
          in_nd := false
        end
      end else begin
        if Str.string_match re_begin_nd_fun l 0 then begin
          Buffer.clear b;
          Buffer.add_string b l;
          Buffer.add_char b '\n';
          in_nd := true;
          line_start := !line_no
        end else begin
          output_string stdout l;
          output_char stdout '\n'
        end
      end
    done
  with End_of_file ->
    close_in ic;
    if !in_nd then error f !line_start "unterminated 'Nondetfunction'"

(* Entry point *)

let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    transl_file Sys.argv.(i)
  done

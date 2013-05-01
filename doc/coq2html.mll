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
open Printf

(** Cross-referencing *)

let current_module = ref ""

type xref =
  | Def of string * string    (* path, type *)
  | Ref of string * string * string (* unit, path, type *)

let xref_table : (string * int, xref) Hashtbl.t = Hashtbl.create 273
let xref_modules : (string, unit) Hashtbl.t = Hashtbl.create 29

let path sp id =
  match sp, id with
  | "<>", "<>" -> ""
  | "<>", _    -> id
  | _   , "<>" -> sp
  | _   , _    -> sp ^ "." ^ id

let add_module m =
  (*eprintf "add_module %s\n" m;*)
  Hashtbl.add xref_modules m ()

let add_reference curmod pos dp sp id ty =
  (*eprintf "add_reference %s %d %s %s %s %s\n" curmod pos dp sp id ty;*)
  if not (Hashtbl.mem xref_table (curmod, pos))
  then Hashtbl.add xref_table (curmod, pos) (Ref(dp, path sp id, ty))

let add_definition curmod pos sp id ty =
  if not (Hashtbl.mem xref_table (curmod, pos))
  then Hashtbl.add xref_table (curmod, pos) (Def(path sp id, ty))

type link = Link of string | Anchor of string | Nolink

let coqlib_url = "http://coq.inria.fr/library/"

let re_coqlib = Str.regexp "Coq\\."
let re_sane_path = Str.regexp "[A-Za-z0-9_.]+$"
let re_shortname = Str.regexp "^.*\\."

let shortname m = Str.replace_first re_shortname "" m

let crossref m pos =
  (*eprintf "crossref %s %d\n" m pos;*)
  try match Hashtbl.find xref_table (m, pos) with
  | Def(p, ty) ->
      Anchor p
  | Ref(m', p, ty) ->
      let url =
        if Hashtbl.mem xref_modules m' then
          shortname m' ^ ".html"
        else if Str.string_match re_coqlib m' 0 then
          coqlib_url ^ m' ^ ".html"
        else
          raise Not_found in
      if p = "" then
        Link url
      else if Str.string_match re_sane_path p 0 then
        Link(url ^ "#" ^ p)
      else
        Nolink
  with Not_found ->
    Nolink

(** Keywords, etc *)

module StringSet = Set.Make(String)

let mkset l = List.fold_right StringSet.add l StringSet.empty

let coq_keywords = mkset [
  "forall"; "match"; "as"; "in"; "return"; "with"; "end"; "let";
  "dest"; "fun"; "if"; "then"; "else"; "Prop"; "Set"; "Type"; ":=";
  "where"; "struct"; "wf"; "measure";
  "AddPath"; "Axiom"; "Abort"; "Boxed"; "Chapter"; "Check";
  "Coercion"; "CoFixpoint"; "CoInductive"; "Corollary"; "Defined";
  "Definition"; "End"; "Eval"; "Example"; "Export"; "Fact"; "Fix";
  "Fixpoint"; "Global"; "Grammar"; "Goal"; "Hint"; "Hypothesis";
  "Hypotheses"; "Resolve"; "Unfold"; "Immediate"; "Extern";
  "Implicit"; "Import"; "Inductive"; "Infix"; "Lemma"; "Let"; "Load";
  "Local"; "Ltac"; "Module"; "Module Type"; "Declare Module";
  "Include"; "Mutual"; "Parameter"; "Parameters"; "Print"; "Proof";
  "Qed"; "Record"; "Recursive"; "Remark"; "Require";
  "Save"; "Scheme"; "Induction"; "for"; "Sort"; "Section"; "Show";
  "Structure"; "Syntactic"; "Syntax"; "Tactic"; "Theorem"; "Set";
  "Types"; "Undo"; "Unset"; "Variable"; "Variables"; "Context";
  "Notation"; "Reserved"; "Tactic"; "Delimit"; "Bind"; "Open";
  "Scope"; "Boxed"; "Unboxed"; "Inline"; "Implicit Arguments"; "Add";
  "Strict"; "Typeclasses"; "Instance"; "Global Instance"; "Class";
  "Instantiation"; "subgoal"; "Program"; "Example"; "Obligation";
  "Obligations"; "Solve"; "using"; "Next"; "Instance"; "Equations";
  "Equations_nocomp"
]

let coq_tactics = mkset [
  "intro"; "intros"; "apply"; "rewrite"; "refine"; "case"; "clear";
  "injection"; "elimtype"; "progress"; "setoid_rewrite"; "destruct";
  "destruction"; "destruct_call"; "dependent"; "elim";
  "extensionality"; "f_equal"; "generalize"; "generalize_eqs";
  "generalize_eqs_vars"; "induction"; "rename"; "move"; "omega";
  "set"; "assert"; "do"; "repeat"; "cut"; "assumption"; "exact";
  "split"; "subst"; "try"; "discriminate"; "simpl"; "unfold"; "red";
  "compute"; "at"; "in"; "by"; "reflexivity"; "symmetry";
  "transitivity"; "replace"; "setoid_replace"; "inversion";
  "inversion_clear"; "pattern"; "intuition"; "congruence"; "fail";
  "fresh"; "trivial"; "exact"; "tauto"; "firstorder"; "ring";
  "clapply"; "program_simpl"; "program_simplify"; "eapply"; "auto";
  "eauto"
]

(** HTML generation *)

let oc = ref stdout

let character = function
  | '<' -> output_string !oc "&lt;"
  | '>' -> output_string !oc "&gt;"
  | '&' -> output_string !oc "&amp;"
  |  c  -> output_char !oc c

let section_level = function
  | "*" -> 1
  | "**" -> 2
  | _ -> 3

let start_section sect =
  fprintf !oc "<h%d>" (section_level sect)
let end_section sect =
  fprintf !oc "</h%d>\n" (section_level sect)

let start_doc_right () =
  fprintf !oc "<span class=\"docright\">(* "
let end_doc_right () =
  fprintf !oc " *)</span>"

let enum_depth = ref 0

let rec set_enum_depth d =
  if !enum_depth < d then begin
    fprintf !oc "<ul>\n";
    fprintf !oc "<li>\n";
    incr enum_depth;
  end 
  else if !enum_depth > d then begin
    fprintf !oc "</li>\n";
    fprintf !oc "</ul>\n";
    decr enum_depth;
  end
  else if !enum_depth > 0 then begin
    fprintf !oc "</li>\n";
    fprintf !oc "<li>\n"
  end

let start_doc () =
  fprintf !oc "<div class=\"doc\">"
let end_doc () =
  set_enum_depth 0;
  fprintf !oc "</div>\n"

let ident pos id =
  if StringSet.mem id coq_keywords then
    fprintf !oc "<span class=\"kwd\">%s</span>" id
  else if StringSet.mem id coq_tactics then
    fprintf !oc "<span class=\"tactic\">%s</span>" id
  else match crossref !current_module pos with
  | Nolink ->
      fprintf !oc "<span class=\"id\">%s</span>" id
  | Link p ->
      fprintf !oc "<span class=\"id\"><a href=\"%s\">%s</a></span>" p id
  | Anchor p ->
      fprintf !oc "<span class=\"id\"><a name=\"%s\">%s</a></span>" p id

let space s =
  for i = 1 to String.length s do fprintf !oc "&nbsp;" done

let newline () =
  fprintf !oc "<br/>\n"

let dashes = function
  | "-" -> set_enum_depth 1
  | "--" -> set_enum_depth 2
  | "---" -> set_enum_depth 3
  | "----" -> set_enum_depth 4
  | _ -> fprintf !oc "<hr/>\n"

let start_verbatim () =
  fprintf !oc "<pre>\n"

let end_verbatim () =
  fprintf !oc "</pre>\n"

let start_bracket () =
  fprintf !oc "<span class=\"bracket\">"

let end_bracket () =
  fprintf !oc "</span>"

let proof_counter = ref 0

let start_proof kwd =
  incr proof_counter;
  fprintf !oc
  "<div class=\"toggleproof\" onclick=\"toggleDisplay('proof%d')\">%s</div>\n"
    !proof_counter kwd;
  fprintf !oc "<div class=\"proofscript\" id=\"proof%d\">\n" !proof_counter

let end_proof kwd =
  fprintf !oc "%s</div>\n" kwd

let start_html_page modname =
  fprintf !oc "\
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">

<head>
<meta http-equiv=\"Content-Type\" content=\"text/html; charset=iso-8859-1\" />
<title>Module %s</title>
<meta name=\"description\" content=\"Documentation of Coq module %s\" />
<link href=\"coq2html.css\" rel=\"stylesheet\" type=\"text/css\" />
<script type=\"text/javascript\" src=\"coq2html.js\"> </script>
</head>

<body onload=\"hideAll('proofscript')\">
<h1 class=\"title\">Module %s</h1>
<div class=\"coq\">
" modname modname modname

let end_html_page () =
  fprintf !oc "\
</div>
<div class=\"footer\"><hr/>Generated by coq2html</div>
</body>
</html>
"

}

let space = [' ' '\t']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let path = ident ("." ident)*
let start_proof = ("Proof" space* ".") | ("Proof" space+ "with") | ("Next" space+ "Obligation.")
let end_proof = "Qed." | "Defined." | "Save." | "Admitted." | "Abort."

let xref = ['A'-'Z' 'a'-'z' '0'-'9' '_' '.']+ | "<>"
let integer = ['0'-'9']+

rule coq_bol = parse
  | space* (start_proof as sp)
      { start_proof sp;
        skip_newline lexbuf }
  | space* "(** " ("*"+ as sect)
      { start_section sect;
        doc lexbuf;
        end_section sect;
        skip_newline lexbuf }
  | space* "(** "
      { start_doc();
        doc lexbuf;
        end_doc();
        skip_newline lexbuf }
  | space* "(*"
      { comment lexbuf;
        skip_newline lexbuf }
  | eof
      { () }
  | space* as s
      { space s; 
        coq lexbuf }

and skip_newline = parse
  | space* "\n"
      { coq_bol lexbuf }
  | ""
      { coq lexbuf }

and coq = parse
  | end_proof as ep
      { end_proof ep;
        skip_newline lexbuf }
  | "(**r "
      { start_doc_right();
        doc lexbuf;
        end_doc_right();
        coq lexbuf }
  | "(*"
      { comment lexbuf;
        coq lexbuf }
  | path as id
      { ident (Lexing.lexeme_start lexbuf) id; coq lexbuf }
  | "\n"
      { newline(); coq_bol lexbuf }
  | eof
      { () }
  | _ as c
      { character c; coq lexbuf }

and bracket = parse
  | ']'
      { () }
  | '['
      { character '['; bracket lexbuf; character ']'; bracket lexbuf }
  | path as id
      { ident (Lexing.lexeme_start lexbuf) id; bracket lexbuf }
  | eof
      { () }
  | _ as c
      { character c; bracket lexbuf }

and comment = parse
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | eof
      { () }
  | _
      { comment lexbuf }

and doc_bol = parse
  | "<<" space* "\n"
      { start_verbatim();
        verbatim lexbuf;
        end_verbatim();
        doc_bol lexbuf }
  | "-"+ as d
      { dashes d; doc lexbuf }
  | "\n"
      { set_enum_depth 0; doc_bol lexbuf }
  | ""
      { doc lexbuf }

and doc = parse
  | "*)"
      { () }
  | "\n"
      { character '\n'; doc_bol lexbuf }
  | "["
      { start_bracket(); bracket lexbuf; end_bracket(); doc lexbuf }
  | "$" [^ '\n' '$']* "$"
      { doc lexbuf }
  | "#" ([^ '\n' '#']* as html) "#"
      { output_string !oc html; doc lexbuf }
  | eof
      { () }
  | _ as c
      { character c; doc lexbuf }

and verbatim = parse
  | "\n>>" space* "\n"
      { () }
  | eof
      { () }
  | _ as c
      { character c; verbatim lexbuf }

and globfile = parse
  | eof
      { () }
  | "F" (path as m) space* "\n"
      { current_module := m; add_module m;
        globfile lexbuf }
  | "R" (integer as pos) ":" (integer as pos2)
    space+ (xref as dp)
    space+ (xref as sp)
    space+ (xref as id)
    space+ (ident as ty)
    space* "\n"
      { add_reference !current_module (int_of_string pos) dp sp id ty;
        globfile lexbuf }
  | (ident as ty)
    space+ (integer as pos) ":" (integer as pos2)
    space+ (xref as sp)
    space+ (xref as id)
    space* "\n"
      { add_definition !current_module (int_of_string pos) sp id ty;
        globfile lexbuf }
  | [^ '\n']* "\n"
      { globfile lexbuf }

{

let output_name = ref "-"

let process_file f =
  if Filename.check_suffix f ".v" then begin
    let pref_f = Filename.chop_suffix f ".v" in
    let base_f = Filename.basename pref_f in
    current_module := 
      "compcert." ^ Str.global_replace (Str.regexp "/") "." pref_f;
    let ic = open_in f in
    if !output_name = "-" then
      oc := stdout
    else
      oc := open_out (Str.global_replace (Str.regexp "%") base_f !output_name);
    start_html_page base_f;
    coq_bol (Lexing.from_channel ic);
    end_html_page();
    if !output_name <> "-" then (close_out !oc; oc := stdout);
    close_in ic
  end else
  if Filename.check_suffix f ".glob" then begin
    current_module := "";
    let ic = open_in f in
    globfile (Lexing.from_channel ic);
    close_in ic
  end else begin
    eprintf "Don't know what to do with file %s\n" f;
    exit 2
  end

let _ =
  Arg.parse [
    "-o", Arg.String (fun s -> output_name := s),
      " <output>   Set output file ('%' replaced by module name)"
  ] process_file
  "Usage: coq2html [options] <file.glob> file.v\nOptions are:"
}

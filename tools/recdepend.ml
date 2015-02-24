(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbstInt Angewandte Informatik GmbH      *)
(*                                                                     *)
(*  Copyright AbstInt Angewandte Informatik GmbH. All rights reserved. *)
(*  This file is distributed under the terms of the GNU General Public *)
(*  License as published by the Free Software Foundation, either       *)
(*  version 2 of the License, or (at your option) any later version.   *)
(*                                                                     *)
(* *********************************************************************)

(* Generate dependencies for directories by calling dependencie tool *)

(* The tools *)
let ocamlfind = ref "ocamlfind"
let ocamldep = ref "ocamldep"
let menhir = ref "menhir"

(* Some controling options *)
let use_ocamlfind = ref false
let use_menhir = ref false
let dirs_to_search = ref ([] : string list)
let target_file = ref (None: string option)
let error_occured = ref false

(* Options for ocamldep *)
let include_dirs = ref ([] : string list)
let ml_synonyms = ref [".ml"]
let mli_synonyms = ref [".mli"]
let slash = ref false
let native_only = ref false
let raw_dependencies = ref false
let pp_command = ref (None: string option)
let ppx_command = ref ([] : string list)
let all_dependencies = ref false
let open_modules = ref ([] : string list)
let one_line = ref false
let ocamlfind_package = ref ""
let ocamlfind_syntax = ref ""
let ocamlfind_ppopt = ref ([] : string list)

(* Helper functions for options *)
let add_to_list li s =
  li := s :: !li

let add_to_synonym_list synonyms suffix =
  if (String.length suffix) > 1 && (String.get suffix 0) = '.' then
    add_to_list synonyms suffix
  else
    Printf.eprintf "Bad file suffix '%s'.\n" suffix

let usage = "Usage: recdepend [options] <directories>\nOptions are:"

type file_type =
  | ML
  | MLI
  | MLL

let get_files () =
  let rec files_of_dir acc dir =
    let files = Sys.readdir dir in
    let contains_files = ref false in
    let acc = Array.fold_left (fun acc f_name ->
      if Sys.is_directory (Filename.concat dir f_name) then
          files_of_dir acc (Filename.concat dir f_name)
      else
        if List.exists (Filename.check_suffix f_name) !ml_synonyms then
          begin
            contains_files := true;
            (ML,(Filename.concat dir f_name))::acc
          end
        else if List.exists (Filename.check_suffix f_name) !mli_synonyms then
          begin
            contains_files := true;
            (MLI,(Filename.concat dir f_name))::acc
          end
        else if !use_menhir && (Filename.check_suffix f_name ".mll") then
          begin
            contains_files := true;
            (MLL,(Filename.concat dir f_name))::acc
          end
        else
            acc) acc files in
    if !contains_files then
      add_to_list include_dirs dir;
    acc in
  try
    List.fold_left files_of_dir [] !dirs_to_search
  with _ ->
    error_occured := true;
    []

let compute_dependencies files =
  try let out_file = match !target_file with
  | None -> Unix.stdout 
  | Some s -> Unix.openfile s [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o666 in
  let call_ocamldep file =
    let args = List.fold_left (fun args s -> "-I"::(s::args)) [file] !include_dirs in
    let args = List.fold_left (fun args syn -> 
      if syn = ".ml" then 
        args 
      else 
        "-ml-synonym"::(syn::args)) args !ml_synonyms in
    let args =   List.fold_left (fun args syn -> 
      if syn = ".mli" then 
        args 
      else 
        "-mli-synonym"::(syn::args)) args !mli_synonyms in
    let args = if !slash then "-slash"::args else args in
    let args = if !native_only then "-native"::args else args in
    let args = if !raw_dependencies then "-modules"::args else args in
    let args = match !pp_command with
    | None -> args
    | Some s -> "-pp"::(s::args) in
    let args = List.fold_left (fun opts ppx -> "-ppx"::(ppx::args)) args !ppx_command in
    let args = if !all_dependencies then "-all"::args else args in
    let args = List.fold_left (fun opts o_mod -> "-open"::(o_mod::opts)) args !open_modules in
    let args = if !one_line then "-one-line"::args else args in
    let args = if !use_ocamlfind then
      let args = if !ocamlfind_package <> "" then
        "-package"::(!ocamlfind_package::args)
      else
        args in
      let args = if !ocamlfind_syntax <> "" then
        "-syntax"::(!ocamlfind_syntax::args)
      else
        args in
      let args = List.fold_left (fun args s -> "-ppopt"::(s::args)) args !ocamlfind_ppopt in
      !ocamlfind::("ocamldep"::args)
    else 
      !ocamldep :: args in
    let argv = Array.of_list args in
    let pid = Unix.create_process argv.(0) argv Unix.stdin out_file Unix.stderr in
    let (_,status) =
      Unix.waitpid [] pid in
    let rc = (match status with
    | Unix.WEXITED rc -> rc
    | Unix.WSIGNALED _
    | Unix.WSTOPPED _ -> -1) in
    error_occured := !error_occured || rc <> 0 in
  let call_menhir file =
    let args = [!menhir;"--depend";"--ocamldep";!ocamldep] in
    let args = if !raw_dependencies then args@["--raw-depend"] else args in
    let argv = Array.of_list args in
    let pid = Unix.create_process argv.(0) argv Unix.stdin out_file Unix.stderr in
    let (_,status) =
      Unix.waitpid [] pid in
    let rc = (match status with
    | Unix.WEXITED rc -> rc
    | Unix.WSIGNALED _
    | Unix.WSTOPPED _ -> -1) in
    error_occured := !error_occured || rc <> 0 in
  List.iter (fun (f_type,f_name) ->
    match f_type with
    | ML
    | MLI -> call_ocamldep f_name
    | MLL -> if !use_menhir then call_menhir f_name) files;
  if !target_file <> None then Unix.close out_file
  with Unix.Unix_error _ ->
      error_occured := true


let _ =
  Arg.parse [
  "-all", Arg.Set all_dependencies,
  " Generate dependencies on all files";
  "-dep", Arg.Set_string ocamldep,
  "<cmd> Use <cmd> instead of ocamldep";
  "-I", Arg.String (add_to_list include_dirs),
  "<dir> Add <dir> to the list of include directories";
  "-menhir", Arg.String (fun s -> use_menhir:= true; menhir := s),
  "<cmd> Use <cmd> instead of menhir";
  "-ml-synonym", Arg.String (add_to_synonym_list ml_synonyms),
  "<e> Consider <e> as synonym of the .ml extension";
  "-mli-synonym", Arg.String (add_to_synonym_list mli_synonyms),
  "<e> Consider <e> as synonym of the .mli extension";
  "-modules", Arg.Set raw_dependencies,
  " Print module dependencies in raw form";
  "-native", Arg.Set native_only,
  " Generate dependencies for native-code only";
  "-o", Arg.String (fun s -> target_file := Some s),
  "<f> Write the dependencies in file <f>";
  "-ocamlfind", Arg.String (fun s -> use_ocamlfind := true; ocamlfind := s),
  "<cmd> Use <cmd> instead of ocamlfind";
  "-one-line", Arg.Set one_line,
  " Output only ine line per file, regardless of length";
  "-open", Arg.String (add_to_list open_modules),
  "<module> Opens the module <module> before typing";
  "-package", Arg.Set_string ocamlfind_package,
  " <p> Pass the package option <p> to ocamlfind";
  "-ppopt", Arg.String (add_to_list ocamlfind_ppopt),
  " <p> Pass the camlp4 option <p> to ocamlfind"; 
  "-pp", Arg.String (fun s -> pp_command := Some s),
  "<cmd> Pipe sources through preprocessor <cmd>";
  "-ppx", Arg.String (add_to_list ppx_command),
  "<cmd> Pipe abstract syntax trees through preprocessor <cmd>";
  "-slash", Arg.Set slash,
  " (Windows) Use foward slash / instead of backslash \\ in file paths";
  "-syntax", Arg.Set_string ocamlfind_syntax,
  " <p> Pass the syntax option <p> to ocamlfind";
  "-use-menhir", Arg.Set use_menhir,
  " Use menhir to callculate the dependencies of .mll files";
  "-use-ocamlfind", Arg.Set use_ocamlfind,
  " Use ocamlfind as driver for ocamldepend";]
    (add_to_list dirs_to_search) usage;
  let files = get_files () in
  compute_dependencies files;
  exit (if !error_occured then 2 else 0)

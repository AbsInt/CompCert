(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

open Printf

let search_argv key =
  let len = Array.length Sys.argv in
  let res: string option ref = ref None in
  for i = 1 to len - 2 do
    if Sys.argv.(i) = key then
      res := Some Sys.argv.(i + 1);
  done;
  !res

let absolute_path base file =
  if Filename.is_relative file then
    Filename.concat base file
  else
    file

(* Locate the .ini file, which is either in the same directory as
  the executable or in the directory ../share *)

let ini_file_name =
  match search_argv "-conf" with
  | Some s -> absolute_path (Sys.getcwd ()) s
  | None ->
      try
        Sys.getenv "COMPCERT_CONFIG"
      with Not_found ->
        let ini_name = match search_argv "-target" with
        | Some s -> s^".ini"
        | None -> "compcert.ini" in
        let exe_dir = Filename.dirname Sys.executable_name in
        let share_dir =
          Filename.concat (Filename.concat exe_dir Filename.parent_dir_name)
            "share" in
        let share_compcert_dir =
          Filename.concat share_dir "compcert" in
        let search_path = [exe_dir;share_dir;share_compcert_dir] in
        let files = List.map (fun s -> Filename.concat s ini_name) search_path in
        try
          List.find  Sys.file_exists files
        with Not_found ->
          begin
            eprintf "Cannot find compcert.ini configuration file.\n";
            exit 2
          end

let ini_dir = Filename.dirname ini_file_name

(* Read in the .ini file *)

let _ =
  try
    Readconfig.read_config_file ini_file_name
  with
  | Readconfig.Error(file, lineno, msg) ->
      eprintf "Error reading configuration file %s.\n" ini_file_name;
      eprintf "%s:%d:%s\n" file lineno msg;
      exit 2
  | Sys_error msg ->
      eprintf "Error reading configuration file %s.\n" ini_file_name;
      eprintf "%s\n" msg;
      exit 2

let get_config key =
  match Readconfig.key_val key with
  | Some v -> v
  | None -> eprintf "Configuration option `%s' is not set\n" key; exit 2

let bad_config key vl =
  eprintf "Invalid value `%s' for configuration option `%s'\n"
          (String.concat " " vl) key;
  exit 2

let get_config_string key =
  match get_config key with
  | [v] -> v
  | vl -> bad_config key vl

let get_config_list key =
  match get_config key with
  | [] -> bad_config key []
  | vl -> vl

let tool_absolute_path tools =
  match tools with
  | [] -> []
  | tool::args -> let tool =
      if Filename.is_implicit tool && Filename.dirname tool = Filename.current_dir_name then
        tool
      else
        absolute_path ini_dir tool in
    tool::args

let opt_config_list key =
  match Readconfig.key_val key with
  | Some v -> v
  | None -> []

let prepro =
  tool_absolute_path (get_config_list "prepro")@(opt_config_list "prepro_options")
let asm =
  tool_absolute_path (get_config_list "asm")@(opt_config_list "asm_options")
let linker =
  tool_absolute_path (get_config_list "linker")@(opt_config_list "linker_options")

let get_bool_config key =
  match get_config_string key with
  | "true" -> true
  | "false" -> false
  | v -> bad_config key [v]

let arch =
  match get_config_string "arch" with
  | "powerpc"|"arm"|"x86" as a -> a
  | v -> bad_config "arch" [v]
let model = get_config_string "model"
let abi = get_config_string "abi"
let is_big_endian =
  match get_config_string "endianness" with
  | "big" -> true
  | "little" -> false
  | v -> bad_config "endianness" [v]
let system = get_config_string "system"
let has_runtime_lib = get_bool_config "has_runtime_lib"
let has_standard_headers = get_bool_config "has_standard_headers"
let stdlib_path =
  if has_runtime_lib then
    let path = get_config_string "stdlib_path" in
    absolute_path ini_dir path
  else
    ""
let asm_supports_cfi = get_bool_config "asm_supports_cfi"


type struct_passing_style =
  | SP_ref_callee                       (* by reference, callee takes copy *)
  | SP_ref_caller                       (* by reference, caller takes copy *)
  | SP_split_args                       (* by value, as a sequence of ints *)

type struct_return_style =
  | SR_int1248      (* return by content if size is 1, 2, 4 or 8 bytes *)
  | SR_int1to4      (* return by content if size is <= 4 *)
  | SR_int1to8      (* return by content if size is <= 8 *)
  | SR_ref          (* always return by assignment to a reference
                       given as extra argument *)

let struct_passing_style =
  match get_config_string "struct_passing_style" with
  | "ref-callee" -> SP_ref_callee
  | "ref-caller" -> SP_ref_caller
  | "ints"       -> SP_split_args
  | v -> bad_config "struct_passing_style" [v]

let struct_return_style =
  match get_config_string "struct_return_style" with
  | "int1248"  -> SR_int1248
  | "int1-4"   -> SR_int1to4
  | "int1-8"   -> SR_int1to8
  | "ref"      -> SR_ref
  | v -> bad_config "struct_return_style" [v]

type response_file_style =
  | Gnu         (* responsefiles in gnu compatible syntax *)
  | Diab        (* responsefiles in diab compatible syntax *)
  | Unsupported (* responsefiles are not supported *)

let response_file_style =
  match get_config_string "response_file_style" with
  | "unsupported" -> Unsupported
  | "gnu" -> Gnu
  | "diab" -> Diab
  | v -> bad_config "response_file_style" [v]

let gnu_toolchain = system <> "diab"

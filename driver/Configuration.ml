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

(* Locate the .ini file, which is either in the same directory as
  the executable or in the directory ../share *)

let ini_file_name =
  try
    Sys.getenv "COMPCERT_CONFIG"
  with Not_found ->
    let exe_dir = Filename.dirname Sys.executable_name in
    let exe_ini = Filename.concat exe_dir "compcert.ini" in
    let share_dir =
      Filename.concat (Filename.concat exe_dir Filename.parent_dir_name)
                      "share" in
    let share_ini = Filename.concat share_dir "compcert.ini" in
    if Sys.file_exists exe_ini then exe_ini
    else if Sys.file_exists share_ini then share_ini
    else begin 
      eprintf "Cannot find compcert.ini configuration file.\n";
      exit 2
    end

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

let prepro = get_config_list "prepro"
let asm = get_config_list "asm"
let linker = get_config_list "linker"
let arch = 
  match get_config_string "arch" with
  | "powerpc"|"arm"|"ia32" as a -> a
  | v -> bad_config "arch" [v]
let model = get_config_string "model"
let abi = get_config_string "abi"
let system = get_config_string "system"
let has_runtime_lib = 
  match get_config_string "has_runtime_lib" with
  | "true" -> true
  | "false" -> false
  | v -> bad_config "has_runtime_lib" [v]
let stdlib_path =
  if has_runtime_lib then
    get_config_string "stdlib_path"
  else
    ""
let asm_supports_cfi = 
  match get_config_string "asm_supports_cfi" with
  | "true" -> true
  | "false" -> false
  | v -> bad_config "asm_supports_cfi" [v]

let version = get_config_string "version"

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

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


let config_vars: (string, string) Hashtbl.t = Hashtbl.create 10


(* Read in the .ini file, which is either in the same directory or in the directory ../share *)
let _ =
  try
    let file = 
      try
        let env_file = Sys.getenv "COMPCERT_CONFIG" in
        open_in env_file
      with Not_found ->
        let dir = Sys.getcwd () 
        and name = Sys.executable_name in
        let dirname = if Filename.is_relative name then
          Filename.dirname (Filename.concat dir name)
        else 
          Filename.dirname name
        in
        let share_dir = Filename.concat (Filename.concat dirname Filename.parent_dir_name) "share" in
        try
          open_in (Filename.concat dirname "compcert.ini")
        with Sys_error _ ->
          open_in (Filename.concat share_dir "compcert.ini")
    in
    (try
      let ini_line = Str.regexp "\\([^=]+\\)=\\(.+\\)" in
      while true do
        let line = input_line file in
        if Str.string_match ini_line line 0 then
          let key = Str.matched_group 1 line
          and value = Str.matched_group 2 line in
          Hashtbl.add config_vars key value
        else
          Printf.eprintf "Wrong value %s in .ini file.\n" line
      done
    with End_of_file -> close_in file)
  with Sys_error msg -> Printf.eprintf "Unable to open .ini file\n"

let get_config key =
  try
    Hashtbl.find config_vars key
  with Not_found ->
    Printf.eprintf "Configuration option `%s' is not set\n" key; exit 2

let bad_config key v =
  Printf.eprintf "Invalid value `%s' for configuation option `%s'\n" v key; exit 2

let prepro = get_config "prepro"
let asm = get_config "asm"
let linker = get_config "linker"
let arch = 
  let v = get_config "arch" in
  (match v with
  | "powerpc"
  | "arm"
  | "ia32" -> ()
  | _ -> bad_config "arch" v);
  v

let model = get_config "model"
let abi = get_config "abi"
let system = get_config "system"
let has_runtime_lib = 
  match get_config "has_runtime_lib" with
  | "true" -> true
  | "false" -> false
  | v -> bad_config "has_runtime_lib" v


let stdlib_path =
  if has_runtime_lib then
    get_config "stdlib_path"
  else
    ""

let asm_supports_cfi = 
  match get_config "asm_supports_cfi" with
  | "true" -> true
  | "false" -> false
  | v -> bad_config "asm_supports_cfi" v

let version = get_config "version"

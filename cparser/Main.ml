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

(* Wrapper around gcc to parse, transform, pretty-print, and call gcc on result *)

let transfs = ref ""

let safe_remove name =
  try Sys.remove name with Sys_error _ -> ()

let process_c_file prepro_opts name =
  let ppname = Filename.temp_file "cparser" ".i" in
  let cpname = Filename.chop_suffix name ".c" ^ ".i" in
  let rc =
    Sys.command
      (Printf.sprintf "gcc -E -U__GNUC__ %s %s > %s"
                      (String.concat " " (List.map Filename.quote prepro_opts))
                      (Filename.quote name) (Filename.quote ppname)) in
  if rc <> 0 then begin
    safe_remove ppname;
    exit 2
  end;
  let r = Parse.preprocessed_file !transfs name ppname in
  safe_remove ppname;
  match r with
  | None -> exit 2
  | Some p -> 
      let oc = open_out cpname in
      let oform = Format.formatter_of_out_channel oc in
      Cprint.program oform p;
      close_out oc;
      cpname

let starts_with pref s =
  String.length s >= String.length pref 
  && String.sub s 0 (String.length pref) = pref

let ends_with suff s =
  String.length s >= String.length suff 
  && String.sub s (String.length s - String.length suff) (String.length suff)
     = suff

let rec parse_cmdline prepro args i =
  if i >= Array.length Sys.argv then List.rev args else begin
    (* should skip arguments more cleanly... *)
    let s = Sys.argv.(i) in
    if s = "-Xsimplif" && i + 1 < Array.length Sys.argv then begin
      transfs := Sys.argv.(i+1);
      parse_cmdline prepro args (i+2)
    end else if (s = "-I" || s = "-D" || s = "-U") 
             && i + 1 < Array.length Sys.argv then 
      parse_cmdline (Sys.argv.(i+1) :: s :: prepro) args (i+2)
    else if starts_with "-I" s
             || starts_with "-D" s
             || starts_with "-U" s then
      parse_cmdline (s :: prepro) args (i + 1)
    else if s = "-Wall" then
      parse_cmdline prepro ("-Wno-parentheses" :: "-Wall" :: args) (i+1)
    else if ends_with ".c" s then begin
      let s' = process_c_file (List.rev prepro) s in
      parse_cmdline prepro (s' :: args) (i + 1)
    end else
      parse_cmdline prepro (s :: args) (i + 1)
  end

let _ =
  Builtins.set GCC.builtins;
  let args = parse_cmdline [] [] 1 in
  let cmd = "gcc " ^ String.concat " " (List.map Filename.quote args) in
  let rc = Sys.command cmd in
  exit rc

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

(* Parsing of command-line flags and arguments *)

open Printf
open Responsefile

type pattern =
  | Exact of string
  | Prefix of string
  | Suffix of string
  | Regexp of Str.regexp

let _Regexp re = Regexp (Str.regexp re)

type action =
  | Set of bool ref
  | Unset of bool ref
  | Self of (string -> unit)
  | String of (string -> unit)
  | Integer of (int -> unit)
  | Ignore
  | Unit of (unit -> unit)

exception CmdError of string

let match_pattern text = function
  | Exact s ->
      text = s
  | Prefix pref ->
      let lpref = String.length pref and ltext = String.length text in
      lpref < ltext && String.sub text 0 lpref = pref
      (* strict prefix: no match if pref = text. See below. *)
  | Suffix suff ->
      let lsuff = String.length suff and ltext = String.length text in
      lsuff < ltext && String.sub text (ltext - lsuff) lsuff = suff
      (* strict suffix: no match if suff = text, so that e.g. ".c"
         causes an error rather than being treated as a C source file. *)
  | Regexp re ->
      Str.string_match re text 0

let rec find_action text = function
  | [] -> None
  | (pat, act) :: rem ->
      if match_pattern text pat then Some act else find_action text rem

let parse_array spec argv first last =
  (* Split the spec into Exact patterns (in a hashtable) and other patterns *)
  let exact_cases = (Hashtbl.create 29 : (string, action) Hashtbl.t) in
  let rec split_spec = function
    | [] -> []
    | (Exact s, act) :: rem -> Hashtbl.add exact_cases s act; split_spec rem
    | (pat, act) :: rem -> (pat, act) :: split_spec rem in
  let inexact_cases = split_spec spec in
  (* Parse the vector of arguments *)
  let rec parse i =
    if i <= last then begin
      let s = argv.(i) in
      let optact =
        try Some (Hashtbl.find exact_cases s)
        with Not_found -> find_action s inexact_cases in
      match optact with
      | None ->
        let msg = sprintf "unknown argument `%s'" s in
        raise (CmdError msg)
      | Some(Set r) ->
          r := true; parse (i+1)
      | Some(Unset r) ->
          r := false; parse (i+1)
      | Some(Self fn) ->
          fn s; parse (i+1)
      | Some(String fn) ->
          if i + 1 <= last then begin
            fn argv.(i+1); parse (i+2)
          end else begin
            let msg = sprintf "option `%s' expects an argument" s in
            raise (CmdError msg)
          end
      | Some(Integer fn) ->
          if i + 1 <= last then begin
            let n =
              try
                int_of_string argv.(i+1)
              with Failure _ ->
                let msg = sprintf "argument to option `%s' must be an integer" s in
                raise (CmdError msg)
            in
            fn n; parse (i+2)
          end else begin
            let msg = sprintf  "option `%s' expects an argument" s in
            raise (CmdError msg)
          end
      | Some (Ignore) ->
          if i + 1 <= last then begin
            parse (i+2)
          end else begin
            let msg = sprintf "option `%s' expects an argument" s in
            raise (CmdError msg)
          end
      | Some (Unit f) -> f (); parse (i+1)
    end
  in parse first

let argv : string array ref = ref [||]

let parse_cmdline spec =
  try
    argv := expandargv Sys.argv;
    parse_array spec !argv 1 (Array.length !argv - 1)
  with Responsefile.Error s ->
    raise (CmdError s)

let long_int_action key s =
  let ls = String.length s
  and lkey = String.length key in
  assert (ls > lkey);
  let s = String.sub s (lkey + 1) (ls - lkey - 1) in
  try
    int_of_string s
  with Failure _ ->
    let msg =  sprintf "argument to option `%s' must be an integer" key in
    raise (CmdError msg)

let longopt_int key f =
  let act s =
    let n = long_int_action key s in
    f n in
  Prefix (key ^ "="),Self act

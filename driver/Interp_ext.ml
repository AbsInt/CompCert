(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Implementing external functions for the reference interpreter.
   The only such function currently implemented is "printf". *)

open Format
open Camlcoq
open AST
open Values
open Memory

(* Extract a string from a global pointer *)

let extract_string m blk ofs =
  let b = Buffer.create 80 in
  let rec extract blk ofs =
    match Mem.load Mint8unsigned m blk ofs with
    | Some(Vint n) ->
        let c = Char.chr (Z.to_int n) in
        if c = '\000' then begin
          Some(Buffer.contents b)
        end else begin
          Buffer.add_char b c; 
          extract blk (Z.succ ofs)
        end
    | _ ->
        None in
  extract blk ofs

(* Emulation of printf *)

(* All ISO C 99 formats except size modifier [L] (long double) *)

let re_conversion = Str.regexp
  "%[-+0# ]*[0-9]*\\(\\.[0-9]*\\)?\\([lhjzt]\\|hh\\|ll\\)?\\([aAcdeEfgGinopsuxX%]\\)"

external format_float: string -> float -> string
  = "caml_format_float"
external format_int32: string -> int32 -> string
  = "caml_int32_format"
external format_int64: string -> int64 -> string
  = "caml_int64_format"

let do_printf m fmt args =

  let b = Buffer.create 80 in
  let len = String.length fmt in

  let opt_search_forward pos =
    try Some(Str.search_forward re_conversion fmt pos)
    with Not_found -> None in

  let rec scan pos args =
    if pos < len then begin
    match opt_search_forward pos with
    | None ->
        Buffer.add_substring b fmt pos (len - pos)
    | Some pos1 ->
        Buffer.add_substring b fmt pos (pos1 - pos);
        let pat = Str.matched_string fmt
        and conv = Str.matched_group 3 fmt
        and pos' = Str.match_end() in
        match args, conv.[0] with
        | _, '%' ->
            Buffer.add_char b '%';
            scan pos' args
        | [], _ ->
            Buffer.add_string b "<missing argument>";
            scan pos' []
        | Vint i :: args', ('d'|'i'|'u'|'o'|'x'|'X'|'c') ->
            Buffer.add_string b (format_int32 pat (camlint_of_coqint i));
            scan pos' args'
        | Vfloat f :: args', ('f'|'e'|'E'|'g'|'G'|'a') ->
            Buffer.add_string b (format_float pat (camlfloat_of_coqfloat f));
            scan pos' args'
        | Vlong i :: args', ('d'|'i'|'u'|'o'|'x'|'X') ->
            let pat = Str.replace_first (Str.regexp "ll") "" pat in
            Buffer.add_string b (format_int64 pat (camlint64_of_coqint i));
            scan pos' args'
        | Vptr(blk, ofs) :: args', 's' ->
            Buffer.add_string b
              (match extract_string m blk ofs with
               | Some s -> s
               | None -> "<bad string>");
            scan pos' args'
        | Vptr(blk, ofs) :: args', 'p' ->
            Printf.bprintf b "<%ld%+ld>" (P.to_int32 blk) (camlint_of_coqint ofs);
            scan pos' args'
        | _ :: args', _ ->
            Buffer.add_string b "<formatting error>";
            scan pos' args'
    end
  in scan 0 args; Buffer.contents b

(* Implementation of external functions *)

let re_stub = Str.regexp "\\$[ifl]*$"

let chop_stub name = Str.replace_first re_stub "" name

let do_external_function id sg args m =
  match chop_stub(extern_atom id), args with
  | "printf", Vptr(b, ofs) :: args' ->
      begin match extract_string m b ofs with
      | Some fmt -> print_string (do_printf m fmt args')
      | None     -> print_string "<bad printf>\n"
      end;
      flush stdout;
      Some Vundef
  | _ ->
      None

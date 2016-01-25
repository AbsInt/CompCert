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

(* Simple functions for JSON printing *)

(* Print a string as json string *)
let p_jstring oc s = fprintf oc "\"%s\"" s

(* Print a list as json array *)
let p_jarray elem oc l =
  match l with
  | [] -> fprintf oc "[]"
  | hd::tail ->
      output_string oc "["; elem oc hd;
      List.iter (fprintf oc ",%a" elem) tail;
      output_string oc "]"

(* Print a bool as json bool *)
let p_jbool oc = fprintf oc "%B"

(* Print a int as json int *)
let p_jint oc = fprintf oc "%d"

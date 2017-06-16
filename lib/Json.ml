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
let p_jstring oc s =
  fprintf oc "\"%s\"" s

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

(* Print an int as json int *)
let p_jint oc = fprintf oc "%d"

(* Print an int32 as json int *)
let p_jint32 oc = fprintf oc "%ld"

(* Print a member *)
let p_jmember oc name p_mem mem =
  fprintf oc "\n%a:%a" p_jstring name p_mem mem

(* Print singleton object *)
let p_jsingle_object oc name p_mem mem =
  fprintf oc "{%a:%a}" p_jstring name p_mem mem

(* Print optional value *)
let p_jopt p_elem oc = function
  | None -> output_string oc "null"
  | Some i -> p_elem oc i

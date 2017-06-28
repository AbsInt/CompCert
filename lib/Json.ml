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

open Format

(* Simple functions for JSON printing *)

(* Print a string as json string *)
let pp_jstring oc s =
  fprintf oc "\"%s\"" s

(* Print a bool as json bool *)
let pp_jbool oc = fprintf oc "%B"

(* Print an int as json int *)
let pp_jint oc = fprintf oc "%d"

(* Print an int32 as json int *)
let pp_jint32 oc = fprintf oc "%ld"

(* Print optional value *)
let pp_jopt pp_elem oc = function
  | None -> output_string oc "null"
  | Some i -> pp_elem oc i

let pp_jobject_start pp =
  fprintf pp "@[<v 1>{"

let pp_jobject_end pp =
  fprintf pp "@;<0 -1>}@]"

(* Print a member *)
let pp_jmember ?(first=false) pp name pp_mem mem =
  let sep = if first then "" else "," in
  fprintf pp "%s@ \"%s\": %a" sep name pp_mem mem

(* Print singleton object *)
let pp_jsingle_object pp name pp_mem mem =
  pp_jobject_start pp;
  pp_jmember ~first:true pp name pp_mem mem;
  pp_jobject_end pp

(* Print a list as json array *)
let pp_jarray elem pp l =
  match l with
  | []  ->  fprintf pp "[]";
  | hd::tail ->
    fprintf pp "@[<v 1>[";
    fprintf pp "%a" elem hd;
    List.iter (fun l -> fprintf pp ",@ %a" elem l) tail;
  fprintf pp "@;<0 -1>]@]"

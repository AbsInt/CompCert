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
open Camlcoq


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

(* Print opening and closing curly braces for json dictionaries *)
let pp_jobject_start pp =
  fprintf pp "@[<v 1>{"

let pp_jobject_end pp =
  fprintf pp "@;<0 -1>}@]"

(* Print a member of a json dictionary *)
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

(* Helper functions for printing coq integer and floats *)
let pp_int pp i =
  fprintf pp "%ld" (camlint_of_coqint i)

let pp_int64 pp i =
  fprintf pp "%Ld" (camlint64_of_coqint i)

let pp_float32 pp f =
  fprintf pp "%ld" (camlint_of_coqint (Floats.Float32.to_bits f))

let pp_float64 pp f =
  fprintf pp "%Ld" (camlint64_of_coqint (Floats.Float.to_bits f))

let pp_z pp z =
  fprintf pp "%s" (Z.to_string z)

(* Helper functions for printing assembler constructs *)
let pp_atom pp a =
  pp_jstring pp (extern_atom a)

let pp_atom_constant pp a =
  pp_jsingle_object pp "Atom" pp_atom a

let pp_int_constant pp i =
  pp_jsingle_object pp "Integer" pp_int i

let pp_float64_constant pp f =
  pp_jsingle_object pp "Float" pp_float64 f

let pp_float32_constant pp f =
  pp_jsingle_object pp "Float" pp_float32 f

let id = ref 0

let next_id () =
  let tmp = !id in
  incr id;
  tmp

let reset_id () =
  id := 0

let pp_id_const pp () =
  let i = next_id () in
  pp_jsingle_object pp "Integer" (fun pp i -> fprintf pp "%d" i) i

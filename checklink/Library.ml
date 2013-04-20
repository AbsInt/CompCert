open Camlcoq

type bitstring = Bitstring.bitstring

module IntMap = Map.Make(struct type t = int let compare = compare end)
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let is_some: 'a option -> bool = function
| Some(_) -> true
| None    -> false

let from_some: 'a option -> 'a = function
| Some(x) -> x
| None    -> raise Not_found

let filter_some (l: 'a option list): 'a list =
  List.(map from_some (filter is_some l))

type 'a or_err =
  | OK of 'a
  | ERR of string

let is_ok: 'a or_err -> bool = function
| OK(_) -> true
| ERR(_) -> false

let is_err x = not (is_ok x)

let from_ok: 'a or_err -> 'a = function
| OK(x) -> x
| ERR(_) -> assert false

let from_err: 'a or_err -> string = function
| OK(_) -> assert false
| ERR(s) -> s

let filter_ok (l: 'a or_err list): 'a list =
  List.(map from_ok (filter is_ok l))

let filter_err (l: 'a or_err list): string list =
  List.(map from_err (filter is_err l))

external id : 'a -> 'a = "%identity"

(** [a; a + 1; ... ; b - 1; b] *)
let list_ab (a: int) (b: int): int list =
  let rec list_ab_aux a b res =
    if b < a
    then res
    else list_ab_aux a (b - 1) (b :: res)
  in list_ab_aux a b []

(** [0; 1; ...; n - 1] *)
let list_n (n: int): int list =
  list_ab 0 (n - 1)

(** Checks for existence of an array element satisfying a condition, and returns
    its index if it exists.
*)
let array_exists (cond: 'a -> bool) (arr: 'a array): int option =
  let rec array_exists_aux ndx =
    if ndx < 0
    then None
    else if cond arr.(ndx)
    then Some ndx
    else array_exists_aux (ndx - 1)
  in array_exists_aux (Array.length arr - 1)

exception IntOverflow
exception Int32Overflow

(* Can only return positive numbers 0 <= res < 2^31 *)
let positive_int32 p =
  let rec positive_int32_unsafe = function
  | P.Coq_xI(p) -> Int32.(add (shift_left (positive_int32_unsafe p) 1) 1l)
  | P.Coq_xO(p) -> Int32.(shift_left (positive_int32_unsafe p) 1)
  | P.Coq_xH    -> 1l
  in
  let res = positive_int32_unsafe p in
  if res >= 0l
  then res
  else raise IntOverflow

(* This allows for 1 bit of overflow, effectively returning a negative *)
let rec positive_int32_lax = function
| P.Coq_xI(p) ->
    let acc = positive_int32_lax p in
    if acc < 0l
    then raise Int32Overflow
    else Int32.(add (shift_left acc 1) 1l)
| P.Coq_xO(p) ->
    let acc = positive_int32_lax p in
    if acc < 0l
    then raise Int32Overflow
    else Int32.shift_left acc 1
| P.Coq_xH -> 1l

let z_int32 = function
| Z.Z0      -> 0l
| Z.Zpos(p) -> positive_int32 p
| Z.Zneg(p) -> Int32.neg (positive_int32 p)

let z_int32_lax = function
| Z.Z0      -> 0l
| Z.Zpos(p) -> positive_int32_lax p
| Z.Zneg(_) -> raise Int32Overflow

let z_int z = Safe32.to_int (z_int32 z)

let z_int_lax z = Safe32.to_int (z_int32_lax z)

let z_int64 = Camlcoq.Z.to_int64

(* Some more printers *)

let string_of_ffloat f = string_of_float (camlfloat_of_coqfloat f)

let string_of_array string_of_elt sep a =
  let b = Buffer.create 1024 in
  Buffer.add_string b "[\n";
  Array.iteri
    (fun ndx elt ->
       if ndx > 0 then Buffer.add_string b sep;
       Buffer.add_string b (string_of_int ndx);
       Buffer.add_string b ": ";
       Buffer.add_string b (string_of_elt elt)
    ) a;
  Buffer.add_string b "\n]";
  Buffer.contents b

let string_of_list string_of_elt sep l =
  String.concat sep (List.map string_of_elt l)

let string_of_bitstring bs =
  let rec string_of_bitset_aux bs =
    bitmatch bs with
    | { bit  : 1  : int       ;
        rest : -1 : bitstring } ->
        (if bit then "1" else "0") ^ (string_of_bitset_aux rest)
    | { _ } -> ""
  in string_of_bitset_aux bs

(* To print addresses/offsets *)
let string_of_int32 = Printf.sprintf "0x%08lx"
let string_of_int64 = Printf.sprintf "0x%08Lx"
(* To print counts/indices *)
let string_of_int32i = Int32.to_string
let string_of_int64i = Int64.to_string

let string_of_positive p = string_of_int32i (positive_int32 p)

let string_of_z z = string_of_int32 (z_int32 z)

let sorted_lookup (compare: 'a -> 'b -> int) (arr: 'a array) (v: 'b): 'a option =
  let rec sorted_lookup_aux (i_from: int) (i_to: int): 'a option =
    if i_from > i_to
    then None
    else
      let i_mid = (i_from + i_to) / 2 in
      let comp = compare arr.(i_mid) v in
      if comp < 0 (* v_mid < v *)
      then sorted_lookup_aux (i_mid + 1) i_to
      else if comp > 0
      then sorted_lookup_aux i_from (i_mid - 1)
      else Some(arr.(i_mid))
  in sorted_lookup_aux 0 (Array.length arr - 1)

let list_false_indices a =
  filter_some (Array.(to_list (mapi (fun ndx b -> if b then None else Some(ndx)) a)))

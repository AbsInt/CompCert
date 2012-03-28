open BinInt
open BinPos

type bitstring = Bitstring.bitstring

let from_some = function
| Some(x) -> x
| None    -> raise Not_found

type 'a on_success =
  | OK of 'a
  | ERR of string

let is_ok: 'a on_success -> bool = function
| OK(_) -> true
| ERR(_) -> false

let from_ok = function
| OK(x) -> x
| ERR(_) -> raise Not_found

let filter_ok l = List.(map from_ok (filter is_ok l))

external id : 'a -> 'a = "%identity"

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

(* Functions for safely converting between numeric types *)

exception Integer_overflow

let int32_int (i32: int32): int =
  let i = Int32.to_int i32 in
  if i32 = Int32.of_int i
  then i
  else raise Integer_overflow

let int_int32 = Int32.of_int

(* Can only return positive numbers 0 <= res < 2^31 *)
let positive_int32 p =
  let rec positive_int32_unsafe = function
  | Coq_xI(p) -> Int32.(add (shift_left (positive_int32_unsafe p) 1) 1l)
  | Coq_xO(p) -> Int32.(shift_left (positive_int32_unsafe p) 1)
  | Coq_xH    -> 1l
  in
  let res = positive_int32_unsafe p in
  if res >= 0l
  then res
  else raise Integer_overflow

(* This allows for 1 bit of overflow, effectively returning a negative *)
let rec positive_int32_lax = function
| Coq_xI(p) ->
    let acc = positive_int32_lax p in
    if acc < 0l
    then raise Integer_overflow
    else Int32.(add (shift_left acc 1) 1l)
| Coq_xO(p) ->
    let acc = positive_int32_lax p in
    if acc < 0l
    then raise Integer_overflow
    else Int32.shift_left acc 1
| Coq_xH -> 1l

let z_int32 = function
| Z0      -> 0l
| Zpos(p) -> positive_int32 p
| Zneg(p) -> Int32.neg (positive_int32 p)

let z_int32_lax = function
| Z0      -> 0l
| Zpos(p) -> positive_int32_lax p
| Zneg(p) -> raise Integer_overflow

let z_int z = int32_int (z_int32 z)

let z_int_lax z = int32_int (z_int32_lax z)

(* Some more printers *)

let string_of_array string_of_elt sep a =
  "[\n" ^
    fst (
      Array.fold_left
        (
          fun accu elt ->
            let (str, ndx) = accu in
            (str ^ (if ndx > 0 then sep else "") ^ string_of_int ndx ^ ": " ^
               string_of_elt elt, ndx + 1)
        )
        ("", 0) a
    ) ^
    "\n]"

let string_of_list string_of_elt sep l =
  String.concat sep (List.map string_of_elt l)

let string_of_bitstring bs =
  let rec string_of_bitset_aux bs =
    bitmatch bs with
    | { bit  : 1  : int       ;
        rest : -1 : bitstring } ->
        (if bit
         then "1"
         else "0") ^ (string_of_bitset_aux rest)
    | { _ } -> ""
  in string_of_bitset_aux bs

(* To print addresses/offsets *)
let string_of_int32 = Printf.sprintf "0x%08lx"
(* To print counts/indices *)
let string_of_int32i = Int32.to_string

let string_of_positive p = string_of_int32i (positive_int32 p)

let string_of_z z = string_of_int32 (z_int32 z)

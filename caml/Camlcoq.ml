(* Library of useful Caml <-> Coq conversions *)

open Datatypes
open CList
open BinPos
open BinInt

(* Integers *)

let rec camlint_of_positive = function
  | Coq_xI p -> Int32.add (Int32.shift_left (camlint_of_positive p) 1) 1l
  | Coq_xO p -> Int32.shift_left (camlint_of_positive p) 1
  | Coq_xH -> 1l

let camlint_of_z = function
  | Z0 -> 0l
  | Zpos p -> camlint_of_positive p
  | Zneg p -> Int32.neg (camlint_of_positive p)

let camlint_of_coqint : Integers.int -> int32 = camlint_of_z

let rec camlint_of_nat = function
  | O -> 0
  | S n -> camlint_of_nat n + 1

let rec nat_of_camlint n =
  assert (n >= 0l);
  if n = 0l then O else S (nat_of_camlint (Int32.sub n 1l))

let rec positive_of_camlint n =
  if n = 0l then assert false else
  if n = 1l then Coq_xH else
  if Int32.logand n 1l = 0l
  then Coq_xO (positive_of_camlint (Int32.shift_right n 1))
  else Coq_xI (positive_of_camlint (Int32.shift_right n 1))

let z_of_camlint n =
  if n = 0l then Z0 else
  if n > 0l then Zpos (positive_of_camlint n)
  else Zneg (positive_of_camlint (Int32.neg n))

let coqint_of_camlint : int32 -> Integers.int = z_of_camlint

(* Strings *)

let atom_of_string = (Hashtbl.create 17 : (string, positive) Hashtbl.t)
let string_of_atom = (Hashtbl.create 17 : (positive, string) Hashtbl.t)
let next_atom = ref Coq_xH

let intern_string s =
  try
    Hashtbl.find atom_of_string s
  with Not_found ->
    let a = !next_atom in
    next_atom := coq_Psucc !next_atom;
    Hashtbl.add atom_of_string s a;
    Hashtbl.add string_of_atom a s;
    a

let extern_atom a =
  try
    Hashtbl.find string_of_atom a
  with Not_found ->
    Printf.sprintf "<unknown atom %ld>" (camlint_of_positive a)

(* Lists *)

let rec coqlist_iter f = function
    Coq_nil -> ()
  | Coq_cons(a,l) -> f a; coqlist_iter f l

(* Helpers *)

let rec list_iter f = function
    [] -> ()
  | a::l -> f a; list_iter f l

let rec list_memq x = function
    [] -> false
  | a::l -> a == x || list_memq x l

let rec list_exists p = function
    [] -> false
  | a::l -> p a || list_exists p l

let rec list_filter p = function
    [] -> []
  | x :: l -> if p x then x :: list_filter p l else list_filter p l

let rec length_coqlist = function
  | Coq_nil -> 0
  | Coq_cons (x, l) -> 1 + length_coqlist l

let array_of_coqlist = function
  | Coq_nil -> [||]
  | Coq_cons(hd, tl) as l ->
      let a = Array.create (length_coqlist l) hd in
      let rec fill i = function
        | Coq_nil -> a
        | Coq_cons(hd, tl) -> a.(i) <- hd; fill (i + 1) tl in
      fill 1 tl


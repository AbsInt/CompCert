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

(* Library of useful Caml <-> Coq conversions *)

open Datatypes
open BinNums
open BinNat
open BinInt
open BinPos
open! Floats

(* Coq's [nat] type and some of its operations *)

module Nat = struct

  type t = nat = O | S of t

  let rec to_int = function
  | O -> 0
  | S n -> succ (to_int n)

  let rec to_int32 = function
  | O -> 0l
  | S n -> Int32.succ(to_int32 n)

  let rec of_int n =
    assert (n >= 0);
    if n = 0 then O else S (of_int (pred n))

  let rec of_int32 n =
    assert (n >= 0l);
    if n = 0l then O else S (of_int32 (Int32.pred n))

end


(* Coq's [positive] type and some of its operations *)

module P = struct

  type t = positive = Coq_xI of t | Coq_xO of t | Coq_xH

  let one = Coq_xH
  let succ = Pos.succ
  let pred = Pos.pred
  let eq x y = (Pos.compare x y = Eq)
  let lt x y = (Pos.compare x y = Lt)
  let gt x y = (Pos.compare x y = Gt)
  let le x y = (Pos.compare x y <> Gt)
  let ge x y = (Pos.compare x y <> Lt)
  let compare x y = match Pos.compare x y with Lt -> -1 | Eq -> 0 | Gt -> 1

  let rec to_int = function
  | Coq_xI p -> let n = to_int p in n + n + 1
  | Coq_xO p -> let n = to_int p in n + n
  | Coq_xH -> 1

  let rec of_int n =
    if n land 1 = 0 then
      if n = 0 then assert false else Coq_xO (of_int (n lsr 1))
    else
      if n = 1 then Coq_xH else Coq_xI (of_int (n lsr 1))

  let rec to_int32 = function
  | Coq_xI p -> Int32.add (Int32.shift_left (to_int32 p) 1) 1l
  | Coq_xO p -> Int32.shift_left (to_int32 p) 1
  | Coq_xH -> 1l

  let rec of_int32 n =
    if Int32.logand n 1l = 0l then
      if n = 0l
      then assert false
      else Coq_xO (of_int32 (Int32.shift_right_logical n 1))
    else
      if n = 1l
      then Coq_xH
      else Coq_xI (of_int32 (Int32.shift_right_logical n 1))

  let rec to_int64 = function
  | Coq_xI p -> Int64.add (Int64.shift_left (to_int64 p) 1) 1L
  | Coq_xO p -> Int64.shift_left (to_int64 p) 1
  | Coq_xH -> 1L

  let rec of_int64 n =
    if Int64.logand n 1L = 0L then
      if n = 0L
      then assert false
      else Coq_xO (of_int64 (Int64.shift_right_logical n 1))
    else
      if n = 1L
      then Coq_xH
      else Coq_xI (of_int64 (Int64.shift_right_logical n 1))

  let (=) = eq
  let (<) = lt
  let (<=) = le
  let (>) = gt
  let (>=) = ge

end

(* Coq's [N] type and some of its operations *)

module N = struct

  type t = coq_N = N0 | Npos of positive

  let zero = N0
  let one = Npos Coq_xH
  let eq x y = (N.compare x y = Eq)
  let lt x y = (N.compare x y = Lt)
  let gt x y = (N.compare x y = Gt)
  let le x y = (N.compare x y <> Gt)
  let ge x y = (N.compare x y <> Lt)
  let compare x y = match N.compare x y with Lt -> -1 | Eq -> 0 | Gt -> 1

  let to_int = function
  | N0 -> 0
  | Npos p -> P.to_int p

  let of_int n =
    if n = 0 then N0 else Npos (P.of_int n)

  let to_int32 = function
  | N0 -> 0l
  | Npos p -> P.to_int32 p

  let of_int32 n =
    if n = 0l then N0 else Npos (P.of_int32 n)

  let to_int64 = function
  | N0 -> 0L
  | Npos p -> P.to_int64 p

  let of_int64 n =
    if n = 0L then N0 else Npos (P.of_int64 n)

  let (=) = eq
  let (<) = lt
  let (<=) = le
  let (>) = gt
  let (>=) = ge
end

(* Coq's [Z] type and some of its operations *)

module Z = struct

  type t = coq_Z = Z0 | Zpos of positive | Zneg of positive

  let zero = Z0
  let one = Zpos Coq_xH
  let mone = Zneg Coq_xH
  let succ = Z.succ
  let pred = Z.pred
  let neg = Z.opp
  let add = Z.add
  let sub = Z.sub
  let mul = Z.mul
  let div = Z.div
  let modulo = Z.modulo
  let eq x y = (Z.compare x y = Eq)
  let lt x y = (Z.compare x y = Lt)
  let gt x y = (Z.compare x y = Gt)
  let le x y = (Z.compare x y <> Gt)
  let ge x y = (Z.compare x y <> Lt)
  let compare x y = match Z.compare x y with Lt -> -1 | Eq -> 0 | Gt -> 1

  let to_int = function
  | Z0 -> 0
  | Zpos p -> P.to_int p
  | Zneg p -> - (P.to_int p)

  let of_sint n =
    if n = 0 then Z0 else
    if n > 0 then Zpos (P.of_int n)
    else Zneg (P.of_int (-n))

  let of_uint n =
    if n = 0 then Z0 else Zpos (P.of_int n)

  let to_int32 = function
  | Z0 -> 0l
  | Zpos p -> P.to_int32 p
  | Zneg p -> Int32.neg (P.to_int32 p)

  let of_sint32 n =
    if n = 0l then Z0 else
    if n > 0l then Zpos (P.of_int32 n)
    else Zneg (P.of_int32 (Int32.neg n))

  let of_uint32 n =
    if n = 0l then Z0 else Zpos (P.of_int32 n)

  let to_int64 = function
  | Z0 -> 0L
  | Zpos p -> P.to_int64 p
  | Zneg p -> Int64.neg (P.to_int64 p)

  let of_sint64 n =
    if n = 0L then Z0 else
    if n > 0L then Zpos (P.of_int64 n)
    else Zneg (P.of_int64 (Int64.neg n))

  let of_uint64 n =
    if n = 0L then Z0 else Zpos (P.of_int64 n)

  let of_N = Z.of_N

  let rec to_string_rec base buff x =
    if x = Z0 then () else begin
      let (q, r) = Z.div_eucl x base in
      to_string_rec base buff q;
      let d = to_int r in
      Buffer.add_char buff (Char.chr
        (if d < 10 then Char.code '0' + d
                         else Char.code 'A' + d - 10))
    end

  let to_string_aux base x =
    match x with
    | Z0 -> "0"
    | Zpos _ ->
        let buff = Buffer.create 10 in
        to_string_rec base buff x;
        Buffer.contents buff
    | Zneg p ->
        let buff = Buffer.create 10 in
        Buffer.add_char buff '-';
        to_string_rec base buff (Zpos p);
        Buffer.contents buff

  let dec = to_string_aux (of_uint 10)

  let hex = to_string_aux (of_uint 16)

  let to_string = dec

  let is_power2 x =
    gt x zero && eq (Z.coq_land x (pred x)) zero

  let (+) = add
  let (-) = sub
  let ( * ) = mul
  let ( / ) = div
  let (=) = eq
  let (<) = lt
  let (<=) = le
  let (>) = gt
  let (>=) = ge
end


(* Alternate names *)

let camlint_of_coqint : Integers.Int.int -> int32 = Z.to_int32
let coqint_of_camlint : int32 -> Integers.Int.int = Z.of_uint32
   (* interpret the int32 as unsigned so that result Z is in range for int *)
let camlint64_of_coqint : Integers.Int64.int -> int64 = Z.to_int64
let coqint_of_camlint64 : int64 -> Integers.Int64.int = Z.of_uint64
   (* interpret the int64 as unsigned so that result Z is in range for int *)
let camlint64_of_ptrofs : Integers.Ptrofs.int -> int64 =
  fun x -> Z.to_int64 (Integers.Ptrofs.signed x)

(* Atoms (positive integers representing strings) *)

type atom = positive

let atom_of_string = (Hashtbl.create 17 : (string, atom) Hashtbl.t)
let string_of_atom = (Hashtbl.create 17 : (atom, string) Hashtbl.t)
let next_atom = ref Coq_xH
let use_canonical_atoms = ref false

(* If [use_canonical_atoms] is false, strings are numbered from 1 up
   in the order in which they are encountered.  This produces small
   numbers, and is therefore efficient, but the number for a given
   string may differ between the compilation of different units.

   If [use_canonical_atoms] is true, strings are Huffman-encoded as bit
   sequences, which are then encoded as positive numbers.  The same
   string is always represented by the same number in all compilation
   units.  However, the numbers are bigger than in the first
   implementation.  Also, this places a hard limit on the number of
   fresh identifiers that can be generated starting with
   [first_unused_ident]. *)

let rec append_bits_pos nbits n p =
  if nbits <= 0 then p else
  if n land 1 = 0
  then Coq_xO (append_bits_pos (nbits - 1) (n lsr 1) p)
  else Coq_xI (append_bits_pos (nbits - 1) (n lsr 1) p)

(* The encoding of strings as bit sequences is optimized for C identifiers:
   - numbers are encoded as a 6-bit integer between 0 and 9
   - lowercase letters are encoded as a 6-bit integer between 10 and 35
   - uppercase letters are encoded as a 6-bit integer between 36 and 61
   - the underscore character is encoded as the 6-bit integer 62
   - all other characters are encoded as 6 "one" bits followed by
     the 8-bit encoding of the character. *)

let append_char_pos c p =
  match c with
  | '0'..'9' -> append_bits_pos 6 (Char.code c - Char.code '0') p
  | 'a'..'z' -> append_bits_pos 6 (Char.code c - Char.code 'a' + 10) p
  | 'A'..'Z' -> append_bits_pos 6 (Char.code c - Char.code 'A' + 36) p
  | '_'      -> append_bits_pos 6 62 p
  | _        -> append_bits_pos 6 63 (append_bits_pos 8 (Char.code c) p)

(* The empty string is represented as the positive "1", that is, [xH]. *)

let pos_of_string s =
  let rec encode i accu =
    if i < 0 then accu else encode (i - 1) (append_char_pos s.[i] accu)
  in encode (String.length s - 1) Coq_xH

let fresh_atom () =
  let a = !next_atom in
  next_atom := Pos.succ !next_atom;
  a

let intern_string s =
  try
    Hashtbl.find atom_of_string s
  with Not_found ->
    let a =
      if !use_canonical_atoms then pos_of_string s else fresh_atom () in
    Hashtbl.add atom_of_string s a;
    Hashtbl.add string_of_atom a s;
    a

let extern_atom a =
  try
    Hashtbl.find string_of_atom a
  with Not_found ->
    Printf.sprintf "$%d" (P.to_int a)

(* Ignoring the terminating "1" bit, canonical encodings of strings can
   be viewed as lists of bits, formed by concatenation of 6-bit fragments
   (for letters, numbers, and underscore) and 14-bit fragments (for other
   characters).  Hence, not all positive numbers are canonical encodings:
   only those whose log2 is of the form [6n + 14m].

   Here are the first intervals of positive numbers corresponding to strings:
   - [1, 1] for the empty string
   - [2^6, 2^7-1] for one "compact" character
   - [2^12, 2^13-1] for two "compact" characters
   - [2^14, 2^14-1] for one "escaped" character

   Hence, between 2^7 and 2^12 - 1, we have 3968 consecutive positive
   numbers that cannot be the encoding of a string.  These are the positive
   numbers we'll use as temporaries in the SimplExpr pass if canonical
   atoms are in use.

   If short atoms are used, we just number the temporaries consecutively
   starting one above the last generated atom.
*)

let first_unused_ident () =
  if !use_canonical_atoms
  then P.of_int 128
  else !next_atom

(* Strings *)

let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

let coqstring_of_camlstring s =
  let rec cstring accu pos =
    if pos < 0 then accu else cstring (s.[pos] :: accu) (pos - 1)
  in cstring [] (String.length s - 1)

let coqstring_uppercase_ascii_of_camlstring s =
  let rec cstring accu pos =
    if pos < 0 then accu else
    let d = if s.[pos] >= 'a' && s.[pos] <= 'z' then
      Char.chr (Char.code s.[pos] - 32)
    else
      s.[pos] in
    cstring (d :: accu) (pos - 1)
  in cstring [] (String.length s - 1)

(* Floats *)

let coqfloat_of_camlfloat f =
  Float.of_bits(coqint_of_camlint64(Int64.bits_of_float f))
let camlfloat_of_coqfloat f =
  Int64.float_of_bits(camlint64_of_coqint(Float.to_bits f))

let coqfloat32_of_camlfloat f =
  Float32.of_bits(coqint_of_camlint(Int32.bits_of_float f))
let camlfloat_of_coqfloat32 f =
  Int32.float_of_bits(camlint_of_coqint(Float32.to_bits f))

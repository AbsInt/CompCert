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

open Camlcoq
open Switch
open CminorSel

let more_likely (c: condexpr) (ifso: stmt) (ifnot: stmt) = false

module IntOrd =
  struct
    type t = Integers.int
    let compare x y =
      if Integers.Int.eq x y then 0 else
      if Integers.Int.ltu x y then -1 else 1
  end

module IntSet = Set.Make(IntOrd)

let normalize_table tbl =
  let rec norm seen = function
  | [] -> []
  | Datatypes.Coq_pair(key, act) :: rem ->
      if IntSet.mem key seen
      then norm seen rem
      else (key, act) :: norm (IntSet.add key seen) rem
  in norm IntSet.empty tbl

let compile_switch default table =
  let sw = Array.of_list (normalize_table table) in
  Array.stable_sort (fun (n1, _) (n2, _) -> IntOrd.compare n1 n2) sw;
  let rec build lo hi minval maxval =
    match hi - lo with
    | 0 ->
       CTaction default
    | 1 ->
       let (key, act) = sw.(lo) in
       if Integers.Int.sub maxval minval = Integers.Int.zero
       then CTaction act
       else CTifeq(key, act, CTaction default)
    | 2 ->
       let (key1, act1) = sw.(lo)
       and (key2, act2) = sw.(lo+1) in
       CTifeq(key1, act1,
         if Integers.Int.sub maxval minval = Integers.Int.one
         then CTaction act2
         else CTifeq(key2, act2, CTaction default))
    | 3 ->
       let (key1, act1) = sw.(lo)
       and (key2, act2) = sw.(lo+1)
       and (key3, act3) = sw.(lo+2) in
       CTifeq(key1, act1, 
        CTifeq(key2, act2,
          if Integers.Int.sub maxval minval = coqint_of_camlint 2l
          then CTaction act3
          else CTifeq(key3, act3, CTaction default)))
    | _ ->
       let mid = (lo + hi) / 2 in
       let (pivot, _) = sw.(mid) in
       CTiflt(pivot,
              build lo mid minval (Integers.Int.sub pivot Integers.Int.one),
              build mid hi pivot maxval)
  in build 0 (Array.length sw) Integers.Int.zero Integers.Int.max_unsigned

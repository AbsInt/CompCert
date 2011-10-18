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
    type t = Integers.Int.int
    let compare x y =
      if Integers.Int.eq x y then 0 else
      if Integers.Int.ltu x y then -1 else 1
  end

module IntSet = Set.Make(IntOrd)

let normalize_table tbl =
  let rec norm keys accu = function
  | [] -> (accu, keys)
  | (key, act) :: rem ->
      if IntSet.mem key keys
      then norm keys accu rem
      else norm (IntSet.add key keys) ((key, act) :: accu) rem
  in norm IntSet.empty [] tbl

let compile_switch_as_tree default tbl =
  let sw = Array.of_list tbl in
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

let uint64_of_coqint n = (* force unsigned interpretation *)
  Int64.logand (Int64.of_int32 (camlint_of_coqint n)) 0xFFFF_FFFFL

let compile_switch_as_jumptable default cases minkey maxkey =
  let tblsize = 1 + Int64.to_int (Int64.sub maxkey minkey) in
  assert (tblsize >= 0 && tblsize <= Sys.max_array_length);
  let tbl = Array.make tblsize default in
  List.iter
    (fun (key, act) ->
       let pos = Int64.to_int (Int64.sub (uint64_of_coqint key) minkey) in
       tbl.(pos) <- act)
    cases;
  CTjumptable(coqint_of_camlint (Int64.to_int32 minkey), 
              coqint_of_camlint (Int32.of_int tblsize),
              Array.to_list tbl,
              CTaction default)

let dense_enough (numcases: int) (minkey: int64) (maxkey: int64) =
  let span = Int64.sub maxkey minkey in
  assert (span >= 0L);
  let tree_size = Int64.mul 4L (Int64.of_int numcases)
  and table_size = Int64.add 8L span in
  numcases >= 7           (* really small jump tables are less efficient *)
  && span < Int64.of_int Sys.max_array_length
  && table_size <= tree_size

let compile_switch default table =
  let (tbl, keys) = normalize_table table in
  if IntSet.is_empty keys then CTaction default else begin
    let minkey = uint64_of_coqint (IntSet.min_elt keys)
    and maxkey = uint64_of_coqint (IntSet.max_elt keys) in
    if dense_enough (List.length tbl) minkey maxkey
    then compile_switch_as_jumptable default tbl minkey maxkey
    else compile_switch_as_tree default tbl
  end

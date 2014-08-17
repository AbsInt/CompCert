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

open Datatypes
open Camlcoq
open Switch

(* Compiling a switch table into a decision tree *)

module ZSet = Set.Make(Z)

let normalize_table tbl =
  let rec norm keys accu = function
  | [] -> (accu, keys)
  | (key, act) :: rem ->
      if ZSet.mem key keys
      then norm keys accu rem
      else norm (ZSet.add key keys) ((key, act) :: accu) rem
  in norm ZSet.empty [] tbl

let compile_switch_as_tree modulus default tbl =
  let sw = Array.of_list tbl in
  Array.stable_sort (fun (n1, _) (n2, _) -> Z.compare n1 n2) sw;
  let rec build lo hi minval maxval =
    match hi - lo with
    | 0 ->
       CTaction default
    | 1 ->
       let (key, act) = sw.(lo) in
       if Z.sub maxval minval = Z.zero
       then CTaction act
       else CTifeq(key, act, CTaction default)
    | 2 ->
       let (key1, act1) = sw.(lo)
       and (key2, act2) = sw.(lo+1) in
       CTifeq(key1, act1,
         if Z.sub maxval minval = Z.one
         then CTaction act2
         else CTifeq(key2, act2, CTaction default))
    | 3 ->
       let (key1, act1) = sw.(lo)
       and (key2, act2) = sw.(lo+1)
       and (key3, act3) = sw.(lo+2) in
       CTifeq(key1, act1, 
        CTifeq(key2, act2,
          if Z.sub maxval minval = Z.of_uint 2
          then CTaction act3
          else CTifeq(key3, act3, CTaction default)))
    | _ ->
       let mid = (lo + hi) / 2 in
       let (pivot, _) = sw.(mid) in
       CTiflt(pivot,
              build lo mid minval (Z.sub pivot Z.one),
              build mid hi pivot maxval)
  in build 0 (Array.length sw) Z.zero modulus

let compile_switch_as_jumptable default cases minkey maxkey =
  let tblsize = 1 + Z.to_int (Z.sub maxkey minkey) in
  assert (tblsize >= 0 && tblsize <= Sys.max_array_length);
  let tbl = Array.make tblsize default in
  List.iter
    (fun (key, act) ->
       let pos = Z.to_int (Z.sub key minkey) in
       tbl.(pos) <- act)
    cases;
  CTjumptable(minkey,
              Z.of_uint tblsize,
              Array.to_list tbl,
              CTaction default)

let dense_enough (numcases: int) (minkey: Z.t) (maxkey: Z.t) =
  let span = Z.sub maxkey minkey in
  assert (Z.ge span Z.zero);
  let tree_size = Z.mul (Z.of_uint 4) (Z.of_uint numcases)
  and table_size = Z.add (Z.of_uint 8) span in
  numcases >= 7           (* small jump tables are always less efficient *)
  && Z.le table_size tree_size
  && Z.lt span (Z.of_uint Sys.max_array_length)

let compile_switch modulus default table =
  let (tbl, keys) = normalize_table table in
  if ZSet.is_empty keys then CTaction default else begin
    let minkey = ZSet.min_elt keys
    and maxkey = ZSet.max_elt keys in
    if dense_enough (List.length tbl) minkey maxkey
    then compile_switch_as_jumptable default tbl minkey maxkey
    else compile_switch_as_tree modulus default tbl
  end



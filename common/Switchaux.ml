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

(* For debugging *)
(**
open Format

let print_table p (tbl, dfl) =
  fprintf p "@[<v 0>";
  List.iter
    (fun (key, act) -> fprintf p "%s -> %d@ " (Z.to_string key) (Nat.to_int act))
    tbl;
  fprintf p "_ -> %d@]" (Nat.to_int dfl)

let rec print_jumptable p = function
  | [] -> fprintf p "<empty>"
  | [n] -> fprintf p "%d" (Nat.to_int n)
  | n::ns -> fprintf p "%d %a" (Nat.to_int n) print_jumptable ns

let rec print_tree p = function
  | CTaction n -> fprintf p "action %d" (Nat.to_int n)
  | CTifeq(key, act, t) ->
      fprintf p "@[<v 2>if (x == %s)@ action %d@;<0 -2>else@ %a@]"
              (Z.to_string key) (Nat.to_int act) print_tree t
  | CTiflt(key, t1, t2) ->
      fprintf p "@[<v 2>if (x <u %s)@ %a@;<0 -2>else@ %a@]"
              (Z.to_string key) print_tree t1 print_tree t2
  | CTjumptable(ofs, sz, acts,t) ->
      fprintf p "@[<v 2>if (x - %s <u %s)@ jumptable %a@;<0 -2>else@ %a@]"
              (Z.to_string ofs) (Z.to_string sz)
              print_jumptable acts print_tree t

let compile_switch modulus default table =
  let t = compile_switch modulus default table in
  printf "@[<v 0>-------------@ ";
  printf "Initial problem:@ %a@ " print_table (table, default);
  printf "Decision tree:@ %a@ @]@." print_tree t;
  t
**)

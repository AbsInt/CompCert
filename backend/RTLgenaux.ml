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
open CminorSel

(* Heuristic to orient if-then-else statements.
   If "false" is returned generates a conditional branch to the "then" branch
   and a fall-through to the "else" branch.
   If "true" is returned generates a conditional branch to the "else" branch
   and a fall-through to the "then" branch.
   The fall-through behavior is generally slightly more efficient,
   for average-case execution time as well as for worst-case.
   The heuristic is based on an estimate of the sizes of the "then" and
   "else" branches, in terms of rough number of instructions, and on
   putting the bigger of the two branches in fall-through position. *)

let rec size_expr = function
  | Evar id -> 0
  | Eop(op, args) -> 1 + size_exprs args
  | Eload(chunk, addr, args) -> 1 + size_exprs args
  | Econdition(ce, e1, e2) ->
      1 + size_condexpr ce + max (size_expr e1) (size_expr e2)
  | Elet(e1, e2) -> size_expr e1 + size_expr e2
  | Eletvar n -> 0
  | Ebuiltin(ef, el) -> 2 + size_exprs el
  | Eexternal(id, sg, el) -> 5 + size_exprs el

and size_exprs = function
  | Enil -> 0
  | Econs(e1, el) -> size_expr e1 + size_exprs el

and size_condexpr = function
  | CEcond(c, args) -> size_exprs args
  | CEcondition(c1, c2, c3) ->
      1 + size_condexpr c1 + size_condexpr c2 + size_condexpr c3
  | CElet(a, c) ->
      size_expr a + size_condexpr c

let rec length_exprs = function
  | Enil -> 0
  | Econs(e1, el) -> 1 + length_exprs el

let size_eos = function
  | Coq_inl e -> size_expr e
  | Coq_inr id -> 0

let rec size_stmt = function
  | Sskip -> 0
  | Sassign(id, a) -> size_expr a
  | Sstore(chunk, addr, args, src) -> 1 + size_exprs args + size_expr src 
  | Scall(optid, sg, eos, args) ->
      3 + size_eos eos + size_exprs args + length_exprs args
  | Stailcall(sg, eos, args) ->
      3 + size_eos eos + size_exprs args + length_exprs args
  | Sbuiltin(optid, ef, args) -> 1 + size_exprs args
  | Sseq(s1, s2) -> size_stmt s1 + size_stmt s2
  | Sifthenelse(ce, s1, s2) ->
      size_condexpr ce + max (size_stmt s1) (size_stmt s2)
  | Sloop s -> 1 + 4 * size_stmt s
  | Sblock s -> size_stmt s
  | Sexit n -> 1
  | Sswitch(arg, tbl, dfl) -> 2 + size_expr arg
  | Sreturn None -> 2
  | Sreturn (Some arg) -> 2 + size_expr arg
  | Slabel(lbl, s) -> size_stmt s
  | Sgoto lbl -> 1

let more_likely (c: condexpr) (ifso: stmt) (ifnot: stmt) = 
  size_stmt ifso > size_stmt ifnot

(* Compiling a switch table into a decision tree *)

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

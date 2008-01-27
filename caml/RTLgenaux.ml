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
  | CList.Coq_nil -> []
  | CList.Coq_cons(Datatypes.Coq_pair(key, act), rem) ->
      if IntSet.mem key seen
      then norm seen rem
      else (key, act) :: norm (IntSet.add key seen) rem
  in norm IntSet.empty tbl

let compile_switch default table =
  let sw = Array.of_list (normalize_table table) in
  Array.stable_sort (fun (n1, _) (n2, _) -> IntOrd.compare n1 n2) sw;
  let rec build lo hi =
    match hi - lo with
    | 0 ->
       CTaction default
    | 1 ->
       CTifeq(fst sw.(lo), snd sw.(lo), CTaction default)
    | 2 ->
       CTifeq(fst sw.(lo), snd sw.(lo),
       CTifeq(fst sw.(lo+1), snd sw.(lo+1),
       CTaction default))
    | 3 ->
       CTifeq(fst sw.(lo), snd sw.(lo),
       CTifeq(fst sw.(lo+1), snd sw.(lo+1),
       CTifeq(fst sw.(lo+2), snd sw.(lo+2),
       CTaction default)))
    | _ ->
       let mid = (lo + hi) / 2 in
       CTiflt(fst sw.(mid), build lo mid, build mid hi)
  in build 0 (Array.length sw)


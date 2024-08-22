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
open AST
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

let size_exprlist al = List.fold_right (fun a s -> size_expr a + s) al 0

let size_builtin_args al = size_exprlist (params_of_builtin_args al)

let rec size_exitexpr = function
  | XEexit n -> 0
  | XEjumptable(arg, tbl) -> 2 + size_expr arg
  | XEcondition(c1, c2, c3) ->
      1 + size_condexpr c1 + size_exitexpr c2 + size_exitexpr c3
  | XElet(a, c) ->
      size_expr a + size_exitexpr c

let rec length_exprs = function
  | Enil -> 0
  | Econs(e1, el) -> 1 + length_exprs el

let size_eos = function
  | Coq_inl e -> size_expr e
  | Coq_inr id -> 0

(* [more_likely] is called once for every if-then-else conditional in
   the current function.  Therefore, [size_stmt] is called once for
   every "then" or "else" branch of a conditional.  This can result in
   time quadratic in the size of the function.  To avoid this,
   we bound the recursion depth of [size_stmt] w.r.t. if-then-else
   conditionals. With a maximal depth of [D], each statement of the current
   function is visited at most [D + 1] times.  *)

let max_depth = 4
let max_size = 100

let rec size_stmt depth s =
  match s with
  | Sskip -> 0
  | Sassign(id, a) -> size_expr a
  | Sstore(chunk, addr, args, src) -> 1 + size_exprs args + size_expr src
  | Scall(optid, sg, eos, args) ->
      3 + size_eos eos + size_exprs args + length_exprs args
  | Stailcall(sg, eos, args) ->
      3 + size_eos eos + size_exprs args + length_exprs args
  | Sbuiltin(_, (EF_annot _ | EF_debug _), _) -> 0
  | Sbuiltin(optid, ef, args) -> 1 + size_builtin_args args
  | Sseq(s1, s2) -> size_stmt depth s1 + size_stmt depth s2
  | Sifthenelse(ce, s1, s2) ->
      if depth <= 0
      then max_size
      else size_condexpr ce
           + max (size_stmt (depth - 1) s1) (size_stmt (depth - 1) s2)
  | Sloop s -> 1 + 4 * size_stmt depth s
  | Sblock s -> size_stmt depth s
  | Sexit n -> 1
  | Sswitch xe -> size_exitexpr xe
  | Sreturn None -> 2
  | Sreturn (Some arg) -> 2 + size_expr arg
  | Slabel(lbl, s) -> size_stmt depth s
  | Sgoto lbl -> 1

let size_stmt s =
  min (size_stmt max_depth s) max_size

let more_likely (c: condexpr) (ifso: stmt) (ifnot: stmt) =
  size_stmt ifso > size_stmt ifnot


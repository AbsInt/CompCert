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
  | Evar _ -> 0
  | Eop(_, args) -> 1 + size_exprs args
  | Eload(_, _, args) -> 1 + size_exprs args
  | Econdition(ce, e1, e2) ->
      1 + size_condexpr ce + max (size_expr e1) (size_expr e2)
  | Elet(e1, e2) -> size_expr e1 + size_expr e2
  | Eletvar _ -> 0
  | Ebuiltin(_, el) -> 2 + size_exprs el
  | Eexternal(_, _, el) -> 5 + size_exprs el

and size_exprs = function
  | Enil -> 0
  | Econs(e1, el) -> size_expr e1 + size_exprs el

and size_condexpr = function
  | CEcond(_, args) -> size_exprs args
  | CEcondition(c1, c2, c3) ->
      1 + size_condexpr c1 + size_condexpr c2 + size_condexpr c3
  | CElet(a, c) ->
      size_expr a + size_condexpr c

let size_exprlist al = List.fold_right (fun a s -> size_expr a + s) al 0

let size_builtin_args al = size_exprlist (params_of_builtin_args al)

let rec size_exitexpr = function
  | XEexit _ -> 0
  | XEjumptable(arg, _) -> 2 + size_expr arg
  | XEcondition(c1, c2, c3) ->
      1 + size_condexpr c1 + size_exitexpr c2 + size_exitexpr c3
  | XElet(a, c) ->
      size_expr a + size_exitexpr c

let rec length_exprs = function
  | Enil -> 0
  | Econs(_, el) -> 1 + length_exprs el

let size_eos = function
  | Coq_inl e -> size_expr e
  | Coq_inr _ -> 0

let rec size_stmt = function
  | Sskip -> 0
  | Sassign(_, a) -> size_expr a
  | Sstore(_, _, args, src) -> 1 + size_exprs args + size_expr src
  | Scall(_, _, eos, args) ->
      3 + size_eos eos + size_exprs args + length_exprs args
  | Stailcall(_, eos, args) ->
      3 + size_eos eos + size_exprs args + length_exprs args
  | Sbuiltin(_, (EF_annot _ | EF_debug _), _) -> 0
  | Sbuiltin(_, _, args) -> 1 + size_builtin_args args
  | Sseq(s1, s2) -> size_stmt s1 + size_stmt s2
  | Sifthenelse(ce, s1, s2) ->
      size_condexpr ce + max (size_stmt s1) (size_stmt s2)
  | Sloop s -> 1 + 4 * size_stmt s
  | Sblock s -> size_stmt s
  | Sexit _ -> 1
  | Sswitch xe -> size_exitexpr xe
  | Sreturn None -> 2
  | Sreturn (Some arg) -> 2 + size_expr arg
  | Slabel(_, s) -> size_stmt s
  | Sgoto _ -> 1

let more_likely (_: condexpr) (ifso: stmt) (ifnot: stmt) =
  size_stmt ifso > size_stmt ifnot


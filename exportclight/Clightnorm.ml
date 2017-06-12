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

(** Clight-to-Clight rewriting to name memory loads *)

(* The effect of this rewriting is to ensure that Clight expressions
  whose evaluation involves a memory load (i.e. a lvalue-to-rvalue
  conversion with By_value access mode) are always bound to a temporary
  and never occur deep inside another expression.  For example,

      tmp = *(x + 0) + *(x + 1)

  in the original Clight is rewritten to

      tmp1 = *(x + 0)
      tmp2 = *(x + 1)
      tmp = tmp1 + tmp2
*)

open Camlcoq
open Ctypes
open Clight

let gen_next : AST.ident ref = ref P.one
let gen_trail : (AST.ident * coq_type) list ref = ref []

let gensym ty =
  let id = !gen_next in
  gen_next := P.succ id;
  gen_trail := (id, ty) :: !gen_trail;
  id

let is_lvalue = function
  | Evar _ | Ederef _ | Efield _ -> true
  | _ -> false

let accesses_memory e =
  is_lvalue e &&
  match access_mode (typeof e) with By_value _ -> true | _ -> false

(** Normalization of an expression.  Return a normalized expression
  and a list of statements to be executed before evaluating the expression. *)

let rec norm_expr e =
  let (sl, e') = norm_expr_1 e in
  if accesses_memory e then begin
    let ty = typeof e in
    let id = gensym ty in
    (sl @ [Sset(id, e')], Etempvar(id, ty))
  end else
    (sl, e')

and norm_expr_1 e =
  match e with
  | Econst_int _ | Econst_float _ | Econst_single _ | Econst_long _ -> ([], e)
  | Evar _ | Etempvar _ -> ([], e)
  | Ederef(e1, t) ->
      let (sl, e1') = norm_expr e1 in (sl, Ederef(e1', t))
  | Eaddrof(e1, t) ->
      let (sl, e1') = norm_expr_lvalue e1 in (sl, Eaddrof(e1', t))
  | Eunop(op, e1, t) ->
      let (sl, e1') = norm_expr e1 in (sl, Eunop(op, e1', t))
  | Ebinop(op, e1, e2, t) ->
      let (sl1, e1') = norm_expr e1 in
      let (sl2, e2') = norm_expr e2 in
      (sl1 @ sl2, Ebinop(op, e1', e2', t))
  | Ecast(e1, t) ->
      let (sl, e1') = norm_expr e1 in (sl, Ecast(e1', t))
  | Efield(e1, id, t) ->
      let (sl, e1') = norm_expr e1 in (sl, Efield(e1', id, t))
  | Esizeof _ | Ealignof _ -> ([], e)

(** An expression in l-value position has no memory dereference at top level,
  by definition of l-values.  Hence, use the [norm_expr_1] variant.. *)
and norm_expr_lvalue e = norm_expr_1 e

(** In a [Sset id e] statement, the [e] expression can contain a memory
  dereference at top level.  Hence, use the [norm_expr_1] variant. *)
let norm_expr_set_top = norm_expr_1

let rec norm_expr_list el =
  match el with
  | [] -> ([], [])
  | e1 :: el ->
      let (sl1, e1') = norm_expr e1 in
      let (sl2, el') = norm_expr_list el in
      (sl1 @ sl2, e1' :: el')

let rec add_sequence sl s =
  match sl with
  | [] -> s
  | s1 :: sl -> Ssequence(s1, add_sequence sl s)

let rec norm_stmt s =
  match s with
  | Sskip -> s
  | Sassign(e1, e2) ->
      let (sl1, e1') = norm_expr_lvalue e1 in
      let (sl2, e2') = norm_expr e2 in
      add_sequence (sl1 @ sl2) (Sassign(e1', e2'))
  | Sset(id, e) ->
      let (sl, e') = norm_expr_set_top e in
      add_sequence sl (Sset(id, e'))
  | Scall(optid, e, el) ->
      let (sl1, e') = norm_expr e in
      let (sl2, el') = norm_expr_list el in
      add_sequence (sl1 @ sl2) (Scall(optid, e', el'))  
  | Sbuiltin(optid, ef, tyl, el) ->
      let (sl, el') = norm_expr_list el in
      add_sequence sl (Sbuiltin(optid, ef, tyl, el'))
  | Ssequence(s1, s2) ->
      Ssequence(norm_stmt s1, norm_stmt s2)
  | Sifthenelse(e, s1, s2) ->
      let (sl, e') = norm_expr e in
      add_sequence sl (Sifthenelse(e', norm_stmt s1, norm_stmt s2))
  | Sloop(s1, s2) ->
      Sloop(norm_stmt s1, norm_stmt s2)
  | Sbreak | Scontinue | Sreturn None -> s
  | Sreturn (Some e) ->
      let (sl, e') = norm_expr e in
      add_sequence sl (Sreturn(Some e'))
  | Sswitch(e, ls) ->
      let (sl, e') = norm_expr e in
      add_sequence sl (Sswitch(e, norm_lbl_stmt ls))
  | Slabel(lbl, s1) ->
      Slabel(lbl, norm_stmt s1)
  | Sgoto lbl -> s

and norm_lbl_stmt ls =
  match ls with
  | LSnil -> LSnil
  | LScons(n, s, ls) -> LScons(n, norm_stmt s, norm_lbl_stmt ls)

let next_var curr (v, _) = if P.lt v curr then curr else P.succ v

let next_var_list vars start = List.fold_left next_var start vars

let norm_function f =
  gen_next := next_var_list f.fn_params
                (next_var_list f.fn_vars
                   (next_var_list f.fn_temps
                     (Camlcoq.first_unused_ident ())));
  gen_trail := [];
  let s' = norm_stmt f.fn_body in
  let new_temps = !gen_trail in
  { f with fn_body = s'; fn_temps = f.fn_temps @ new_temps }

let norm_fundef = function
  | Internal f -> Internal (norm_function f)
  | External _ as fd -> fd

let norm_program p =
  let p1 = AST.transform_program norm_fundef (program_of_program p) in
  { p with prog_defs = p1.AST.prog_defs }

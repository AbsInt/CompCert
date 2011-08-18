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

(* Elimination of read-modify-write operators (+=, ++, etc) applied
   to volatile expressions. *)

open Printf
open C
open Cutil
open Transform

(* Expansion of read-write-modify constructs. *)

(** [l = r]. *)

let mk_assign ctx l r =
  match ctx with
  | Effects ->
      eassign l r
  | Val ->
      let tmp = new_temp l.etyp in
      ecomma (eassign tmp r) (ecomma (eassign l tmp) tmp)

(** [l op= r].  Warning: [l] is evaluated twice. *)

let mk_assignop ctx op l r ty =
  let op' =
    match op with
    | Oadd_assign -> Oadd | Osub_assign -> Osub
    | Omul_assign -> Omul | Odiv_assign -> Odiv | Omod_assign -> Omod
    | Oand_assign -> Oand | Oor_assign -> Oor   | Oxor_assign -> Oxor
    | Oshl_assign -> Oshl | Oshr_assign -> Oshr
    | _ -> assert false in
  let res = {edesc = EBinop(op', l, r, ty); etyp = ty} in
  match ctx with
  | Effects ->
      eassign l res
  | Val ->
      let tmp = new_temp l.etyp in
      ecomma (eassign tmp res) (ecomma (eassign l tmp) tmp)

(** [++l] or [--l].  Warning: [l] is evaluated twice. *)

let mk_preincrdecr ctx op l ty =
  let op' =
    match op with
    | Opreincr -> Oadd_assign
    | Opredecr -> Osub_assign
    | _ -> assert false in  
  mk_assignop ctx op' l (intconst 1L IInt) ty

(** [l++] or [l--].  Warning: [l] is evaluated twice. *)

let mk_postincrdecr ctx op l ty =
  let op' =
    match op with
    | Opostincr -> Oadd
    | Opostdecr -> Osub
    | _ -> assert false in  
  match ctx with
  | Effects ->
      let newval = {edesc = EBinop(op', l, intconst 1L IInt, ty); etyp = ty} in
      eassign l newval
  | Val ->
      let tmp = new_temp l.etyp in
      let newval = {edesc = EBinop(op', tmp, intconst 1L IInt, ty); etyp = ty} in
      ecomma (eassign tmp l) (ecomma (eassign l newval) tmp)

(* Rewriting of expressions *)

let transf_expr loc env ctx e =

  let is_volatile ty =
    List.mem AVolatile (attributes_of_type env ty) in

  let rec texp ctx e =
    match e.edesc with
    | EConst _ -> e
    | ESizeof _ -> e
    | EVar _ -> e
    | EUnop((Opreincr|Opredecr as op), e1) when is_volatile e1.etyp ->
        bind_lvalue env (texp Val e1)
          (fun l -> mk_preincrdecr ctx op l (unary_conversion env l.etyp))
    | EUnop((Opostincr|Opostdecr as op), e1) when is_volatile e1.etyp ->
        bind_lvalue env (texp Val e1)
          (fun l -> mk_postincrdecr ctx op l (unary_conversion env l.etyp))
    | EUnop(op, e1) ->
        {edesc = EUnop(op, texp Val e1); etyp = e.etyp}
    | EBinop(Oassign, e1, e2, ty) when is_volatile e1.etyp ->
        mk_assign ctx (texp Val e1) (texp Val e2)
    | EBinop((Oadd_assign | Osub_assign | Omul_assign
              | Odiv_assign | Omod_assign
              | Oand_assign | Oor_assign | Oxor_assign
              | Oshl_assign | Oshr_assign) as op, e1, e2, ty)
      when is_volatile e1.etyp ->
        bind_lvalue env (texp Val e1)
          (fun l -> mk_assignop ctx op l (texp Val e2) ty)
    | EBinop(Ocomma, e1, e2, ty) ->
        {edesc = EBinop(Ocomma, texp Effects e1, texp ctx e2, ty);
         etyp = e.etyp}
    | EBinop(op, e1, e2, ty) ->
        {edesc = EBinop(op, texp Val e1, texp Val e2, ty); etyp = e.etyp}
    | EConditional(e1, e2, e3) ->
        {edesc = EConditional(texp Val e1, texp ctx e2, texp ctx e3);
         etyp = e.etyp}
    | ECast(ty, e1) ->
        {edesc = ECast(ty, texp Val e1); etyp = e.etyp}
    | ECall(e1, el) ->
        {edesc = ECall(texp Val e1, List.map (texp Val) el); etyp = e.etyp}

  in texp ctx e

(* Statements *)

let transf_stmt env s =
  Transform.stmt transf_expr env s

(* Functions *)

let transf_fundef env f =
  Transform.fundef transf_stmt env f

(* Programs *)

let program p =
  Transform.program ~fundef:transf_fundef p

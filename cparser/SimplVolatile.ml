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
        expand_preincrdecr ~read:(fun e -> e) ~write:eassign
                           env ctx op (texp Val e1)
    | EUnop((Opostincr|Opostdecr as op), e1) when is_volatile e1.etyp ->
        expand_postincrdecr ~read:(fun e -> e) ~write:eassign
                            env ctx op (texp Val e1)
    | EUnop(op, e1) ->
        {edesc = EUnop(op, texp Val e1); etyp = e.etyp}
    | EBinop(Oassign, e1, e2, ty) when is_volatile e1.etyp ->
        expand_assign ~write:eassign env ctx (texp Val e1) (texp Val e2)
    | EBinop((Oadd_assign | Osub_assign | Omul_assign
              | Odiv_assign | Omod_assign
              | Oand_assign | Oor_assign | Oxor_assign
              | Oshl_assign | Oshr_assign) as op, e1, e2, ty)
      when is_volatile e1.etyp ->
        expand_assignop ~read:(fun e -> e) ~write:eassign
                        env ctx op (texp Val e1) (texp Val e2) ty
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

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

(* Expand assignments between structs and between unions *)

(* Assumes: unblocked code.
   Preserves: unblocked code *)

open C
open Machine
open Cutil
open Env
open Errors
open Transform

(* Finding appropriate memcpy functions *)

let memcpy_decl = ref (None : ident option)

let memcpy_type =
  TFun(TPtr(TVoid [], []),
       Some [(Env.fresh_ident "", TPtr(TVoid [], []));
             (Env.fresh_ident "", TPtr(TVoid [AConst], []));
             (Env.fresh_ident "", TInt(size_t_ikind, []))],
       false, [])

let lookup_function env name =
  match Env.lookup_ident env name with
  | (id, II_ident(sto, ty)) -> (id, ty)
  | (id, II_enum _) -> raise (Env.Error(Env.Unbound_identifier name))

let default_memcpy () =
  match !memcpy_decl with
  | Some id ->
      (id, memcpy_type)
  | None ->
      let id = Env.fresh_ident "memcpy" in
      memcpy_decl := Some id;
      (id, memcpy_type)

let find_memcpy env =
  try
    (lookup_function env "__builtin_memcpy_aligned", true)
  with Env.Error _ ->
  try
    (lookup_function env "__builtin_memcpy", false)
  with Env.Error _ ->
  try
    (lookup_function env "memcpy", false)
  with Env.Error _ ->
    (default_memcpy(), false)

(* Smart constructor that "bubble up" sequence expressions *)

let rec edot f e ty =
  match e.edesc with
  | EBinop(Ocomma, e1, e2, _) -> ecomma e1 (edot f e2 ty)
  | _ -> { edesc = EUnop(Odot f, e); etyp = ty }

(* Translate an assignment [lhs = rhs] between composite types.
   [lhs] and [rhs] must be l-values. *)

let transf_assign env lhs rhs =
  let al =
     match Cutil.alignof env lhs.etyp with Some al -> al | None -> 1 in
  let ((ident, ty), four_args) = find_memcpy env in
  let memcpy = {edesc = EVar(ident); etyp = ty} in
  let e_lhs = eaddrof lhs
  and e_rhs = eaddrof rhs
  and e_size = {edesc = ESizeof(lhs.etyp); etyp = TInt(size_t_ikind, [])}
  and e_align = intconst (Int64.of_int al) size_t_ikind in
  let args =
    if four_args
    then [e_lhs; e_rhs; e_size; e_align]
    else [e_lhs; e_rhs; e_size] in
  {edesc = ECall(memcpy, args); etyp = TVoid[]}

(* Transformation of expressions. *)

let transf_expr loc env ctx e =
  let rec texp ctx e =
  match e.edesc with
  | EBinop(Oassign, lhs, rhs, _) when is_composite_type env lhs.etyp ->
      let lhs' = texp Val lhs in
      let rhs' = texp Val rhs in
      begin match ctx with
      | Effects ->
          transf_assign env lhs' rhs'
      | Val ->
          bind_lvalue env lhs' (fun l -> ecomma (transf_assign env l rhs') l)
      end
  | EConst c -> e
  | ESizeof ty -> e
  | EVar x ->
      if ctx = Effects && is_composite_type env e.etyp
      then nullconst
      else e
  | EUnop(Oaddrof, e1) ->
      eaddrof (texp Val e1)
  | EUnop(Oderef, e1) ->
      if ctx = Effects && is_composite_type env e.etyp
      then texp Effects e1
      else {edesc = EUnop(Oderef, texp Val e1); etyp = e.etyp}
  | EUnop(Odot f, e1) ->
      if ctx = Effects && is_composite_type env e.etyp
      then texp Effects e1
      else edot f (texp Val e1) e.etyp
  | EUnop(Oarrow f, e1) ->
      if ctx = Effects && is_composite_type env e.etyp
      then texp Effects e1
      else {edesc = EUnop(Oarrow f, texp Val e1); etyp = e.etyp}
  | EUnop(op, e1) ->
      {edesc = EUnop(op, texp Val e1); etyp = e.etyp}
  | EBinop(Oindex, e1, e2, ty) ->
      if ctx = Effects && is_composite_type env e.etyp
      then ecomma (texp Effects e1) (texp Effects e2)
      else {edesc = EBinop(Oindex, texp Val e1, texp Val e2, ty); etyp = e.etyp}
  | EBinop(Ocomma, e1, e2, ty) ->
      ecomma (texp Effects e1) (texp ctx e2)
  | EBinop(op, e1, e2, ty) ->
      {edesc = EBinop(op, texp Val e1, texp Val e2, ty);
       etyp = e.etyp}
  | EConditional(e1, e2, e3) ->
      {edesc = EConditional(texp Val e1, texp ctx e2, texp ctx e3);
       etyp = e.etyp}
  | ECast(ty, e1) ->
      {edesc = ECast(ty, texp Val e1); etyp = e.etyp}
  | ECall(e1, el) ->
      {edesc = ECall(texp Val e1,
                     List.map (texp Val) el);
       etyp = e.etyp}
  in texp ctx e

(* Transformation of statements *)

let transf_stmt env s =
  Transform.stmt transf_expr env s

(* Transformation of function definitions *)

let transf_fundef env f =
  Transform.fundef transf_stmt env f

(* Transformation of programs *)

let program p =
  memcpy_decl := None;
  let p' = Transform.program ~fundef:transf_fundef p in
  match !memcpy_decl with
  | None -> p'
  | Some id ->
      {gdesc = Gdecl(Storage_extern, id, memcpy_type, None); gloc = no_loc}
      :: p'

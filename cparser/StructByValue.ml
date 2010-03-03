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

(* Eliminate by-value passing of structs and unions. *)

(* Assumes: nothing.
   Preserves: simplified code, unblocked code *)

open C
open Cutil
open Transform

(* In function argument types, struct s -> struct s *
   In function result types, struct s -> void + add 1st parameter struct s *
   Try to preserve original typedef names when no change.
*)

let rec transf_type env t =
  match unroll env t with
  | TFun(tres, None, vararg, attr) ->
      let tres' = transf_type env tres in
      TFun((if is_composite_type env tres then TVoid [] else tres'),
           None, vararg, attr)
  | TFun(tres, Some args, vararg, attr) ->
      let args' = List.map (transf_funarg env) args in
      let tres' = transf_type env tres in
      if is_composite_type env tres then begin
        let res = Env.fresh_ident "_res" in
        TFun(TVoid [], Some((res, TPtr(tres', [])) :: args'), vararg, attr)
      end else
        TFun(tres', Some args', vararg, attr)
  | TPtr(t1, attr) ->
      let t1' = transf_type env t1 in
      if t1' = t1 then t else TPtr(transf_type env t1, attr)
  | TArray(t1, sz, attr) ->
      let t1' = transf_type env t1 in
      if t1' = t1 then t else TArray(transf_type env t1, sz, attr)
  | _ -> t

and transf_funarg env (id, t) =
  let t = transf_type env t in
  if is_composite_type env t
  then (id, TPtr(add_attributes_type [AConst] t, []))
  else (id, t)

(* Simple exprs: no change in structure, since calls cannot occur within,
   but need to rewrite the types. *)

let rec transf_expr env e =
  { etyp = transf_type env e.etyp;
    edesc = match e.edesc with
      | EConst c -> EConst c
      | ESizeof ty -> ESizeof (transf_type env ty)
      | EVar x -> EVar x
      | EUnop(op, e1) -> EUnop(op, transf_expr env e1)
      | EBinop(op, e1, e2, ty) ->
          EBinop(op, transf_expr env e1, transf_expr env e2, transf_type env ty)
      | EConditional(e1, e2, e3) ->
          assert (not (is_composite_type env e.etyp));
          EConditional(transf_expr env e1, transf_expr env e2, transf_expr env e3)
      | ECast(ty, e1) -> ECast(transf_type env ty, transf_expr env e1)
      | ECall(e1, el) -> assert false
  }

(* Initializers *)

let rec transf_init env = function
  | Init_single e ->
      Init_single (transf_expr env e)
  | Init_array il ->
      Init_array (List.map (transf_init env) il)
  | Init_struct(id, fil) ->
      Init_struct (id, List.map (fun (fld, i) -> (fld, transf_init env i)) fil)
  | Init_union(id, fld, i) ->
      Init_union(id, fld, transf_init env i)

(* Declarations *)

let transf_decl env (sto, id, ty, init) =
  (sto, id, transf_type env ty,
   match init with None -> None | Some i -> Some (transf_init env i))

(* Transformation of statements and function bodies *)

let transf_funbody env body optres =

let transf_type t = transf_type env t
and transf_expr e = transf_expr env e in

(* Function arguments: pass by reference those having struct/union type *)

let transf_arg e =
  let e' = transf_expr e in
  if is_composite_type env e'.etyp
  then {edesc = EUnop(Oaddrof, e'); etyp = TPtr(e'.etyp, [])}
  else e'
in

(* Function calls: if return type is struct or union,
     lv = f(...)   -> f(&lv, ...)
     f(...)        -> f(&newtemp, ...)
   Returns: if return type is struct or union,
     return x      -> _res = x; return
*)

let rec transf_stmt s =
  match s.sdesc with
  | Sskip -> s
  | Sdo {edesc = ECall(fn, args); etyp = ty} ->
      let fn = transf_expr fn in
      let args = List.map transf_arg args in
      if is_composite_type env ty then begin
        let tmp = new_temp ~name:"_res" ty in
        let arg0 = {edesc = EUnop(Oaddrof, tmp); etyp = TPtr(ty, [])} in
        {s with sdesc = Sdo {edesc = ECall(fn, arg0 :: args); etyp = TVoid []}}
      end else
        {s with sdesc = Sdo {edesc = ECall(fn, args); etyp = ty}}
  | Sdo {edesc = EBinop(Oassign, dst, {edesc = ECall(fn, args); etyp = ty}, _)} ->
      let dst = transf_expr dst in
      let fn = transf_expr fn in
      let args = List.map transf_arg args in
      let ty = transf_type ty in
      if is_composite_type env ty then begin
        let arg0 = {edesc = EUnop(Oaddrof, dst); etyp = TPtr(dst.etyp, [])} in
        {s with sdesc = Sdo {edesc = ECall(fn, arg0 :: args); etyp = TVoid []}}
      end else
        sassign s.sloc dst {edesc = ECall(fn, args); etyp = ty}
  | Sdo e ->
      {s with sdesc = Sdo(transf_expr e)}
  | Sseq(s1, s2) ->
      {s with sdesc = Sseq(transf_stmt s1, transf_stmt s2)}
  | Sif(e, s1, s2) ->
      {s with sdesc = Sif(transf_expr e, transf_stmt s1, transf_stmt s2)}
  | Swhile(e, s1) ->
      {s with sdesc = Swhile(transf_expr e, transf_stmt s1)}
  | Sdowhile(s1, e) ->
      {s with sdesc = Sdowhile(transf_stmt s1, transf_expr e)}
  | Sfor(s1, e, s2, s3) ->
      {s with sdesc = Sfor(transf_stmt s1, transf_expr e,
                           transf_stmt s2, transf_stmt s3)}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {s with sdesc = Sswitch(transf_expr e, transf_stmt s1)}
  | Slabeled(lbl, s1) ->
      {s with sdesc = Slabeled(lbl, transf_stmt s1)}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn(Some e) ->
      let e = transf_expr e in
      begin match optres with
      | None ->
          {s with sdesc = Sreturn(Some e)}
      | Some dst ->
          sseq s.sloc
            (sassign s.sloc dst e)
            {sdesc = Sreturn None; sloc = s.sloc}
      end
  | Sblock sl ->
      {s with sdesc = Sblock(List.map transf_stmt sl)}
  | Sdecl d ->
      {s with sdesc = Sdecl(transf_decl env d)}

in
  transf_stmt body

let transf_params loc env params =
  let rec transf_prm = function
  | [] ->
      ([], [], sskip)
  | (id, ty) :: params ->
      let ty = transf_type env ty in
      if is_composite_type env ty then begin
        let id' = Env.fresh_ident id.name in
        let ty' = TPtr(add_attributes_type [AConst] ty, []) in
        let (params', decls, init) = transf_prm params in
        ((id', ty') :: params',
         (Storage_default, id, ty, None) :: decls,
         sseq loc
          (sassign loc {edesc = EVar id; etyp = ty}
                       {edesc = EUnop(Oderef, {edesc = EVar id'; etyp = ty'});
                        etyp = ty})
          init)
      end else begin
        let (params', decls, init) = transf_prm params in
        ((id, ty) :: params', decls, init)
      end
  in transf_prm params

let transf_fundef env f =
  reset_temps();
  let ret = transf_type env f.fd_ret in
  let (params, newdecls, init) = transf_params f.fd_body.sloc env f.fd_params in
  let (ret1, params1, body1) =
    if is_composite_type env ret then begin
      let vres = Env.fresh_ident "_res" in
      let tres = TPtr(ret, []) in
      let eres = {edesc = EVar vres; etyp = tres} in
      let eeres = {edesc = EUnop(Oderef, eres); etyp = ret} in
      (TVoid [],
       (vres, tres) :: params,
       transf_funbody env f.fd_body (Some eeres))
    end else
      (ret, params, transf_funbody env f.fd_body None) in
  let body2 = sseq body1.sloc init body1 in
  let temps = get_temps() in
  {f with fd_ret = ret1; fd_params = params1;
          fd_locals = newdecls @ f.fd_locals @ temps; fd_body = body2}

(* Composites *)

let transf_composite env su id fl =
  List.map (fun f -> {f with fld_typ = transf_type env f.fld_typ}) fl

(* Entry point *)

let program p =
  Transform.program
    ~decl:transf_decl
    ~fundef:transf_fundef
    ~composite:transf_composite
    ~typedef:(fun env id ty -> transf_type env ty)
    p

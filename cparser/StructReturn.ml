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

(* Eliminate structs and unions being returned by value as function results *)

open Machine
open C
open Cutil
open Transform

(* Classification of function return types. *)

type return_kind =
  | Ret_scalar    (**r a scalar type, returned as usual *)
  | Ret_ref       (**r a composite type, returned by reference *)
  | Ret_value of typ (**r a small composite type, returned as an integer *)

let classify_return env ty =
  if is_composite_type env ty then begin
    match sizeof env ty with
    | None -> Ret_ref  (* should not happen *)
    | Some sz ->
        if (!config).struct_return_as_int >= 4 && sz <= 4 then
          Ret_value (TInt(IUInt, []))
        else if (!config).struct_return_as_int >= 8 && sz <= 8 then
          Ret_value (TInt(IULongLong, []))
        else Ret_ref
  end else
    Ret_scalar

(* Rewriting of function types.
      return kind scalar   -> no change
      return kind ref      -> return type void + add 1st parameter struct s *
      return kind value(t) -> return type t.
   Try to preserve original typedef names when no change.
*)

let rec transf_type env t =
  match unroll env t with
  | TFun(tres, None, vararg, attr) ->
      let tres' = transf_type env tres in
      let tres'' =
        match classify_return env tres with
        | Ret_scalar -> tres'
        | Ret_ref -> TVoid []
        | Ret_value ty -> ty in
      TFun(tres'', None, vararg, attr)
  | TFun(tres, Some args, vararg, attr) ->
      let args' = List.map (transf_funarg env) args in
      let tres' = transf_type env tres in
      begin match classify_return env tres with
      | Ret_scalar ->
          TFun(tres', Some args', vararg, attr)
      | Ret_ref ->
          let res = Env.fresh_ident "_res" in
          TFun(TVoid [], Some((res, TPtr(tres', [])) :: args'), vararg, attr)
      | Ret_value ty ->
          TFun(ty, Some args', vararg, attr)
      end
  | TPtr(t1, attr) ->
      let t1' = transf_type env t1 in
      if t1' = t1 then t else TPtr(transf_type env t1, attr)
  | TArray(t1, sz, attr) ->
      let t1' = transf_type env t1 in
      if t1' = t1 then t else TArray(transf_type env t1, sz, attr)
  | _ -> t

and transf_funarg env (id, t) = (id, transf_type env t)

(* Expressions: transform calls + rewrite the types *)

let ereinterpret ty e =
  { edesc = EUnop(Oderef, ecast (TPtr(ty, [])) (eaddrof e)); etyp = ty }

let rec transf_expr env ctx e =
  let newty = transf_type env e.etyp in
  match e.edesc with
  | EConst c ->
      {edesc = EConst c; etyp = newty}
  | ESizeof ty ->
      {edesc = ESizeof (transf_type env ty); etyp = newty}
  | EAlignof ty ->
      {edesc = EAlignof (transf_type env ty); etyp = newty}
  | EVar x ->
      {edesc = EVar x; etyp = newty}
  | EUnop(op, e1) ->
      {edesc = EUnop(op, transf_expr env Val e1); etyp = newty}
  | EBinop(Oassign, lhs, {edesc = ECall(fn, args); etyp = ty}, _) ->
      transf_call env ctx (Some lhs) fn args ty
  | EBinop(Ocomma, e1, e2, ty) ->
      ecomma (transf_expr env Effects e1) (transf_expr env ctx e2)
  | EBinop(op, e1, e2, ty) ->
      {edesc = EBinop(op, transf_expr env Val e1,
                          transf_expr env Val e2,
                          transf_type env ty);
       etyp = newty}
  | EConditional(e1, e2, e3) ->
      {edesc = EConditional(transf_expr env Val e1,
                            transf_expr env ctx e2,
                            transf_expr env ctx e3);
       etyp = newty}
  | ECast(ty, e1) ->
      {edesc = ECast(transf_type env ty, transf_expr env Val e1); etyp = newty}
  | ECall(fn, args) ->
      transf_call env ctx None fn args e.etyp

(* Function calls returning a composite by reference: add first argument.
    ctx = Effects:   lv = f(...)     -> f(&lv, ...)      [copy optimization]
                     f(...)          -> f(&newtemp, ...)
    ctx = Val:       lv = f(...)     -> f(&newtemp, ...), lv = newtemp
                     f(...)          -> f(&newtemp, ...), newtemp
   Function calls returning a composite by value:
    ctx = Effects:   lv = f(...)     -> newtemp = f(...), lv = newtemp
                     f(...)          -> f(...)
    ctx = Val:       lv = f(...)     -> newtemp = f(...), lv = newtemp
                     f(...)          -> newtemp = f(...), newtemp
*)

and transf_call env ctx opt_lhs fn args ty =
  let ty' = transf_type env ty in
  let fn' = transf_expr env Val fn in
  let args' = List.map (transf_expr env Val) args in
  let opt_eassign e =
    match opt_lhs with
    | None -> e
    | Some lhs -> eassign (transf_expr env Val lhs) e in
  match classify_return env ty with
  | Ret_scalar ->
      opt_eassign {edesc = ECall(fn', args'); etyp = ty'}
  | Ret_ref ->
      begin match ctx, opt_lhs with
      | Effects, None ->
          let tmp = new_temp ~name:"_res" ty in
          {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []}
      | Effects, Some lhs ->
          let lhs' = transf_expr env Val lhs in
          {edesc = ECall(fn', eaddrof lhs' :: args'); etyp = TVoid []}
      | Val, None ->
          let tmp = new_temp ~name:"_res" ty in
          ecomma {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []} tmp
      | Val, Some lhs ->
          let lhs' = transf_expr env Val lhs in
          let tmp = new_temp ~name:"_res" ty in
          ecomma {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []}
                 (eassign lhs' tmp)
      end
  | Ret_value ty_ret ->
      let ecall = {edesc = ECall(fn', args'); etyp = ty_ret} in
      begin match ctx, opt_lhs with
      | Effects, None ->
          ecall
      | _, _ ->
          let tmp = new_temp ~name:"_res" ty_ret in
          opt_eassign
            (ecomma (eassign tmp ecall)
                    (ereinterpret ty' tmp))
      end

(* Initializers *)

let rec transf_init env = function
  | Init_single e ->
      Init_single (transf_expr env Val e)
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

let transf_expr ctx e = transf_expr env ctx e in

(* Function returns:
     return kind scalar    -> return e
     return kind ref       -> _res = x; return
     return kind value ty  -> *((struct s * )_res) = x; return _res
*)

let rec transf_stmt s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e ->
      {s with sdesc = Sdo(transf_expr Effects e)}
  | Sseq(s1, s2) ->
      {s with sdesc = Sseq(transf_stmt s1, transf_stmt s2)}
  | Sif(e, s1, s2) ->
      {s with sdesc = Sif(transf_expr Val e,
                          transf_stmt s1, transf_stmt s2)}
  | Swhile(e, s1) ->
      {s with sdesc = Swhile(transf_expr Val e, transf_stmt s1)}
  | Sdowhile(s1, e) ->
      {s with sdesc = Sdowhile(transf_stmt s1, transf_expr Val e)}
  | Sfor(s1, e, s2, s3) ->
      {s with sdesc = Sfor(transf_stmt s1, transf_expr Val e,
                           transf_stmt s2, transf_stmt s3)}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {s with sdesc = Sswitch(transf_expr Val e, transf_stmt s1)}
  | Slabeled(lbl, s1) ->
      {s with sdesc = Slabeled(lbl, transf_stmt s1)}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn(Some e) ->
      let e' = transf_expr Val e in
      begin match classify_return env e'.etyp, optres with
      | Ret_scalar, None ->
          {s with sdesc = Sreturn(Some e')}
      | Ret_ref, Some dst ->
          sseq s.sloc
            (sassign s.sloc dst e')
            {sdesc = Sreturn None; sloc = s.sloc}
      | Ret_value ty, Some dst ->
          sseq s.sloc
            (sassign s.sloc (ereinterpret e'.etyp dst) e')
            {sdesc = Sreturn (Some dst); sloc = s.sloc}
      | _, _ ->
          assert false
      end
  | Sblock sl ->
      {s with sdesc = Sblock(List.map transf_stmt sl)}
  | Sdecl d ->
      {s with sdesc = Sdecl(transf_decl env d)}
  | Sasm _ -> s

in
  transf_stmt body

let transf_fundef env f =
  reset_temps();
  let ret = transf_type env f.fd_ret in
  let params =
    List.map (fun (id, ty) -> (id, transf_type env ty)) f.fd_params in
  let (ret1, params1, body1) =
    match classify_return env f.fd_ret with
    | Ret_scalar ->
        (ret, params, transf_funbody env f.fd_body None)
    | Ret_ref ->
        let vres = Env.fresh_ident "_res" in
        let tres = TPtr(ret, []) in
        let eres = {edesc = EVar vres; etyp = tres} in
        let eeres = {edesc = EUnop(Oderef, eres); etyp = ret} in
        (TVoid [],
         (vres, tres) :: params,
         transf_funbody env f.fd_body (Some eeres))
    | Ret_value ty ->
        let eres = new_temp ~name:"_res" ty in
        (ty, params, transf_funbody env f.fd_body (Some eres)) in
  let temps = get_temps() in
  {f with fd_ret = ret1; fd_params = params1;
          fd_locals = f.fd_locals @ temps; fd_body = body1}

(* Composites *)

let transf_composite env su id attr fl =
  (attr, List.map (fun f -> {f with fld_typ = transf_type env f.fld_typ}) fl)

(* Entry point *)

let program p =
  Transform.program
    ~decl:transf_decl
    ~fundef:transf_fundef
    ~composite:transf_composite
    ~typedef:(fun env id ty -> transf_type env ty)
    p

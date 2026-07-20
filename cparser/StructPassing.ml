(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(* Handle structs and unions that are returned by value as function results. *)

open C
open Cutil
open Transform

let attr_structret = [Attr("__structreturn", [])]

(* Rewriting of function types.  If the return type is a composite type t,
   change return type to void and add first parameter of type t * *)

let rec transf_type env t =
  match unroll env t with
  | TFun(tres, None, vararg, attr) ->
      let tres' = transf_type env tres in
      if is_composite_type env tres' then
        TFun(TVoid [], None, vararg, add_attributes attr attr_structret) 
      else
        TFun(tres', None, vararg, attr)
  | TFun(tres, Some args, vararg, attr) ->
      let args' = transf_funargs env args in
      let tres' = transf_type env tres in
      if is_composite_type env tres' then begin
        let res = Env.fresh_ident "_res" in
        TFun(TVoid [], Some((res, TPtr(tres', [])) :: args'), vararg,
             add_attributes attr attr_structret)
      end else
        TFun(tres', Some args', vararg, attr)
  | TPtr(t1, attr) ->
      let t1' = transf_type env t1 in
      if t1' = t1 then t else TPtr(transf_type env t1, attr)
  | TArray(t1, sz, attr) ->
      let t1' = transf_type env t1 in
      if t1' = t1 then t else TArray(transf_type env t1, sz, attr)
  | _ -> t

and transf_funargs env = function
  | [] -> []
  | (id, t) :: args -> (id, transf_type env t) :: transf_funargs env args

(* Expressions: transform calls + rewrite the types *)

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
      transf_call env ctx (Some (transf_expr env Val lhs)) fn args ty
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
  | ECompound(ty, ie) ->
      {edesc = ECompound(transf_type env ty, transf_init env ie); etyp = newty}
  | ECall(fn, args) ->
      transf_call env ctx None fn args e.etyp

(* Function calls returning a composite: add first argument.
    ctx = Effects:   lv = f(...)     -> f(&newtemp, ...), lv = newtemp
                     f(...)          -> f(&newtemp, ...)
    ctx = Val:       lv = f(...)     -> f(&newtemp, ...), lv = newtemp
                     f(...)          -> f(&newtemp, ...), newtemp

   We used to do a copy optimization:
     ctx = Effects:   lv = f(...)     -> f(&lv, ...)
   but it is not correct in case of overlap (see test/regression/struct12.c)
*)

and transf_call env ctx opt_lhs fn args ty =
  let ty' = transf_type env ty in
  let fn' = transf_expr env Val fn in
  let args' = List.map (fun arg -> transf_expr env Val arg) args in
  let opt_eassign e =
    match opt_lhs with
    | None -> e
    | Some lhs -> eassign lhs e in
  match fn with
  | {edesc = EVar { C.name = "__builtin_va_arg" } } ->
      (* Do not transform the call in this case, __builtin_va_arg
         just returns a pointer to the composite value *)
      opt_eassign {edesc = ECall(fn, args'); etyp = ty}
  | _ ->
      if is_composite_type env ty then begin
       let tmp = new_temp ~name:"_res" ty in
       match ctx, opt_lhs with
       | Effects, None ->
           {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []}
       | Val, None ->
           ecomma {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []}
                  tmp
       | _, Some lhs ->
           ecomma {edesc = ECall(fn', eaddrof tmp :: args'); etyp = TVoid []}
                  (eassign lhs tmp)
      end else
        opt_eassign {edesc = ECall(fn', args'); etyp = ty'}

(* Initializers *)

and transf_init env = function
  | Init_single e ->
      Init_single (transf_expr env Val e)
  | Init_array il ->
      Init_array (List.rev (List.rev_map (transf_init env) il))
  | Init_struct(id, fil) ->
      Init_struct (id, List.map (fun (fld, i) -> (fld, transf_init env i)) fil)
  | Init_union(id, fld, i) ->
      Init_union(id, fld, transf_init env i)

(* Declarations *)

let transf_decl env loc (sto, id, ty, init) =
  (sto, id, transf_type env ty,
   match init with None -> None | Some i -> Some (transf_init env i))

(* Transformation of statements and function bodies *)

let transf_funbody env body optres =

let transf_expr ctx e = transf_expr env ctx e in
let transf_asm_operand (lbl, cstr, e) = (lbl, cstr, transf_expr Val e) in

(* Function returns.  If the return type is composite,
     return x  --->  _res = x; return
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
      begin match optres with
      | None ->
          assert (not (is_composite_type env e'.etyp));
          {s with sdesc = Sreturn(Some e')}
      | Some dst ->
          assert (is_composite_type env e'.etyp);
          sseq s.sloc
            (sassign s.sloc dst e')
            {sdesc = Sreturn None; sloc = s.sloc}
      end
  | Sblock sl ->
      {s with sdesc = Sblock(List.map transf_stmt sl)}
  | Sdecl d ->
      {s with sdesc = Sdecl(transf_decl env s.sloc d)}
  | Sasm(attr, template, outputs, inputs, clob) ->
      {s with sdesc = Sasm(attr, template,
                           List.map transf_asm_operand outputs,
                           List.map transf_asm_operand inputs, clob)}

in
  transf_stmt body

(* Function definitions *)

let transf_fundef env loc f =
  reset_temps();
  let ret = transf_type env f.fd_ret
  and params = transf_funargs env f.fd_params in
  let locals = List.map (transf_decl env loc) f.fd_locals in
  let (attr1, ret1, params1, body1) =
    if is_composite_type env f.fd_ret then begin
      let vres = Env.fresh_ident "_res" in
      let tres = TPtr(ret, []) in
      let eres = {edesc = EVar vres; etyp = tres} in
      let eeres = {edesc = EUnop(Oderef, eres); etyp = ret} in
      (add_attributes f.fd_attrib attr_structret,
       TVoid [],
       (vres, tres) :: params,
       transf_funbody env f.fd_body (Some eeres))
    end else
      (f.fd_attrib,
       ret,
       params,
       transf_funbody env f.fd_body None) in
  let temps = get_temps() in
  {f with fd_attrib = attr1;
          fd_ret = ret1;
          fd_params = params1;
          fd_locals = locals @ temps;
          fd_body = body1}

(* Composites *)

let transf_composite env loc su id attr fl =
  (attr, List.map (fun f -> {f with fld_typ = transf_type env f.fld_typ}) fl)

(* Entry point *)

let program p =
  Transform.program
    ~decl:transf_decl
    ~fundef:transf_fundef
    ~composite:transf_composite
    ~typedef:(fun env loc id ty -> transf_type env ty)
    p

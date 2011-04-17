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

(* Max number of assignments that can be inlined.  Above this threshold,
   we call memcpy() instead. *)

let maxsize = ref 8

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

let memcpy_ident env =
  try lookup_function env "__builtin_memcpy"
  with Env.Error _ ->
  try lookup_function env "memcpy"
  with Env.Error _ ->
  match !memcpy_decl with
  | Some id ->
      (id, memcpy_type)
  | None ->
      let id = Env.fresh_ident "memcpy" in
      memcpy_decl := Some id;
      (id, memcpy_type)

let memcpy_words_ident env =
  try lookup_function env "__builtin_memcpy_words"
  with Env.Error _ -> memcpy_ident env

(* Smart constructor for "," expressions *)

let comma e1 e2 =
  match e1.edesc, e2.edesc with
  | EConst _, _ -> e2
  | _, EConst _ -> e1
  | _, _ ->  ecomma e1 e2

(* Translate an assignment [lhs = rhs] between composite types.
   [lhs] and [rhs] must be pure, invariant l-values. *)

let transf_assign env lhs rhs =

  let num_assign = ref 0 in

  let assign l r =
    incr num_assign;
    if !num_assign > !maxsize 
    then raise Exit
    else eassign l r in

  let rec transf l r =
    match unroll env l.etyp with
    | TStruct(id, attr) ->
        let ci = Env.find_struct env id in
        transf_struct l r ci.ci_members
    | TUnion(id, attr) ->
        raise Exit
    | TArray(ty_elt, Some sz, attr) ->
        transf_array l r ty_elt 0L sz
    | TArray(ty_elt, None, attr) ->
        assert false
    | _ ->
        assign l r

  and transf_struct l r = function
    | [] -> nullconst
    | f :: fl ->
        comma (transf {edesc = EUnop(Odot f.fld_name, l); etyp = f.fld_typ}
                      {edesc = EUnop(Odot f.fld_name, r); etyp = f.fld_typ})
              (transf_struct l r fl)

  and transf_array l r ty idx sz =
    if idx >= sz then nullconst else begin
      let e = intconst idx size_t_ikind in
      comma (transf {edesc = EBinop(Oindex, l, e, ty); etyp = ty}
                    {edesc = EBinop(Oindex, r, e, ty); etyp = ty})
            (transf_array l r ty (Int64.add idx 1L) sz)
    end
  in

  try
    transf lhs rhs
  with Exit ->
    let by_words =
      match Cutil.alignof env lhs.etyp, Cutil.sizeof env lhs.etyp with
      | Some al, Some sz -> 
          al mod !config.sizeof_ptr = 0 && sz mod !config.sizeof_ptr = 0
      | _, _->
          false in
    let (ident, ty) =
      if by_words
      then memcpy_words_ident env
      else memcpy_ident env in
    let memcpy = {edesc = EVar(ident); etyp = ty} in
    let e_lhs = {edesc = EUnop(Oaddrof, lhs); etyp = TPtr(lhs.etyp, [])} in
    let e_rhs = {edesc = EUnop(Oaddrof, rhs); etyp = TPtr(rhs.etyp, [])} in
    let e_size = {edesc = ESizeof(lhs.etyp); etyp = TInt(size_t_ikind, [])} in
    {edesc = ECall(memcpy, [e_lhs; e_rhs; e_size]); etyp = TVoid[]}

(* Detect invariant l-values *)

let not_volatile env ty = not (List.mem AVolatile (attributes_of_type env ty))

let rec invariant_lvalue env e =
  match e.edesc with
  | EVar _ -> true
  | EUnop(Oderef, {edesc = EVar _; etyp = ty}) -> not_volatile env ty
  | EUnop(Odot _, e1) -> invariant_lvalue env e1
  | _ -> false

(* Bind a l-value to a temporary variable if it is not invariant. *)

let rec bind_lvalue env e fn =
  match e.edesc with
  | EBinop(Ocomma, e1, e2, _) ->
      ecomma e1 (bind_lvalue env e2 fn)
  | _ ->
      if invariant_lvalue env e then
        fn e
      else begin
        let tmp = new_temp (TPtr(e.etyp, [])) in
        ecomma (eassign tmp (eaddrof e))
               (fn {edesc = EUnop(Oderef, tmp); etyp = e.etyp})
      end

(* Transformation of expressions. *)

type context = Val | Effects

let rec transf_expr env ctx e =
  match e.edesc with
  | EBinop(Oassign, lhs, rhs, _) when is_composite_type env lhs.etyp ->
      bind_lvalue env (transf_expr env Val lhs) (fun l ->
      bind_lvalue env (transf_expr env Val rhs) (fun r ->
        let e' = transf_assign env l r in
        if ctx = Val then ecomma e' l else e'))
  | EConst c -> e
  | ESizeof ty -> e
  | EVar x -> e
  | EUnop(op, e1) ->
      {edesc = EUnop(op, transf_expr env Val e1); etyp = e.etyp}
  | EBinop(Ocomma, e1, e2, ty) ->
      {edesc = EBinop(Ocomma, transf_expr env Effects e1,
                              transf_expr env ctx e2, ty);
       etyp = e.etyp}
  | EBinop(op, e1, e2, ty) ->
      {edesc = EBinop(op, transf_expr env Val e1,
                          transf_expr env Val e2, ty);
       etyp = e.etyp}
  | EConditional(e1, e2, e3) ->
      {edesc = EConditional(transf_expr env Val e1,
                            transf_expr env ctx e2, transf_expr env ctx e3);
       etyp = e.etyp}
  | ECast(ty, e1) ->
      {edesc = ECast(ty, transf_expr env Val e1); etyp = e.etyp}
  | ECall(e1, el) ->
      {edesc = ECall(transf_expr env Val e1,
                     List.map (transf_expr env Val) el);
       etyp = e.etyp}

(* Transformation of statements *)

let rec transf_stmt env s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e -> {s with sdesc = Sdo(transf_expr env Effects e)}
  | Sseq(s1, s2) ->
      {s with sdesc = Sseq(transf_stmt env s1, transf_stmt env s2)}
  | Sif(e, s1, s2) ->
      {s with sdesc = Sif(transf_expr env Val e,
                          transf_stmt env s1, transf_stmt env s2)}
  | Swhile(e, s1) ->
      {s with sdesc = Swhile(transf_expr env Val e, transf_stmt env s1)}
  | Sdowhile(s1, e) ->
      {s with sdesc = Sdowhile(transf_stmt env s1, transf_expr env Val e)}
  | Sfor(s1, e, s2, s3) ->
      {s with sdesc = Sfor(transf_stmt env s1, transf_expr env Val e,
                           transf_stmt env s2, transf_stmt env s3)}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {s with sdesc = Sswitch(transf_expr env Val e, transf_stmt env s1)}
  | Slabeled(lbl, s1) ->
      {s with sdesc = Slabeled(lbl, transf_stmt env s1)}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn (Some e) -> {s with sdesc = Sreturn(Some(transf_expr env Val e))}
  | Sblock _ | Sdecl _ -> assert false (* not in unblocked code *)

let transf_fundef env f =
  reset_temps();
  let newbody = transf_stmt env f.fd_body in
  let temps = get_temps() in
  {f with fd_locals = f.fd_locals @ temps; fd_body = newbody}

let program p =
  memcpy_decl := None;
  let p' = Transform.program ~fundef:transf_fundef p in
  match !memcpy_decl with
  | None -> p'
  | Some id ->
      {gdesc = Gdecl(Storage_extern, id, memcpy_type, None); gloc = no_loc}
      :: p'

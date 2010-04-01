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

(* Materialize implicit casts *)

(* Assumes: simplified code
   Produces: simplified code
   Preserves: unblocked code *)

open C
open Cutil
open Transform

(* We have the option of materializing all casts or leave "widening"
   casts implicit.  Widening casts are:
- from a small integer type to a larger integer type,
- from a small float type to a larger float type,
- from a pointer type to void *. 
*)

let omit_widening_casts = ref false

let widening_cast env tfrom tto =
  begin match unroll env tfrom, unroll env tto with
  | TInt(k1, _), TInt(k2, _) ->
      let r1 = integer_rank k1 and r2 = integer_rank k2 in
      r1 < r2 || (r1 = r2 && is_signed_ikind k1 = is_signed_ikind k2)
  | TFloat(k1, _), TFloat(k2, _) ->
      float_rank k1 <= float_rank k2
  | TPtr(ty1, _), TPtr(ty2, _) -> is_void_type env ty2
  | _, _ -> false
  end

let cast_not_needed env tfrom tto =
  let tfrom = pointer_decay env tfrom
  and tto = pointer_decay env tto in
  compatible_types env tfrom tto
  || (!omit_widening_casts && widening_cast env tfrom tto)

let cast env e tto =
  if cast_not_needed env e.etyp tto
  then e
  else {edesc = ECast(tto, e); etyp = tto}

(* Note: this pass applies only to simplified expressions 
   because casts cannot be materialized in op= expressions... *)

let rec add_expr env e =
  match e.edesc with
  | EConst _ -> e
  | EVar _ -> e
  | ESizeof _ -> e
  | EUnop(op, e1) ->
      let e1' = add_expr env e1 in
      let desc =
        match op with
        | Ominus | Oplus | Onot ->
            EUnop(op, cast env e1' e.etyp)
        | Olognot | Oderef | Oaddrof
        | Odot _ | Oarrow _ ->
            EUnop(op, e1')
        | Opreincr | Opredecr | Opostincr | Opostdecr ->
            assert false (* not simplified *)
      in { edesc = desc; etyp = e.etyp }
  | EBinop(op, e1, e2, ty) ->
      let e1' = add_expr env e1 in
      let e2' = add_expr env e2 in
      let desc =
        match op with
        | Oadd ->
            if is_pointer_type env ty
            then EBinop(Oadd, e1', e2', ty)
            else EBinop(Oadd, cast env e1' ty, cast env e2' ty, ty)
        | Osub ->
            if is_pointer_type env ty
            then EBinop(Osub, e1', e2', ty)
            else EBinop(Osub, cast env e1' ty, cast env e2' ty, ty)
        | Omul|Odiv|Omod|Oand|Oor|Oxor|Oeq|One|Olt|Ogt|Ole|Oge ->
            EBinop(op, cast env e1' ty, cast env e2' ty, ty)
        | Oshl|Oshr ->
            EBinop(op, cast env e1' ty, e2', ty)
        | Oindex | Ologand | Ologor | Ocomma ->
            EBinop(op, e1', e2', ty)
        | Oassign
        | Oadd_assign|Osub_assign|Omul_assign|Odiv_assign|Omod_assign
        | Oand_assign|Oor_assign|Oxor_assign|Oshl_assign|Oshr_assign ->
            assert false (* not simplified *)
      in { edesc = desc; etyp = e.etyp }
  | EConditional(e1, e2, e3) ->
      { edesc = 
          EConditional(add_expr env e1, add_expr env e2, add_expr env e3);
        etyp = e.etyp }
  | ECast(ty, e1) ->
      { edesc = ECast(ty, add_expr env e1); etyp = e.etyp }
  | ECall(e1, el) ->
      assert false (* not simplified *)

(* Arguments to a prototyped function *)

let rec add_proto env args params =
  match args, params with
  | [], _ -> []
  | _::_, [] -> add_noproto env args
  | arg1 :: argl, (_, ty_p) :: paraml ->
      cast env (add_expr env arg1) ty_p ::
      add_proto env argl paraml

(* Arguments to a non-prototyped function *)

and add_noproto env args =
  match args with
  | [] -> []
  | arg1 :: argl ->
      cast env (add_expr env arg1) (default_argument_conversion env arg1.etyp) ::
      add_noproto env argl

(* Arguments to function calls in general *)

let add_arguments env ty_fun args =
  let ty_args =
    match unroll env ty_fun with
    | TFun(res, args, vararg, a) -> args
    | TPtr(ty, a) ->
        begin match unroll env ty with
        | TFun(res, args, vararg, a) -> args
        | _ -> assert false
        end
    | _ -> assert false in
  match ty_args with
  | None -> add_noproto env args
  | Some targs -> add_proto env args targs

(* Toplevel expressions (appearing in Sdo statements) *)

let add_topexpr env loc e =
  match e.edesc with
  | EBinop(Oassign, lhs, {edesc = ECall(e1, el); etyp = ty}, _) ->
      let ecall =
        {edesc = ECall(add_expr env e1, add_arguments env e1.etyp el);
         etyp = ty} in
      if cast_not_needed env ty lhs.etyp then
        sassign loc (add_expr env lhs) ecall
      else begin
        let tmp = new_temp (erase_attributes_type env ty) in
        sseq loc (sassign loc tmp ecall) 
                 (sassign loc (add_expr env lhs) (cast env tmp lhs.etyp))
      end
  | EBinop(Oassign, lhs, rhs, _) ->
      sassign loc (add_expr env lhs) (cast env (add_expr env rhs) lhs.etyp)
  | ECall(e1, el) ->
      let ecall =
        {edesc = ECall(add_expr env e1, add_arguments env e1.etyp el);
         etyp = e.etyp} in
      {sdesc = Sdo ecall; sloc = loc}
  | _ ->
      assert false

(* Initializers *)

let rec add_init env tto = function
  | Init_single e ->
      Init_single (cast env (add_expr env e) tto)
  | Init_array il ->
      let ty_elt =
        match unroll env tto with
        | TArray(ty, _, _) -> ty | _ -> assert false in
      Init_array (List.map (add_init env ty_elt) il)
  | Init_struct(id, fil) ->
      Init_struct (id, List.map
                         (fun (fld, i) -> (fld, add_init env fld.fld_typ i))
                         fil)
  | Init_union(id, fld, i) ->
      Init_union(id, fld, add_init env fld.fld_typ i)

(* Declarations *)

let add_decl env (sto, id, ty, optinit) =
  (sto, id, ty,
   begin match optinit with
         | None -> None
         | Some init -> Some(add_init env ty init)
   end)

(* Statements *)

let rec add_stmt env f s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e -> add_topexpr env s.sloc e
  | Sseq(s1, s2) -> 
      {sdesc = Sseq(add_stmt env f s1, add_stmt env f s2); sloc = s.sloc }
  | Sif(e, s1, s2) ->
      {sdesc = Sif(add_expr env e, add_stmt env f s1, add_stmt env f s2);
       sloc = s.sloc}
  | Swhile(e, s1) ->
      {sdesc = Swhile(add_expr env e, add_stmt env f s1);
       sloc = s.sloc}
  | Sdowhile(s1, e) ->
      {sdesc = Sdowhile(add_stmt env f s1, add_expr env e);
       sloc = s.sloc}
  | Sfor(s1, e, s2, s3) ->
      {sdesc = Sfor(add_stmt env f s1, add_expr env e, add_stmt env f s2,
                    add_stmt env f s3);
       sloc = s.sloc}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {sdesc = Sswitch(add_expr env e, add_stmt env f s1); sloc = s.sloc}
  | Slabeled(lbl, s) ->
      {sdesc = Slabeled(lbl, add_stmt env f s); sloc = s.sloc}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn (Some e) ->
      {sdesc = Sreturn(Some(cast env (add_expr env e) f.fd_ret)); sloc = s.sloc}
  | Sblock sl ->
      {sdesc = Sblock(List.map (add_stmt env f) sl); sloc = s.sloc}
  | Sdecl d ->
      {sdesc = Sdecl(add_decl env d); sloc = s.sloc}

let add_fundef env f =
  reset_temps();
  let body' = add_stmt env f f.fd_body in
  let temps = get_temps () in
  (* fd_locals have no initializers, so no need to transform them *)
  { f with fd_locals = f.fd_locals @ temps; fd_body = body' }


let program ?(all = false) p =
  omit_widening_casts := not all;
  Transform.program ~decl:add_decl ~fundef:add_fundef p

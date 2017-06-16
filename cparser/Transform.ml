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

(* Generic program transformation *)

open C
open Cutil
open Env

(* Recording fresh temporaries *)

let temporaries = ref ([]: decl list)

let reset_temps () =
  temporaries := []

let get_temps () =
  let temps = !temporaries in
  temporaries := [];
  List.rev temps

let new_temp_var ?(name = "t") ty =
  let id = Env.fresh_ident name in
  temporaries := (Storage_default, id, ty, None) :: !temporaries;
  id

let new_temp ?(name = "t") ty =
  let id = new_temp_var ~name ty in
  { edesc = EVar id; etyp = ty }

(* Temporaries should not be [const] because we assign into them
   and not be [volatile] because they are local and not observable *)

let attributes_to_remove_from_temp = add_attributes [AConst] [AVolatile]

let mk_temp env ty =
  new_temp (remove_attributes_type env attributes_to_remove_from_temp ty)

(* Bind a l-value to a temporary variable if it is not invariant. *)

let rec invariant_lvalue env e =
  match e.edesc with
  | EVar _ -> true
  | EUnop(Odot _, e1) -> invariant_lvalue env e1
  | _ -> false

let bind_lvalue env e fn =
  if invariant_lvalue env e then
    fn e
  else begin
    let tmp = new_temp (TPtr(e.etyp, [])) in
    ecomma (eassign tmp (eaddrof e))
           (fn {edesc = EUnop(Oderef, tmp); etyp = e.etyp})
  end

(* Most transformations over expressions can be optimized if the
   value of the expression is not needed and it is evaluated only
   for its side-effects.  The type [context] records whether
   we are in a side-effects-only position ([Effects]) or not ([Val]). *)

type context = Val | Effects

(* Expansion of assignment expressions *)

let op_for_assignop = function
  | Oadd_assign -> Oadd
  | Osub_assign -> Osub
  | Omul_assign -> Omul
  | Odiv_assign -> Odiv
  | Omod_assign -> Omod
  | Oand_assign -> Oand
  | Oor_assign -> Oor
  | Oxor_assign -> Oxor
  | Oshl_assign -> Oshl
  | Oshr_assign -> Oshr
  | _ -> assert false

let op_for_incr_decr = function
  | Opreincr -> Oadd
  | Opredecr -> Osub
  | Opostincr -> Oadd
  | Opostdecr -> Osub
  | _ -> assert false

let assignop_for_incr_decr = function
  | Opreincr -> Oadd_assign
  | Opredecr -> Osub_assign
  | _ -> assert false

let expand_assign ~write env ctx l r =
  match ctx with
  | Effects ->
      write l r
  | Val ->
      let tmp = mk_temp env l.etyp in
      ecomma (eassign tmp r) (ecomma (write l tmp) tmp)

let expand_assignop ~read ~write env ctx op l r ty =
  bind_lvalue env l (fun l ->
    let res = {edesc = EBinop(op_for_assignop op, read l, r, ty); etyp = ty} in
    match ctx with
    | Effects ->
        write l res
    | Val ->
        let tmp = mk_temp env l.etyp in
        ecomma (eassign tmp res) (ecomma (write l tmp) tmp))

let expand_preincrdecr ~read ~write env ctx op l =
  expand_assignop ~read ~write env ctx (assignop_for_incr_decr op)
              l (intconst 1L IInt) (unary_conversion env l.etyp)

let expand_postincrdecr ~read ~write env ctx op l =
  bind_lvalue env l (fun l ->
    let ty = unary_conversion env l.etyp in
    match ctx with
    | Effects ->
        let newval =
          {edesc = EBinop(op_for_incr_decr op, read l, intconst 1L IInt, ty);
           etyp = ty} in
        write l newval
    | Val ->
        let tmp = mk_temp env l.etyp in
        let newval =
          {edesc = EBinop(op_for_incr_decr op, tmp, intconst 1L IInt, ty);
           etyp = ty} in
        ecomma (eassign tmp (read l)) (ecomma (write l newval) tmp))

(* Generic transformation of a statement, transforming expressions within
   and preserving the statement structure.
   If [decl] is not given, it applies only to unblocked code. *)

let stmt ~expr ?(decl = fun env decl -> assert false) env s =
  let rec stm s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e ->
      {s with sdesc = Sdo(expr s.sloc env Effects e)}
  | Sseq(s1, s2) ->
      {s with sdesc = Sseq(stm s1, stm s2)}
  | Sif(e, s1, s2) ->
      {s with sdesc = Sif(expr s.sloc env Val e, stm s1, stm s2)}
  | Swhile(e, s1) ->
      {s with sdesc = Swhile(expr s.sloc env Val e, stm s1)}
  | Sdowhile(s1, e) ->
      {s with sdesc = Sdowhile(stm s1, expr s.sloc env Val e)}
  | Sfor(s1, e, s2, s3) ->
      {s with sdesc = Sfor(stm s1, expr s.sloc env Val e, stm s2, stm s3)}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {s with sdesc = Sswitch(expr s.sloc env Val e, stm s1)}
  | Slabeled(lbl, s) ->
      {s with sdesc = Slabeled(lbl, stm s)}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn (Some e) ->
      {s with sdesc = Sreturn(Some(expr s.sloc env Val e))}
  | Sasm(attr, template, outputs, inputs, clob) ->
      let asm_operand (lbl, cstr, e) =
        (lbl, cstr, expr s.sloc env Val e) in
      {s with sdesc = Sasm(attr, template,
                           List.map asm_operand outputs,
                           List.map asm_operand inputs, clob)}
  | Sblock sl ->
      {s with sdesc = Sblock (List.map stm sl)}
  | Sdecl d ->
      {s with sdesc = Sdecl (decl env d)}

  in stm s

(* Generic transformation of a function definition *)

let fundef trstmt env f =
  reset_temps();
  let newbody = trstmt env f.fd_body in
  let temps = get_temps() in
  {f with fd_locals = f.fd_locals @ temps; fd_body = newbody}

(* Generic transformation of a program *)

let program
    ?(decl = fun env d -> d)
    ?(fundef = fun env fd -> fd)
    ?(composite = fun env su id attr fl -> (attr, fl))
    ?(typedef = fun env id ty -> ty)
    ?(enum = fun env id attr members -> (attr, members))
    ?(pragma = fun env s -> s)
    p =

  let rec transf_globdecls env accu = function
  | [] -> List.rev accu
  | g :: gl ->
      let (desc', env') =
        match g.gdesc with
        | Gdecl((sto, id, ty, init) as d) ->
           (Gdecl(decl env d), Env.add_ident env id sto ty)
        | Gfundef f ->
           (Gfundef(fundef env f),
            Env.add_ident env f.fd_name f.fd_storage (fundef_typ f))
        | Gcompositedecl(su, id, attr) ->
            (Gcompositedecl(su, id, attr),
             Env.add_composite env id (composite_info_decl su attr))
        | Gcompositedef(su, id, attr, fl) ->
            let (attr', fl') = composite env su id attr fl in
            (Gcompositedef(su, id, attr', fl'),
             Env.add_composite env id (composite_info_def env su attr fl))
        | Gtypedef(id, ty) ->
            (Gtypedef(id, typedef env id ty), Env.add_typedef env id ty)
        | Genumdef(id, attr, members) ->
            let (attr', members') = enum env id attr members in
            (Genumdef(id, attr', members'),
             Env.add_enum env id {ei_members =  members; ei_attr = attr})
        | Gpragma s ->
            (Gpragma(pragma env s), env)
      in
        transf_globdecls env' ({g with gdesc = desc'} :: accu) gl

  in transf_globdecls (Builtins.environment()) [] p

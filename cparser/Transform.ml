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

let new_temp_var ?(name = "t") ty =
  let id = Env.fresh_ident name in
  temporaries := (Storage_default, id, ty, None) :: !temporaries;
  id

let new_temp ?(name = "t") ty =
  let id = new_temp_var ~name ty in
  { edesc = EVar id; etyp = ty }

let get_temps () =
  let temps = !temporaries in
  temporaries := [];
  List.rev temps

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

(* Generic transformation of a statement, transforming expressions within
   and preserving the statement structure.  Applies only to unblocked code. *)

type context = Val | Effects

let stmt trexpr env s =
  let rec stm s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e ->
      {s with sdesc = Sdo(trexpr s.sloc env Effects e)}
  | Sseq(s1, s2) -> 
      {s with sdesc = Sseq(stm s1, stm s2)}
  | Sif(e, s1, s2) ->
      {s with sdesc = Sif(trexpr s.sloc env Val e, stm s1, stm s2)}
  | Swhile(e, s1) ->
      {s with sdesc = Swhile(trexpr s.sloc env Val e, stm s1)}
  | Sdowhile(s1, e) ->
      {s with sdesc = Sdowhile(stm s1, trexpr s.sloc env Val e)}
  | Sfor(s1, e, s2, s3) ->
      {s with sdesc = Sfor(stm s1, trexpr s.sloc env Val e, stm s2, stm s3)}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {s with sdesc = Sswitch(trexpr s.sloc env Val e, stm s1)}
  | Slabeled(lbl, s) ->
      {s with sdesc = Slabeled(lbl, stm s)}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn (Some e) ->
      {s with sdesc = Sreturn(Some(trexpr s.sloc env Val e))}
  | Sblock _ | Sdecl _ ->
      assert false     (* should not occur in unblocked code *)
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
    ?(enum = fun env id members -> members)
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
             Env.add_composite env id (composite_info_decl env su attr))
        | Gcompositedef(su, id, attr, fl) ->
            let (attr', fl') = composite env su id attr fl in
            (Gcompositedef(su, id, attr', fl'),
             Env.add_composite env id (composite_info_def env su attr fl))
        | Gtypedef(id, ty) ->
            (Gtypedef(id, typedef env id ty), Env.add_typedef env id ty)
        | Genumdef(id, members) ->
            (Genumdef(id, enum env id members), env)
        | Gpragma s ->
            (Gpragma(pragma env s), env)
      in
        transf_globdecls env' ({g with gdesc = desc'} :: accu) gl

  in transf_globdecls (Builtins.environment()) [] p

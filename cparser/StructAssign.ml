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

(* Assumes: simplified code.
   Preserves: simplified code, unblocked code *)

open C
open Machine
open Cutil
open Env
open Errors

let maxsize = ref 8

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

let transf_assign env loc lhs rhs =

  let num_assign = ref 0 in

  let assign l r =
    incr num_assign;
    if !num_assign > !maxsize 
    then raise Exit
    else sassign loc l r in

  let rec transf l r =
    match unroll env l.etyp with
    | TStruct(id, attr) ->
        let ci = Env.find_struct env id in
        if ci.ci_sizeof = None then
          error "%a: Error: incomplete struct '%s'" formatloc loc id.name;
        transf_struct l r ci.ci_members
    | TUnion(id, attr) ->
        raise Exit
    | TArray(ty_elt, Some sz, attr) ->
        transf_array l r ty_elt 0L sz
    | TArray(ty_elt, None, attr) ->
        error "%a: Error: array of unknown size" formatloc loc;
        sskip                           (* will be ignored later *)
    | _ ->
        assign l r

  and transf_struct l r = function
    | [] -> sskip
    | f :: fl ->
        sseq loc (transf {edesc = EUnop(Odot f.fld_name, l); etyp = f.fld_typ}
                         {edesc = EUnop(Odot f.fld_name, r); etyp = f.fld_typ})
                 (transf_struct l r fl)

  and transf_array l r ty idx sz =
    if idx >= sz then sskip else begin
      let e = intconst idx size_t_ikind in
      sseq loc (transf {edesc = EBinop(Oindex, l, e, ty); etyp = ty}
                       {edesc = EBinop(Oindex, r, e, ty); etyp = ty})
               (transf_array l r ty (Int64.add idx 1L) sz)
    end
  in

  try
    transf lhs rhs
  with Exit ->
    let by_words =
      match Cutil.sizeof env lhs.etyp with
      | Some n -> n mod !config.sizeof_ptr = 0
      | None -> false in
    let (ident, ty) =
      if by_words
      then memcpy_words_ident env
      else memcpy_ident env in
    let memcpy = {edesc = EVar(ident); etyp = ty} in
    let e_lhs = {edesc = EUnop(Oaddrof, lhs); etyp = TPtr(lhs.etyp, [])} in
    let e_rhs = {edesc = EUnop(Oaddrof, rhs); etyp = TPtr(rhs.etyp, [])} in
    let e_size = {edesc = ESizeof(lhs.etyp); etyp = TInt(size_t_ikind, [])} in
    {sdesc = Sdo {edesc = ECall(memcpy, [e_lhs; e_rhs; e_size]);
                  etyp = TVoid[]};
     sloc = loc}

let rec transf_stmt env s =
  match s.sdesc with
  | Sskip -> s
  | Sdo {edesc = EBinop(Oassign, lhs, rhs, _)}
    when is_composite_type env lhs.etyp ->
      transf_assign env s.sloc lhs rhs
  | Sdo _ -> s
  | Sseq(s1, s2) ->
      {s with sdesc = Sseq(transf_stmt env s1, transf_stmt env s2)}
  | Sif(e, s1, s2) ->
      {s with sdesc = Sif(e, transf_stmt env s1, transf_stmt env s2)}
  | Swhile(e, s1) ->
      {s with sdesc = Swhile(e, transf_stmt env s1)}
  | Sdowhile(s1, e) ->
      {s with sdesc = Sdowhile(transf_stmt env s1, e)}
  | Sfor(s1, e, s2, s3) ->
      {s with sdesc = Sfor(transf_stmt env s1, e,
                           transf_stmt env s2, transf_stmt env s3)}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {s with sdesc = Sswitch(e, transf_stmt env s1)}
  | Slabeled(lbl, s1) ->
      {s with sdesc = Slabeled(lbl, transf_stmt env s1)}
  | Sgoto lbl -> s
  | Sreturn _ -> s
  | Sblock sl ->
      {s with sdesc = Sblock(List.map (transf_stmt env) sl)}
  | Sdecl d -> s

let transf_fundef env fd =
  {fd with fd_body = transf_stmt env fd.fd_body}

let program p =
  memcpy_decl := None;
  let p' = Transform.program ~fundef:transf_fundef p in
  match !memcpy_decl with
  | None -> p'
  | Some id ->
      {gdesc = Gdecl(Storage_extern, id, memcpy_type, None); gloc = no_loc}
      :: p'

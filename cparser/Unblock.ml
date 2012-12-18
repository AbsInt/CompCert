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

(* Simplification of blocks and initializers within functions *)

(* Assumes: nothing
   Produces: unblocked code *)

open C
open Cutil
open Cerrors

(* Convert an initializer to a list of assignments.
   Prepend those assignments to the given statement. *)

let sdoseq loc e s =
  sseq loc {sdesc = Sdo e; sloc = loc} s

let rec local_initializer loc env path init k =
  match init with
  | Init_single e ->
      sdoseq loc
        { edesc = EBinop(Oassign, path, e, path.etyp); etyp = path.etyp }
        k
  | Init_array il ->
      let ty_elt =
        match unroll env path.etyp with
        | TArray(ty_elt, _, _) -> ty_elt
        | _ -> fatal_error "%aWrong type for array initializer" 
                           formatloc loc in
      let rec array_init pos = function
        | [] -> k
        | i :: il ->
            local_initializer loc env
              { edesc = EBinop(Oindex, path, intconst pos IInt, TPtr(ty_elt, []));
                etyp = ty_elt }
              i
              (array_init (Int64.succ pos) il) in
      array_init 0L il
  | Init_struct(id, fil) ->
      let field_init (fld, i) k =
        local_initializer loc env
          { edesc = EUnop(Odot fld.fld_name, path); etyp = fld.fld_typ } 
          i k in
      List.fold_right field_init fil k
  | Init_union(id, fld, i) ->
      local_initializer loc env
        { edesc = EUnop(Odot fld.fld_name, path); etyp = fld.fld_typ }
        i k

(* Record new variables to be locally defined *)

let local_variables = ref ([]: decl list)

(* Note: "const int x = y - 1;" is legal, but we turn it into 
   "const int x; x = y - 1;", which is not.  Therefore, remove
   top-level 'const' attribute.  Also remove it on element type of
   array type. *)

let remove_const env ty = remove_attributes_type env [AConst] ty

(* Process a variable declaration.
   The variable is entered in [local_variables].
   The initializer, if any, is converted into assignments and
   prepended to [k]. *)

let process_decl loc env (sto, id, ty, optinit) k =
  let ty' = remove_const env ty in
  local_variables := (sto, id, ty', None) :: !local_variables;
  match optinit with
  | None -> k
  | Some init ->
      local_initializer loc env { edesc = EVar id; etyp = ty' } init k

(* Simplification of blocks within a statement *)

let rec unblock_stmt env s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e -> s
  | Sseq(s1, s2) ->
      {s with sdesc = Sseq(unblock_stmt env s1, unblock_stmt env s2)}
  | Sif(e, s1, s2) -> 
      {s with sdesc = Sif(e, unblock_stmt env s1, unblock_stmt env s2)}
  | Swhile(e, s1) -> 
      {s with sdesc = Swhile(e, unblock_stmt env s1)}
  | Sdowhile(s1, e) ->
      {s with sdesc = Sdowhile(unblock_stmt env s1, e)}
  | Sfor(s1, e, s2, s3) ->
      {s with sdesc = Sfor(unblock_stmt env s1, e, unblock_stmt env s2, unblock_stmt env s3)}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {s with sdesc = Sswitch(e, unblock_stmt env s1)}
  | Slabeled(lbl, s1) -> 
      {s with sdesc = Slabeled(lbl, unblock_stmt env s1)}
  | Sgoto lbl -> s
  | Sreturn opte -> s
  | Sblock sl -> unblock_block env sl
  | Sdecl d -> assert false
  | Sasm _ -> s

and unblock_block env = function
  | [] -> sskip
  | {sdesc = Sdecl d; sloc = loc} :: sl ->
      process_decl loc env d (unblock_block env sl)
  | s :: sl ->
      sseq s.sloc (unblock_stmt env s) (unblock_block env sl)

(* Simplification of blocks within a function *)

let unblock_fundef env f =
  local_variables := [];
  let body = unblock_stmt env f.fd_body in
  let decls = !local_variables in
  local_variables := [];
  { f with fd_locals = f.fd_locals @ decls; fd_body = body }

(* Entry point *)

let program p =
  Transform.program ~fundef:unblock_fundef p

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Bernhard Schommer, AbsInt Angewandte Informatik GmbH        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open C
open Cerrors
open Cutil

let attribute_string = function
  | AConst -> "const"
  | AVolatile -> "volatile"
  | ARestrict -> "restrict"
  | AAlignas n -> "_Alignas"
  | Attr(name, _) ->  name

let unknown_attrs loc attrs =
  let unknown attr =
    let attr_class = class_of_attribute attr in
    if attr_class = Attr_unknown then
      warning loc Unknown_attribute
        "unknown attribute '%s' ignored" (attribute_string attr) in
  List.iter unknown attrs

let unknown_attrs_typ env loc ty =
  let attr = attributes_of_type env ty in
  unknown_attrs loc attr

let unknown_attrs_decl env loc (sto, id, ty, init) =
  unknown_attrs_typ env loc ty

let rec unknown_attrs_stmt env s =
  match s.sdesc with
  | Sskip
  | Sbreak
  | Scontinue
  | Slabeled _
  | Sgoto _
  | Sreturn _
  | Sasm _
  | Sdo _ -> ()
  | Sif (_,s1,s2)
  | Sseq (s1,s2) ->
    unknown_attrs_stmt env s1;
    unknown_attrs_stmt env s2
  | Sfor (s1,e,s2,s3) ->
    unknown_attrs_stmt env s1;
    unknown_attrs_stmt env s2;
    unknown_attrs_stmt env s3
  | Swhile(_,s)
  | Sdowhile (s,_)
  | Sswitch (_,s) -> unknown_attrs_stmt env s
  | Sblock sl -> List.iter (unknown_attrs_stmt env) sl
  | Sdecl d -> unknown_attrs_decl env s.sloc d

let unknown_attrs_program p =
  let rec unknown_attrs_globdecls env = function
    | [] -> ()
    | g :: gl ->
      let env' =
        match g.gdesc with
        | Gdecl ((sto, id, ty, init) as d) ->
          unknown_attrs_decl env g.gloc d;
          Env.add_ident env id sto ty
        | Gfundef f ->
          unknown_attrs g.gloc f.fd_attrib;
          unknown_attrs_stmt env f.fd_body;
          List.iter (unknown_attrs_decl env g.gloc) f.fd_locals;
          Env.add_ident env f.fd_name f.fd_storage (fundef_typ f)
        | Gcompositedecl(su, id, attr) ->
          Env.add_composite env id (composite_info_decl su attr)
        | Gcompositedef(su, id, attr, fl) ->
          unknown_attrs g.gloc attr;
          List.iter (fun fld ->  unknown_attrs_typ env g.gloc fld.fld_typ) fl;
          Env.add_composite env id (composite_info_def env su attr fl)
        | Gtypedef(id, ty) ->
          unknown_attrs_typ env g.gloc ty;
          Env.add_typedef env id ty
        | Genumdef(id, attr, members) ->
          unknown_attrs g.gloc attr;
          Env.add_enum env id {Env.ei_members =  members; ei_attr = attr}
        | Gpragma s ->
          env
      in
        unknown_attrs_globdecls env' gl
  in unknown_attrs_globdecls (Builtins.environment()) p

let rec vars_used_expr env e =
  match e.edesc with
  | EConst _
  | ESizeof _
  | EAlignof _ -> env
  | EVar id -> IdentSet.add id env
  | ECast (_,e)
  | EUnop (_,e) -> vars_used_expr env e
  | EBinop (_,e1,e2,_) ->
    let env = vars_used_expr env e1 in
    vars_used_expr env e2
  | EConditional (e1,e2,e3) ->
    let env = vars_used_expr env e1 in
    let env = vars_used_expr env e2 in
    vars_used_expr env e3
  | ECompound (_,init) -> vars_used_init env init
  | ECall (e,p) ->
    let env = vars_used_expr env e in
    List.fold_left vars_used_expr env p

and vars_used_init env = function
  | Init_single e -> vars_used_expr env e
  | Init_array al -> List.fold_left vars_used_init env al
  | Init_struct (_,sl) -> List.fold_left (fun env (_,i) -> vars_used_init env i) env sl
  | Init_union (_,_,ui) -> vars_used_init env ui

let rec vars_used_stmt ((dec_env,used_env) as acc) s =
  match s.sdesc with
  | Sbreak
  | Scontinue
  | Sgoto _
  | Sreturn None
  | Sskip -> acc
  | Sreturn (Some e)
  | Sdo e -> dec_env,(vars_used_expr used_env e)
  | Sseq (s1,s2) ->
    let acc = vars_used_stmt acc s1 in
    vars_used_stmt acc s2
  | Sif (e,s1,s2) ->
    let used_env = vars_used_expr used_env e in
    let acc = vars_used_stmt (dec_env,used_env) s1 in
    vars_used_stmt acc s2
  | Sfor (s1,e,s2,s3) ->
    let used_env = vars_used_expr used_env e in
    let acc = vars_used_stmt (dec_env,used_env) s1 in
    let acc = vars_used_stmt acc s2 in
    vars_used_stmt acc s3
  | Sswitch (e,s)
  | Swhile (e,s)
  | Sdowhile (s,e) ->
    let used_env = vars_used_expr used_env e in
    vars_used_stmt (dec_env,used_env) s
  | Sblock sl -> List.fold_left vars_used_stmt acc sl
  | Sdecl (sto,id,ty,init) ->
    let dec_env = IdentMap.add id s.sloc dec_env
    and used_env = match init with
      | Some init ->vars_used_init used_env init
      | None -> used_env in
    dec_env,used_env
  | Slabeled (lbl,s) -> vars_used_stmt acc s
  | Sasm (attr,str,op,op2,constr) ->
    let vars_asm_op env (_,_,e) =
      vars_used_expr env e in
    let used_env = List.fold_left vars_asm_op used_env op in
    let used_env = List.fold_left vars_asm_op used_env op2 in
    dec_env,used_env

let unused_variables p =
  List.iter (fun g -> match g.gdesc with
      | Gfundef fd ->
        let dec_env,used_env = vars_used_stmt (IdentMap.empty,IdentSet.empty) fd.fd_body in
        IdentMap.iter (fun id loc -> if not (IdentSet.mem id used_env) then
                          warning loc Unused_variable "unused variable '%s'" id.name) dec_env
      | _ -> ()) p

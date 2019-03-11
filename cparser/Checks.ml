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
open Diagnostics
open Cutil
open Env

let unknown_attrs loc attrs =
  let unknown attr =
    let attr_class = class_of_attribute attr in
    if attr_class = Attr_unknown then
      warning loc Unknown_attribute
        "unknown attribute '%s' ignored" (name_of_attribute attr) in
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

let traverse_program
    ?(decl = fun env loc d -> ())
    ?(fundef = fun env loc fd -> ())
    ?(compositedecl = fun env loc su id attr -> ())
    ?(compositedef = fun env loc su id attr fl -> ())
    ?(typedef = fun env loc id ty -> ())
    ?(enum = fun env loc id attr members -> ())
    ?(pragma = fun env loc s -> ())
    p =
  let rec traverse env = function
    | [] -> ()
    | g :: gl ->
      let env =
        match g.gdesc with
        | Gdecl ((sto, id, ty, init) as d) ->
          decl env g.gloc d;
          add_ident env id sto ty
        | Gfundef f ->
          fundef env g.gloc f;
          add_ident env f.fd_name f.fd_storage (fundef_typ f)
        | Gcompositedecl (su,id,attr) ->
          compositedecl env g.gloc su id attr;
          add_composite env id (composite_info_decl su attr)
        | Gcompositedef (su,id,attr,fl) ->
          compositedef env g.gloc su id attr fl;
          add_composite env id (composite_info_def env su attr fl)
        | Gtypedef (id,ty) ->
          typedef env g.gloc id ty;
          add_typedef env id ty
        | Genumdef (id,attr,members) ->
          enum env g.gloc id attr members;
          add_enum env id {ei_members = members; ei_attr = attr}
        | Gpragma s ->
          pragma env g.gloc s;
          env in
      traverse env gl in
  traverse (Builtins.environment ()) p

let unknown_attrs_program p =
  let decl env loc d =
    unknown_attrs_decl env loc d
  and fundef env loc f =
     List.iter (fun (id,typ) -> unknown_attrs_typ env loc typ) f.fd_params;
     unknown_attrs loc f.fd_attrib;
     unknown_attrs_stmt env f.fd_body;
     List.iter (unknown_attrs_decl env loc) f.fd_locals;
  and compositedecl env loc su id attr =
    unknown_attrs loc attr
  and compositedef env loc su id attr fl =
    unknown_attrs loc attr;
    List.iter (fun fld ->  unknown_attrs_typ env loc fld.fld_typ) fl
  and typedef env loc id ty =
    unknown_attrs_typ env loc ty
  and enum env loc id attr members =
    unknown_attrs loc attr
  in
  traverse_program
    ~decl:decl
    ~fundef:fundef
    ~compositedecl:compositedecl
    ~compositedef:compositedef
    ~typedef:typedef
    ~enum:enum
    p


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

let rec vars_used_stmt env s =
  match s.sdesc with
  | Sbreak
  | Scontinue
  | Sgoto _
  | Sreturn None
  | Sskip -> env
  | Sreturn (Some e)
  | Sdo e -> (vars_used_expr env e)
  | Sseq (s1,s2) ->
    let env = vars_used_stmt env s1 in
    vars_used_stmt env s2
  | Sif (e,s1,s2) ->
    let env = vars_used_expr env e in
    let env = vars_used_stmt env s1 in
    vars_used_stmt env s2
  | Sfor (s1,e,s2,s3) ->
    let env = vars_used_expr env e in
    let env = vars_used_stmt env s1 in
    let env = vars_used_stmt env s2 in
    vars_used_stmt env s3
  | Sswitch (e,s)
  | Swhile (e,s)
  | Sdowhile (s,e) ->
    let env = vars_used_expr env e in
    vars_used_stmt env s
  | Sblock sl -> List.fold_left vars_used_stmt env sl
  | Sdecl (sto,id,ty,init) ->
    let env = match init with
      | Some init ->vars_used_init env init
      | None -> env in
    env
  | Slabeled (lbl,s) -> vars_used_stmt env s
  | Sasm (attr,str,op,op2,constr) ->
    let vars_asm_op env (_,_,e) =
      vars_used_expr env e in
    let env = List.fold_left vars_asm_op env op in
    let env = List.fold_left vars_asm_op env op2 in
    env

let unused_variable env used loc (id,ty) =
  let attr = attributes_of_type env ty in
  let unused_attr = find_custom_attributes ["unused";"__unused__"] attr <> [] in
  if not ((IdentSet.mem id used) || unused_attr) then
    warning loc Unused_variable "unused variable '%s'" id.name

let rec unused_variables_stmt env used s =
  match s.sdesc with
  | Sbreak
  | Scontinue
  | Sgoto _
  | Sreturn _
  | Sskip
  | Sasm _
  | Sdo _ -> ()
  | Sseq (s1,s2)
  | Sif (_,s1,s2) ->
    unused_variables_stmt env used s1;
    unused_variables_stmt env used s2
  | Sfor (s1,e,s2,s3) ->
    unused_variables_stmt env used s1;
    unused_variables_stmt env used s2;
    unused_variables_stmt env used s3
  | Slabeled (_,s)
  | Sswitch (_,s)
  | Swhile (_,s)
  | Sdowhile (s,_) ->
    unused_variables_stmt env used s
  | Sblock sl -> List.iter (unused_variables_stmt env used) sl
  | Sdecl (sto,id,ty,init) ->
    unused_variable env used s.sloc (id,ty)

let unused_variables p =
  let fundef env loc fd =
    let used = vars_used_stmt IdentSet.empty fd.fd_body in
    unused_variables_stmt env used fd.fd_body;
    List.iter (unused_variable env used loc) fd.fd_params in
  traverse_program
    ~fundef:fundef
    p

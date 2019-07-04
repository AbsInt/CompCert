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

(* AST traversal functions *)

let fold_over_stmt_loc ~(expr: 'a -> location -> exp -> 'a)
    ~(decl: 'a -> location -> decl -> 'a)
    (a: 'a) (s: stmt) : 'a =
  let rec fold a s =
    match s.sdesc with
    | Sskip -> a
    | Sbreak -> a
    | Scontinue -> a
    | Slabeled(_, s1) -> fold a s1
    | Sgoto _ -> a
    | Sreturn None -> a
    | Sreturn (Some e) -> expr a s.sloc e
    | Sasm(_, _, outs, ins, _) -> asm_operands (asm_operands a s.sloc outs) s.sloc ins
    | Sdo e -> expr a s.sloc e
    | Sif (e, s1, s2) -> fold (fold (expr a s.sloc e) s1) s2
    | Sseq (s1, s2) -> fold (fold a s1) s2
    | Sfor (s1, e, s2, s3) -> fold (fold (expr (fold a s1) s.sloc e) s2) s3
    | Swhile(e, s1) -> fold (expr a s.sloc e) s1
    | Sdowhile (s1, e) -> expr (fold a s1) s.sloc e
    | Sswitch (e, s1) -> fold (expr a s.sloc e) s1
    | Sblock sl -> List.fold_left fold a sl
    | Sdecl d -> decl a s.sloc d
  and asm_operands a loc l =
    List.fold_left (fun a (_, _, e) -> expr a loc e) a l
  in fold a s

let iter_over_stmt_loc
    ?(expr = fun loc e -> ())
    ?(decl = fun loc decl -> ())
    (s: stmt) : unit =
  fold_over_stmt_loc ~expr: (fun () loc e -> expr loc e)
    ~decl: (fun () loc d -> decl loc d)
    () s

let fold_over_stmt ~(expr: 'a -> exp -> 'a)
    ~(decl: 'a -> location -> decl -> 'a)
    (a: 'a) (s: stmt) : 'a =
  fold_over_stmt_loc ~expr:(fun a _ e -> expr a e) ~decl:decl a s

let iter_over_stmt ?(expr = fun e -> ())
    ?(decl = fun loc decl -> ())
    (s:stmt) : unit =
  fold_over_stmt_loc ~expr:(fun () _ e -> expr e)
    ~decl:(fun () loc d -> decl loc d) () s

let fold_over_init ~(expr: 'a -> exp -> 'a) (a: 'a) (i: init) : 'a =
  let rec fold a = function
  | Init_single e -> expr a e
  | Init_array il -> List.fold_left fold a il
  | Init_struct (_, sl) -> List.fold_left (fun a (_,i) -> fold a i) a sl
  | Init_union (_, _, ui) -> fold a ui
  in fold a i

let iter_over_init ~(expr: exp -> unit) (i:init) : unit =
  fold_over_init ~expr:(fun () e -> expr e) () i

let fold_over_decl ~(expr: 'a -> exp -> 'a) (a: 'a) loc (sto, id, ty, init) : 'a=
  match init with
  | Some i -> fold_over_init ~expr a i
  | None -> a

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

(* Unknown attributes warning *)

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

let unknown_attrs_stmt env s =
  iter_over_stmt ~decl:(unknown_attrs_decl env) s

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

(* Unused variables and parameters warning *)

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

and vars_used_init env init =
  fold_over_init ~expr:vars_used_expr env init

let vars_used_stmt env s =
  fold_over_stmt ~expr: vars_used_expr
    ~decl: (fold_over_decl ~expr: vars_used_expr) env s

let unused_variable env used loc (id, ty) =
  let attr = attributes_of_type env ty in
  let unused_attr = find_custom_attributes ["unused";"__unused__"] attr <> [] in
  if not ((IdentSet.mem id used) || unused_attr) then
    warning loc Unused_variable "unused variable '%s'" id.name

let unused_variables_stmt env used s =
  iter_over_stmt ~decl:(fun loc (sto, id, ty, init) -> unused_variable env used loc (id,ty)) s

let unused_variables p =
  let fundef env loc fd =
    let used = vars_used_stmt IdentSet.empty fd.fd_body in
    unused_variables_stmt env used fd.fd_body;
    List.iter (unused_variable env used loc) fd.fd_params in
  traverse_program
    ~fundef:fundef
    p

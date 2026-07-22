(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Bernhard Schommer, AbsInt Angewandte Informatik GmbH        *)
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

let iter_over_decl ~(expr: exp -> unit) loc (sto, id, ty, init) : unit =
  match init with
  | Some i -> iter_over_init ~expr i
  | None -> ()

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
  traverse (Env.initial ()) p

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

(* Warning for conditionals that cannot be transformed into linear code *)

(* Compute the set of local variables that do not have their address taken *)

let rec non_stack_locals_expr vars e =
  match e.edesc with
  | ECast (_,e) -> non_stack_locals_expr vars e
  | EUnop (Oaddrof,e) ->
    begin match e.edesc with
    | EVar id ->
      IdentSet.remove id vars
    | _ -> vars
    end
  | EUnop (Oderef, e) ->
    (* Special optimization *(& ...) is removed in SimplExpr *)
    begin match e.edesc with
      | EUnop (Oaddrof,e) -> non_stack_locals_expr vars e
      | _ -> non_stack_locals_expr vars e
    end
  | EUnop (_, e) ->
    non_stack_locals_expr vars e
  | EBinop (_,e1,e2,_) ->
    let vars = non_stack_locals_expr vars e1 in
    non_stack_locals_expr vars e2
  | EConditional (e1,e2,e3) ->
    let vars = non_stack_locals_expr vars e1 in
    let vars = non_stack_locals_expr vars e2 in
    non_stack_locals_expr vars e3
  | ECompound (_,init) -> non_stack_locals_init vars init
  | ECall (e,p) ->
    let vars = non_stack_locals_expr vars e in
    List.fold_left non_stack_locals_expr vars p
  | _ -> vars

and non_stack_locals_init vars init =
  fold_over_init ~expr:non_stack_locals_expr vars init

let add_vars env vars (id,ty) =
  let volatile = List.mem AVolatile (attributes_of_type env ty) in
  if not volatile then
    IdentSet.add id vars
  else
    vars

let non_stack_locals_stmt env vars s =
  let decl vars loc (sto, id, ty, init) =
    let vars = match init with
      | Some init -> non_stack_locals_init vars init
      | None -> vars in
    add_vars env vars (id,ty) in
  fold_over_stmt ~expr:non_stack_locals_expr ~decl:decl
    vars s

(* Check whether an expression is safe and can be always evaluated *)

let safe_cast env tfrom tto =
  match unroll env tfrom, unroll env tto with
  | (TInt _ | TPtr _ | TArray _ | TFun _ | TEnum _),
    (TInt _ | TPtr _ | TEnum _) -> true
  | TFloat _, TFloat _ -> true
  | _, _ -> equal_types env tfrom tto

let safe_expr vars env e =
  let rec expr e =
    match e.edesc with
    | EConst _ | ESizeof _ | EAlignof _   | ECompound _  -> true
    | EVar id -> (IdentSet.mem id vars) || not (is_scalar_type env e.etyp)
    | ECast (ty, e) ->
      safe_cast env e.etyp ty && expr e
    | EUnop (op, e) ->
      unop op  e
    | EBinop (op, e1, e2, ty) ->
      binop op e1  e2
    | EConditional _  -> false
    | ECall _ -> false
  and binop op e1 e2 =
    let is_long_long_type ty =
      match unroll env ty with
      | TInt (ILongLong, _)
      | TInt (IULongLong, _) -> true
      | _ -> false in
    match op with
    | Oadd | Osub | Omul | Oand | Oor | Oxor | Oshl | Oshr ->
      expr e1 && expr e2
    | Oeq | One | Olt | Ogt | Ole | Oge ->
      let not_long_long = not (is_long_long_type e1.etyp) && not (is_long_long_type e2.etyp) in
      not_long_long && expr e1 && expr e2
    | _ -> false
  (* x.f if f has array or struct or union type *)
  and unop  op e =
    match op with
    | Ominus | Onot | Olognot | Oplus -> expr e
    | Oaddrof ->
      begin match e.edesc with
        (* skip &*e *)
        | EUnop (Oderef, e) -> expr e
        (* skip &(e.f) *)
        | EUnop (Odot f, e) -> expr e
        | _ -> expr e
      end
    (* skip *&e *)
    | Oderef ->
      begin match e.edesc with
        | EUnop (Oaddrof,e) -> expr e
        | _ -> false
      end
    (* e.f is okay if f has array or composite type *)
    | Odot m ->
      let fld = field_of_dot_access env e.etyp m in
      (is_array_type env fld.fld_typ || is_composite_type env fld.fld_typ) && expr e
    | _ -> false in
  expr e

(* Check expressions if they contain conditionals that cannot be transformed in
   linear code. The inner_cond parameter is used to mimic the translation of short
   circuit logical or and logical and as well as conditional to if statements in
   SimplExpr. *)

let rec non_linear_cond_expr inner_cond vars env loc e =
  match e.edesc with
  | EConst _ | ESizeof _ | EAlignof _ | EVar _ -> ()
  | ECast (_ , e) | EUnop (_, e)-> non_linear_cond_expr false vars env loc e
  | EBinop (op, e1, e2, ty) ->
    let inner_cond = match op with
      | Ocomma -> inner_cond
      | Ologand | Ologor -> true
      | _ -> false
    in
    non_linear_cond_expr false vars env loc e1;
    non_linear_cond_expr inner_cond vars env loc e2
  | EConditional (c, e1, e2) ->
    let can_cast = safe_cast env e1.etyp e.etyp && safe_cast env e2.etyp e.etyp in
    if not can_cast || inner_cond || not (safe_expr vars env e1) || not (safe_expr vars env e2) then
      warning loc Non_linear_cond_expr "conditional expression may not be linearized";
    non_linear_cond_expr true vars env loc e1;
    non_linear_cond_expr true vars env loc e2;
  | ECompound (ty, init) -> non_linear_cond_init vars env loc init
  | ECall (e, params) ->
    non_linear_cond_expr false vars env loc e;
    List.iter (non_linear_cond_expr false vars env loc) params

and non_linear_cond_init vars env loc init =
  iter_over_init ~expr:(non_linear_cond_expr false vars env loc) init

let non_linear_cond_stmt vars env s =
  let decl loc (sto, id, ty, init) =
    match init with
    | None -> ()
    | Some init -> non_linear_cond_init vars env loc init in
  iter_over_stmt_loc ~expr:(non_linear_cond_expr false vars env) ~decl:decl s

let non_linear_conditional p =
  if active_warning Non_linear_cond_expr && !Clflags.option_Obranchless then begin
    let fundef env loc fd =
      let vars = List.fold_left (add_vars env) IdentSet.empty fd.fd_params in
      let vars = non_stack_locals_stmt env vars fd.fd_body in
      non_linear_cond_stmt vars env fd.fd_body;
    in
    traverse_program
      ~fundef:fundef
      p
  end

(** ** Warn for ABI incompatibilities, esp. nonstandard calling conventions *)

module ABI_compat = struct

(** ABI-dependent checks for function parameters *)

type checker = {
  incompatible_argument: typ -> bool;
  add_argument: typ -> unit
}

let aarch64_macOS_checker () =
  let num_int = ref 0 in   (* number of integer arguments already seen *)
  { incompatible_argument =
      (* incompatibility for integers of size 1 or 2 passed on stack *)
      (function
        | TInt(ik, _) -> !num_int >= 8 && sizeof_ikind ik < 4
        | _ -> false);
    add_argument =
      (function
        | TInt _ | TEnum _ -> incr num_int
        | _ -> ()) }

let arm_hf_checker () =
  let num_f32 = ref 0     (* number of single FP arguments already seen *)
  and num_f64 = ref 0 in  (* number of double FP arguments already seen *)
  { incompatible_argument =
      (* incompatibility for float arguments that the ABI would pass
         in a single FP register and that CompCert passes on stack *)
      (function
        | TFloat((FFloat16|FFloat), _) -> !num_f32 + !num_f64 >= 8 && !num_f32 > 0
        | _ -> false);
    add_argument =
      (function
        | TFloat((FFloat16|FFloat), _) -> incr num_f32
        | TFloat((FDouble|FLongDouble), _) -> incr num_f64
        | _ -> ()) }

let default_checker () =
  { incompatible_argument = (fun _ -> false);
    add_argument = (fun _ -> ()) }

let argument_checker =
  match Configuration.arch, Configuration.abi with
  | "aarch64", "apple" -> aarch64_macOS_checker
  | "arm", "hardfloat" -> arm_hf_checker
  | _, _               -> default_checker

(** CompCert uses pass-by-copy-out for returning structs from functions.
    Some ABIs do the same, except for small structs, which are returned
    in registers.  The following quantity is the largest size (in bytes)
    of a struct that is not returned by copy-out. *)

let max_size_struct_return_by_value =
  match Configuration.arch, Configuration.model with
  | "arm", _ -> 4
  | "x86", "32" -> 0      (* always returned by copy-out *)
  | "powerpc", _ -> 8
  | "riscV", "32" -> 8    (* 2 * XLEN *)
  | "riscV", "64" -> 16   (* 2 * XLEN *)
  | _, _ -> max_int       (* don't know, or doesn't fit the CompCert model at all *)

(** [long double] types are compatible only if the ABI says they are represented
    like [double].  If the [-flongdouble] option is not given, an error
    will be raised in [C2C], so let's not warn.

    Likewise, if the [-fstruct-passing] option is off, we don't warn
    for structs passed by value, since an error will be raised in [C2C].
*)

let float_incompatible fk =
  fk = FLongDouble
  && !Clflags.option_flongdouble
  && sizeof_fkind FLongDouble <> sizeof_fkind FDouble

let result_type_incompatible env tres =
  match unroll env tres with
  | TFloat(fk, _) -> float_incompatible fk
  | TStruct _ | TUnion _ when !Clflags.option_fstruct_passing ->
      begin match sizeof env tres with
      | Some sz  -> sz <= max_size_struct_return_by_value
      | None -> true
      end
  | _ -> false

let argument_type_incompatible env st targ =
  st.incompatible_argument targ ||
  begin match unroll env targ with
  | TFloat(fk, _) -> float_incompatible fk
  | TStruct _ | TUnion _ -> !Clflags.option_fstruct_passing
  | _ -> false
  end

(** Recording and explaining incompatibilities *)

type incompatibility =
  | Result of typ
  | Argument of int * ident * typ

let print_incompatibilities loc incomps =
  List.iter
    (function
      | Result ty ->
          info loc "incompatible result of type %a" Cprint.typ ty
      | Argument(pos, id, ty) ->
          if id.name = "" then
            info loc "incompatible argument #%d of type %a" pos Cprint.typ ty
          else
            info loc "incompatible argument '%s' of type %a" id.name Cprint.typ ty)
    incomps

(** Check a function type.  Return a list of incompatibilities.
    This list is empty if the function is ABI compatible. *)

let check_function_type env tres targs =
  let incomp = ref [] in
  let add_incomp reason = incomp := reason :: !incomp in
  (* Check the result type *)
  if result_type_incompatible env tres then
    add_incomp (Result tres);
  (* Check the argument types *)
  let rec check_args pos st = function
    | [] -> ()
    | (id, targ) :: targs ->
        if argument_type_incompatible env st targ then
          add_incomp (Argument(pos, id, targ));
        st.add_argument (unroll env targ);
        check_args (pos + 1) st targs
  in
  begin match targs with
  | None -> ()
  | Some targs -> check_args 1 (argument_checker()) targs
  end;
  !incomp

let rec check_type env ty =
  match unroll env ty with
  | TFun(tres, targs, _, _) -> check_function_type env tres targs
  | TPtr(t, _) -> check_type env t
  | _ -> []

(** Traversal of an expression, with special treatment for variables
    and for calls to known functions. *)

let iter_over_expr ~(var : ident -> typ -> unit)
                   ~(call: ident -> typ -> unit) : exp -> unit =
  let rec iter e =
    match e.edesc with
    | EConst _ | ESizeof _ | EAlignof _ -> ()
    | EVar id -> var id e.etyp
    | EUnop(op, e1) -> iter e1
    | EBinop(op, e1, e2, ty) -> iter e1; iter e2
    | EConditional(e1, e2, e3) -> iter e1; iter e2; iter e3
    | ECast(ty, e1) -> iter e1
    | ECall(e1, el) ->
        begin match e1.edesc with
        | EVar id -> call id e1.etyp
        | _ -> iter e1
        end;
        List.iter iter el
    | ECompound(ty, il) ->
        iter_over_init ~expr:iter il
  in iter

(** Check the functions used in an expression *)

let check_expr defined_in_compunit env loc e =
  let var id ty =
    let incomps = check_type env ty in
    if incomps <> [] then begin
      warning loc ABI_conformance "ABI incompatibility. The function '%s' can only be called from CompCert-compiled code." id.name;
      print_incompatibilities loc incomps
    end
  and call id ty =
    if not (IdentSet.mem id defined_in_compunit) then begin
      let incomps = check_type env ty in
      if incomps <> [] then begin
        warning loc ABI_conformance "ABI incompatibility if the called function '%s' is not compiled by CompCert." id.name;
        print_incompatibilities loc incomps
      end
   end in
  iter_over_expr ~var ~call e

let check_decl defined_in_compunit env loc d =
  iter_over_decl ~expr:(check_expr defined_in_compunit env loc) loc d

(** Check a function definition *)

let check_fundef defined_in_compunit env loc f =
  let incomps = check_function_type env f.fd_ret (Some f.fd_params) in
  if incomps <> [] then begin
    warning loc ABI_conformance "ABI incompatibility. The function '%s' can only be called from CompCert-compiled code." f.fd_name.name;
    print_incompatibilities loc incomps
  end;
  iter_over_stmt_loc
    ~expr: (check_expr defined_in_compunit env)
    ~decl: (check_decl defined_in_compunit env)
    f.fd_body

(** Check a program *)

let check_program p =
  let defined_in_compunit =
    List.fold_left
      (fun def g ->
        match g.gdesc with
        | Gfundef f -> IdentSet.add f.fd_name def
        | _ -> def)
      IdentSet.empty p in
  traverse_program ~fundef:(check_fundef defined_in_compunit) p

end

let abi_conformance p =
  if active_warning ABI_conformance then ABI_compat.check_program p


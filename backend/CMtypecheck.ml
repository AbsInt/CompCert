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

(* A type-checker for Cminor *)

open Printf
open Datatypes
open Camlcoq
open AST
open Integers
open Cminor

exception Error of string

let name_of_typ = function Tint -> "int" | Tfloat -> "float"

type ty = Base of typ | Var of ty option ref

let newvar () = Var (ref None)
let tint = Base Tint
let tfloat = Base Tfloat

let ty_of_typ = function Tint -> tint | Tfloat -> tfloat

let ty_of_sig_args tyl = List.map ty_of_typ tyl

let rec repr t =
  match t with
  | Base _ -> t
  | Var r -> match !r with None -> t | Some t' -> repr t'

let unify t1 t2 =
  match (repr t1, repr t2) with
  | Base b1, Base b2 ->
      if b1 <> b2 then
        raise (Error (sprintf "Expected type %s, actual type %s\n"
                              (name_of_typ b1) (name_of_typ b2)))
  | Base b, Var r -> r := Some (Base b)
  | Var r, Base b -> r := Some (Base b)
  | Var r1, Var r2 -> r1 := Some (Var r2)

let unify_list l1 l2 =
  let ll1 = List.length l1 and ll2 = List.length l2 in
  if ll1 <> ll2 then
    raise (Error (sprintf "Arity mismatch: expected %d, actual %d\n" ll1 ll2));
  List.iter2 unify l1 l2

let type_var env id =
  try
    List.assoc id env
  with Not_found ->
    raise (Error (sprintf "Unbound variable %s\n" (extern_atom id)))

let type_letvar env n =
  let n = camlint_of_nat n in
  try
    List.nth env n
  with Not_found ->
    raise (Error (sprintf "Unbound let variable #%d\n" n))

let name_of_comparison = function
  | Ceq -> "eq"
  | Cne -> "ne"
  | Clt -> "lt"
  | Cle -> "le"
  | Cgt -> "gt"
  | Cge -> "ge"

let type_constant = function
  | Ointconst _ -> tint
  | Ofloatconst _ -> tfloat
  | Oaddrsymbol _ -> tint
  | Oaddrstack _ -> tint

let type_unary_operation = function
  | Ocast8signed -> tint, tint
  | Ocast16signed -> tint, tint
  | Ocast8unsigned -> tint, tint
  | Ocast16unsigned -> tint, tint
  | Onegint -> tint, tint
  | Oboolval -> tint, tint
  | Onotbool -> tint, tint
  | Onotint -> tint, tint
  | Onegf -> tfloat, tfloat
  | Oabsf -> tfloat, tfloat
  | Osingleoffloat -> tfloat, tfloat
  | Ointoffloat -> tfloat, tint
  | Ointuoffloat -> tfloat, tint
  | Ofloatofint -> tint, tfloat
  | Ofloatofintu -> tint, tfloat

let type_binary_operation = function
  | Oadd -> tint, tint, tint
  | Osub -> tint, tint, tint
  | Omul -> tint, tint, tint
  | Odiv -> tint, tint, tint
  | Odivu -> tint, tint, tint
  | Omod -> tint, tint, tint
  | Omodu -> tint, tint, tint
  | Oand -> tint, tint, tint
  | Oor -> tint, tint, tint
  | Oxor -> tint, tint, tint
  | Oshl -> tint, tint, tint
  | Oshr -> tint, tint, tint
  | Oshru -> tint, tint, tint
  | Oaddf -> tfloat, tfloat, tfloat
  | Osubf -> tfloat, tfloat, tfloat
  | Omulf -> tfloat, tfloat, tfloat
  | Odivf -> tfloat, tfloat, tfloat
  | Ocmp _ -> tint, tint, tint
  | Ocmpu _ -> tint, tint, tint
  | Ocmpf _ -> tfloat, tfloat, tint

let name_of_constant = function
  | Ointconst n -> sprintf "intconst %ld" (camlint_of_coqint n)
  | Ofloatconst n -> sprintf "floatconst %g" (camlfloat_of_coqfloat n)
  | Oaddrsymbol (s, ofs) -> sprintf "addrsymbol %s %ld" (extern_atom s) (camlint_of_coqint ofs)
  | Oaddrstack n -> sprintf "addrstack %ld" (camlint_of_coqint n)

let name_of_unary_operation = function
  | Ocast8signed -> "cast8signed"
  | Ocast16signed -> "cast16signed"
  | Ocast8unsigned -> "cast8unsigned"
  | Ocast16unsigned -> "cast16unsigned"
  | Onegint -> "negint"
  | Oboolval -> "notbool"
  | Onotbool -> "notbool"
  | Onotint -> "notint"
  | Onegf -> "negf"
  | Oabsf -> "absf"
  | Osingleoffloat -> "singleoffloat"
  | Ointoffloat -> "intoffloat"
  | Ointuoffloat -> "intuoffloat"
  | Ofloatofint -> "floatofint"
  | Ofloatofintu -> "floatofintu"

let name_of_binary_operation = function
  | Oadd -> "add"
  | Osub -> "sub"
  | Omul -> "mul"
  | Odiv -> "div"
  | Odivu -> "divu"
  | Omod -> "mod"
  | Omodu -> "modu"
  | Oand -> "and"
  | Oor -> "or"
  | Oxor -> "xor"
  | Oshl -> "shl"
  | Oshr -> "shr"
  | Oshru -> "shru"
  | Oaddf -> "addf"
  | Osubf -> "subf"
  | Omulf -> "mulf"
  | Odivf -> "divf"
  | Ocmp c -> sprintf "cmp %s" (name_of_comparison c)
  | Ocmpu c -> sprintf "cmpu %s" (name_of_comparison c)
  | Ocmpf c -> sprintf "cmpf %s" (name_of_comparison c)

let type_chunk = function
  | Mint8signed -> tint
  | Mint8unsigned -> tint
  | Mint16signed -> tint
  | Mint16unsigned -> tint
  | Mint32 -> tint
  | Mfloat32 -> tfloat
  | Mfloat64 -> tfloat

let name_of_chunk = function
  | Mint8signed -> "int8signed"
  | Mint8unsigned -> "int8unsigned"
  | Mint16signed -> "int16signed"
  | Mint16unsigned -> "int16unsigned"
  | Mint32 -> "int32"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"

let rec type_expr env lenv e =
  match e with
  | Evar id ->
      type_var env id
  | Econst cst ->
      type_constant cst
  | Eunop(op, e1) ->
      let te1 = type_expr env lenv e1 in
      let (targ, tres) = type_unary_operation op in
      begin try
        unify targ te1
      with Error s ->
        raise (Error (sprintf "In application of operator %s:\n%s"
                              (name_of_unary_operation op) s))
      end;
      tres
  | Ebinop(op, e1, e2) ->
      let te1 = type_expr env lenv e1 in
      let te2 = type_expr env lenv e2 in
      let (targ1, targ2, tres) = type_binary_operation op in
      begin try
        unify targ1 te1; unify targ2 te2
      with Error s ->
        raise (Error (sprintf "In application of operator %s:\n%s"
                              (name_of_binary_operation op) s))
      end;
      tres
  | Eload(chunk, e) ->
      let te = type_expr env lenv e in
      begin try
        unify tint te
      with Error s ->
        raise (Error (sprintf "In load %s:\n%s"
                              (name_of_chunk chunk) s))
      end;
      type_chunk chunk
  | Econdition(e1, e2, e3) ->
      type_condexpr env lenv e1;
      let te2 = type_expr env lenv e2 in
      let te3 = type_expr env lenv e3 in
      begin try
        unify te2 te3
      with Error s ->
        raise (Error (sprintf "In conditional expression:\n%s" s))
      end;
      te2
(*
  | Elet(e1, e2) ->
      let te1 = type_expr env lenv e1 in
      let te2 = type_expr env (te1 :: lenv) e2 in
      te2
  | Eletvar n ->
      type_letvar lenv n
*)

and type_exprlist env lenv el =
  match el with
  | [] -> []
  | e1 :: et ->
      let te1 = type_expr env lenv e1 in
      let tet = type_exprlist env lenv et in
      (te1 :: tet)

and type_condexpr env lenv e =
  let te = type_expr env lenv e in
  begin try
    unify tint te
  with Error s ->
    raise (Error (sprintf "In condition:\n%s" s))
  end

let rec type_stmt env blk ret s =
  match s with
  | Sskip -> ()
  | Sassign(id, e1) ->
      let tid = type_var env id in
      let te1 = type_expr env [] e1 in
      begin try
        unify tid te1
      with Error s ->
        raise (Error (sprintf "In assignment to %s:\n%s" (extern_atom id) s))
      end
  | Sstore(chunk, e1, e2) ->
      let te1 = type_expr env [] e1 in
      let te2 = type_expr env [] e2 in
      begin try
        unify tint te1;
        unify (type_chunk chunk) te2
      with Error s ->
        raise (Error (sprintf "In store %s:\n%s"
                              (name_of_chunk chunk) s))
      end
  | Scall(optid, sg, e1, el) ->
      let te1 = type_expr env [] e1 in
      let tel = type_exprlist env [] el in
      begin try
        unify tint te1;
        unify_list (ty_of_sig_args sg.sig_args) tel;
        let ty_res =
          match sg.sig_res with
          | None -> tint (*???*)
          | Some t -> ty_of_typ t in
        begin match optid with
        | None -> ()
        | Some id -> unify (type_var env id) ty_res
        end
      with Error s ->
        raise (Error (sprintf "In call:\n%s" s))
      end
  | Sbuiltin(optid, ef, el) ->
      let sg = ef_sig ef in
      let tel = type_exprlist env [] el in
      begin try
        unify_list (ty_of_sig_args sg.sig_args) tel;
        let ty_res =
          match sg.sig_res with
          | None -> tint (*???*)
          | Some t -> ty_of_typ t in
        begin match optid with
        | None -> ()
        | Some id -> unify (type_var env id) ty_res
        end
      with Error s ->
        raise (Error (sprintf "In builtin call:\n%s" s))
      end
  | Sseq(s1, s2) ->
      type_stmt env blk ret s1;
      type_stmt env blk ret s2
  | Sifthenelse(ce, s1, s2) ->
      type_condexpr env [] ce;
      type_stmt env blk ret s1;
      type_stmt env blk ret s2
  | Sloop s1 ->
      type_stmt env blk ret s1
  | Sblock s1 ->
      type_stmt env (blk + 1) ret s1
  | Sexit n ->
      if camlint_of_nat n >= blk then
        raise (Error (sprintf "Bad exit(%d)\n" (camlint_of_nat n)))
  | Sswitch(e, cases, deflt) ->
      unify (type_expr env [] e) tint
  | Sreturn None ->
      begin match ret with
      | None -> ()
      | Some tret -> raise (Error ("return without argument"))
      end
  | Sreturn (Some e) ->
      begin match ret with
      | None -> raise (Error "return with argument")
      | Some tret -> 
          begin try
            unify (type_expr env [] e) (ty_of_typ tret)
          with Error s ->
            raise (Error (sprintf "In return:\n%s" s))
          end
      end
  | Stailcall(sg, e1, el) ->
      let te1 = type_expr env [] e1 in
      let tel = type_exprlist env [] el in
      begin try
        unify tint te1;
        unify_list (ty_of_sig_args sg.sig_args) tel
      with Error s ->
        raise (Error (sprintf "In tail call:\n%s" s))
      end
  | Slabel(lbl, s1) ->
      type_stmt env blk ret s1
  | Sgoto lbl ->
      ()

let rec env_of_vars idl =
  match idl with
  | [] -> []
  | id1 :: idt -> (id1, newvar()) :: env_of_vars idt

let type_function id f =
  try
    type_stmt
       (env_of_vars f.fn_vars @ env_of_vars f.fn_params)
       0 f.fn_sig.sig_res f.fn_body
  with Error s ->
    raise (Error (sprintf "In function %s:\n%s" (extern_atom id) s))

let type_fundef (id, fd) =
  match fd with
  | Internal f -> type_function id f
  | External ef -> ()

let type_program p =
  List.iter type_fundef p.prog_funct; p

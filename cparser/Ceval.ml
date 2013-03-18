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

(* Evaluation of compile-time constants *)

open C
open Cutil
open Machine

(* Extra arith on int64 *)

(* Unsigned comparison: do signed comparison after shifting range *)

let int64_unsigned_compare x y =
  Int64.compare (Int64.add x Int64.min_int) (Int64.add y Int64.min_int)

(* Unsigned division and modulus: synthesized from signed division
   as described in "Hacker's Delight", section 9.3. *)

let int64_unsigned_div n d =
  if d < 0L then
    if int64_unsigned_compare n d < 0 then 0L else 1L
  else begin
    let q = Int64.shift_left (Int64.div (Int64.shift_right_logical n 1) d) 1 in
    let r = Int64.sub n (Int64.mul q d) in
    if int64_unsigned_compare r d >= 0 then Int64.succ q else q
  end

let int64_unsigned_mod n d =
  if d < 0L then
    if int64_unsigned_compare n d < 0 then n else Int64.sub n d
  else begin
    let q = Int64.shift_left (Int64.div (Int64.shift_right_logical n 1) d) 1 in
    let r = Int64.sub n (Int64.mul q d) in
    if int64_unsigned_compare r d >= 0 then Int64.sub r d else r
  end

exception Notconst

(* Reduce n to the range of representable integers of the given kind *)

let normalize_int n ik =
  if ik = IBool then
    if n = 0L then 0L else 1L
  else begin
    let bitsize = sizeof_ikind ik * 8
    and signed = is_signed_ikind ik in
    if bitsize >= 64 then n else begin
      let a = 64 - bitsize in
      let p = Int64.shift_left n a in
      if signed
      then Int64.shift_right p a
      else Int64.shift_right_logical p a
    end
  end

(* Reduce n to the range of representable floats of the given kind *)

type value =
  | I of int64
  | S of string
  | WS of int64 list

let boolean_value v =
  match v with
  | I n -> n <> 0L
  | S _ | WS _ -> true

let constant = function
  | CInt(v, ik, _) -> I (normalize_int v ik)
  | CFloat(v, fk) -> raise Notconst
  | CStr s -> S s
  | CWStr s -> WS s
  | CEnum(id, v) -> I v

let is_signed env ty =
  match unroll env ty with
  | TInt(ik, _) -> is_signed_ikind ik
  | TEnum(_, _) -> is_signed_ikind enum_ikind
  | _ -> false

let cast env ty_to ty_from v =
  match unroll env ty_to, v with
  | TInt(IBool, _), _ ->
      if boolean_value v then I 1L else I 0L
  | TInt(ik, _), I n ->
      I(normalize_int n ik)
  | TInt(ik, _), (S _ | WS _) ->
      if sizeof_ikind ik >= !config.sizeof_ptr
      then v
      else raise Notconst
  | TPtr(ty, _), I n ->
      I (normalize_int n ptr_t_ikind)
  | TPtr(ty, _), (S _ | WS _) ->
      v
  | TEnum(_, _), I n ->
      I (normalize_int n enum_ikind)
  | _, _ ->
      raise Notconst

let unop env op tyres ty v =
  let res =
   match op, tyres, v with
   | Ominus, TInt _, I n -> I (Int64.neg n)
   | Oplus, TInt _, I n -> I n
   | Olognot, _, _ -> if boolean_value v then I 0L else I 1L
   | Onot, _, I n -> I (Int64.lognot n)
   | _ -> raise Notconst
  in cast env ty tyres res

let comparison env direction ptraction tyop ty1 v1 ty2 v2 =
  (* tyop = type at which the comparison is done *)
  let b =
    match cast env tyop ty1 v1, cast env tyop ty2 v2 with
    | I n1, I n2 -> 
        if is_signed env tyop
        then direction (compare n1 n2) 0
        else direction (int64_unsigned_compare n1 n2) 0 (* including pointers *)
    | (S _ | WS _), I 0L ->
        begin match ptraction with None -> raise Notconst | Some b -> b end
    | I 0L, (S _ | WS _) ->
        begin match ptraction with None -> raise Notconst | Some b -> b end
    | _, _ ->
        raise Notconst
  in if b then I 1L else I 0L

let binop env op tyop tyres ty1 v1 ty2 v2 =
  (* tyop = type at which the computation is done
     tyres = expected result type *)
  let res =
    match op with
    | Oadd ->
        if is_arith_type env ty1 && is_arith_type env ty2 then begin
          match cast env tyop ty1 v1, cast env tyop ty2 v2 with
          | I n1, I n2 -> I (Int64.add n1 n2)
          | _, _ -> raise Notconst
        end else
          raise Notconst
    | Osub ->
        if is_arith_type env ty1 && is_arith_type env ty2 then begin
          match cast env tyop ty1 v1, cast env tyop ty2 v2 with
          | I n1, I n2 -> I (Int64.sub n1 n2)
          | _, _ -> raise Notconst
        end else
          raise Notconst
    | Omul ->
        begin match cast env tyop ty1 v1, cast env tyop ty2 v2 with
          | I n1, I n2 -> I (Int64.mul n1 n2)
          | _, _ -> raise Notconst
        end
    | Odiv ->
        begin match cast env tyop ty1 v1, cast env tyop ty2 v2 with
          | I n1, I n2 -> 
              if n2 = 0L then raise Notconst else
              if is_signed env tyop then I (Int64.div n1 n2)
              else I (int64_unsigned_div n1 n2)
          | _, _ -> raise Notconst
        end
    | Omod ->
        begin match v1, v2 with
          | I n1, I n2 -> 
              if n2 = 0L then raise Notconst else
              if is_signed env tyop then I (Int64.rem n1 n2)
              else I (int64_unsigned_mod n1 n2)
          | _, _ -> raise Notconst
        end
    | Oand ->
        begin match v1, v2 with
          | I n1, I n2 -> I (Int64.logand n1 n2)
          | _, _ -> raise Notconst
        end
    | Oor ->
        begin match v1, v2 with
          | I n1, I n2 -> I (Int64.logor n1 n2)
          | _, _ -> raise Notconst
        end
    | Oxor ->
        begin match v1, v2 with
          | I n1, I n2 -> I (Int64.logxor n1 n2)
          | _, _ -> raise Notconst
        end
    | Oshl ->
        begin match v1, v2 with
          | I n1, I n2 when n2 >= 0L && n2 < 64L ->
               I (Int64.shift_left n1 (Int64.to_int n2))
          | _, _ -> raise Notconst
        end
    | Oshr ->
        begin match v1, v2 with
          | I n1, I n2 when n2 >= 0L && n2 < 64L ->
              if is_signed env tyop
              then I (Int64.shift_right n1 (Int64.to_int n2))
              else I (Int64.shift_right_logical n1 (Int64.to_int n2))
          | _, _ -> raise Notconst
        end
    | Oeq ->
        comparison env (=) (Some false) tyop ty1 v1 ty2 v2
    | One ->
        comparison env (<>) (Some true) tyop ty1 v1 ty2 v2
    | Olt ->
        comparison env (<) None tyop ty1 v1 ty2 v2
    | Ogt ->
        comparison env (>) None tyop ty1 v1 ty2 v2
    | Ole ->
        comparison env (<=) None tyop ty1 v1 ty2 v2
    | Oge ->
        comparison env (>=) None tyop ty1 v1 ty2 v2
    | Ocomma ->
        v2
    | Ologand ->
        if boolean_value v1 
        then if boolean_value v2 then I 1L else I 0L
        else I 0L
    | Ologor ->
        if boolean_value v1 
        then I 1L
        else if boolean_value v2 then I 1L else I 0L
    | _ -> raise Notconst
  (* force normalization of result, e.g. of double to float *)
  in cast env tyres tyres res

let rec expr env e =
  match e.edesc with
  | EConst c ->
      constant c
  | ESizeof ty ->
      begin match sizeof env ty with
      | None -> raise Notconst
      | Some n -> I(Int64.of_int n)
      end
  | EAlignof ty ->
      begin match alignof env ty with
      | None -> raise Notconst
      | Some n -> I(Int64.of_int n)
      end
  | EVar _ ->
      raise Notconst
  | EUnop(op, e1) ->
      unop env op e.etyp e1.etyp (expr env e1)
  | EBinop(op, e1, e2, ty) ->
      binop env op ty e.etyp e1.etyp (expr env e1) e2.etyp (expr env e2)
  | EConditional(e1, e2, e3) ->
      if boolean_value (expr env e1)
      then cast env e.etyp e2.etyp (expr env e2)
      else cast env e.etyp e3.etyp (expr env e3)
  (* | ECast(TInt (_, _), EConst (CFloat (_, _))) -> TODO *)
  | ECast(ty, e1) ->
      cast env ty e1.etyp (expr env e1)
  | ECall _ ->
      raise Notconst

let integer_expr env e =
  try
    match cast env (TInt(ILongLong, [])) e.etyp (expr env e) with
    | I n -> Some n
    | _   -> None
  with Notconst -> None

let constant_expr env ty e =
  try
    match unroll env ty, cast env ty e.etyp (expr env e) with
    | TInt(ik, _), I n -> Some(CInt(n, ik, ""))
    | TPtr(_, _), I 0L -> Some(CInt(0L, IInt, ""))
    | TPtr(_, _), S s -> Some(CStr s)
    | TPtr(_, _), WS s -> Some(CWStr s)
    | TEnum(_, _), I n -> Some(CInt(n, enum_ikind, ""))
    | _   -> None
  with Notconst -> None

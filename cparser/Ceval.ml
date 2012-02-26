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

external int64_unsigned_to_float: int64 -> float 
  = "cparser_int64_unsigned_to_float"
external int64_unsigned_div: int64 -> int64 -> int64
  = "cparser_int64_unsigned_div"
external int64_unsigned_mod: int64 -> int64 -> int64
  = "cparser_int64_unsigned_mod"
external int64_unsigned_compare: int64 -> int64 -> int
  = "cparser_int64_unsigned_compare"

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

let normalize_float f fk =
  match fk with
  | FFloat -> Int32.float_of_bits (Int32.bits_of_float f)
  | FDouble -> f
  | FLongDouble -> raise Notconst (* cannot accurately compute on this type *)

type value =
  | I of int64
  | F of float
  | S of string
  | WS of int64 list

let boolean_value v =
  match v with
  | I n -> n <> 0L
  | F n -> n <> 0.0
  | S _ | WS _ -> true

let constant = function
  | CInt(v, ik, _) -> I (normalize_int v ik)
  | CFloat(v, fk, _) -> F (normalize_float v fk)
  | CStr s -> S s
  | CWStr s -> WS s
  | CEnum(id, v) -> I v

let is_signed env ty =
  match unroll env ty with
  | TInt(ik, _) -> is_signed_ikind ik
  | _ -> false

let cast env ty_to ty_from v =
  match unroll env ty_to, v with
  | TInt(IBool, _), _ ->
      if boolean_value v then I 1L else I 0L
  | TInt(ik, _), I n ->
      I(normalize_int n ik)
  | TInt(ik, _), F n ->
      I(normalize_int (Int64.of_float n) ik)
  | TInt(ik, _), (S _ | WS _) ->
      if sizeof_ikind ik >= !config.sizeof_ptr
      then v
      else raise Notconst
  | TFloat(fk, _), F n ->
      F(normalize_float n fk)
  | TFloat(fk, _), I n ->
      if is_signed env ty_from
      then F(normalize_float (Int64.to_float n) fk)
      else F(normalize_float (int64_unsigned_to_float n) fk)
  | TPtr(ty, _), I n ->
      I (normalize_int n ptr_t_ikind)
  | TPtr(ty, _), F n ->
      if n = 0.0 then I 0L else raise Notconst
  | TPtr(ty, _), (S _ | WS _) ->
      v
  | _, _ ->
      raise Notconst

let unop env op tyres ty v =
  let res =
   match op, tyres, v with
   | Ominus, TInt _, I n -> I (Int64.neg n)
   | Ominus, TFloat _, F n -> F (-. n)
   | Oplus, TInt _, I n -> I n
   | Oplus, TFloat _, F n -> F n
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
    | F n1, F n2 ->
        direction (compare n1 n2) 0
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
          | F n1, F n2 -> F (n1 +. n2)
          | _, _ -> raise Notconst
        end else
          raise Notconst
    | Osub ->
        if is_arith_type env ty1 && is_arith_type env ty2 then begin
          match cast env tyop ty1 v1, cast env tyop ty2 v2 with
          | I n1, I n2 -> I (Int64.sub n1 n2)
          | F n1, F n2 -> F (n1 -. n2)
          | _, _ -> raise Notconst
        end else
          raise Notconst
    | Omul ->
        begin match cast env tyop ty1 v1, cast env tyop ty2 v2 with
          | I n1, I n2 -> I (Int64.mul n1 n2)
          | F n1, F n2 -> F (n1 *. n2)
          | _, _ -> raise Notconst
        end
    | Odiv ->
        begin match cast env tyop ty1 v1, cast env tyop ty2 v2 with
          | I n1, I n2 -> 
              if n2 = 0L then raise Notconst else
              if is_signed env tyop then I (Int64.div n1 n2)
              else I (int64_unsigned_div n1 n2)
          | F n1, F n2 -> F (n1 /. n2)
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
    | TFloat(fk, _), F n -> Some(CFloat(n, fk, ""))
    | TPtr(_, _), I 0L -> Some(CInt(0L, IInt, ""))
    | TPtr(_, _), S s -> Some(CStr s)
    | TPtr(_, _), WS s -> Some(CWStr s)
    | _   -> None
  with Notconst -> None

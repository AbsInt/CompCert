(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition of combined operations, addressing modes and conditions
  during the [CSE] phase. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import CSEdomain.

Section COMBINE.

Variable get: valnum -> option rhs.

Function combine_compimm_ne_0 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (c, ys)
  | Some(Op (Oandimm n) ys) => Some (Cmasknotzero n, ys)
  | Some(Op (Oxorimm n) ys) =>
      if Int.eq n (Int.sign_ext 16 n) then Some (Ccompimm Cne n, ys) else None
  | _ => None
  end.

Function combine_compimm_eq_0 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (negate_condition c, ys)
  | Some(Op (Oandimm n) ys) => Some (Cmaskzero n, ys)
  | Some(Op (Oxorimm n) ys) =>
      if Int.eq n (Int.sign_ext 16 n) then Some (Ccompimm Ceq n, ys) else None
  | _ => None
  end.

Function combine_compimm_eq_1 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (c, ys)
  | _ => None
  end.

Function combine_compimm_ne_1 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (negate_condition c, ys)
  | _ => None
  end.

Function combine_cond (cond: condition) (args: list valnum) : option(condition * list valnum) :=
  match cond, args with
  | Ccompimm Cne n, x::nil =>
      if Int.eq_dec n Int.zero then combine_compimm_ne_0 x
      else if Int.eq_dec n Int.one then combine_compimm_ne_1 x
      else None
  | Ccompimm Ceq n, x::nil =>
      if Int.eq_dec n Int.zero then combine_compimm_eq_0 x
      else if Int.eq_dec n Int.one then combine_compimm_eq_1 x
      else None
  | Ccompuimm Cne n, x::nil =>
      if Int.eq_dec n Int.zero then combine_compimm_ne_0 x
      else if Int.eq_dec n Int.one then combine_compimm_ne_1 x
      else None
  | Ccompuimm Ceq n, x::nil =>
      if Int.eq_dec n Int.zero then combine_compimm_eq_0 x
      else if Int.eq_dec n Int.one then combine_compimm_eq_1 x
      else None
  | _, _ => None
  end.

Definition combine_cond' (cond: condition) (args: list valnum) : option bool :=
  match cond, args with
  | (Ccomp c | Ccompu c), x :: y :: nil => combine_comparison c x y
  | _, _ => None
  end.

Function combine_addr (addr: addressing) (args: list valnum) : option(addressing * list valnum) :=
  match addr, args with
  | Aindexed n, x::nil =>
      match get x with
      | Some(Op (Oaddimm m) ys) => Some(Aindexed (Int.add m n), ys)
      | _ => None
      end
  | _, _ => None
  end.

Function combine_op (op: operation) (args: list valnum) : option(operation * list valnum) :=
  match op, args with
  | Oaddimm n, x :: nil =>
      match get x with
      | Some(Op (Oaddimm m) ys) => Some(Oaddimm (Int.add m n), ys)
      | Some(Op (Osubimm m) ys) => Some(Osubimm (Int.add m n), ys)
      | _ => None
      end
  | Osubimm n, x :: nil =>
      match get x with
      | Some(Op (Oaddimm m) ys) => Some(Osubimm (Int.sub n m), ys)
      | _ => None
      end
  | Oandimm n, x :: nil =>
      match get x with
      | Some(Op (Oandimm m) ys) =>
          Some(let p := Int.and m n in
               if Int.eq p m then (Omove, x :: nil) else (Oandimm p, ys))
      | Some(Op (Orolm amount m) ys) =>
          Some(let p := Int.and m n in
               if Int.eq p m then (Omove, x :: nil) else (Orolm amount p, ys))
      | _ => None
      end
  | Oorimm n, x :: nil =>
      match get x with
      | Some(Op (Oorimm m) ys) => Some(Oorimm (Int.or m n), ys)
      | _ => None
      end
  | Oxorimm n, x :: nil =>
      match get x with
      | Some(Op (Oxorimm m) ys) => Some(Oxorimm (Int.xor m n), ys)
      | _ => None
      end
  | Orolm amount2 mask2, x :: nil =>
      match get x with
      | Some(Op (Oandimm mask1) ys) =>
           Some(Orolm (Int.modu amount2 Int.iwordsize)
                     (Int.and (Int.rol mask1 amount2) mask2), ys)
      | Some(Op (Orolm amount1 mask1) ys) =>
           Some(Orolm (Int.modu (Int.add amount1 amount2) Int.iwordsize)
                     (Int.and (Int.rol mask1 amount2) mask2), ys)
      | _ => None
      end
  | Ocmp cond, _ =>
      match combine_cond' cond args with
      | Some b => Some ((if b then Ointconst Int.one else Ointconst Int.zero), nil)
      | None =>
          match combine_cond cond args with
          | Some(cond', args') => Some(Ocmp cond', args')
          | None => None
          end
      end
  | Osel cond ty, x :: y :: args =>
      match combine_cond' cond args with
      | Some b => Some (Omove, (if b then x else y) :: nil)
      | None =>
          if eq_valnum x y then Some (Omove, x :: nil) else
          match combine_cond cond args with
          | Some (cond', args') => Some (Osel cond' ty, x :: y :: args')
          | None => None
          end
      end
  | _, _ => None
  end.

End COMBINE.

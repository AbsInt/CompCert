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
Require SelectOp.

Definition valnum := positive.

Inductive rhs : Type :=
  | Op: operation -> list valnum -> rhs
  | Load: memory_chunk -> addressing -> list valnum -> rhs.

Section COMBINE.

Variable get: valnum -> option rhs.

Function combine_compimm_ne_0 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (c, ys)
  | Some(Op (Oandimm n) ys) => Some (Cmasknotzero n, ys)
  | _ => None
  end.

Function combine_compimm_eq_0 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (negate_condition c, ys)
  | Some(Op (Oandimm n) ys) => Some (Cmaskzero n, ys)
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

Function combine_addr (addr: addressing) (args: list valnum) : option(addressing * list valnum) :=
  match addr, args with
  | Aindexed n, x::nil =>
      match get x with
      | Some(Op (Olea a) ys) => Some(SelectOp.offset_addressing a n, ys)
      | _ => None
      end
  | _, _ => None
  end.

Function combine_op (op: operation) (args: list valnum) : option(operation * list valnum) :=
  match op, args with
  | Olea addr, _ =>
      match combine_addr addr args with
      | Some(addr', args') => Some(Olea addr', args')
      | None => None
      end
  | Ocmp cond, _ =>
      match combine_cond cond args with
      | Some(cond', args') => Some(Ocmp cond', args')
      | None => None
      end
  | _, _ => None
  end.

End COMBINE.



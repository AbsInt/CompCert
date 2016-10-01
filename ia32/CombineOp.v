(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition of combined operations, addressing modes and conditions
  during the [CSE] phase. *)

Require Import Coqlib.
Require Import AST Integers.
Require Import Op CSEdomain.

Definition valnum := positive.

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

Function combine_addr_32 (addr: addressing) (args: list valnum) : option(addressing * list valnum) :=
  match addr, args with
  | Aindexed n, x::nil =>
      match get x with
      | Some(Op (Olea a) ys) =>
          match offset_addressing a n with Some a' => Some (a', ys) | None => None end
      | _ => None
      end
  | _, _ => None
  end.

Function combine_addr_64 (addr: addressing) (args: list valnum) : option(addressing * list valnum) :=
  match addr, args with
  | Aindexed n, x::nil =>
      match get x with
      | Some(Op (Oleal a) ys) =>
          match offset_addressing a n with Some a' => Some (a', ys) | None => None end
      | _ => None
      end
  | _, _ => None
  end.

Definition combine_addr (addr: addressing) (args: list valnum) : option(addressing * list valnum) :=
  if Archi.ptr64 then combine_addr_64 addr args else combine_addr_32 addr args.

Function combine_op (op: operation) (args: list valnum) : option(operation * list valnum) :=
  match op, args with
  | Olea addr, _ =>
      match combine_addr_32 addr args with
      | Some(addr', args') => Some(Olea addr', args')
      | None => None
      end
  | Oleal addr, _ =>
      match combine_addr_64 addr args with
      | Some(addr', args') => Some(Oleal addr', args')
      | None => None
      end
  | Oandimm n, x :: nil =>
      match get x with
      | Some(Op (Oandimm m) ys) => Some(Oandimm (Int.and m n), ys)
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
  | Oandlimm n, x :: nil =>
      match get x with
      | Some(Op (Oandlimm m) ys) => Some(Oandlimm (Int64.and m n), ys)
      | _ => None
      end
  | Oorlimm n, x :: nil =>
      match get x with
      | Some(Op (Oorlimm m) ys) => Some(Oorlimm (Int64.or m n), ys)
      | _ => None
      end
  | Oxorlimm n, x :: nil =>
      match get x with
      | Some(Op (Oxorlimm m) ys) => Some(Oxorlimm (Int64.xor m n), ys)
      | _ => None
      end
  | Ocmp cond, _ =>
      match combine_cond cond args with
      | Some(cond', args') => Some(Ocmp cond', args')
      | None => None
      end
  | _, _ => None
  end.

End COMBINE.



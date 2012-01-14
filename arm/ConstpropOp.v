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

(** Static analysis and strength reduction for operators 
  and conditions.  This is the machine-dependent part of [Constprop]. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Op.
Require Import Registers.

(** * Static analysis *)

(** To each pseudo-register at each program point, the static analysis 
  associates a compile-time approximation taken from the following set. *)

Inductive approx : Type :=
  | Novalue: approx      (** No value possible, code is unreachable. *)
  | Unknown: approx      (** All values are possible,
                             no compile-time information is available. *)
  | I: int -> approx     (** A known integer value. *)
  | F: float -> approx   (** A known floating-point value. *)
  | G: ident -> int -> approx
                         (** The value is the address of the given global
                             symbol plus the given integer offset. *)
  | S: int -> approx.    (** The value is the stack pointer plus the offset. *)


(** We now define the abstract interpretations of conditions and operators
  over this set of approximations.  For instance, the abstract interpretation
  of the operator [Oaddf] applied to two expressions [a] and [b] is
  [F(Float.add f g)] if [a] and [b] have static approximations [F f]
  and [F g] respectively, and [Unknown] otherwise.

  The static approximations are defined by large pattern-matchings over
  the approximations of the results.  We write these matchings in the
  indirect style described in file [SelectOp] to avoid excessive
  duplication of cases in proofs. *)

Definition eval_static_shift (s: shift) (n: int) : int :=
  match s with
  | Slsl x => Int.shl n x
  | Slsr x => Int.shru n x
  | Sasr x => Int.shr n x
  | Sror x => Int.ror n x
  end.

(** Original definition:
<<
Nondetfunction eval_static_condition (cond: condition) (vl: list approx) :=
  match cond, vl with
  | Ccomp c, I n1 :: I n2 :: nil => Some(Int.cmp c n1 n2)
  | Ccompu c, I n1 :: I n2 :: nil => Some(Int.cmpu c n1 n2)
  | Ccompshift c s, I n1 :: I n2 :: nil => Some(Int.cmp c n1 (eval_static_shift s n2))
  | Ccompushift c s, I n1 :: I n2 :: nil => Some(Int.cmpu c n1 (eval_static_shift s n2))
  | Ccompimm c n, I n1 :: nil => Some(Int.cmp c n1 n)
  | Ccompuimm c n, I n1 :: nil => Some(Int.cmpu c n1 n)
  | Ccompf c, F n1 :: F n2 :: nil => Some(Float.cmp c n1 n2)
  | Cnotcompf c, F n1 :: F n2 :: nil => Some(negb(Float.cmp c n1 n2))
  | _, _ => None
  end.
>>
*)

Inductive eval_static_condition_cases: forall (cond: condition) (vl: list approx), Type :=
  | eval_static_condition_case1: forall c n1 n2, eval_static_condition_cases (Ccomp c) (I n1 :: I n2 :: nil)
  | eval_static_condition_case2: forall c n1 n2, eval_static_condition_cases (Ccompu c) (I n1 :: I n2 :: nil)
  | eval_static_condition_case3: forall c s n1 n2, eval_static_condition_cases (Ccompshift c s) (I n1 :: I n2 :: nil)
  | eval_static_condition_case4: forall c s n1 n2, eval_static_condition_cases (Ccompushift c s) (I n1 :: I n2 :: nil)
  | eval_static_condition_case5: forall c n n1, eval_static_condition_cases (Ccompimm c n) (I n1 :: nil)
  | eval_static_condition_case6: forall c n n1, eval_static_condition_cases (Ccompuimm c n) (I n1 :: nil)
  | eval_static_condition_case7: forall c n1 n2, eval_static_condition_cases (Ccompf c) (F n1 :: F n2 :: nil)
  | eval_static_condition_case8: forall c n1 n2, eval_static_condition_cases (Cnotcompf c) (F n1 :: F n2 :: nil)
  | eval_static_condition_default: forall (cond: condition) (vl: list approx), eval_static_condition_cases cond vl.

Definition eval_static_condition_match (cond: condition) (vl: list approx) :=
  match cond as zz1, vl as zz2 return eval_static_condition_cases zz1 zz2 with
  | Ccomp c, I n1 :: I n2 :: nil => eval_static_condition_case1 c n1 n2
  | Ccompu c, I n1 :: I n2 :: nil => eval_static_condition_case2 c n1 n2
  | Ccompshift c s, I n1 :: I n2 :: nil => eval_static_condition_case3 c s n1 n2
  | Ccompushift c s, I n1 :: I n2 :: nil => eval_static_condition_case4 c s n1 n2
  | Ccompimm c n, I n1 :: nil => eval_static_condition_case5 c n n1
  | Ccompuimm c n, I n1 :: nil => eval_static_condition_case6 c n n1
  | Ccompf c, F n1 :: F n2 :: nil => eval_static_condition_case7 c n1 n2
  | Cnotcompf c, F n1 :: F n2 :: nil => eval_static_condition_case8 c n1 n2
  | cond, vl => eval_static_condition_default cond vl
  end.

Definition eval_static_condition (cond: condition) (vl: list approx) :=
  match eval_static_condition_match cond vl with
  | eval_static_condition_case1 c n1 n2 => (* Ccomp c, I n1 :: I n2 :: nil *) 
      Some(Int.cmp c n1 n2)
  | eval_static_condition_case2 c n1 n2 => (* Ccompu c, I n1 :: I n2 :: nil *) 
      Some(Int.cmpu c n1 n2)
  | eval_static_condition_case3 c s n1 n2 => (* Ccompshift c s, I n1 :: I n2 :: nil *) 
      Some(Int.cmp c n1 (eval_static_shift s n2))
  | eval_static_condition_case4 c s n1 n2 => (* Ccompushift c s, I n1 :: I n2 :: nil *) 
      Some(Int.cmpu c n1 (eval_static_shift s n2))
  | eval_static_condition_case5 c n n1 => (* Ccompimm c n, I n1 :: nil *) 
      Some(Int.cmp c n1 n)
  | eval_static_condition_case6 c n n1 => (* Ccompuimm c n, I n1 :: nil *) 
      Some(Int.cmpu c n1 n)
  | eval_static_condition_case7 c n1 n2 => (* Ccompf c, F n1 :: F n2 :: nil *) 
      Some(Float.cmp c n1 n2)
  | eval_static_condition_case8 c n1 n2 => (* Cnotcompf c, F n1 :: F n2 :: nil *) 
      Some(negb(Float.cmp c n1 n2))
  | eval_static_condition_default cond vl =>
      None
  end.


Definition eval_static_condition_val (cond: condition) (vl: list approx) :=
  match eval_static_condition cond vl with
  | None => Unknown
  | Some b => I(if b then Int.one else Int.zero)
  end.

Definition eval_static_intoffloat (f: float) :=
  match Float.intoffloat f with Some x => I x | None => Unknown end.

Definition eval_static_intuoffloat (f: float) :=
  match Float.intuoffloat f with Some x => I x | None => Unknown end.

(** Original definition:
<<
Nondetfunction eval_static_operation (op: operation) (vl: list approx) :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Ofloatconst n, nil => F n
  | Oaddrsymbol s n, nil => G s n
  | Oaddrstack n, nil => S n
  | Oadd, I n1 :: I n2 :: nil => I(Int.add n1 n2)
  | Oaddshift s, I n1 :: I n2 :: nil => I(Int.add n1 (eval_static_shift s n2))
  | Oadd, G s1 n1 :: I n2 :: nil => G s1 (Int.add n1 n2)
  | Oaddshift s, G s1 n1 :: I n2 :: nil => G s1 (Int.add n1 (eval_static_shift s n2))
  | Oadd, S n1 :: I n2 :: nil => S (Int.add n1 n2)
  | Oaddshift s, S n1 :: I n2 :: nil => S (Int.add n1 (eval_static_shift s n2))
  | Oadd, I n1 :: G s2 n2 :: nil => G s2 (Int.add n1 n2)
  | Oadd, I n1 :: S n2 :: nil => S (Int.add n1 n2)
  | Oaddimm n, I n1 :: nil => I (Int.add n1 n)
  | Oaddimm n, G s1 n1 :: nil => G s1 (Int.add n1 n)
  | Oaddimm n, S n1 :: nil => S (Int.add n1 n)
  | Osub, I n1 :: I n2 :: nil => I(Int.sub n1 n2)
  | Osubshift s, I n1 :: I n2 :: nil => I(Int.sub n1 (eval_static_shift s n2))
  | Osub, G s1 n1 :: I n2 :: nil => G s1 (Int.sub n1 n2)
  | Osub, S n1 :: I n2 :: nil => S (Int.sub n1 n2)
  | Osubshift s, G s1 n1 :: I n2 :: nil => G s1 (Int.sub n1 (eval_static_shift s n2))
  | Orsubshift s, I n1 :: I n2 :: nil => I(Int.sub (eval_static_shift s n2) n1)
  | Orsubimm n, I n1 :: nil => I (Int.sub n n1)
  | Omul, I n1 :: I n2 :: nil => I(Int.mul n1 n2)
  | Odiv, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.divs n1 n2)
  | Odivu, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.divu n1 n2)
  | Oand, I n1 :: I n2 :: nil => I(Int.and n1 n2)
  | Oandshift s, I n1 :: I n2 :: nil => I(Int.and n1 (eval_static_shift s n2))
  | Oandimm n, I n1 :: nil => I(Int.and n1 n)
  | Oor, I n1 :: I n2 :: nil => I(Int.or n1 n2)
  | Oorshift s, I n1 :: I n2 :: nil => I(Int.or n1 (eval_static_shift s n2))
  | Oorimm n, I n1 :: nil => I(Int.or n1 n)
  | Oxor, I n1 :: I n2 :: nil => I(Int.xor n1 n2)
  | Oxorshift s, I n1 :: I n2 :: nil => I(Int.xor n1 (eval_static_shift s n2))
  | Oxorimm n, I n1 :: nil => I(Int.xor n1 n)
  | Obic, I n1 :: I n2 :: nil => I(Int.and n1 (Int.not n2))
  | Obicshift s, I n1 :: I n2 :: nil => I(Int.and n1 (Int.not (eval_static_shift s n2)))
  | Onot, I n1 :: nil => I(Int.not n1)
  | Onotshift s, I n1 :: nil => I(Int.not (eval_static_shift s n1))
  | Oshl, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shl n1 n2) else Unknown
  | Oshr, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shr n1 n2) else Unknown
  | Oshru, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shru n1 n2) else Unknown
  | Oshift s, I n1 :: nil => I(eval_static_shift s n1)
  | Onegf, F n1 :: nil => F(Float.neg n1)
  | Oabsf, F n1 :: nil => F(Float.abs n1)
  | Oaddf, F n1 :: F n2 :: nil => F(Float.add n1 n2)
  | Osubf, F n1 :: F n2 :: nil => F(Float.sub n1 n2)
  | Omulf, F n1 :: F n2 :: nil => F(Float.mul n1 n2)
  | Odivf, F n1 :: F n2 :: nil => F(Float.div n1 n2)
  | Osingleoffloat, F n1 :: nil => F(Float.singleoffloat n1)
  | Ointoffloat, F n1 :: nil => eval_static_intoffloat n1
  | Ointuoffloat, F n1 :: nil => eval_static_intuoffloat n1
  | Ofloatofint, I n1 :: nil => F(Float.floatofint n1)
  | Ofloatofintu, I n1 :: nil => F(Float.floatofintu n1)
  | Ocmp c, vl => eval_static_condition_val c vl
  | _, _ => Unknown
  end.
>>
*)

Inductive eval_static_operation_cases: forall (op: operation) (vl: list approx), Type :=
  | eval_static_operation_case1: forall v1, eval_static_operation_cases (Omove) (v1::nil)
  | eval_static_operation_case2: forall n, eval_static_operation_cases (Ointconst n) (nil)
  | eval_static_operation_case3: forall n, eval_static_operation_cases (Ofloatconst n) (nil)
  | eval_static_operation_case4: forall s n, eval_static_operation_cases (Oaddrsymbol s n) (nil)
  | eval_static_operation_case5: forall n, eval_static_operation_cases (Oaddrstack n) (nil)
  | eval_static_operation_case6: forall n1 n2, eval_static_operation_cases (Oadd) (I n1 :: I n2 :: nil)
  | eval_static_operation_case7: forall s n1 n2, eval_static_operation_cases (Oaddshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case8: forall s1 n1 n2, eval_static_operation_cases (Oadd) (G s1 n1 :: I n2 :: nil)
  | eval_static_operation_case9: forall s s1 n1 n2, eval_static_operation_cases (Oaddshift s) (G s1 n1 :: I n2 :: nil)
  | eval_static_operation_case10: forall n1 n2, eval_static_operation_cases (Oadd) (S n1 :: I n2 :: nil)
  | eval_static_operation_case11: forall s n1 n2, eval_static_operation_cases (Oaddshift s) (S n1 :: I n2 :: nil)
  | eval_static_operation_case12: forall n1 s2 n2, eval_static_operation_cases (Oadd) (I n1 :: G s2 n2 :: nil)
  | eval_static_operation_case13: forall n1 n2, eval_static_operation_cases (Oadd) (I n1 :: S n2 :: nil)
  | eval_static_operation_case14: forall n n1, eval_static_operation_cases (Oaddimm n) (I n1 :: nil)
  | eval_static_operation_case15: forall n s1 n1, eval_static_operation_cases (Oaddimm n) (G s1 n1 :: nil)
  | eval_static_operation_case16: forall n n1, eval_static_operation_cases (Oaddimm n) (S n1 :: nil)
  | eval_static_operation_case17: forall n1 n2, eval_static_operation_cases (Osub) (I n1 :: I n2 :: nil)
  | eval_static_operation_case18: forall s n1 n2, eval_static_operation_cases (Osubshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case19: forall s1 n1 n2, eval_static_operation_cases (Osub) (G s1 n1 :: I n2 :: nil)
  | eval_static_operation_case20: forall n1 n2, eval_static_operation_cases (Osub) (S n1 :: I n2 :: nil)
  | eval_static_operation_case21: forall s s1 n1 n2, eval_static_operation_cases (Osubshift s) (G s1 n1 :: I n2 :: nil)
  | eval_static_operation_case22: forall s n1 n2, eval_static_operation_cases (Orsubshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case23: forall n n1, eval_static_operation_cases (Orsubimm n) (I n1 :: nil)
  | eval_static_operation_case24: forall n1 n2, eval_static_operation_cases (Omul) (I n1 :: I n2 :: nil)
  | eval_static_operation_case25: forall n1 n2, eval_static_operation_cases (Odiv) (I n1 :: I n2 :: nil)
  | eval_static_operation_case26: forall n1 n2, eval_static_operation_cases (Odivu) (I n1 :: I n2 :: nil)
  | eval_static_operation_case27: forall n1 n2, eval_static_operation_cases (Oand) (I n1 :: I n2 :: nil)
  | eval_static_operation_case28: forall s n1 n2, eval_static_operation_cases (Oandshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case29: forall n n1, eval_static_operation_cases (Oandimm n) (I n1 :: nil)
  | eval_static_operation_case30: forall n1 n2, eval_static_operation_cases (Oor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case31: forall s n1 n2, eval_static_operation_cases (Oorshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case32: forall n n1, eval_static_operation_cases (Oorimm n) (I n1 :: nil)
  | eval_static_operation_case33: forall n1 n2, eval_static_operation_cases (Oxor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case34: forall s n1 n2, eval_static_operation_cases (Oxorshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case35: forall n n1, eval_static_operation_cases (Oxorimm n) (I n1 :: nil)
  | eval_static_operation_case36: forall n1 n2, eval_static_operation_cases (Obic) (I n1 :: I n2 :: nil)
  | eval_static_operation_case37: forall s n1 n2, eval_static_operation_cases (Obicshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case38: forall n1, eval_static_operation_cases (Onot) (I n1 :: nil)
  | eval_static_operation_case39: forall s n1, eval_static_operation_cases (Onotshift s) (I n1 :: nil)
  | eval_static_operation_case40: forall n1 n2, eval_static_operation_cases (Oshl) (I n1 :: I n2 :: nil)
  | eval_static_operation_case41: forall n1 n2, eval_static_operation_cases (Oshr) (I n1 :: I n2 :: nil)
  | eval_static_operation_case42: forall n1 n2, eval_static_operation_cases (Oshru) (I n1 :: I n2 :: nil)
  | eval_static_operation_case43: forall s n1, eval_static_operation_cases (Oshift s) (I n1 :: nil)
  | eval_static_operation_case44: forall n1, eval_static_operation_cases (Onegf) (F n1 :: nil)
  | eval_static_operation_case45: forall n1, eval_static_operation_cases (Oabsf) (F n1 :: nil)
  | eval_static_operation_case46: forall n1 n2, eval_static_operation_cases (Oaddf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case47: forall n1 n2, eval_static_operation_cases (Osubf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case48: forall n1 n2, eval_static_operation_cases (Omulf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case49: forall n1 n2, eval_static_operation_cases (Odivf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case50: forall n1, eval_static_operation_cases (Osingleoffloat) (F n1 :: nil)
  | eval_static_operation_case51: forall n1, eval_static_operation_cases (Ointoffloat) (F n1 :: nil)
  | eval_static_operation_case52: forall n1, eval_static_operation_cases (Ointuoffloat) (F n1 :: nil)
  | eval_static_operation_case53: forall n1, eval_static_operation_cases (Ofloatofint) (I n1 :: nil)
  | eval_static_operation_case54: forall n1, eval_static_operation_cases (Ofloatofintu) (I n1 :: nil)
  | eval_static_operation_case55: forall c vl, eval_static_operation_cases (Ocmp c) (vl)
  | eval_static_operation_default: forall (op: operation) (vl: list approx), eval_static_operation_cases op vl.

Definition eval_static_operation_match (op: operation) (vl: list approx) :=
  match op as zz1, vl as zz2 return eval_static_operation_cases zz1 zz2 with
  | Omove, v1::nil => eval_static_operation_case1 v1
  | Ointconst n, nil => eval_static_operation_case2 n
  | Ofloatconst n, nil => eval_static_operation_case3 n
  | Oaddrsymbol s n, nil => eval_static_operation_case4 s n
  | Oaddrstack n, nil => eval_static_operation_case5 n
  | Oadd, I n1 :: I n2 :: nil => eval_static_operation_case6 n1 n2
  | Oaddshift s, I n1 :: I n2 :: nil => eval_static_operation_case7 s n1 n2
  | Oadd, G s1 n1 :: I n2 :: nil => eval_static_operation_case8 s1 n1 n2
  | Oaddshift s, G s1 n1 :: I n2 :: nil => eval_static_operation_case9 s s1 n1 n2
  | Oadd, S n1 :: I n2 :: nil => eval_static_operation_case10 n1 n2
  | Oaddshift s, S n1 :: I n2 :: nil => eval_static_operation_case11 s n1 n2
  | Oadd, I n1 :: G s2 n2 :: nil => eval_static_operation_case12 n1 s2 n2
  | Oadd, I n1 :: S n2 :: nil => eval_static_operation_case13 n1 n2
  | Oaddimm n, I n1 :: nil => eval_static_operation_case14 n n1
  | Oaddimm n, G s1 n1 :: nil => eval_static_operation_case15 n s1 n1
  | Oaddimm n, S n1 :: nil => eval_static_operation_case16 n n1
  | Osub, I n1 :: I n2 :: nil => eval_static_operation_case17 n1 n2
  | Osubshift s, I n1 :: I n2 :: nil => eval_static_operation_case18 s n1 n2
  | Osub, G s1 n1 :: I n2 :: nil => eval_static_operation_case19 s1 n1 n2
  | Osub, S n1 :: I n2 :: nil => eval_static_operation_case20 n1 n2
  | Osubshift s, G s1 n1 :: I n2 :: nil => eval_static_operation_case21 s s1 n1 n2
  | Orsubshift s, I n1 :: I n2 :: nil => eval_static_operation_case22 s n1 n2
  | Orsubimm n, I n1 :: nil => eval_static_operation_case23 n n1
  | Omul, I n1 :: I n2 :: nil => eval_static_operation_case24 n1 n2
  | Odiv, I n1 :: I n2 :: nil => eval_static_operation_case25 n1 n2
  | Odivu, I n1 :: I n2 :: nil => eval_static_operation_case26 n1 n2
  | Oand, I n1 :: I n2 :: nil => eval_static_operation_case27 n1 n2
  | Oandshift s, I n1 :: I n2 :: nil => eval_static_operation_case28 s n1 n2
  | Oandimm n, I n1 :: nil => eval_static_operation_case29 n n1
  | Oor, I n1 :: I n2 :: nil => eval_static_operation_case30 n1 n2
  | Oorshift s, I n1 :: I n2 :: nil => eval_static_operation_case31 s n1 n2
  | Oorimm n, I n1 :: nil => eval_static_operation_case32 n n1
  | Oxor, I n1 :: I n2 :: nil => eval_static_operation_case33 n1 n2
  | Oxorshift s, I n1 :: I n2 :: nil => eval_static_operation_case34 s n1 n2
  | Oxorimm n, I n1 :: nil => eval_static_operation_case35 n n1
  | Obic, I n1 :: I n2 :: nil => eval_static_operation_case36 n1 n2
  | Obicshift s, I n1 :: I n2 :: nil => eval_static_operation_case37 s n1 n2
  | Onot, I n1 :: nil => eval_static_operation_case38 n1
  | Onotshift s, I n1 :: nil => eval_static_operation_case39 s n1
  | Oshl, I n1 :: I n2 :: nil => eval_static_operation_case40 n1 n2
  | Oshr, I n1 :: I n2 :: nil => eval_static_operation_case41 n1 n2
  | Oshru, I n1 :: I n2 :: nil => eval_static_operation_case42 n1 n2
  | Oshift s, I n1 :: nil => eval_static_operation_case43 s n1
  | Onegf, F n1 :: nil => eval_static_operation_case44 n1
  | Oabsf, F n1 :: nil => eval_static_operation_case45 n1
  | Oaddf, F n1 :: F n2 :: nil => eval_static_operation_case46 n1 n2
  | Osubf, F n1 :: F n2 :: nil => eval_static_operation_case47 n1 n2
  | Omulf, F n1 :: F n2 :: nil => eval_static_operation_case48 n1 n2
  | Odivf, F n1 :: F n2 :: nil => eval_static_operation_case49 n1 n2
  | Osingleoffloat, F n1 :: nil => eval_static_operation_case50 n1
  | Ointoffloat, F n1 :: nil => eval_static_operation_case51 n1
  | Ointuoffloat, F n1 :: nil => eval_static_operation_case52 n1
  | Ofloatofint, I n1 :: nil => eval_static_operation_case53 n1
  | Ofloatofintu, I n1 :: nil => eval_static_operation_case54 n1
  | Ocmp c, vl => eval_static_operation_case55 c vl
  | op, vl => eval_static_operation_default op vl
  end.

Definition eval_static_operation (op: operation) (vl: list approx) :=
  match eval_static_operation_match op vl with
  | eval_static_operation_case1 v1 => (* Omove, v1::nil *) 
      v1
  | eval_static_operation_case2 n => (* Ointconst n, nil *) 
      I n
  | eval_static_operation_case3 n => (* Ofloatconst n, nil *) 
      F n
  | eval_static_operation_case4 s n => (* Oaddrsymbol s n, nil *) 
      G s n
  | eval_static_operation_case5 n => (* Oaddrstack n, nil *) 
      S n
  | eval_static_operation_case6 n1 n2 => (* Oadd, I n1 :: I n2 :: nil *) 
      I(Int.add n1 n2)
  | eval_static_operation_case7 s n1 n2 => (* Oaddshift s, I n1 :: I n2 :: nil *) 
      I(Int.add n1 (eval_static_shift s n2))
  | eval_static_operation_case8 s1 n1 n2 => (* Oadd, G s1 n1 :: I n2 :: nil *) 
      G s1 (Int.add n1 n2)
  | eval_static_operation_case9 s s1 n1 n2 => (* Oaddshift s, G s1 n1 :: I n2 :: nil *) 
      G s1 (Int.add n1 (eval_static_shift s n2))
  | eval_static_operation_case10 n1 n2 => (* Oadd, S n1 :: I n2 :: nil *) 
      S (Int.add n1 n2)
  | eval_static_operation_case11 s n1 n2 => (* Oaddshift s, S n1 :: I n2 :: nil *) 
      S (Int.add n1 (eval_static_shift s n2))
  | eval_static_operation_case12 n1 s2 n2 => (* Oadd, I n1 :: G s2 n2 :: nil *) 
      G s2 (Int.add n1 n2)
  | eval_static_operation_case13 n1 n2 => (* Oadd, I n1 :: S n2 :: nil *) 
      S (Int.add n1 n2)
  | eval_static_operation_case14 n n1 => (* Oaddimm n, I n1 :: nil *) 
      I (Int.add n1 n)
  | eval_static_operation_case15 n s1 n1 => (* Oaddimm n, G s1 n1 :: nil *) 
      G s1 (Int.add n1 n)
  | eval_static_operation_case16 n n1 => (* Oaddimm n, S n1 :: nil *) 
      S (Int.add n1 n)
  | eval_static_operation_case17 n1 n2 => (* Osub, I n1 :: I n2 :: nil *) 
      I(Int.sub n1 n2)
  | eval_static_operation_case18 s n1 n2 => (* Osubshift s, I n1 :: I n2 :: nil *) 
      I(Int.sub n1 (eval_static_shift s n2))
  | eval_static_operation_case19 s1 n1 n2 => (* Osub, G s1 n1 :: I n2 :: nil *) 
      G s1 (Int.sub n1 n2)
  | eval_static_operation_case20 n1 n2 => (* Osub, S n1 :: I n2 :: nil *) 
      S (Int.sub n1 n2)
  | eval_static_operation_case21 s s1 n1 n2 => (* Osubshift s, G s1 n1 :: I n2 :: nil *) 
      G s1 (Int.sub n1 (eval_static_shift s n2))
  | eval_static_operation_case22 s n1 n2 => (* Orsubshift s, I n1 :: I n2 :: nil *) 
      I(Int.sub (eval_static_shift s n2) n1)
  | eval_static_operation_case23 n n1 => (* Orsubimm n, I n1 :: nil *) 
      I (Int.sub n n1)
  | eval_static_operation_case24 n1 n2 => (* Omul, I n1 :: I n2 :: nil *) 
      I(Int.mul n1 n2)
  | eval_static_operation_case25 n1 n2 => (* Odiv, I n1 :: I n2 :: nil *) 
      if Int.eq n2 Int.zero then Unknown else I(Int.divs n1 n2)
  | eval_static_operation_case26 n1 n2 => (* Odivu, I n1 :: I n2 :: nil *) 
      if Int.eq n2 Int.zero then Unknown else I(Int.divu n1 n2)
  | eval_static_operation_case27 n1 n2 => (* Oand, I n1 :: I n2 :: nil *) 
      I(Int.and n1 n2)
  | eval_static_operation_case28 s n1 n2 => (* Oandshift s, I n1 :: I n2 :: nil *) 
      I(Int.and n1 (eval_static_shift s n2))
  | eval_static_operation_case29 n n1 => (* Oandimm n, I n1 :: nil *) 
      I(Int.and n1 n)
  | eval_static_operation_case30 n1 n2 => (* Oor, I n1 :: I n2 :: nil *) 
      I(Int.or n1 n2)
  | eval_static_operation_case31 s n1 n2 => (* Oorshift s, I n1 :: I n2 :: nil *) 
      I(Int.or n1 (eval_static_shift s n2))
  | eval_static_operation_case32 n n1 => (* Oorimm n, I n1 :: nil *) 
      I(Int.or n1 n)
  | eval_static_operation_case33 n1 n2 => (* Oxor, I n1 :: I n2 :: nil *) 
      I(Int.xor n1 n2)
  | eval_static_operation_case34 s n1 n2 => (* Oxorshift s, I n1 :: I n2 :: nil *) 
      I(Int.xor n1 (eval_static_shift s n2))
  | eval_static_operation_case35 n n1 => (* Oxorimm n, I n1 :: nil *) 
      I(Int.xor n1 n)
  | eval_static_operation_case36 n1 n2 => (* Obic, I n1 :: I n2 :: nil *) 
      I(Int.and n1 (Int.not n2))
  | eval_static_operation_case37 s n1 n2 => (* Obicshift s, I n1 :: I n2 :: nil *) 
      I(Int.and n1 (Int.not (eval_static_shift s n2)))
  | eval_static_operation_case38 n1 => (* Onot, I n1 :: nil *) 
      I(Int.not n1)
  | eval_static_operation_case39 s n1 => (* Onotshift s, I n1 :: nil *) 
      I(Int.not (eval_static_shift s n1))
  | eval_static_operation_case40 n1 n2 => (* Oshl, I n1 :: I n2 :: nil *) 
      if Int.ltu n2 Int.iwordsize then I(Int.shl n1 n2) else Unknown
  | eval_static_operation_case41 n1 n2 => (* Oshr, I n1 :: I n2 :: nil *) 
      if Int.ltu n2 Int.iwordsize then I(Int.shr n1 n2) else Unknown
  | eval_static_operation_case42 n1 n2 => (* Oshru, I n1 :: I n2 :: nil *) 
      if Int.ltu n2 Int.iwordsize then I(Int.shru n1 n2) else Unknown
  | eval_static_operation_case43 s n1 => (* Oshift s, I n1 :: nil *) 
      I(eval_static_shift s n1)
  | eval_static_operation_case44 n1 => (* Onegf, F n1 :: nil *) 
      F(Float.neg n1)
  | eval_static_operation_case45 n1 => (* Oabsf, F n1 :: nil *) 
      F(Float.abs n1)
  | eval_static_operation_case46 n1 n2 => (* Oaddf, F n1 :: F n2 :: nil *) 
      F(Float.add n1 n2)
  | eval_static_operation_case47 n1 n2 => (* Osubf, F n1 :: F n2 :: nil *) 
      F(Float.sub n1 n2)
  | eval_static_operation_case48 n1 n2 => (* Omulf, F n1 :: F n2 :: nil *) 
      F(Float.mul n1 n2)
  | eval_static_operation_case49 n1 n2 => (* Odivf, F n1 :: F n2 :: nil *) 
      F(Float.div n1 n2)
  | eval_static_operation_case50 n1 => (* Osingleoffloat, F n1 :: nil *) 
      F(Float.singleoffloat n1)
  | eval_static_operation_case51 n1 => (* Ointoffloat, F n1 :: nil *) 
      eval_static_intoffloat n1
  | eval_static_operation_case52 n1 => (* Ointuoffloat, F n1 :: nil *) 
      eval_static_intuoffloat n1
  | eval_static_operation_case53 n1 => (* Ofloatofint, I n1 :: nil *) 
      F(Float.floatofint n1)
  | eval_static_operation_case54 n1 => (* Ofloatofintu, I n1 :: nil *) 
      F(Float.floatofintu n1)
  | eval_static_operation_case55 c vl => (* Ocmp c, vl *) 
      eval_static_condition_val c vl
  | eval_static_operation_default op vl =>
      Unknown
  end.


(** * Operator strength reduction *)

(** We now define auxiliary functions for strength reduction of
  operators and addressing modes: replacing an operator with a cheaper
  one if some of its arguments are statically known.  These are again
  large pattern-matchings expressed in indirect style. *)

Section STRENGTH_REDUCTION.

(** Original definition:
<<
Nondetfunction cond_strength_reduction 
              (cond: condition) (args: list reg) (vl: list approx) :=
  match cond, args, vl with
  | Ccomp c, r1 :: r2 :: nil, I n1 :: v2 :: nil =>
      (Ccompimm (swap_comparison c) n1, r2 :: nil)
  | Ccomp c, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Ccompimm c n2, r1 :: nil)
  | Ccompu c, r1 :: r2 :: nil, I n1 :: v2 :: nil =>
      (Ccompuimm (swap_comparison c) n1, r2 :: nil)
  | Ccompu c, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Ccompuimm c n2, r1 :: nil)
  | Ccompshift c s, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Ccompimm c (eval_static_shift s n2), r1 :: nil)
  | Ccompushift c s, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Ccompuimm c (eval_static_shift s n2), r1 :: nil)
  | _, _, _ => 
      (cond, args)
  end.
>>
*)

Inductive cond_strength_reduction_cases: forall (cond: condition) (args: list reg) (vl: list approx), Type :=
  | cond_strength_reduction_case1: forall c r1 r2 n1 v2, cond_strength_reduction_cases (Ccomp c) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | cond_strength_reduction_case2: forall c r1 r2 v1 n2, cond_strength_reduction_cases (Ccomp c) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | cond_strength_reduction_case3: forall c r1 r2 n1 v2, cond_strength_reduction_cases (Ccompu c) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | cond_strength_reduction_case4: forall c r1 r2 v1 n2, cond_strength_reduction_cases (Ccompu c) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | cond_strength_reduction_case5: forall c s r1 r2 v1 n2, cond_strength_reduction_cases (Ccompshift c s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | cond_strength_reduction_case6: forall c s r1 r2 v1 n2, cond_strength_reduction_cases (Ccompushift c s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | cond_strength_reduction_default: forall (cond: condition) (args: list reg) (vl: list approx), cond_strength_reduction_cases cond args vl.

Definition cond_strength_reduction_match (cond: condition) (args: list reg) (vl: list approx) :=
  match cond as zz1, args as zz2, vl as zz3 return cond_strength_reduction_cases zz1 zz2 zz3 with
  | Ccomp c, r1 :: r2 :: nil, I n1 :: v2 :: nil => cond_strength_reduction_case1 c r1 r2 n1 v2
  | Ccomp c, r1 :: r2 :: nil, v1 :: I n2 :: nil => cond_strength_reduction_case2 c r1 r2 v1 n2
  | Ccompu c, r1 :: r2 :: nil, I n1 :: v2 :: nil => cond_strength_reduction_case3 c r1 r2 n1 v2
  | Ccompu c, r1 :: r2 :: nil, v1 :: I n2 :: nil => cond_strength_reduction_case4 c r1 r2 v1 n2
  | Ccompshift c s, r1 :: r2 :: nil, v1 :: I n2 :: nil => cond_strength_reduction_case5 c s r1 r2 v1 n2
  | Ccompushift c s, r1 :: r2 :: nil, v1 :: I n2 :: nil => cond_strength_reduction_case6 c s r1 r2 v1 n2
  | cond, args, vl => cond_strength_reduction_default cond args vl
  end.

Definition cond_strength_reduction (cond: condition) (args: list reg) (vl: list approx) :=
  match cond_strength_reduction_match cond args vl with
  | cond_strength_reduction_case1 c r1 r2 n1 v2 => (* Ccomp c, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      (Ccompimm (swap_comparison c) n1, r2 :: nil)
  | cond_strength_reduction_case2 c r1 r2 v1 n2 => (* Ccomp c, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Ccompimm c n2, r1 :: nil)
  | cond_strength_reduction_case3 c r1 r2 n1 v2 => (* Ccompu c, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      (Ccompuimm (swap_comparison c) n1, r2 :: nil)
  | cond_strength_reduction_case4 c r1 r2 v1 n2 => (* Ccompu c, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Ccompuimm c n2, r1 :: nil)
  | cond_strength_reduction_case5 c s r1 r2 v1 n2 => (* Ccompshift c s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Ccompimm c (eval_static_shift s n2), r1 :: nil)
  | cond_strength_reduction_case6 c s r1 r2 v1 n2 => (* Ccompushift c s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Ccompuimm c (eval_static_shift s n2), r1 :: nil)
  | cond_strength_reduction_default cond args vl =>
      (cond, args)
  end.


Definition make_addimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oaddimm n, r :: nil).

Definition make_shlimm (n: int) (r1 r2: reg) :=
  if Int.eq n Int.zero then
    (Omove, r1 :: nil)
  else if Int.ltu n Int.iwordsize then
    (Oshift (Slsl (mk_shift_amount n)), r1 :: nil)
  else
    (Oshl, r1 :: r2 :: nil).

Definition make_shrimm (n: int) (r1 r2: reg) :=
  if Int.eq n Int.zero then
    (Omove, r1 :: nil)
  else if Int.ltu n Int.iwordsize then
    (Oshift (Sasr (mk_shift_amount n)), r1 :: nil)
  else
    (Oshr, r1 :: r2 :: nil).

Definition make_shruimm (n: int) (r1 r2: reg) :=
  if Int.eq n Int.zero then
    (Omove, r1 :: nil)
  else if Int.ltu n Int.iwordsize then
    (Oshift (Slsr (mk_shift_amount n)), r1 :: nil)
  else
    (Oshru, r1 :: r2 :: nil).

Definition make_mulimm (n: int) (r1 r2: reg) :=
  if Int.eq n Int.zero then
    (Ointconst Int.zero, nil)
  else if Int.eq n Int.one then
    (Omove, r1 :: nil)
  else
    match Int.is_power2 n with
    | Some l => (Oshift (Slsl (mk_shift_amount l)), r1 :: nil)
    | None => (Omul, r1 :: r2 :: nil)
    end.

Definition make_divimm (n: int) (r1 r2: reg) :=
  match Int.is_power2 n with
  | Some l => if Int.ltu l (Int.repr 31)
              then (Oshrximm l, r1 :: nil)
              else (Odiv, r1 :: r2 :: nil)
  | None   => (Odiv, r1 :: r2 :: nil)
  end.

Definition make_divuimm (n: int) (r1 r2: reg) :=
  match Int.is_power2 n with
  | Some l => (Oshift (Slsr (mk_shift_amount l)), r1 :: nil)
  | None   => (Odivu, r1 :: r2 :: nil)
  end.

Definition make_andimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then (Ointconst Int.zero, nil)
  else if Int.eq n Int.mone then (Omove, r :: nil)
  else (Oandimm n, r :: nil).

Definition make_orimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then (Omove, r :: nil)
  else if Int.eq n Int.mone then (Ointconst Int.mone, nil)
  else (Oorimm n, r :: nil).

Definition make_xorimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then (Omove, r :: nil)
  else if Int.eq n Int.mone then (Onot, r :: nil)
  else (Oxorimm n, r :: nil).

(** Original definition:
<<
Nondetfunction op_strength_reduction 
              (op: operation) (args: list reg) (vl: list approx) :=
  match op, args, vl with
  | Oadd, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_addimm n1 r2
  | Oadd, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_addimm n2 r1
  | Oaddshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_addimm (eval_static_shift s n2) r1
  | Osub, r1 :: r2 :: nil, I n1 :: v2 :: nil => (Orsubimm n1, r2 :: nil)
  | Osub, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_addimm (Int.neg n2) r1
  | Osubshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_addimm (Int.neg (eval_static_shift s n2)) r1
  | Orsubshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => (Orsubimm (eval_static_shift s n2), r1 :: nil)
  | Omul, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_mulimm n1 r2 r1
  | Omul, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_mulimm n2 r1 r2
  | Odiv, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_divimm n2 r1 r2
  | Odivu, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_divuimm n2 r1 r2
  | Oand, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_andimm n1 r2
  | Oand, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_andimm n2 r1
  | Oandshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_andimm (eval_static_shift s n2) r1
  | Oor, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_orimm n1 r2
  | Oor, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_orimm n2 r1
  | Oorshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_orimm (eval_static_shift s n2) r1
  | Oxor, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_xorimm n1 r2
  | Oxor, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_xorimm n2 r1
  | Oxorshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_xorimm (eval_static_shift s n2) r1
  | Obic, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_andimm (Int.not n2) r1
  | Obicshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_andimm (Int.not (eval_static_shift s n2)) r1
  | Oshl, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_shlimm n2 r1 r2
  | Oshr, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_shrimm n2 r1 r2
  | Oshru, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_shruimm n2 r1 r2
  | Ocmp c, args, vl =>
      let (c', args') := cond_strength_reduction c args vl in (Ocmp c', args')
  | _, _, _ => (op, args)
  end.
>>
*)

Inductive op_strength_reduction_cases: forall (op: operation) (args: list reg) (vl: list approx), Type :=
  | op_strength_reduction_case1: forall r1 r2 n1 v2, op_strength_reduction_cases (Oadd) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case2: forall r1 r2 v1 n2, op_strength_reduction_cases (Oadd) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case3: forall s r1 r2 v1 n2, op_strength_reduction_cases (Oaddshift s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case4: forall r1 r2 n1 v2, op_strength_reduction_cases (Osub) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case5: forall r1 r2 v1 n2, op_strength_reduction_cases (Osub) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case6: forall s r1 r2 v1 n2, op_strength_reduction_cases (Osubshift s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case7: forall s r1 r2 v1 n2, op_strength_reduction_cases (Orsubshift s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case8: forall r1 r2 n1 v2, op_strength_reduction_cases (Omul) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case9: forall r1 r2 v1 n2, op_strength_reduction_cases (Omul) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case10: forall r1 r2 v1 n2, op_strength_reduction_cases (Odiv) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case11: forall r1 r2 v1 n2, op_strength_reduction_cases (Odivu) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case12: forall r1 r2 n1 v2, op_strength_reduction_cases (Oand) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case13: forall r1 r2 v1 n2, op_strength_reduction_cases (Oand) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case14: forall s r1 r2 v1 n2, op_strength_reduction_cases (Oandshift s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case15: forall r1 r2 n1 v2, op_strength_reduction_cases (Oor) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case16: forall r1 r2 v1 n2, op_strength_reduction_cases (Oor) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case17: forall s r1 r2 v1 n2, op_strength_reduction_cases (Oorshift s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case18: forall r1 r2 n1 v2, op_strength_reduction_cases (Oxor) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case19: forall r1 r2 v1 n2, op_strength_reduction_cases (Oxor) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case20: forall s r1 r2 v1 n2, op_strength_reduction_cases (Oxorshift s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case21: forall r1 r2 v1 n2, op_strength_reduction_cases (Obic) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case22: forall s r1 r2 v1 n2, op_strength_reduction_cases (Obicshift s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case23: forall r1 r2 v1 n2, op_strength_reduction_cases (Oshl) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case24: forall r1 r2 v1 n2, op_strength_reduction_cases (Oshr) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case25: forall r1 r2 v1 n2, op_strength_reduction_cases (Oshru) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case26: forall c args vl, op_strength_reduction_cases (Ocmp c) (args) (vl)
  | op_strength_reduction_default: forall (op: operation) (args: list reg) (vl: list approx), op_strength_reduction_cases op args vl.

Definition op_strength_reduction_match (op: operation) (args: list reg) (vl: list approx) :=
  match op as zz1, args as zz2, vl as zz3 return op_strength_reduction_cases zz1 zz2 zz3 with
  | Oadd, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case1 r1 r2 n1 v2
  | Oadd, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case2 r1 r2 v1 n2
  | Oaddshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case3 s r1 r2 v1 n2
  | Osub, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case4 r1 r2 n1 v2
  | Osub, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case5 r1 r2 v1 n2
  | Osubshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case6 s r1 r2 v1 n2
  | Orsubshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case7 s r1 r2 v1 n2
  | Omul, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case8 r1 r2 n1 v2
  | Omul, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case9 r1 r2 v1 n2
  | Odiv, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case10 r1 r2 v1 n2
  | Odivu, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case11 r1 r2 v1 n2
  | Oand, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case12 r1 r2 n1 v2
  | Oand, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case13 r1 r2 v1 n2
  | Oandshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case14 s r1 r2 v1 n2
  | Oor, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case15 r1 r2 n1 v2
  | Oor, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case16 r1 r2 v1 n2
  | Oorshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case17 s r1 r2 v1 n2
  | Oxor, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case18 r1 r2 n1 v2
  | Oxor, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case19 r1 r2 v1 n2
  | Oxorshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case20 s r1 r2 v1 n2
  | Obic, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case21 r1 r2 v1 n2
  | Obicshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case22 s r1 r2 v1 n2
  | Oshl, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case23 r1 r2 v1 n2
  | Oshr, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case24 r1 r2 v1 n2
  | Oshru, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case25 r1 r2 v1 n2
  | Ocmp c, args, vl => op_strength_reduction_case26 c args vl
  | op, args, vl => op_strength_reduction_default op args vl
  end.

Definition op_strength_reduction (op: operation) (args: list reg) (vl: list approx) :=
  match op_strength_reduction_match op args vl with
  | op_strength_reduction_case1 r1 r2 n1 v2 => (* Oadd, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_addimm n1 r2
  | op_strength_reduction_case2 r1 r2 v1 n2 => (* Oadd, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_addimm n2 r1
  | op_strength_reduction_case3 s r1 r2 v1 n2 => (* Oaddshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_addimm (eval_static_shift s n2) r1
  | op_strength_reduction_case4 r1 r2 n1 v2 => (* Osub, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      (Orsubimm n1, r2 :: nil)
  | op_strength_reduction_case5 r1 r2 v1 n2 => (* Osub, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_addimm (Int.neg n2) r1
  | op_strength_reduction_case6 s r1 r2 v1 n2 => (* Osubshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_addimm (Int.neg (eval_static_shift s n2)) r1
  | op_strength_reduction_case7 s r1 r2 v1 n2 => (* Orsubshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Orsubimm (eval_static_shift s n2), r1 :: nil)
  | op_strength_reduction_case8 r1 r2 n1 v2 => (* Omul, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_mulimm n1 r2 r1
  | op_strength_reduction_case9 r1 r2 v1 n2 => (* Omul, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_mulimm n2 r1 r2
  | op_strength_reduction_case10 r1 r2 v1 n2 => (* Odiv, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_divimm n2 r1 r2
  | op_strength_reduction_case11 r1 r2 v1 n2 => (* Odivu, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_divuimm n2 r1 r2
  | op_strength_reduction_case12 r1 r2 n1 v2 => (* Oand, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_andimm n1 r2
  | op_strength_reduction_case13 r1 r2 v1 n2 => (* Oand, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_andimm n2 r1
  | op_strength_reduction_case14 s r1 r2 v1 n2 => (* Oandshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_andimm (eval_static_shift s n2) r1
  | op_strength_reduction_case15 r1 r2 n1 v2 => (* Oor, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_orimm n1 r2
  | op_strength_reduction_case16 r1 r2 v1 n2 => (* Oor, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_orimm n2 r1
  | op_strength_reduction_case17 s r1 r2 v1 n2 => (* Oorshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_orimm (eval_static_shift s n2) r1
  | op_strength_reduction_case18 r1 r2 n1 v2 => (* Oxor, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_xorimm n1 r2
  | op_strength_reduction_case19 r1 r2 v1 n2 => (* Oxor, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_xorimm n2 r1
  | op_strength_reduction_case20 s r1 r2 v1 n2 => (* Oxorshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_xorimm (eval_static_shift s n2) r1
  | op_strength_reduction_case21 r1 r2 v1 n2 => (* Obic, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_andimm (Int.not n2) r1
  | op_strength_reduction_case22 s r1 r2 v1 n2 => (* Obicshift s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_andimm (Int.not (eval_static_shift s n2)) r1
  | op_strength_reduction_case23 r1 r2 v1 n2 => (* Oshl, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_shlimm n2 r1 r2
  | op_strength_reduction_case24 r1 r2 v1 n2 => (* Oshr, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_shrimm n2 r1 r2
  | op_strength_reduction_case25 r1 r2 v1 n2 => (* Oshru, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_shruimm n2 r1 r2
  | op_strength_reduction_case26 c args vl => (* Ocmp c, args, vl *) 
      let (c', args') := cond_strength_reduction c args vl in (Ocmp c', args')
  | op_strength_reduction_default op args vl =>
      (op, args)
  end.



(** Original definition:
<<
Nondetfunction addr_strength_reduction
                (addr: addressing) (args: list reg) (vl: list approx) :=
  match addr, args, vl with
  | Aindexed2, r1 :: r2 :: nil, S n1 :: I n2 :: nil =>
      (Ainstack (Int.add n1 n2), nil)
  | Aindexed2, r1 :: r2 :: nil, I n1 :: S n2 :: nil =>
      (Ainstack (Int.add n1 n2), nil)
  | Aindexed2, r1 :: r2 :: nil, I n1 :: v2 :: nil =>
      (Aindexed n1, r2 :: nil)
  | Aindexed2, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Aindexed n2, r1 :: nil)
  | Aindexed2shift s, r1 :: r2 :: nil, S n1 :: I n2 :: nil =>
      (Ainstack (Int.add n1 (eval_static_shift s n2)), nil)
  | Aindexed2shift s, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Aindexed (eval_static_shift s n2), r1 :: nil)
  | Aindexed n, r1 :: nil, S n1 :: nil =>
      (Ainstack (Int.add n1 n), nil)
  | _, _, _ =>
      (addr, args)
  end.
>>
*)

Inductive addr_strength_reduction_cases: forall (addr: addressing) (args: list reg) (vl: list approx), Type :=
  | addr_strength_reduction_case1: forall r1 r2 n1 n2, addr_strength_reduction_cases (Aindexed2) (r1 :: r2 :: nil) (S n1 :: I n2 :: nil)
  | addr_strength_reduction_case2: forall r1 r2 n1 n2, addr_strength_reduction_cases (Aindexed2) (r1 :: r2 :: nil) (I n1 :: S n2 :: nil)
  | addr_strength_reduction_case3: forall r1 r2 n1 v2, addr_strength_reduction_cases (Aindexed2) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | addr_strength_reduction_case4: forall r1 r2 v1 n2, addr_strength_reduction_cases (Aindexed2) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | addr_strength_reduction_case5: forall s r1 r2 n1 n2, addr_strength_reduction_cases (Aindexed2shift s) (r1 :: r2 :: nil) (S n1 :: I n2 :: nil)
  | addr_strength_reduction_case6: forall s r1 r2 v1 n2, addr_strength_reduction_cases (Aindexed2shift s) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | addr_strength_reduction_case7: forall n r1 n1, addr_strength_reduction_cases (Aindexed n) (r1 :: nil) (S n1 :: nil)
  | addr_strength_reduction_default: forall (addr: addressing) (args: list reg) (vl: list approx), addr_strength_reduction_cases addr args vl.

Definition addr_strength_reduction_match (addr: addressing) (args: list reg) (vl: list approx) :=
  match addr as zz1, args as zz2, vl as zz3 return addr_strength_reduction_cases zz1 zz2 zz3 with
  | Aindexed2, r1 :: r2 :: nil, S n1 :: I n2 :: nil => addr_strength_reduction_case1 r1 r2 n1 n2
  | Aindexed2, r1 :: r2 :: nil, I n1 :: S n2 :: nil => addr_strength_reduction_case2 r1 r2 n1 n2
  | Aindexed2, r1 :: r2 :: nil, I n1 :: v2 :: nil => addr_strength_reduction_case3 r1 r2 n1 v2
  | Aindexed2, r1 :: r2 :: nil, v1 :: I n2 :: nil => addr_strength_reduction_case4 r1 r2 v1 n2
  | Aindexed2shift s, r1 :: r2 :: nil, S n1 :: I n2 :: nil => addr_strength_reduction_case5 s r1 r2 n1 n2
  | Aindexed2shift s, r1 :: r2 :: nil, v1 :: I n2 :: nil => addr_strength_reduction_case6 s r1 r2 v1 n2
  | Aindexed n, r1 :: nil, S n1 :: nil => addr_strength_reduction_case7 n r1 n1
  | addr, args, vl => addr_strength_reduction_default addr args vl
  end.

Definition addr_strength_reduction (addr: addressing) (args: list reg) (vl: list approx) :=
  match addr_strength_reduction_match addr args vl with
  | addr_strength_reduction_case1 r1 r2 n1 n2 => (* Aindexed2, r1 :: r2 :: nil, S n1 :: I n2 :: nil *) 
      (Ainstack (Int.add n1 n2), nil)
  | addr_strength_reduction_case2 r1 r2 n1 n2 => (* Aindexed2, r1 :: r2 :: nil, I n1 :: S n2 :: nil *) 
      (Ainstack (Int.add n1 n2), nil)
  | addr_strength_reduction_case3 r1 r2 n1 v2 => (* Aindexed2, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      (Aindexed n1, r2 :: nil)
  | addr_strength_reduction_case4 r1 r2 v1 n2 => (* Aindexed2, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Aindexed n2, r1 :: nil)
  | addr_strength_reduction_case5 s r1 r2 n1 n2 => (* Aindexed2shift s, r1 :: r2 :: nil, S n1 :: I n2 :: nil *) 
      (Ainstack (Int.add n1 (eval_static_shift s n2)), nil)
  | addr_strength_reduction_case6 s r1 r2 v1 n2 => (* Aindexed2shift s, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Aindexed (eval_static_shift s n2), r1 :: nil)
  | addr_strength_reduction_case7 n r1 n1 => (* Aindexed n, r1 :: nil, S n1 :: nil *) 
      (Ainstack (Int.add n1 n), nil)
  | addr_strength_reduction_default addr args vl =>
      (addr, args)
  end.


End STRENGTH_REDUCTION.

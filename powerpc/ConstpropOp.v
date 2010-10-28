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
  | S: ident -> int -> approx.
                         (** The value is the address of the given global
                             symbol plus the given integer offset. *)

(** We now define the abstract interpretations of conditions and operators
  over this set of approximations.  For instance, the abstract interpretation
  of the operator [Oaddf] applied to two expressions [a] and [b] is
  [F(Float.add f g)] if [a] and [b] have static approximations [Vfloat f]
  and [Vfloat g] respectively, and [Unknown] otherwise.

  The static approximations are defined by large pattern-matchings over
  the approximations of the results.  We write these matchings in the
  indirect style described in file [Cmconstr] to avoid excessive
  duplication of cases in proofs. *)

(*
Definition eval_static_condition (cond: condition) (vl: list approx) :=
  match cond, vl with
  | Ccomp c, I n1 :: I n2 :: nil => Some(Int.cmp c n1 n2)
  | Ccompu c, I n1 :: I n2 :: nil => Some(Int.cmpu c n1 n2)
  | Ccompimm c n, I n1 :: nil => Some(Int.cmp c n1 n)
  | Ccompuimm c n, I n1 :: nil => Some(Int.cmpu c n1 n)
  | Ccompf c, F n1 :: F n2 :: nil => Some(Float.cmp c n1 n2)
  | Cnotcompf c, F n1 :: F n2 :: nil => Some(negb(Float.cmp c n1 n2))
  | Cmaskzero n, I n1 :: nil => Some(Int.eq (Int.and n1 n) Int.zero)
  | Cmasknotzero n, n1::nil => Some(negb(Int.eq (Int.and n1 n) Int.zero))
  | _, _ => None
  end.
*)

Inductive eval_static_condition_cases: forall (cond: condition) (vl: list approx), Type :=
  | eval_static_condition_case1:
      forall c n1 n2,
      eval_static_condition_cases (Ccomp c) (I n1 :: I n2 :: nil)
  | eval_static_condition_case2:
      forall c n1 n2,
      eval_static_condition_cases (Ccompu c) (I n1 :: I n2 :: nil)
  | eval_static_condition_case3:
      forall c n n1,
      eval_static_condition_cases (Ccompimm c n) (I n1 :: nil)
  | eval_static_condition_case4:
      forall c n n1,
      eval_static_condition_cases (Ccompuimm c n) (I n1 :: nil)
  | eval_static_condition_case5:
      forall c n1 n2,
      eval_static_condition_cases (Ccompf c) (F n1 :: F n2 :: nil)
  | eval_static_condition_case6:
      forall c n1 n2,
      eval_static_condition_cases (Cnotcompf c) (F n1 :: F n2 :: nil)
  | eval_static_condition_case7:
      forall n n1,
      eval_static_condition_cases (Cmaskzero n) (I n1 :: nil)
  | eval_static_condition_case8:
      forall n n1,
      eval_static_condition_cases (Cmasknotzero n) (I n1 :: nil)
  | eval_static_condition_default:
      forall (cond: condition) (vl: list approx),
      eval_static_condition_cases cond vl.

Definition eval_static_condition_match (cond: condition) (vl: list approx) :=
  match cond as z1, vl as z2 return eval_static_condition_cases z1 z2 with
  | Ccomp c, I n1 :: I n2 :: nil =>
      eval_static_condition_case1 c n1 n2
  | Ccompu c, I n1 :: I n2 :: nil =>
      eval_static_condition_case2 c n1 n2
  | Ccompimm c n, I n1 :: nil =>
      eval_static_condition_case3 c n n1
  | Ccompuimm c n, I n1 :: nil =>
      eval_static_condition_case4 c n n1
  | Ccompf c, F n1 :: F n2 :: nil =>
      eval_static_condition_case5 c n1 n2
  | Cnotcompf c, F n1 :: F n2 :: nil =>
      eval_static_condition_case6 c n1 n2
  | Cmaskzero n, I n1 :: nil =>
      eval_static_condition_case7 n n1
  | Cmasknotzero n, I n1 :: nil =>
      eval_static_condition_case8 n n1
  | cond, vl =>
      eval_static_condition_default cond vl
  end.

Definition eval_static_condition (cond: condition) (vl: list approx) :=
  match eval_static_condition_match cond vl with
  | eval_static_condition_case1 c n1 n2 =>
      Some(Int.cmp c n1 n2)
  | eval_static_condition_case2 c n1 n2 =>
      Some(Int.cmpu c n1 n2)
  | eval_static_condition_case3 c n n1 =>
      Some(Int.cmp c n1 n)
  | eval_static_condition_case4 c n n1 =>
      Some(Int.cmpu c n1 n)
  | eval_static_condition_case5 c n1 n2 =>
      Some(Float.cmp c n1 n2)
  | eval_static_condition_case6 c n1 n2 =>
      Some(negb(Float.cmp c n1 n2))
  | eval_static_condition_case7 n n1 =>
      Some(Int.eq (Int.and n1 n) Int.zero)
  | eval_static_condition_case8 n n1 =>
      Some(negb(Int.eq (Int.and n1 n) Int.zero))
  | eval_static_condition_default cond vl =>
      None
  end.

(*
Definition eval_static_operation (op: operation) (vl: list approx) :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Ofloatconst n, nil => F n
  | Oaddrsymbol s n, nil => S s n
  | Ocast8signed, I n1 :: nil => I(Int.sign_ext 8 n)
  | Ocast8unsigned, I n1 :: nil => I(Int.zero_ext 8 n)
  | Ocast16signed, I n1 :: nil => I(Int.sign_ext 16 n)
  | Ocast16unsigned, I n1 :: nil => I(Int.zero_ext 16 n)
  | Oadd, I n1 :: I n2 :: nil => I(Int.add n1 n2)
  | Oadd, S s1 n1 :: I n2 :: nil => S s1 (Int.add n1 n2)
  | Oaddimm n, I n1 :: nil => I (Int.add n1 n)
  | Oaddimm n, S s1 n1 :: nil => S s1 (Int.add n1 n)
  | Osub, I n1 :: I n2 :: nil => I(Int.sub n1 n2)
  | Osub, S s1 n1 :: I n2 :: nil => S s1 (Int.sub n1 n2)
  | Osubimm n, I n1 :: nil => I (Int.sub n n1)
  | Omul, I n1 :: I n2 :: nil => I(Int.mul n1 n2)
  | Omulimm n, I n1 :: nil => I(Int.mul n1 n)
  | Odiv, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.divs n1 n2)
  | Odivu, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.divu n1 n2)
  | Oand, I n1 :: I n2 :: nil => I(Int.and n1 n2)
  | Oandimm n, I n1 :: nil => I(Int.and n1 n)
  | Oor, I n1 :: I n2 :: nil => I(Int.or n1 n2)
  | Oorimm n, I n1 :: nil => I(Int.or n1 n)
  | Oxor, I n1 :: I n2 :: nil => I(Int.xor n1 n2)
  | Oxorimm n, I n1 :: nil => I(Int.xor n1 n)
  | Onand, I n1 :: I n2 :: nil => I(Int.xor (Int.and n1 n2) Int.mone)
  | Onor, I n1 :: I n2 :: nil => I(Int.xor (Int.or n1 n2) Int.mone)
  | Onxor, I n1 :: I n2 :: nil => I(Int.xor (Int.xor n1 n2) Int.mone)
  | Oshl, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shl n1 n2) else Unknown
  | Oshr, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shr n1 n2) else Unknown
  | Oshrimm n, I n1 :: nil => if Int.ltu n Int.iwordsize then I(Int.shr n1 n) else Unknown
  | Oshrximm n, I n1 :: nil => if Int.ltu n Int.iwordsize then I(Int.shrx n1 n) else Unknown
  | Oshru, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shru n1 n2) else Unknown
  | Orolm amount mask, I n1 :: nil => I(Int.rolm n1 amount mask)
  | Onegf, F n1 :: nil => F(Float.neg n1)
  | Oabsf, F n1 :: nil => F(Float.abs n1)
  | Oaddf, F n1 :: F n2 :: nil => F(Float.add n1 n2)
  | Osubf, F n1 :: F n2 :: nil => F(Float.sub n1 n2)
  | Omulf, F n1 :: F n2 :: nil => F(Float.mul n1 n2)
  | Odivf, F n1 :: F n2 :: nil => F(Float.div n1 n2)
  | Omuladdf, F n1 :: F n2 :: F n3 :: nil => F(Float.add (Float.mul n1 n2) n3)
  | Omulsubf, F n1 :: F n2 :: F n3 :: nil => F(Float.sub (Float.mul n1 n2) n3)
  | Osingleoffloat, F n1 :: nil => F(Float.singleoffloat n1)
  | Ointoffloat, F n1 :: nil => match Float.intoffloat n1 with Some x => I x | None => Unknown end
  | Ofloatofwords, I n1 :: I n2 :: nil => F(Float.from_words n1 n2)
  | Ocmp c, vl =>
      match eval_static_condition c vl with
      | None => Unknown
      | Some b => I(if b then Int.one else Int.zero)
      end
  | _, _ => Unknown
  end.
*)

Inductive eval_static_operation_cases: forall (op: operation) (vl: list approx), Type :=
  | eval_static_operation_case1:
      forall v1,
      eval_static_operation_cases (Omove) (v1::nil)
  | eval_static_operation_case2:
      forall n,
      eval_static_operation_cases (Ointconst n) (nil)
  | eval_static_operation_case3:
      forall n,
      eval_static_operation_cases (Ofloatconst n) (nil)
  | eval_static_operation_case4:
      forall s n,
      eval_static_operation_cases (Oaddrsymbol s n) (nil)
  | eval_static_operation_case6:
      forall n1,
      eval_static_operation_cases (Ocast8signed) (I n1 :: nil)
  | eval_static_operation_case7:
      forall n1,
      eval_static_operation_cases (Ocast16signed) (I n1 :: nil)
  | eval_static_operation_case8:
      forall n1 n2,
      eval_static_operation_cases (Oadd) (I n1 :: I n2 :: nil)
  | eval_static_operation_case9:
      forall s1 n1 n2,
      eval_static_operation_cases (Oadd) (S s1 n1 :: I n2 :: nil)
  | eval_static_operation_case11:
      forall n n1,
      eval_static_operation_cases (Oaddimm n) (I n1 :: nil)
  | eval_static_operation_case12:
      forall n s1 n1,
      eval_static_operation_cases (Oaddimm n) (S s1 n1 :: nil)
  | eval_static_operation_case13:
      forall n1 n2,
      eval_static_operation_cases (Osub) (I n1 :: I n2 :: nil)
  | eval_static_operation_case14:
      forall s1 n1 n2,
      eval_static_operation_cases (Osub) (S s1 n1 :: I n2 :: nil)
  | eval_static_operation_case15:
      forall n n1,
      eval_static_operation_cases (Osubimm n) (I n1 :: nil)
  | eval_static_operation_case16:
      forall n1 n2,
      eval_static_operation_cases (Omul) (I n1 :: I n2 :: nil)
  | eval_static_operation_case17:
      forall n n1,
      eval_static_operation_cases (Omulimm n) (I n1 :: nil)
  | eval_static_operation_case18:
      forall n1 n2,
      eval_static_operation_cases (Odiv) (I n1 :: I n2 :: nil)
  | eval_static_operation_case19:
      forall n1 n2,
      eval_static_operation_cases (Odivu) (I n1 :: I n2 :: nil)
  | eval_static_operation_case20:
      forall n1 n2,
      eval_static_operation_cases (Oand) (I n1 :: I n2 :: nil)
  | eval_static_operation_case21:
      forall n n1,
      eval_static_operation_cases (Oandimm n) (I n1 :: nil)
  | eval_static_operation_case22:
      forall n1 n2,
      eval_static_operation_cases (Oor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case23:
      forall n n1,
      eval_static_operation_cases (Oorimm n) (I n1 :: nil)
  | eval_static_operation_case24:
      forall n1 n2,
      eval_static_operation_cases (Oxor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case25:
      forall n n1,
      eval_static_operation_cases (Oxorimm n) (I n1 :: nil)
  | eval_static_operation_case26:
      forall n1 n2,
      eval_static_operation_cases (Onand) (I n1 :: I n2 :: nil)
  | eval_static_operation_case27:
      forall n1 n2,
      eval_static_operation_cases (Onor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case28:
      forall n1 n2,
      eval_static_operation_cases (Onxor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case29:
      forall n1 n2,
      eval_static_operation_cases (Oshl) (I n1 :: I n2 :: nil)
  | eval_static_operation_case30:
      forall n1 n2,
      eval_static_operation_cases (Oshr) (I n1 :: I n2 :: nil)
  | eval_static_operation_case31:
      forall n n1,
      eval_static_operation_cases (Oshrimm n) (I n1 :: nil)
  | eval_static_operation_case32:
      forall n n1,
      eval_static_operation_cases (Oshrximm n) (I n1 :: nil)
  | eval_static_operation_case33:
      forall n1 n2,
      eval_static_operation_cases (Oshru) (I n1 :: I n2 :: nil)
  | eval_static_operation_case34:
      forall amount mask n1,
      eval_static_operation_cases (Orolm amount mask) (I n1 :: nil)
  | eval_static_operation_case35:
      forall n1,
      eval_static_operation_cases (Onegf) (F n1 :: nil)
  | eval_static_operation_case36:
      forall n1,
      eval_static_operation_cases (Oabsf) (F n1 :: nil)
  | eval_static_operation_case37:
      forall n1 n2,
      eval_static_operation_cases (Oaddf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case38:
      forall n1 n2,
      eval_static_operation_cases (Osubf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case39:
      forall n1 n2,
      eval_static_operation_cases (Omulf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case40:
      forall n1 n2,
      eval_static_operation_cases (Odivf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case41:
      forall n1 n2 n3,
      eval_static_operation_cases (Omuladdf) (F n1 :: F n2 :: F n3 :: nil)
  | eval_static_operation_case42:
      forall n1 n2 n3,
      eval_static_operation_cases (Omulsubf) (F n1 :: F n2 :: F n3 :: nil)
  | eval_static_operation_case43:
      forall n1,
      eval_static_operation_cases (Osingleoffloat) (F n1 :: nil)
  | eval_static_operation_case44:
      forall n1,
      eval_static_operation_cases (Ointoffloat) (F n1 :: nil)
  | eval_static_operation_case45:
      forall n1 n2,
      eval_static_operation_cases (Ofloatofwords) (I n1 :: I n2 :: nil)
  | eval_static_operation_case47:
      forall c vl,
      eval_static_operation_cases (Ocmp c) (vl)
  | eval_static_operation_case48:
      forall n1,
      eval_static_operation_cases (Ocast8unsigned) (I n1 :: nil)
  | eval_static_operation_case49:
      forall n1,
      eval_static_operation_cases (Ocast16unsigned) (I n1 :: nil)
  | eval_static_operation_default:
      forall (op: operation) (vl: list approx),
      eval_static_operation_cases op vl.

Definition eval_static_operation_match (op: operation) (vl: list approx) :=
  match op as z1, vl as z2 return eval_static_operation_cases z1 z2 with
  | Omove, v1::nil =>
      eval_static_operation_case1 v1
  | Ointconst n, nil =>
      eval_static_operation_case2 n
  | Ofloatconst n, nil =>
      eval_static_operation_case3 n
  | Oaddrsymbol s n, nil =>
      eval_static_operation_case4 s n
  | Ocast8signed, I n1 :: nil =>
      eval_static_operation_case6 n1
  | Ocast16signed, I n1 :: nil =>
      eval_static_operation_case7 n1
  | Oadd, I n1 :: I n2 :: nil =>
      eval_static_operation_case8 n1 n2
  | Oadd, S s1 n1 :: I n2 :: nil =>
      eval_static_operation_case9 s1 n1 n2
  | Oaddimm n, I n1 :: nil =>
      eval_static_operation_case11 n n1
  | Oaddimm n, S s1 n1 :: nil =>
      eval_static_operation_case12 n s1 n1
  | Osub, I n1 :: I n2 :: nil =>
      eval_static_operation_case13 n1 n2
  | Osub, S s1 n1 :: I n2 :: nil =>
      eval_static_operation_case14 s1 n1 n2
  | Osubimm n, I n1 :: nil =>
      eval_static_operation_case15 n n1
  | Omul, I n1 :: I n2 :: nil =>
      eval_static_operation_case16 n1 n2
  | Omulimm n, I n1 :: nil =>
      eval_static_operation_case17 n n1
  | Odiv, I n1 :: I n2 :: nil =>
      eval_static_operation_case18 n1 n2
  | Odivu, I n1 :: I n2 :: nil =>
      eval_static_operation_case19 n1 n2
  | Oand, I n1 :: I n2 :: nil =>
      eval_static_operation_case20 n1 n2
  | Oandimm n, I n1 :: nil =>
      eval_static_operation_case21 n n1
  | Oor, I n1 :: I n2 :: nil =>
      eval_static_operation_case22 n1 n2
  | Oorimm n, I n1 :: nil =>
      eval_static_operation_case23 n n1
  | Oxor, I n1 :: I n2 :: nil =>
      eval_static_operation_case24 n1 n2
  | Oxorimm n, I n1 :: nil =>
      eval_static_operation_case25 n n1
  | Onand, I n1 :: I n2 :: nil =>
      eval_static_operation_case26 n1 n2
  | Onor, I n1 :: I n2 :: nil =>
      eval_static_operation_case27 n1 n2
  | Onxor, I n1 :: I n2 :: nil =>
      eval_static_operation_case28 n1 n2
  | Oshl, I n1 :: I n2 :: nil =>
      eval_static_operation_case29 n1 n2
  | Oshr, I n1 :: I n2 :: nil =>
      eval_static_operation_case30 n1 n2
  | Oshrimm n, I n1 :: nil =>
      eval_static_operation_case31 n n1
  | Oshrximm n, I n1 :: nil =>
      eval_static_operation_case32 n n1
  | Oshru, I n1 :: I n2 :: nil =>
      eval_static_operation_case33 n1 n2
  | Orolm amount mask, I n1 :: nil =>
      eval_static_operation_case34 amount mask n1
  | Onegf, F n1 :: nil =>
      eval_static_operation_case35 n1
  | Oabsf, F n1 :: nil =>
      eval_static_operation_case36 n1
  | Oaddf, F n1 :: F n2 :: nil =>
      eval_static_operation_case37 n1 n2
  | Osubf, F n1 :: F n2 :: nil =>
      eval_static_operation_case38 n1 n2
  | Omulf, F n1 :: F n2 :: nil =>
      eval_static_operation_case39 n1 n2
  | Odivf, F n1 :: F n2 :: nil =>
      eval_static_operation_case40 n1 n2
  | Omuladdf, F n1 :: F n2 :: F n3 :: nil =>
      eval_static_operation_case41 n1 n2 n3
  | Omulsubf, F n1 :: F n2 :: F n3 :: nil =>
      eval_static_operation_case42 n1 n2 n3
  | Osingleoffloat, F n1 :: nil =>
      eval_static_operation_case43 n1
  | Ointoffloat, F n1 :: nil =>
      eval_static_operation_case44 n1
  | Ofloatofwords, I n1 :: I n2 :: nil =>
      eval_static_operation_case45 n1 n2
  | Ocmp c, vl =>
      eval_static_operation_case47 c vl
  | Ocast8unsigned, I n1 :: nil =>
      eval_static_operation_case48 n1
  | Ocast16unsigned, I n1 :: nil =>
      eval_static_operation_case49 n1
  | op, vl =>
      eval_static_operation_default op vl
  end.

Definition eval_static_operation (op: operation) (vl: list approx) :=
  match eval_static_operation_match op vl with
  | eval_static_operation_case1 v1 =>
      v1
  | eval_static_operation_case2 n =>
      I n
  | eval_static_operation_case3 n =>
      F n
  | eval_static_operation_case4 s n =>
      S s n
  | eval_static_operation_case6 n1 =>
      I(Int.sign_ext 8 n1)
  | eval_static_operation_case7 n1 =>
      I(Int.sign_ext 16 n1)
  | eval_static_operation_case8 n1 n2 =>
      I(Int.add n1 n2)
  | eval_static_operation_case9 s1 n1 n2 =>
      S s1 (Int.add n1 n2)
  | eval_static_operation_case11 n n1 =>
      I (Int.add n1 n)
  | eval_static_operation_case12 n s1 n1 =>
      S s1 (Int.add n1 n)
  | eval_static_operation_case13 n1 n2 =>
      I(Int.sub n1 n2)
  | eval_static_operation_case14 s1 n1 n2 =>
      S s1 (Int.sub n1 n2)
  | eval_static_operation_case15 n n1 =>
      I (Int.sub n n1)
  | eval_static_operation_case16 n1 n2 =>
      I(Int.mul n1 n2)
  | eval_static_operation_case17 n n1 =>
      I(Int.mul n1 n)
  | eval_static_operation_case18 n1 n2 =>
      if Int.eq n2 Int.zero then Unknown else I(Int.divs n1 n2)
  | eval_static_operation_case19 n1 n2 =>
      if Int.eq n2 Int.zero then Unknown else I(Int.divu n1 n2)
  | eval_static_operation_case20 n1 n2 =>
      I(Int.and n1 n2)
  | eval_static_operation_case21 n n1 =>
      I(Int.and n1 n)
  | eval_static_operation_case22 n1 n2 =>
      I(Int.or n1 n2)
  | eval_static_operation_case23 n n1 =>
      I(Int.or n1 n)
  | eval_static_operation_case24 n1 n2 =>
      I(Int.xor n1 n2)
  | eval_static_operation_case25 n n1 =>
      I(Int.xor n1 n)
  | eval_static_operation_case26 n1 n2 =>
      I(Int.xor (Int.and n1 n2) Int.mone)
  | eval_static_operation_case27 n1 n2 =>
      I(Int.xor (Int.or n1 n2) Int.mone)
  | eval_static_operation_case28 n1 n2 =>
      I(Int.xor (Int.xor n1 n2) Int.mone)
  | eval_static_operation_case29 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shl n1 n2) else Unknown
  | eval_static_operation_case30 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shr n1 n2) else Unknown
  | eval_static_operation_case31 n n1 =>
      if Int.ltu n Int.iwordsize then I(Int.shr n1 n) else Unknown
  | eval_static_operation_case32 n n1 =>
      if Int.ltu n Int.iwordsize then I(Int.shrx n1 n) else Unknown
  | eval_static_operation_case33 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shru n1 n2) else Unknown
  | eval_static_operation_case34 amount mask n1 =>
      I(Int.rolm n1 amount mask)
  | eval_static_operation_case35 n1 =>
      F(Float.neg n1)
  | eval_static_operation_case36 n1 =>
      F(Float.abs n1)
  | eval_static_operation_case37 n1 n2 =>
      F(Float.add n1 n2)
  | eval_static_operation_case38 n1 n2 =>
      F(Float.sub n1 n2)
  | eval_static_operation_case39 n1 n2 =>
      F(Float.mul n1 n2)
  | eval_static_operation_case40 n1 n2 =>
      F(Float.div n1 n2)
  | eval_static_operation_case41 n1 n2 n3 =>
      F(Float.add (Float.mul n1 n2) n3)
  | eval_static_operation_case42 n1 n2 n3 =>
      F(Float.sub (Float.mul n1 n2) n3)
  | eval_static_operation_case43 n1 =>
      F(Float.singleoffloat n1)
  | eval_static_operation_case44 n1 =>
      match Float.intoffloat n1 with Some x => I x | None => Unknown end
  | eval_static_operation_case45 n1 n2 =>
      F(Float.from_words n1 n2)
  | eval_static_operation_case47 c vl =>
      match eval_static_condition c vl with
      | None => Unknown
      | Some b => I(if b then Int.one else Int.zero)
      end
  | eval_static_operation_case48 n1 =>
      I(Int.zero_ext 8 n1)
  | eval_static_operation_case49 n1 =>
      I(Int.zero_ext 16 n1)
  | eval_static_operation_default op vl =>
      Unknown
  end.

(** * Operator strength reduction *)

(** We now define auxiliary functions for strength reduction of
  operators and addressing modes: replacing an operator with a cheaper
  one if some of its arguments are statically known.  These are again
  large pattern-matchings expressed in indirect style. *)

Section STRENGTH_REDUCTION.

Variable app: reg -> approx.

Definition intval (r: reg) : option int :=
  match app r with I n => Some n | _ => None end.

Inductive cond_strength_reduction_cases: condition -> list reg -> Type :=
  | csr_case1:
      forall c r1 r2,
      cond_strength_reduction_cases (Ccomp c) (r1 :: r2 :: nil)
  | csr_case2:
      forall c r1 r2,
      cond_strength_reduction_cases (Ccompu c) (r1 :: r2 :: nil)
  | csr_default:
      forall c rl,
      cond_strength_reduction_cases c rl.

Definition cond_strength_reduction_match (cond: condition) (rl: list reg) :=
  match cond as x, rl as y return cond_strength_reduction_cases x y with
  | Ccomp c, r1 :: r2 :: nil =>
      csr_case1 c r1 r2
  | Ccompu c, r1 :: r2 :: nil =>
      csr_case2 c r1 r2
  | cond, rl =>
      csr_default cond rl
  end.

Definition cond_strength_reduction
              (cond: condition) (args: list reg) : condition * list reg :=
  match cond_strength_reduction_match cond args with
  | csr_case1 c r1 r2 =>
      match intval r1, intval r2 with
      | Some n, _ =>
          (Ccompimm (swap_comparison c) n, r2 :: nil)
      | _, Some n =>
          (Ccompimm c n, r1 :: nil)
      | _, _ =>
          (cond, args)
      end
  | csr_case2 c r1 r2 =>
      match intval r1, intval r2 with
      | Some n, _ =>
          (Ccompuimm (swap_comparison c) n, r2 :: nil)
      | _, Some n =>
          (Ccompuimm c n, r1 :: nil)
      | _, _ =>
          (cond, args)
      end
  | csr_default cond args =>
      (cond, args)
  end.

Definition make_addimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oaddimm n, r :: nil).

Definition make_shlimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Orolm n (Int.shl Int.mone n), r :: nil).

Definition make_shrimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oshrimm n, r :: nil).

Definition make_shruimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Orolm (Int.sub Int.iwordsize n) (Int.shru Int.mone n), r :: nil).

Definition make_mulimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then
    (Ointconst Int.zero, nil)
  else if Int.eq n Int.one then
    (Omove, r :: nil)
  else
    match Int.is_power2 n with
    | Some l => make_shlimm l r
    | None => (Omulimm n, r :: nil)
    end.

Definition make_andimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Ointconst Int.zero, nil)
  else if Int.eq n Int.mone then (Omove, r :: nil)
  else (Oandimm n, r :: nil).

Definition make_orimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then (Omove, r :: nil)
  else if Int.eq n Int.mone then (Ointconst Int.mone, nil)
  else (Oorimm n, r :: nil).

Definition make_xorimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oxorimm n, r :: nil).

Inductive op_strength_reduction_cases: operation -> list reg -> Type :=
  | op_strength_reduction_case1:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Oadd (r1 :: r2 :: nil)
  | op_strength_reduction_case2:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Osub (r1 :: r2 :: nil)
  | op_strength_reduction_case3:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Omul (r1 :: r2 :: nil)
  | op_strength_reduction_case4:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Odiv (r1 :: r2 :: nil)
  | op_strength_reduction_case5:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Odivu (r1 :: r2 :: nil)
  | op_strength_reduction_case6:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Oand (r1 :: r2 :: nil)
  | op_strength_reduction_case7:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Oor (r1 :: r2 :: nil)
  | op_strength_reduction_case8:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Oxor (r1 :: r2 :: nil)
  | op_strength_reduction_case9:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Oshl (r1 :: r2 :: nil)
  | op_strength_reduction_case10:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Oshr (r1 :: r2 :: nil)
  | op_strength_reduction_case11:
      forall (r1: reg) (r2: reg),
      op_strength_reduction_cases Oshru (r1 :: r2 :: nil)
  | op_strength_reduction_case12:
      forall (c: condition) (rl: list reg),
      op_strength_reduction_cases (Ocmp c) rl
  | op_strength_reduction_default:
      forall (op: operation) (args: list reg),
      op_strength_reduction_cases op args.

Definition op_strength_reduction_match (op: operation) (args: list reg) :=
  match op as z1, args as z2 return op_strength_reduction_cases z1 z2 with
  | Oadd, r1 :: r2 :: nil =>
      op_strength_reduction_case1 r1 r2
  | Osub, r1 :: r2 :: nil =>
      op_strength_reduction_case2 r1 r2
  | Omul, r1 :: r2 :: nil =>
      op_strength_reduction_case3 r1 r2
  | Odiv, r1 :: r2 :: nil =>
      op_strength_reduction_case4 r1 r2
  | Odivu, r1 :: r2 :: nil =>
      op_strength_reduction_case5 r1 r2
  | Oand, r1 :: r2 :: nil =>
      op_strength_reduction_case6 r1 r2
  | Oor, r1 :: r2 :: nil =>
      op_strength_reduction_case7 r1 r2
  | Oxor, r1 :: r2 :: nil =>
      op_strength_reduction_case8 r1 r2
  | Oshl, r1 :: r2 :: nil =>
      op_strength_reduction_case9 r1 r2
  | Oshr, r1 :: r2 :: nil =>
      op_strength_reduction_case10 r1 r2
  | Oshru, r1 :: r2 :: nil =>
      op_strength_reduction_case11 r1 r2
  | Ocmp c, rl =>
      op_strength_reduction_case12 c rl
  | op, args =>
      op_strength_reduction_default op args
  end.

Definition op_strength_reduction (op: operation) (args: list reg) :=
  match op_strength_reduction_match op args with
  | op_strength_reduction_case1 r1 r2 => (* Oadd *)
      match intval r1, intval r2 with
      | Some n, _ => make_addimm n r2
      | _, Some n => make_addimm n r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case2 r1 r2 => (* Osub *)
      match intval r1, intval r2 with
      | Some n, _ => (Osubimm n, r2 :: nil)
      | _, Some n => make_addimm (Int.neg n) r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case3 r1 r2 => (* Omul *)
      match intval r1, intval r2 with
      | Some n, _ => make_mulimm n r2
      | _, Some n => make_mulimm n r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case4 r1 r2 => (* Odiv *)
      match intval r2 with
      | Some n =>
          match Int.is_power2 n with
          | Some l => (Oshrximm l, r1 :: nil)
          | None   => (op, args)
          end
      | None =>
          (op, args)
      end
  | op_strength_reduction_case5 r1 r2 => (* Odivu *)
      match intval r2 with
      | Some n =>
          match Int.is_power2 n with
          | Some l => make_shruimm l r1
          | None   => (op, args)
          end
      | None =>
          (op, args)
      end
  | op_strength_reduction_case6 r1 r2 => (* Oand *)
      match intval r1, intval r2 with
      | Some n, _ => make_andimm n r2
      | _, Some n => make_andimm n r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case7 r1 r2 => (* Oor *)
      match intval r1, intval r2 with
      | Some n, _ => make_orimm n r2
      | _, Some n => make_orimm n r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case8 r1 r2 => (* Oxor *)
      match intval r1, intval r2 with
      | Some n, _ => make_xorimm n r2
      | _, Some n => make_xorimm n r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case9 r1 r2 => (* Oshl *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shlimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case10 r1 r2 => (* Oshr *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shrimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case11 r1 r2 => (* Oshru *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shruimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case12 c args => (* Ocmp *)
      let (c', args') := cond_strength_reduction c args in
      (Ocmp c', args')
  | op_strength_reduction_default op args => (* default *)
      (op, args)
  end.

Inductive addr_strength_reduction_cases: forall (addr: addressing) (args: list reg), Type :=
  | addr_strength_reduction_case1:
      forall (r1: reg) (r2: reg),
      addr_strength_reduction_cases (Aindexed2) (r1 :: r2 :: nil)
  | addr_strength_reduction_case2:
      forall (symb: ident) (ofs: int) (r1: reg),
      addr_strength_reduction_cases (Abased symb ofs) (r1 :: nil)
  | addr_strength_reduction_case3:
      forall n r1,
      addr_strength_reduction_cases (Aindexed n) (r1 :: nil)
  | addr_strength_reduction_default:
      forall (addr: addressing) (args: list reg),
      addr_strength_reduction_cases addr args.

Definition addr_strength_reduction_match (addr: addressing) (args: list reg) :=
  match addr as z1, args as z2 return addr_strength_reduction_cases z1 z2 with
  | Aindexed2, r1 :: r2 :: nil =>
      addr_strength_reduction_case1 r1 r2
  | Abased symb ofs, r1 :: nil =>
      addr_strength_reduction_case2 symb ofs r1
  | Aindexed n, r1 :: nil =>
      addr_strength_reduction_case3 n r1
  | addr, args =>
      addr_strength_reduction_default addr args
  end.

Definition addr_strength_reduction (addr: addressing) (args: list reg) :=
  match addr_strength_reduction_match addr args with
  | addr_strength_reduction_case1 r1 r2 => (* Aindexed2 *)
      match app r1, app r2 with
      | S symb n1, I n2 => (Aglobal symb (Int.add n1 n2), nil)
      | S symb n1, _ => (Abased symb n1, r2 :: nil)
      | I n1, S symb n2 => (Aglobal symb (Int.add n1 n2), nil)
      | I n1, _ => (Aindexed n1, r2 :: nil)
      | _, S symb n2 => (Abased symb n2, r1 :: nil)
      | _, I n2 => (Aindexed n2, r1 :: nil)
      | _, _ => (addr, args)
      end
  | addr_strength_reduction_case2 symb ofs r1 => (* Abased *)
      match intval r1 with
      | Some n => (Aglobal symb (Int.add ofs n), nil)
      | _ => (addr, args)
      end
  | addr_strength_reduction_case3 n r1 => (* Aindexed *)
      match app r1 with
      | S symb ofs => (Aglobal symb (Int.add ofs n), nil)
      | _ => (addr, args)
      end
  | addr_strength_reduction_default addr args => (* default *)
      (addr, args)
  end.

End STRENGTH_REDUCTION.

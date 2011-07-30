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
  [F(Float.add f g)] if [a] and [b] have static approximations [F f]
  and [F g] respectively, and [Unknown] otherwise.

  The static approximations are defined by large pattern-matchings over
  the approximations of the results.  We write these matchings in the
  indirect style described in file [Selection] to avoid excessive
  duplication of cases in proofs. *)

(*
Definition eval_static_condition (cond: condition) (vl: list approx) :=
  match cond, vl with
  | Ccomp c, I n1 :: I n2 :: nil => Some(Int.cmp c n1 n2)
  | Ccompu c, I n1 :: I n2 :: nil => Some(Int.cmpu c n1 n2)
  | Ccompshift c s, I n1 :: I n2 :: nil => Some(Int.cmp c n1 (eval_shift s n2))
  | Ccompushift c s, I n1 :: I n2 :: nil => Some(Int.cmpu c n1 (eval_shift s n2))
  | Ccompimm c n, I n1 :: nil => Some(Int.cmp c n1 n)
  | Ccompuimm c n, I n1 :: nil => Some(Int.cmpu c n1 n)
  | Ccompf c, F n1 :: F n2 :: nil => Some(Float.cmp c n1 n2)
  | Cnotcompf c, F n1 :: F n2 :: nil => Some(negb(Float.cmp c n1 n2))
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
      forall c s n1 n2,
      eval_static_condition_cases (Ccompshift c s) (I n1 :: I n2 :: nil)
  | eval_static_condition_case4:
      forall c s n1 n2,
      eval_static_condition_cases (Ccompushift c s) (I n1 :: I n2 :: nil)
  | eval_static_condition_case5:
      forall c n n1,
      eval_static_condition_cases (Ccompimm c n) (I n1 :: nil)
  | eval_static_condition_case6:
      forall c n n1,
      eval_static_condition_cases (Ccompuimm c n) (I n1 :: nil)
  | eval_static_condition_case7:
      forall c n1 n2,
      eval_static_condition_cases (Ccompf c) (F n1 :: F n2 :: nil)
  | eval_static_condition_case8:
      forall c n1 n2,
      eval_static_condition_cases (Cnotcompf c) (F n1 :: F n2 :: nil)
  | eval_static_condition_default:
      forall (cond: condition) (vl: list approx),
      eval_static_condition_cases cond vl.

Definition eval_static_condition_match (cond: condition) (vl: list approx) :=
  match cond as z1, vl as z2 return eval_static_condition_cases z1 z2 with
  | Ccomp c, I n1 :: I n2 :: nil =>
      eval_static_condition_case1 c n1 n2
  | Ccompu c, I n1 :: I n2 :: nil =>
      eval_static_condition_case2 c n1 n2
  | Ccompshift c s, I n1 :: I n2 :: nil =>
      eval_static_condition_case3 c s n1 n2
  | Ccompushift c s, I n1 :: I n2 :: nil =>
      eval_static_condition_case4 c s n1 n2
  | Ccompimm c n, I n1 :: nil =>
      eval_static_condition_case5 c n n1
  | Ccompuimm c n, I n1 :: nil =>
      eval_static_condition_case6 c n n1
  | Ccompf c, F n1 :: F n2 :: nil =>
      eval_static_condition_case7 c n1 n2
  | Cnotcompf c, F n1 :: F n2 :: nil =>
      eval_static_condition_case8 c n1 n2
  | cond, vl =>
      eval_static_condition_default cond vl
  end.

Definition eval_static_condition (cond: condition) (vl: list approx) :=
  match eval_static_condition_match cond vl with
  | eval_static_condition_case1 c n1 n2 =>
      Some(Int.cmp c n1 n2)
  | eval_static_condition_case2 c n1 n2 =>
      Some(Int.cmpu c n1 n2)
  | eval_static_condition_case3 c s n1 n2 =>
      Some(Int.cmp c n1 (eval_shift s n2))
  | eval_static_condition_case4 c s n1 n2 =>
      Some(Int.cmpu c n1 (eval_shift s n2))
  | eval_static_condition_case5 c n n1 =>
      Some(Int.cmp c n1 n)
  | eval_static_condition_case6 c n n1 =>
      Some(Int.cmpu c n1 n)
  | eval_static_condition_case7 c n1 n2 =>
      Some(Float.cmp c n1 n2)
  | eval_static_condition_case8 c n1 n2 =>
      Some(negb(Float.cmp c n1 n2))
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
  | Oaddshift s, I n1 :: I n2 :: nil => I(Int.add n1 (eval_shift s n2))
  | Oadd, S s1 n1 :: I n2 :: nil => S s1 (Int.add n1 n2)
  | Oaddshift s, S s1 n1 :: I n2 :: nil => S s1 (Int.add n1 (eval_shift s n2))
  | Oaddimm n, I n1 :: nil => I (Int.add n1 n)
  | Oaddimm n, S s1 n1 :: nil => S s1 (Int.add n1 n)
  | Osub, I n1 :: I n2 :: nil => I(Int.sub n1 n2)
  | Osubshift s, I n1 :: I n2 :: nil => I(Int.sub n1 (eval_shift s n2))
  | Osub, S s1 n1 :: I n2 :: nil => S s1 (Int.sub n1 n2)
  | Osubshift s, S s1 n1 :: I n2 :: nil => S s1 (Int.sub n1 (eval_shift s n2))
  | Orsubshift s, I n1 :: I n2 :: nil => I(Int.sub (eval_shift s n2) n1)
  | Orsubimm n, I n1 :: nil => I (Int.sub n n1)
  | Omul, I n1 :: I n2 :: nil => I(Int.mul n1 n2)
  | Odiv, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.divs n1 n2)
  | Odivu, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.divu n1 n2)
  | Oand, I n1 :: I n2 :: nil => I(Int.and n1 n2)
  | Oandshift s, I n1 :: I n2 :: nil => I(Int.and n1 (eval_shift s n2))
  | Oandimm n, I n1 :: nil => I(Int.and n1 n)
  | Oor, I n1 :: I n2 :: nil => I(Int.or n1 n2)
  | Oorshift s, I n1 :: I n2 :: nil => I(Int.or n1 (eval_shift s n2))
  | Oorimm n, I n1 :: nil => I(Int.or n1 n)
  | Oxor, I n1 :: I n2 :: nil => I(Int.xor n1 n2)
  | Oxorshift s, I n1 :: I n2 :: nil => I(Int.xor n1 (eval_shift s n2))
  | Oxorimm n, I n1 :: nil => I(Int.xor n1 n)
  | Obic, I n1 :: I n2 :: nil => I(Int.and n1 (Int.not n2))
  | Obicshift s, I n1 :: I n2 :: nil => I(Int.and n1 (Int.not (eval_shift s n2)))
  | Onot, I n1 :: nil => I(Int.not n1)
  | Onotshift s, I n1 :: nil => I(Int.not (eval_shift s n1))
  | Oshl, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shl n1 n2) else Unknown
  | Oshr, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shr n1 n2) else Unknown
  | Oshru, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shru n1 n2) else Unknown
  | Oshift s, I n1 :: nil => I(eval_shift s n1)
  | Onegf, F n1 :: nil => F(Float.neg n1)
  | Oabsf, F n1 :: nil => F(Float.abs n1)
  | Oaddf, F n1 :: F n2 :: nil => F(Float.add n1 n2)
  | Osubf, F n1 :: F n2 :: nil => F(Float.sub n1 n2)
  | Omulf, F n1 :: F n2 :: nil => F(Float.mul n1 n2)
  | Odivf, F n1 :: F n2 :: nil => F(Float.div n1 n2)
  | Osingleoffloat, F n1 :: nil => F(Float.singleoffloat n1)
  | Ointoffloat, F n1 :: nil =>  match Float.intoffloat n1 with Some x => I x | None => Unknown end
  | Ofloatofint, I n1 :: nil => F(Float.floatofint n1)
  | Ofloatofintu, I n1 :: nil => F(Float.floatofintu n1)
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
  | eval_static_operation_case5:
      forall n1,
      eval_static_operation_cases (Ocast8signed) (I n1 :: nil)
  | eval_static_operation_case6:
      forall n1,
      eval_static_operation_cases (Ocast8unsigned) (I n1 :: nil)
  | eval_static_operation_case7:
      forall n1,
      eval_static_operation_cases (Ocast16signed) (I n1 :: nil)
  | eval_static_operation_case8:
      forall n1,
      eval_static_operation_cases (Ocast16unsigned) (I n1 :: nil)
  | eval_static_operation_case9:
      forall n1 n2,
      eval_static_operation_cases (Oadd) (I n1 :: I n2 :: nil)
  | eval_static_operation_case10:
      forall s n1 n2,
      eval_static_operation_cases (Oaddshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case11:
      forall s1 n1 n2,
      eval_static_operation_cases (Oadd) (S s1 n1 :: I n2 :: nil)
  | eval_static_operation_case12:
      forall s s1 n1 n2,
      eval_static_operation_cases (Oaddshift s) (S s1 n1 :: I n2 :: nil)
  | eval_static_operation_case13:
      forall n n1,
      eval_static_operation_cases (Oaddimm n) (I n1 :: nil)
  | eval_static_operation_case14:
      forall n s1 n1,
      eval_static_operation_cases (Oaddimm n) (S s1 n1 :: nil)
  | eval_static_operation_case15:
      forall n1 n2,
      eval_static_operation_cases (Osub) (I n1 :: I n2 :: nil)
  | eval_static_operation_case16:
      forall s n1 n2,
      eval_static_operation_cases (Osubshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case17:
      forall s1 n1 n2,
      eval_static_operation_cases (Osub) (S s1 n1 :: I n2 :: nil)
  | eval_static_operation_case18:
      forall s s1 n1 n2,
      eval_static_operation_cases (Osubshift s) (S s1 n1 :: I n2 :: nil)
  | eval_static_operation_case19:
      forall s n1 n2,
      eval_static_operation_cases (Orsubshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case20:
      forall n n1,
      eval_static_operation_cases (Orsubimm n) (I n1 :: nil)
  | eval_static_operation_case21:
      forall n1 n2,
      eval_static_operation_cases (Omul) (I n1 :: I n2 :: nil)
  | eval_static_operation_case22:
      forall n1 n2,
      eval_static_operation_cases (Odiv) (I n1 :: I n2 :: nil)
  | eval_static_operation_case23:
      forall n1 n2,
      eval_static_operation_cases (Odivu) (I n1 :: I n2 :: nil)
  | eval_static_operation_case24:
      forall n1 n2,
      eval_static_operation_cases (Oand) (I n1 :: I n2 :: nil)
  | eval_static_operation_case25:
      forall s n1 n2,
      eval_static_operation_cases (Oandshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case26:
      forall n n1,
      eval_static_operation_cases (Oandimm n) (I n1 :: nil)
  | eval_static_operation_case27:
      forall n1 n2,
      eval_static_operation_cases (Oor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case28:
      forall s n1 n2,
      eval_static_operation_cases (Oorshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case29:
      forall n n1,
      eval_static_operation_cases (Oorimm n) (I n1 :: nil)
  | eval_static_operation_case30:
      forall n1 n2,
      eval_static_operation_cases (Oxor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case31:
      forall s n1 n2,
      eval_static_operation_cases (Oxorshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case32:
      forall n n1,
      eval_static_operation_cases (Oxorimm n) (I n1 :: nil)
  | eval_static_operation_case33:
      forall n1 n2,
      eval_static_operation_cases (Obic) (I n1 :: I n2 :: nil)
  | eval_static_operation_case34:
      forall s n1 n2,
      eval_static_operation_cases (Obicshift s) (I n1 :: I n2 :: nil)
  | eval_static_operation_case35:
      forall n1,
      eval_static_operation_cases (Onot) (I n1 :: nil)
  | eval_static_operation_case36:
      forall s n1,
      eval_static_operation_cases (Onotshift s) (I n1 :: nil)
  | eval_static_operation_case37:
      forall n1 n2,
      eval_static_operation_cases (Oshl) (I n1 :: I n2 :: nil)
  | eval_static_operation_case38:
      forall n1 n2,
      eval_static_operation_cases (Oshr) (I n1 :: I n2 :: nil)
  | eval_static_operation_case39:
      forall n1 n2,
      eval_static_operation_cases (Oshru) (I n1 :: I n2 :: nil)
  | eval_static_operation_case40:
      forall s n1,
      eval_static_operation_cases (Oshift s) (I n1 :: nil)
  | eval_static_operation_case41:
      forall n1,
      eval_static_operation_cases (Onegf) (F n1 :: nil)
  | eval_static_operation_case42:
      forall n1,
      eval_static_operation_cases (Oabsf) (F n1 :: nil)
  | eval_static_operation_case43:
      forall n1 n2,
      eval_static_operation_cases (Oaddf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case44:
      forall n1 n2,
      eval_static_operation_cases (Osubf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case45:
      forall n1 n2,
      eval_static_operation_cases (Omulf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case46:
      forall n1 n2,
      eval_static_operation_cases (Odivf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case47:
      forall n1,
      eval_static_operation_cases (Osingleoffloat) (F n1 :: nil)
  | eval_static_operation_case48:
      forall n1,
      eval_static_operation_cases (Ointoffloat) (F n1 :: nil)
  | eval_static_operation_case49:
      forall n1,
      eval_static_operation_cases (Ofloatofint) (I n1 :: nil)
  | eval_static_operation_case50:
      forall n1,
      eval_static_operation_cases (Ointuoffloat) (F n1 :: nil)
  | eval_static_operation_case53:
      forall n1,
      eval_static_operation_cases (Ofloatofintu) (I n1 :: nil)
  | eval_static_operation_case51:
      forall c vl,
      eval_static_operation_cases (Ocmp c) (vl)
  | eval_static_operation_case52:
      forall n n1,
      eval_static_operation_cases (Oshrximm n) (I n1 :: nil)
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
      eval_static_operation_case5 n1
  | Ocast8unsigned, I n1 :: nil =>
      eval_static_operation_case6 n1
  | Ocast16signed, I n1 :: nil =>
      eval_static_operation_case7 n1
  | Ocast16unsigned, I n1 :: nil =>
      eval_static_operation_case8 n1
  | Oadd, I n1 :: I n2 :: nil =>
      eval_static_operation_case9 n1 n2
  | Oaddshift s, I n1 :: I n2 :: nil =>
      eval_static_operation_case10 s n1 n2
  | Oadd, S s1 n1 :: I n2 :: nil =>
      eval_static_operation_case11 s1 n1 n2
  | Oaddshift s, S s1 n1 :: I n2 :: nil =>
      eval_static_operation_case12 s s1 n1 n2
  | Oaddimm n, I n1 :: nil =>
      eval_static_operation_case13 n n1
  | Oaddimm n, S s1 n1 :: nil =>
      eval_static_operation_case14 n s1 n1
  | Osub, I n1 :: I n2 :: nil =>
      eval_static_operation_case15 n1 n2
  | Osubshift s, I n1 :: I n2 :: nil =>
      eval_static_operation_case16 s n1 n2
  | Osub, S s1 n1 :: I n2 :: nil =>
      eval_static_operation_case17 s1 n1 n2
  | Osubshift s, S s1 n1 :: I n2 :: nil =>
      eval_static_operation_case18 s s1 n1 n2
  | Orsubshift s, I n1 :: I n2 :: nil =>
      eval_static_operation_case19 s n1 n2
  | Orsubimm n, I n1 :: nil =>
      eval_static_operation_case20 n n1
  | Omul, I n1 :: I n2 :: nil =>
      eval_static_operation_case21 n1 n2
  | Odiv, I n1 :: I n2 :: nil =>
      eval_static_operation_case22 n1 n2
  | Odivu, I n1 :: I n2 :: nil =>
      eval_static_operation_case23 n1 n2
  | Oand, I n1 :: I n2 :: nil =>
      eval_static_operation_case24 n1 n2
  | Oandshift s, I n1 :: I n2 :: nil =>
      eval_static_operation_case25 s n1 n2
  | Oandimm n, I n1 :: nil =>
      eval_static_operation_case26 n n1
  | Oor, I n1 :: I n2 :: nil =>
      eval_static_operation_case27 n1 n2
  | Oorshift s, I n1 :: I n2 :: nil =>
      eval_static_operation_case28 s n1 n2
  | Oorimm n, I n1 :: nil =>
      eval_static_operation_case29 n n1
  | Oxor, I n1 :: I n2 :: nil =>
      eval_static_operation_case30 n1 n2
  | Oxorshift s, I n1 :: I n2 :: nil =>
      eval_static_operation_case31 s n1 n2
  | Oxorimm n, I n1 :: nil =>
      eval_static_operation_case32 n n1
  | Obic, I n1 :: I n2 :: nil =>
      eval_static_operation_case33 n1 n2
  | Obicshift s, I n1 :: I n2 :: nil =>
      eval_static_operation_case34 s n1 n2
  | Onot, I n1 :: nil =>
      eval_static_operation_case35 n1
  | Onotshift s, I n1 :: nil =>
      eval_static_operation_case36 s n1
  | Oshl, I n1 :: I n2 :: nil =>
      eval_static_operation_case37 n1 n2
  | Oshr, I n1 :: I n2 :: nil =>
      eval_static_operation_case38 n1 n2
  | Oshru, I n1 :: I n2 :: nil =>
      eval_static_operation_case39 n1 n2
  | Oshift s, I n1 :: nil =>
      eval_static_operation_case40 s n1
  | Onegf, F n1 :: nil =>
      eval_static_operation_case41 n1
  | Oabsf, F n1 :: nil =>
      eval_static_operation_case42 n1
  | Oaddf, F n1 :: F n2 :: nil =>
      eval_static_operation_case43 n1 n2
  | Osubf, F n1 :: F n2 :: nil =>
      eval_static_operation_case44 n1 n2
  | Omulf, F n1 :: F n2 :: nil =>
      eval_static_operation_case45 n1 n2
  | Odivf, F n1 :: F n2 :: nil =>
      eval_static_operation_case46 n1 n2
  | Osingleoffloat, F n1 :: nil =>
      eval_static_operation_case47 n1
  | Ointoffloat, F n1 :: nil =>
      eval_static_operation_case48 n1
  | Ofloatofint, I n1 :: nil =>
      eval_static_operation_case49 n1
  | Ointuoffloat, F n1 :: nil =>
      eval_static_operation_case50 n1
  | Ofloatofintu, I n1 :: nil =>
      eval_static_operation_case53 n1
  | Ocmp c, vl =>
      eval_static_operation_case51 c vl
  | Oshrximm n, I n1 :: nil =>
      eval_static_operation_case52 n n1
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
  | eval_static_operation_case5 n =>
      I(Int.sign_ext 8 n)
  | eval_static_operation_case6 n =>
      I(Int.zero_ext 8 n)
  | eval_static_operation_case7 n =>
      I(Int.sign_ext 16 n)
  | eval_static_operation_case8 n =>
      I(Int.zero_ext 16 n)
  | eval_static_operation_case9 n1 n2 =>
      I(Int.add n1 n2)
  | eval_static_operation_case10 s n1 n2 =>
      I(Int.add n1 (eval_shift s n2))
  | eval_static_operation_case11 s1 n1 n2 =>
      S s1 (Int.add n1 n2)
  | eval_static_operation_case12 s s1 n1 n2 =>
      S s1 (Int.add n1 (eval_shift s n2))
  | eval_static_operation_case13 n n1 =>
      I (Int.add n1 n)
  | eval_static_operation_case14 n s1 n1 =>
      S s1 (Int.add n1 n)
  | eval_static_operation_case15 n1 n2 =>
      I(Int.sub n1 n2)
  | eval_static_operation_case16 s n1 n2 =>
      I(Int.sub n1 (eval_shift s n2))
  | eval_static_operation_case17 s1 n1 n2 =>
      S s1 (Int.sub n1 n2)
  | eval_static_operation_case18 s s1 n1 n2 =>
      S s1 (Int.sub n1 (eval_shift s n2))
  | eval_static_operation_case19 s n1 n2 =>
      I(Int.sub (eval_shift s n2) n1)
  | eval_static_operation_case20 n n1 =>
      I (Int.sub n n1)
  | eval_static_operation_case21 n1 n2 =>
      I(Int.mul n1 n2)
  | eval_static_operation_case22 n1 n2 =>
      if Int.eq n2 Int.zero then Unknown else I(Int.divs n1 n2)
  | eval_static_operation_case23 n1 n2 =>
      if Int.eq n2 Int.zero then Unknown else I(Int.divu n1 n2)
  | eval_static_operation_case24 n1 n2 =>
      I(Int.and n1 n2)
  | eval_static_operation_case25 s n1 n2 =>
      I(Int.and n1 (eval_shift s n2))
  | eval_static_operation_case26 n n1 =>
      I(Int.and n1 n)
  | eval_static_operation_case27 n1 n2 =>
      I(Int.or n1 n2)
  | eval_static_operation_case28 s n1 n2 =>
      I(Int.or n1 (eval_shift s n2))
  | eval_static_operation_case29 n n1 =>
      I(Int.or n1 n)
  | eval_static_operation_case30 n1 n2 =>
      I(Int.xor n1 n2)
  | eval_static_operation_case31 s n1 n2 =>
      I(Int.xor n1 (eval_shift s n2))
  | eval_static_operation_case32 n n1 =>
      I(Int.xor n1 n)
  | eval_static_operation_case33 n1 n2 =>
      I(Int.and n1 (Int.not n2))
  | eval_static_operation_case34 s n1 n2 =>
      I(Int.and n1 (Int.not (eval_shift s n2)))
  | eval_static_operation_case35 n1 =>
      I(Int.not n1)
  | eval_static_operation_case36 s n1 =>
      I(Int.not (eval_shift s n1))
  | eval_static_operation_case37 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shl n1 n2) else Unknown
  | eval_static_operation_case38 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shr n1 n2) else Unknown
  | eval_static_operation_case39 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shru n1 n2) else Unknown
  | eval_static_operation_case40 s n1 =>
      I(eval_shift s n1)
  | eval_static_operation_case41 n1 =>
      F(Float.neg n1)
  | eval_static_operation_case42 n1 =>
      F(Float.abs n1)
  | eval_static_operation_case43 n1 n2 =>
      F(Float.add n1 n2)
  | eval_static_operation_case44 n1 n2 =>
      F(Float.sub n1 n2)
  | eval_static_operation_case45 n1 n2 =>
      F(Float.mul n1 n2)
  | eval_static_operation_case46 n1 n2 =>
      F(Float.div n1 n2)
  | eval_static_operation_case47 n1 =>
      F(Float.singleoffloat n1)
  | eval_static_operation_case48 n1 =>
      match Float.intoffloat n1 with Some x => I x | None => Unknown end
  | eval_static_operation_case49 n1 =>
      F(Float.floatofint n1)
  | eval_static_operation_case50 n1 =>
      match Float.intuoffloat n1 with Some x => I x | None => Unknown end
  | eval_static_operation_case53 n1 =>
      F(Float.floatofintu n1)
  | eval_static_operation_case51 c vl =>
      match eval_static_condition c vl with
      | None => Unknown
      | Some b => I(if b then Int.one else Int.zero)
      end
  | eval_static_operation_case52 n n1 =>
      if Int.ltu n (Int.repr 31) then I(Int.shrx n1 n) else Unknown
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

(*
Definition cond_strength_reduction (cond: condition) (args: list reg) :=
  match cond, args with
  | Ccomp c, r1 :: r2 :: nil =>
  | Ccompu c, r1 :: r2 :: nil =>
  | Ccompshift c s, r1 :: r2 :: nil =>
  | Ccompushift c s, r1 :: r2 :: nil =>
  | _ =>
  end.
*)

Inductive cond_strength_reduction_cases: forall (cond: condition) (args: list reg), Type :=
  | cond_strength_reduction_case1:
      forall c r1 r2,
      cond_strength_reduction_cases (Ccomp c) (r1 :: r2 :: nil)
  | cond_strength_reduction_case2:
      forall c r1 r2,
      cond_strength_reduction_cases (Ccompu c) (r1 :: r2 :: nil)
  | cond_strength_reduction_case3:
      forall c s r1 r2,
      cond_strength_reduction_cases (Ccompshift c s) (r1 :: r2 :: nil)
  | cond_strength_reduction_case4:
      forall c s r1 r2,
      cond_strength_reduction_cases (Ccompushift c s) (r1 :: r2 :: nil)
  | cond_strength_reduction_default:
      forall (cond: condition) (args: list reg),
      cond_strength_reduction_cases cond args.

Definition cond_strength_reduction_match (cond: condition) (args: list reg) :=
  match cond as z1, args as z2 return cond_strength_reduction_cases z1 z2 with
  | Ccomp c, r1 :: r2 :: nil =>
      cond_strength_reduction_case1 c r1 r2
  | Ccompu c, r1 :: r2 :: nil =>
      cond_strength_reduction_case2 c r1 r2
  | Ccompshift c s, r1 :: r2 :: nil =>
      cond_strength_reduction_case3 c s r1 r2
  | Ccompushift c s, r1 :: r2 :: nil =>
      cond_strength_reduction_case4 c s r1 r2
  | cond, args =>
      cond_strength_reduction_default cond args
  end.

Definition cond_strength_reduction (cond: condition) (args: list reg) :=
  match cond_strength_reduction_match cond args with
  | cond_strength_reduction_case1 c r1 r2 =>
      match intval r1, intval r2 with
      | Some n, _ =>
          (Ccompimm (swap_comparison c) n, r2 :: nil)
      | _, Some n =>
          (Ccompimm c n, r1 :: nil)
      | _, _ =>
          (cond, args)
      end
  | cond_strength_reduction_case2 c r1 r2 =>
      match intval r1, intval r2 with
      | Some n, _ =>
          (Ccompuimm (swap_comparison c) n, r2 :: nil)
      | _, Some n =>
          (Ccompuimm c n, r1 :: nil)
      | _, _ =>
          (cond, args)
      end
  | cond_strength_reduction_case3 c s r1 r2 =>
      match intval r2 with
      | Some n =>
          (Ccompimm c (eval_shift s n), r1 :: nil)
      | None =>
          (cond, args)
      end      
  | cond_strength_reduction_case4 c s r1 r2 =>
      match intval r2 with
      | Some n =>
          (Ccompuimm c (eval_shift s n), r1 :: nil)
      | None =>
          (cond, args)
      end      
  | cond_strength_reduction_default cond args =>
      (cond, args)
  end.

Definition make_addimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oaddimm n, r :: nil).

Definition make_shlimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then
    (Omove, r :: nil)
  else match is_shift_amount n with
  | Some n' => (Oshift (Slsl n'), r :: nil)
  | None => (Ointconst Int.zero, nil) (* never happens *)
  end.

Definition make_shrimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then
    (Omove, r :: nil)
  else match is_shift_amount n with
  | Some n' => (Oshift (Sasr n'), r :: nil)
  | None => (Ointconst Int.zero, nil) (* never happens *)
  end.

Definition make_shruimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then
    (Omove, r :: nil)
  else match is_shift_amount n with
  | Some n' => (Oshift (Slsr n'), r :: nil)
  | None => (Ointconst Int.zero, nil) (* never happens *)
  end.

Definition make_mulimm (n: int) (r: reg) (r': reg) :=
  if Int.eq n Int.zero then
    (Ointconst Int.zero, nil)
  else if Int.eq n Int.one then
    (Omove, r :: nil)
  else
    match Int.is_power2 n with
    | Some l => make_shlimm l r
    | None => (Omul, r :: r' :: nil)
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
  if Int.eq n Int.zero then (Omove, r :: nil)
  else if Int.eq n Int.mone then (Onot, r :: nil)
  else (Oxorimm n, r :: nil).

(*
Definition op_strength_reduction (op: operation) (args: list reg) :=
  match op, args with
  | Oadd, r1 :: r2 :: nil =>
  | Oaddshift s, r1 :: r2 :: nil =>
  | Osub, r1 :: r2 :: nil =>
  | Osubshift s, r1 :: r2 :: nil =>
  | Orsubshift s, r1 :: r2 :: nil =>
  | Omul, r1 :: r2 :: nil =>
  | Odivu, r1 :: r2 :: nil =>
  | Oand, r1 :: r2 :: nil =>
  | Oandshift s, r1 :: r2 :: nil =>
  | Oor, r1 :: r2 :: nil =>
  | Oorshift s, r1 :: r2 :: nil =>
  | Oxor, r1 :: r2 :: nil =>
  | Oxorshift s, r1 :: r2 :: nil =>
  | Obic, r1 :: r2 :: nil =>
  | Obicshift s, r1 :: r2 :: nil =>
  | Oshl, r1 :: r2 :: nil =>
  | Oshr, r1 :: r2 :: nil =>
  | Oshru, r1 :: r2 :: nil =>
  | Ocmp c, rl =>
  | _, _ =>
  end.
*)

Inductive op_strength_reduction_cases: forall (op: operation) (args: list reg), Type :=
  | op_strength_reduction_case1:
      forall r1 r2,
      op_strength_reduction_cases (Oadd) (r1 :: r2 :: nil)
  | op_strength_reduction_case2:
      forall s r1 r2,
      op_strength_reduction_cases (Oaddshift s) (r1 :: r2 :: nil)
  | op_strength_reduction_case3:
      forall r1 r2,
      op_strength_reduction_cases (Osub) (r1 :: r2 :: nil)
  | op_strength_reduction_case4:
      forall s r1 r2,
      op_strength_reduction_cases (Osubshift s) (r1 :: r2 :: nil)
  | op_strength_reduction_case5:
      forall s r1 r2,
      op_strength_reduction_cases (Orsubshift s) (r1 :: r2 :: nil)
  | op_strength_reduction_case6:
      forall r1 r2,
      op_strength_reduction_cases (Omul) (r1 :: r2 :: nil)
  | op_strength_reduction_case7:
      forall r1 r2,
      op_strength_reduction_cases (Odivu) (r1 :: r2 :: nil)
  | op_strength_reduction_case8:
      forall r1 r2,
      op_strength_reduction_cases (Oand) (r1 :: r2 :: nil)
  | op_strength_reduction_case9:
      forall s r1 r2,
      op_strength_reduction_cases (Oandshift s) (r1 :: r2 :: nil)
  | op_strength_reduction_case10:
      forall r1 r2,
      op_strength_reduction_cases (Oor) (r1 :: r2 :: nil)
  | op_strength_reduction_case11:
      forall s r1 r2,
      op_strength_reduction_cases (Oorshift s) (r1 :: r2 :: nil)
  | op_strength_reduction_case12:
      forall r1 r2,
      op_strength_reduction_cases (Oxor) (r1 :: r2 :: nil)
  | op_strength_reduction_case13:
      forall s r1 r2,
      op_strength_reduction_cases (Oxorshift s) (r1 :: r2 :: nil)
  | op_strength_reduction_case14:
      forall r1 r2,
      op_strength_reduction_cases (Obic) (r1 :: r2 :: nil)
  | op_strength_reduction_case15:
      forall s r1 r2,
      op_strength_reduction_cases (Obicshift s) (r1 :: r2 :: nil)
  | op_strength_reduction_case16:
      forall r1 r2,
      op_strength_reduction_cases (Oshl) (r1 :: r2 :: nil)
  | op_strength_reduction_case17:
      forall r1 r2,
      op_strength_reduction_cases (Oshr) (r1 :: r2 :: nil)
  | op_strength_reduction_case18:
      forall r1 r2,
      op_strength_reduction_cases (Oshru) (r1 :: r2 :: nil)
  | op_strength_reduction_case19:
      forall c rl,
      op_strength_reduction_cases (Ocmp c) rl
  | op_strength_reduction_default:
      forall (op: operation) (args: list reg),
      op_strength_reduction_cases op args.

Definition op_strength_reduction_match (op: operation) (args: list reg) :=
  match op as z1, args as z2 return op_strength_reduction_cases z1 z2 with
  | Oadd, r1 :: r2 :: nil =>
      op_strength_reduction_case1 r1 r2
  | Oaddshift s, r1 :: r2 :: nil =>
      op_strength_reduction_case2 s r1 r2
  | Osub, r1 :: r2 :: nil =>
      op_strength_reduction_case3 r1 r2
  | Osubshift s, r1 :: r2 :: nil =>
      op_strength_reduction_case4 s r1 r2
  | Orsubshift s, r1 :: r2 :: nil =>
      op_strength_reduction_case5 s r1 r2
  | Omul, r1 :: r2 :: nil =>
      op_strength_reduction_case6 r1 r2
  | Odivu, r1 :: r2 :: nil =>
      op_strength_reduction_case7 r1 r2
  | Oand, r1 :: r2 :: nil =>
      op_strength_reduction_case8 r1 r2
  | Oandshift s, r1 :: r2 :: nil =>
      op_strength_reduction_case9 s r1 r2
  | Oor, r1 :: r2 :: nil =>
      op_strength_reduction_case10 r1 r2
  | Oorshift s, r1 :: r2 :: nil =>
      op_strength_reduction_case11 s r1 r2
  | Oxor, r1 :: r2 :: nil =>
      op_strength_reduction_case12 r1 r2
  | Oxorshift s, r1 :: r2 :: nil =>
      op_strength_reduction_case13 s r1 r2
  | Obic, r1 :: r2 :: nil =>
      op_strength_reduction_case14 r1 r2
  | Obicshift s, r1 :: r2 :: nil =>
      op_strength_reduction_case15 s r1 r2
  | Oshl, r1 :: r2 :: nil =>
      op_strength_reduction_case16 r1 r2
  | Oshr, r1 :: r2 :: nil =>
      op_strength_reduction_case17 r1 r2
  | Oshru, r1 :: r2 :: nil =>
      op_strength_reduction_case18 r1 r2
  | Ocmp c, rl =>
      op_strength_reduction_case19 c rl
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
  | op_strength_reduction_case2 s r1 r2 => (* Oaddshift *)
      match intval r2 with
      | Some n => make_addimm (eval_shift s n) r1
      | _ => (op, args)
      end
  | op_strength_reduction_case3 r1 r2 => (* Osub *)
      match intval r1, intval r2 with
      | Some n, _ => (Orsubimm n, r2 :: nil)
      | _, Some n => make_addimm (Int.neg n) r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case4 s r1 r2 => (* Osubshift *)
      match intval r2 with
      | Some n => make_addimm (Int.neg (eval_shift s n)) r1
      | _ => (op, args)
      end
  | op_strength_reduction_case5 s r1 r2 => (* Orsubshift *)
      match intval r2 with
      | Some n => (Orsubimm (eval_shift s n), r1 :: nil)
      | _ => (op, args)
      end
  | op_strength_reduction_case6 r1 r2 => (* Omul *)
      match intval r1, intval r2 with
      | Some n, _ => make_mulimm n r2 r1
      | _, Some n => make_mulimm n r1 r2
      | _, _ => (op, args)
      end
  | op_strength_reduction_case7 r1 r2 => (* Odivu *)
      match intval r2 with
      | Some n =>
          match Int.is_power2 n with
          | Some l => make_shruimm l r1
          | None   => (op, args)
          end
      | None =>
          (op, args)
      end
  | op_strength_reduction_case8 r1 r2 => (* Oand *)
      match intval r1, intval r2 with
      | Some n, _ => make_andimm n r2
      | _, Some n => make_andimm n r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case9 s r1 r2 => (* Oandshift *)
      match intval r2 with
      | Some n => make_andimm (eval_shift s n) r1
      | _ => (op, args)
      end
  | op_strength_reduction_case10 r1 r2 => (* Oor *)
      match intval r1, intval r2 with
      | Some n, _ => make_orimm n r2
      | _, Some n => make_orimm n r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case11 s r1 r2 => (* Oorshift *)
      match intval r2 with
      | Some n => make_orimm (eval_shift s n) r1
      | _ => (op, args)
      end
  | op_strength_reduction_case12 r1 r2 => (* Oxor *)
      match intval r1, intval r2 with
      | Some n, _ => make_xorimm n r2
      | _, Some n => make_xorimm n r1
      | _, _ => (op, args)
      end
  | op_strength_reduction_case13 s r1 r2 => (* Oxorshift *)
      match intval r2 with
      | Some n => make_xorimm (eval_shift s n) r1
      | _ => (op, args)
      end
  | op_strength_reduction_case14 r1 r2 => (* Obic *)
      match intval r2 with
      | Some n => make_andimm (Int.not n) r1
      | _ => (op, args)
      end
  | op_strength_reduction_case15 s r1 r2 => (* Obicshift *)
      match intval r2 with
      | Some n => make_andimm (Int.not (eval_shift s n)) r1
      | _ => (op, args)
      end
  | op_strength_reduction_case16 r1 r2 => (* Oshl *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shlimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case17 r1 r2 => (* Oshr *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shrimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case18 r1 r2 => (* Oshru *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shruimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case19 c rl => (* Ocmp *)
      let (c', args') := cond_strength_reduction c args in
      (Ocmp c', args')
  | op_strength_reduction_default op args => (* default *)
      (op, args)
  end.

(*
Definition addr_strength_reduction (addr: addressing) (args: list reg) :=
  match addr, args with
  | Aindexed2, r1 :: r2 :: nil =>
  | Aindexed2shift s, r1 :: r2 :: nil =>
  | _, _ =>
  end.
*)

Inductive addr_strength_reduction_cases: forall (addr: addressing) (args: list reg), Type :=
  | addr_strength_reduction_case1:
      forall r1 r2,
      addr_strength_reduction_cases (Aindexed2) (r1 :: r2 :: nil)
  | addr_strength_reduction_case2:
      forall s r1 r2,
      addr_strength_reduction_cases (Aindexed2shift s) (r1 :: r2 :: nil)
  | addr_strength_reduction_default:
      forall (addr: addressing) (args: list reg),
      addr_strength_reduction_cases addr args.

Definition addr_strength_reduction_match (addr: addressing) (args: list reg) :=
  match addr as z1, args as z2 return addr_strength_reduction_cases z1 z2 with
  | Aindexed2, r1 :: r2 :: nil =>
      addr_strength_reduction_case1 r1 r2
  | Aindexed2shift s, r1 :: r2 :: nil =>
      addr_strength_reduction_case2 s r1 r2
  | addr, args =>
      addr_strength_reduction_default addr args
  end.

Definition addr_strength_reduction (addr: addressing) (args: list reg) :=
  match addr_strength_reduction_match addr args with
  | addr_strength_reduction_case1 r1 r2 => (* Aindexed2 *)
      match intval r1, intval r2 with
      | Some n1, _ => (Aindexed n1, r2 :: nil)
      | _, Some n2 => (Aindexed n2, r1 :: nil)
      | _, _ => (addr, args)
      end
  | addr_strength_reduction_case2 s r1 r2 => (* Aindexed2shift *)
      match intval r2 with
      | Some n2 => (Aindexed (eval_shift s n2), r1 :: nil)
      | _ => (addr, args)
      end
  | addr_strength_reduction_default addr args =>
      (addr, args)      
  end.

End STRENGTH_REDUCTION.

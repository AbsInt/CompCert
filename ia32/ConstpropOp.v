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
Definition eval_static_addressing (addr: addressing) (vl: list approx) :=
  match op, vl with
  | Aindexed n, I n1::nil => I (Int.add n1 n)
  | Aindexed n, S id ofs::nil => S id (Int.add ofs n)
  | Aindexed2 n, I n1::I n2::nil => I (Int.add (Int.add n1 n2) n)
  | Aindexed2 n, S id ofs::I n2::nil => S id (Int.add (Int.add ofs n2) n)
  | Aindexed2 n, I n1::S id ofs::nil => S id (Int.add (Int.add ofs n1) n)
  | Ascaled sc n, I n1::nil => I (Int.add (Int.mul n1 sc) n)
  | Aindexed2scaled sc n, I n1::I n2::nil => I (Int.add n1 (Int.add (Int.mul n2 sc) n))
  | Aindexed2scaled sc n, S id ofs::I n2::nil => S id (Int.add ofs (Int.add (Int.mul n2 sc) n))
  | Aglobal id ofs, nil => S id ofs
  | Abased id ofs, I n1::nil => S id (Int.add ofs n1)
  | Abasedscaled sc id ofs, I n1::nil => S id (Int.add ofs (Int.mul sc n1))
  | _, _ => Unknown
  end.
*)

Inductive eval_static_addressing_cases: forall (addr: addressing) (vl: list approx), Type :=
  | eval_static_addressing_case1:
      forall n n1,
      eval_static_addressing_cases (Aindexed n) (I n1::nil)
  | eval_static_addressing_case2:
      forall n id ofs,
      eval_static_addressing_cases (Aindexed n) (S id ofs::nil)
  | eval_static_addressing_case3:
      forall n n1 n2,
      eval_static_addressing_cases (Aindexed2 n) (I n1::I n2::nil)
  | eval_static_addressing_case4:
      forall n id ofs n2,
      eval_static_addressing_cases (Aindexed2 n) (S id ofs::I n2::nil)
  | eval_static_addressing_case5:
      forall n n1 id ofs,
      eval_static_addressing_cases (Aindexed2 n) (I n1::S id ofs::nil)
  | eval_static_addressing_case6:
      forall sc n n1,
      eval_static_addressing_cases (Ascaled sc n) (I n1::nil)
  | eval_static_addressing_case7:
      forall sc n n1 n2,
      eval_static_addressing_cases (Aindexed2scaled sc n) (I n1::I n2::nil)
  | eval_static_addressing_case8:
      forall sc n id ofs n2,
      eval_static_addressing_cases (Aindexed2scaled sc n) (S id ofs::I n2::nil)
  | eval_static_addressing_case9:
      forall id ofs,
      eval_static_addressing_cases (Aglobal id ofs) (nil)
  | eval_static_addressing_case10:
      forall id ofs n1,
      eval_static_addressing_cases (Abased id ofs) (I n1::nil)
  | eval_static_addressing_case11:
      forall sc id ofs n1,
      eval_static_addressing_cases (Abasedscaled sc id ofs) (I n1::nil)
  | eval_static_addressing_default:
      forall (addr: addressing) (vl: list approx),
      eval_static_addressing_cases addr vl.

Definition eval_static_addressing_match (addr: addressing) (vl: list approx) :=
  match addr as z1, vl as z2 return eval_static_addressing_cases z1 z2 with
  | Aindexed n, I n1::nil =>
      eval_static_addressing_case1 n n1
  | Aindexed n, S id ofs::nil =>
      eval_static_addressing_case2 n id ofs
  | Aindexed2 n, I n1::I n2::nil =>
      eval_static_addressing_case3 n n1 n2
  | Aindexed2 n, S id ofs::I n2::nil =>
      eval_static_addressing_case4 n id ofs n2
  | Aindexed2 n, I n1::S id ofs::nil =>
      eval_static_addressing_case5 n n1 id ofs
  | Ascaled sc n, I n1::nil =>
      eval_static_addressing_case6 sc n n1
  | Aindexed2scaled sc n, I n1::I n2::nil =>
      eval_static_addressing_case7 sc n n1 n2
  | Aindexed2scaled sc n, S id ofs::I n2::nil =>
      eval_static_addressing_case8 sc n id ofs n2
  | Aglobal id ofs, nil =>
      eval_static_addressing_case9 id ofs
  | Abased id ofs, I n1::nil =>
      eval_static_addressing_case10 id ofs n1
  | Abasedscaled sc id ofs, I n1::nil =>
      eval_static_addressing_case11 sc id ofs n1
  | addr, vl =>
      eval_static_addressing_default addr vl
  end.

Definition eval_static_addressing (addr: addressing) (vl: list approx) :=
  match eval_static_addressing_match addr vl with
  | eval_static_addressing_case1 n n1 =>
      I (Int.add n1 n)
  | eval_static_addressing_case2 n id ofs =>
      S id (Int.add ofs n)
  | eval_static_addressing_case3 n n1 n2 =>
      I (Int.add (Int.add n1 n2) n)
  | eval_static_addressing_case4 n id ofs n2 =>
      S id (Int.add (Int.add ofs n2) n)
  | eval_static_addressing_case5 n n1 id ofs =>
      S id (Int.add (Int.add ofs n1) n)
  | eval_static_addressing_case6 sc n n1 =>
      I (Int.add (Int.mul n1 sc) n)
  | eval_static_addressing_case7 sc n n1 n2 =>
      I (Int.add n1 (Int.add (Int.mul n2 sc) n))
  | eval_static_addressing_case8 sc n id ofs n2 =>
      S id (Int.add ofs (Int.add (Int.mul n2 sc) n))
  | eval_static_addressing_case9 id ofs =>
      S id ofs
  | eval_static_addressing_case10 id ofs n1 =>
      S id (Int.add ofs n1)
  | eval_static_addressing_case11 sc id ofs n1 =>
      S id (Int.add ofs (Int.mul sc n1))
  | eval_static_addressing_default addr vl =>
      Unknown
  end.

(*
Definition eval_static_operation (op: operation) (vl: list approx) :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Ofloatconst n, nil => F n
  | Ocast8signed, I n1 :: nil => I(Int.sign_ext 8 n1)
  | Ocast8unsigned, I n1 :: nil => I(Int.zero_ext 8 n1)
  | Ocast16signed, I n1 :: nil => I(Int.sign_ext 16 n1)
  | Ocast16unsigned, I n1 :: nil => I(Int.zero_ext 16 n1)
  | Oneg, I n1 :: nil => I(Int.neg n1)
  | Osub, I n1 :: I n2 :: nil => I(Int.sub n1 n2)
  | Osub, S s1 n1 :: I n2 :: nil => S s1 (Int.sub n1 n2)
  | Omul, I n1 :: I n2 :: nil => I(Int.mul n1 n2)
  | Omulimm n, I n1 :: nil => I(Int.mul n1 n)
  | Odiv, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.divs n1 n2)
  | Odivu, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.divu n1 n2)
  | Omod, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.mods n1 n2)
  | Omodu, I n1 :: I n2 :: nil => if Int.eq n2 Int.zero then Unknown else I(Int.modu n1 n2)
  | Oand, I n1 :: I n2 :: nil => I(Int.and n1 n2)
  | Oandimm n, I n1 :: nil => I(Int.and n1 n)
  | Oor, I n1 :: I n2 :: nil => I(Int.or n1 n2)
  | Oorimm n, I n1 :: nil => I(Int.or n1 n)
  | Oxor, I n1 :: I n2 :: nil => I(Int.xor n1 n2)
  | Oxorimm n, I n1 :: nil => I(Int.xor n1 n)
  | Oshl, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shl n1 n2) else Unknown
  | Oshlimm n, I n1 :: nil => if Int.ltu n Int.iwordsize then I(Int.shl n1 n) else Unknown
  | Oshr, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shr n1 n2) else Unknown
  | Oshrimm n, I n1 :: nil => if Int.ltu n Int.iwordsize then I(Int.shr n1 n) else Unknown
  | Oshrximm n, I n1 :: nil => if Int.ltu n Int.iwordsize then I(Int.shrx n1 n) else Unknown
  | Oshru, I n1 :: I n2 :: nil => if Int.ltu n2 Int.iwordsize then I(Int.shru n1 n2) else Unknown
  | Oshruimm n, I n1 :: nil => if Int.ltu n Int.iwordsize then I(Int.shru n1 n) else Unknown
  | Ororimm n, I n1 :: nil => if Int.ltu n Int.iwordsize then I(Int.ror n1 n) else Unknown
  | Olea mode, vl => eval_static_addressing mode vl
  | Onegf, F n1 :: nil => F(Float.neg n1)
  | Oabsf, F n1 :: nil => F(Float.abs n1)
  | Oaddf, F n1 :: F n2 :: nil => F(Float.add n1 n2)
  | Osubf, F n1 :: F n2 :: nil => F(Float.sub n1 n2)
  | Omulf, F n1 :: F n2 :: nil => F(Float.mul n1 n2)
  | Odivf, F n1 :: F n2 :: nil => F(Float.div n1 n2)
  | Osingleoffloat, F n1 :: nil => F(Float.singleoffloat n1)
  | Ointoffloat, F n1 :: nil => match Float.intoffloat n1 with Some x => I x | None => Unknown end
  | Ofloatofint, I n1 :: nil => F(Float.floatofint n1)
  | Ocmp c, vl => match eval_static_condition c vl with None => Unknown | Some b => I(if b then Int.one else Int.zero) end
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
      forall n1,
      eval_static_operation_cases (Ocast8signed) (I n1 :: nil)
  | eval_static_operation_case5:
      forall n1,
      eval_static_operation_cases (Ocast8unsigned) (I n1 :: nil)
  | eval_static_operation_case6:
      forall n1,
      eval_static_operation_cases (Ocast16signed) (I n1 :: nil)
  | eval_static_operation_case7:
      forall n1,
      eval_static_operation_cases (Ocast16unsigned) (I n1 :: nil)
  | eval_static_operation_case8:
      forall n1,
      eval_static_operation_cases (Oneg) (I n1 :: nil)
  | eval_static_operation_case9:
      forall n1 n2,
      eval_static_operation_cases (Osub) (I n1 :: I n2 :: nil)
  | eval_static_operation_case10:
      forall s1 n1 n2,
      eval_static_operation_cases (Osub) (S s1 n1 :: I n2 :: nil)
  | eval_static_operation_case11:
      forall n1 n2,
      eval_static_operation_cases (Omul) (I n1 :: I n2 :: nil)
  | eval_static_operation_case12:
      forall n n1,
      eval_static_operation_cases (Omulimm n) (I n1 :: nil)
  | eval_static_operation_case13:
      forall n1 n2,
      eval_static_operation_cases (Odiv) (I n1 :: I n2 :: nil)
  | eval_static_operation_case14:
      forall n1 n2,
      eval_static_operation_cases (Odivu) (I n1 :: I n2 :: nil)
  | eval_static_operation_case15:
      forall n1 n2,
      eval_static_operation_cases (Omod) (I n1 :: I n2 :: nil)
  | eval_static_operation_case16:
      forall n1 n2,
      eval_static_operation_cases (Omodu) (I n1 :: I n2 :: nil)
  | eval_static_operation_case17:
      forall n1 n2,
      eval_static_operation_cases (Oand) (I n1 :: I n2 :: nil)
  | eval_static_operation_case18:
      forall n n1,
      eval_static_operation_cases (Oandimm n) (I n1 :: nil)
  | eval_static_operation_case19:
      forall n1 n2,
      eval_static_operation_cases (Oor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case20:
      forall n n1,
      eval_static_operation_cases (Oorimm n) (I n1 :: nil)
  | eval_static_operation_case21:
      forall n1 n2,
      eval_static_operation_cases (Oxor) (I n1 :: I n2 :: nil)
  | eval_static_operation_case22:
      forall n n1,
      eval_static_operation_cases (Oxorimm n) (I n1 :: nil)
  | eval_static_operation_case23:
      forall n1 n2,
      eval_static_operation_cases (Oshl) (I n1 :: I n2 :: nil)
  | eval_static_operation_case24:
      forall n n1,
      eval_static_operation_cases (Oshlimm n) (I n1 :: nil)
  | eval_static_operation_case25:
      forall n1 n2,
      eval_static_operation_cases (Oshr) (I n1 :: I n2 :: nil)
  | eval_static_operation_case26:
      forall n n1,
      eval_static_operation_cases (Oshrimm n) (I n1 :: nil)
  | eval_static_operation_case27:
      forall n n1,
      eval_static_operation_cases (Oshrximm n) (I n1 :: nil)
  | eval_static_operation_case28:
      forall n1 n2,
      eval_static_operation_cases (Oshru) (I n1 :: I n2 :: nil)
  | eval_static_operation_case29:
      forall n n1,
      eval_static_operation_cases (Oshruimm n) (I n1 :: nil)
  | eval_static_operation_case30:
      forall n n1,
      eval_static_operation_cases (Ororimm n) (I n1 :: nil)
  | eval_static_operation_case31:
      forall mode vl,
      eval_static_operation_cases (Olea mode) (vl)
  | eval_static_operation_case32:
      forall n1,
      eval_static_operation_cases (Onegf) (F n1 :: nil)
  | eval_static_operation_case33:
      forall n1,
      eval_static_operation_cases (Oabsf) (F n1 :: nil)
  | eval_static_operation_case34:
      forall n1 n2,
      eval_static_operation_cases (Oaddf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case35:
      forall n1 n2,
      eval_static_operation_cases (Osubf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case36:
      forall n1 n2,
      eval_static_operation_cases (Omulf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case37:
      forall n1 n2,
      eval_static_operation_cases (Odivf) (F n1 :: F n2 :: nil)
  | eval_static_operation_case38:
      forall n1,
      eval_static_operation_cases (Osingleoffloat) (F n1 :: nil)
  | eval_static_operation_case39:
      forall n1,
      eval_static_operation_cases (Ointoffloat) (F n1 :: nil)
  | eval_static_operation_case41:
      forall n1,
      eval_static_operation_cases (Ofloatofint) (I n1 :: nil)
  | eval_static_operation_case43:
      forall c vl,
      eval_static_operation_cases (Ocmp c) vl
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
  | Ocast8signed, I n1 :: nil =>
      eval_static_operation_case4 n1
  | Ocast8unsigned, I n1 :: nil =>
      eval_static_operation_case5 n1
  | Ocast16signed, I n1 :: nil =>
      eval_static_operation_case6 n1
  | Ocast16unsigned, I n1 :: nil =>
      eval_static_operation_case7 n1
  | Oneg, I n1 :: nil =>
      eval_static_operation_case8 n1
  | Osub, I n1 :: I n2 :: nil =>
      eval_static_operation_case9 n1 n2
  | Osub, S s1 n1 :: I n2 :: nil =>
      eval_static_operation_case10 s1 n1 n2
  | Omul, I n1 :: I n2 :: nil =>
      eval_static_operation_case11 n1 n2
  | Omulimm n, I n1 :: nil =>
      eval_static_operation_case12 n n1
  | Odiv, I n1 :: I n2 :: nil =>
      eval_static_operation_case13 n1 n2
  | Odivu, I n1 :: I n2 :: nil =>
      eval_static_operation_case14 n1 n2
  | Omod, I n1 :: I n2 :: nil =>
      eval_static_operation_case15 n1 n2
  | Omodu, I n1 :: I n2 :: nil =>
      eval_static_operation_case16 n1 n2
  | Oand, I n1 :: I n2 :: nil =>
      eval_static_operation_case17 n1 n2
  | Oandimm n, I n1 :: nil =>
      eval_static_operation_case18 n n1
  | Oor, I n1 :: I n2 :: nil =>
      eval_static_operation_case19 n1 n2
  | Oorimm n, I n1 :: nil =>
      eval_static_operation_case20 n n1
  | Oxor, I n1 :: I n2 :: nil =>
      eval_static_operation_case21 n1 n2
  | Oxorimm n, I n1 :: nil =>
      eval_static_operation_case22 n n1
  | Oshl, I n1 :: I n2 :: nil =>
      eval_static_operation_case23 n1 n2
  | Oshlimm n, I n1 :: nil =>
      eval_static_operation_case24 n n1
  | Oshr, I n1 :: I n2 :: nil =>
      eval_static_operation_case25 n1 n2
  | Oshrimm n, I n1 :: nil =>
      eval_static_operation_case26 n n1
  | Oshrximm n, I n1 :: nil =>
      eval_static_operation_case27 n n1
  | Oshru, I n1 :: I n2 :: nil =>
      eval_static_operation_case28 n1 n2
  | Oshruimm n, I n1 :: nil =>
      eval_static_operation_case29 n n1
  | Ororimm n, I n1 :: nil =>
      eval_static_operation_case30 n n1
  | Olea mode, vl =>
      eval_static_operation_case31 mode vl
  | Onegf, F n1 :: nil =>
      eval_static_operation_case32 n1
  | Oabsf, F n1 :: nil =>
      eval_static_operation_case33 n1
  | Oaddf, F n1 :: F n2 :: nil =>
      eval_static_operation_case34 n1 n2
  | Osubf, F n1 :: F n2 :: nil =>
      eval_static_operation_case35 n1 n2
  | Omulf, F n1 :: F n2 :: nil =>
      eval_static_operation_case36 n1 n2
  | Odivf, F n1 :: F n2 :: nil =>
      eval_static_operation_case37 n1 n2
  | Osingleoffloat, F n1 :: nil =>
      eval_static_operation_case38 n1
  | Ointoffloat, F n1 :: nil =>
      eval_static_operation_case39 n1
  | Ofloatofint, I n1 :: nil =>
      eval_static_operation_case41 n1
  | Ocmp c, vl =>
      eval_static_operation_case43 c vl
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
  | eval_static_operation_case4 n1 =>
      I(Int.sign_ext 8 n1)
  | eval_static_operation_case5 n1 =>
      I(Int.zero_ext 8 n1)
  | eval_static_operation_case6 n1 =>
      I(Int.sign_ext 16 n1)
  | eval_static_operation_case7 n1 =>
      I(Int.zero_ext 16 n1)
  | eval_static_operation_case8 n1 =>
      I(Int.neg n1)
  | eval_static_operation_case9 n1 n2 =>
      I(Int.sub n1 n2)
  | eval_static_operation_case10 s1 n1 n2 =>
      S s1 (Int.sub n1 n2)
  | eval_static_operation_case11 n1 n2 =>
      I(Int.mul n1 n2)
  | eval_static_operation_case12 n n1 =>
      I(Int.mul n1 n)
  | eval_static_operation_case13 n1 n2 =>
      if Int.eq n2 Int.zero then Unknown else I(Int.divs n1 n2)
  | eval_static_operation_case14 n1 n2 =>
      if Int.eq n2 Int.zero then Unknown else I(Int.divu n1 n2)
  | eval_static_operation_case15 n1 n2 =>
      if Int.eq n2 Int.zero then Unknown else I(Int.mods n1 n2)
  | eval_static_operation_case16 n1 n2 =>
      if Int.eq n2 Int.zero then Unknown else I(Int.modu n1 n2)
  | eval_static_operation_case17 n1 n2 =>
      I(Int.and n1 n2)
  | eval_static_operation_case18 n n1 =>
      I(Int.and n1 n)
  | eval_static_operation_case19 n1 n2 =>
      I(Int.or n1 n2)
  | eval_static_operation_case20 n n1 =>
      I(Int.or n1 n)
  | eval_static_operation_case21 n1 n2 =>
      I(Int.xor n1 n2)
  | eval_static_operation_case22 n n1 =>
      I(Int.xor n1 n)
  | eval_static_operation_case23 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shl n1 n2) else Unknown
  | eval_static_operation_case24 n n1 =>
      if Int.ltu n Int.iwordsize then I(Int.shl n1 n) else Unknown
  | eval_static_operation_case25 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shr n1 n2) else Unknown
  | eval_static_operation_case26 n n1 =>
      if Int.ltu n Int.iwordsize then I(Int.shr n1 n) else Unknown
  | eval_static_operation_case27 n n1 =>
      if Int.ltu n (Int.repr 31) then I(Int.shrx n1 n) else Unknown
  | eval_static_operation_case28 n1 n2 =>
      if Int.ltu n2 Int.iwordsize then I(Int.shru n1 n2) else Unknown
  | eval_static_operation_case29 n n1 =>
      if Int.ltu n Int.iwordsize then I(Int.shru n1 n) else Unknown
  | eval_static_operation_case30 n n1 =>
      if Int.ltu n Int.iwordsize then I(Int.ror n1 n) else Unknown
  | eval_static_operation_case31 mode vl =>
      eval_static_addressing mode vl
  | eval_static_operation_case32 n1 =>
      F(Float.neg n1)
  | eval_static_operation_case33 n1 =>
      F(Float.abs n1)
  | eval_static_operation_case34 n1 n2 =>
      F(Float.add n1 n2)
  | eval_static_operation_case35 n1 n2 =>
      F(Float.sub n1 n2)
  | eval_static_operation_case36 n1 n2 =>
      F(Float.mul n1 n2)
  | eval_static_operation_case37 n1 n2 =>
      F(Float.div n1 n2)
  | eval_static_operation_case38 n1 =>
      F(Float.singleoffloat n1)
  | eval_static_operation_case39 n1 =>
      match Float.intoffloat n1 with Some x => I x | None => Unknown end
  | eval_static_operation_case41 n1 =>
      F(Float.floatofint n1)
  | eval_static_operation_case43 c vl =>
      match eval_static_condition c vl with
      | None => Unknown
      | Some b => I(if b then Int.one else Int.zero)
      end
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

(*
Definition addr_strength_reduction (addr: addressing) (args: list reg) :=
  match addr, args with
  | Aindexed ofs, r1 :: nil => (* Aindexed *)
  | Aindexed2 ofs, r1 :: r2 :: nil => (* Aindexed2 *)
  | Aindexed2scaled sc ofs, r1 :: r2 :: nil => (* Aindexed2scaled *)
  | Abased id ofs, r1 :: nil => (* Abased *)
  | Abasedscaled sc id ofs, r1 :: nil => (* Abasedscaled *)
  | _, _ => (* default *)
  end.
*)

Inductive addr_strength_reduction_cases: forall (addr: addressing) (args: list reg), Type :=
  | addr_strength_reduction_case1:
      forall ofs r1,
      addr_strength_reduction_cases (Aindexed ofs) (r1 :: nil)
  | addr_strength_reduction_case2:
      forall ofs r1 r2,
      addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil)
  | addr_strength_reduction_case3:
      forall sc ofs r1 r2,
      addr_strength_reduction_cases (Aindexed2scaled sc ofs) (r1 :: r2 :: nil)
  | addr_strength_reduction_case4:
      forall id ofs r1,
      addr_strength_reduction_cases (Abased id ofs) (r1 :: nil)
  | addr_strength_reduction_case5:
      forall sc id ofs r1,
      addr_strength_reduction_cases (Abasedscaled sc id ofs) (r1 :: nil)
  | addr_strength_reduction_default:
      forall (addr: addressing) (args: list reg),
      addr_strength_reduction_cases addr args.

Definition addr_strength_reduction_match (addr: addressing) (args: list reg) :=
  match addr as z1, args as z2 return addr_strength_reduction_cases z1 z2 with
  | Aindexed ofs, r1 :: nil =>
      addr_strength_reduction_case1 ofs r1
  | Aindexed2 ofs, r1 :: r2 :: nil =>
      addr_strength_reduction_case2 ofs r1 r2
  | Aindexed2scaled sc ofs, r1 :: r2 :: nil =>
      addr_strength_reduction_case3 sc ofs r1 r2
  | Abased id ofs, r1 :: nil =>
      addr_strength_reduction_case4 id ofs r1
  | Abasedscaled sc id ofs, r1 :: nil =>
      addr_strength_reduction_case5 sc id ofs r1
  | addr, args =>
      addr_strength_reduction_default addr args
  end.

Definition addr_strength_reduction (addr: addressing) (args: list reg) :=
  match addr_strength_reduction_match addr args with
  | addr_strength_reduction_case1 ofs r1 =>
      (* Aindexed *)
      match app r1 with
      | S symb n => (Aglobal symb (Int.add ofs n), nil)
      | _ => (addr, args)
      end
  | addr_strength_reduction_case2 ofs r1 r2 =>
      (* Aindexed2 *)
      match app r1, app r2 with
      | S symb n1, I n2 => (Aglobal symb (Int.add (Int.add n1 n2) ofs), nil)
      | I n1, S symb n2 => (Aglobal symb (Int.add (Int.add n1 n2) ofs), nil)
      | S symb n1, _ => (Abased symb (Int.add n1 ofs), r2 :: nil)
      | _, S symb n2 => (Abased symb (Int.add n2 ofs), r1 :: nil)
      | I n1, _ => (Aindexed (Int.add n1 ofs), r2 :: nil)
      | _, I n2 => (Aindexed (Int.add n2 ofs), r1 :: nil)
      | _, _ => (addr, args)
      end
  | addr_strength_reduction_case3 sc ofs r1 r2 =>
      (* Aindexed2scaled *)
      match app r1, app r2 with
      | S symb n1, I n2 => (Aglobal symb (Int.add (Int.add n1 (Int.mul n2 sc)) ofs), nil)
      | S symb n1, _ => (Abasedscaled sc symb (Int.add n1 ofs), r2 :: nil)
      | _, I n2 => (Aindexed (Int.add (Int.mul n2 sc) ofs), r1 :: nil)
      | _, _ => (addr, args)
      end
  | addr_strength_reduction_case4 id ofs r1 =>
      (* Abased *)
      match app r1 with
      | I n1 => (Aglobal id (Int.add ofs n1), nil)
      | _ => (addr, args)
      end
  | addr_strength_reduction_case5 sc id ofs r1 =>
      (* Abasedscaled *)
      match app r1 with
      | I n1 => (Aglobal id (Int.add ofs (Int.mul sc n1)), nil)
      | _ => (addr, args)
      end
  | addr_strength_reduction_default addr args =>
      (addr, args)
  end.

Definition make_addimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oaddimm n, r :: nil).

Definition make_shlimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oshlimm n, r :: nil).

Definition make_shrimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oshrimm n, r :: nil).

Definition make_shruimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Oshruimm n, r :: nil).

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

(*
Definition op_strength_reduction (op: operation) (args: list reg) :=
  match op, args with
  | Osub, r1 :: r2 :: nil => (* Osub *)
  | Omul, r1 :: r2 :: nil => (* Omul *)
  | Odiv, r1 :: r2 :: nil => (* Odiv *)
  | Odivu, r1 :: r2 :: nil => (* Odivu *)
  | Omodu, r1 :: r2 :: nil => (* Omodu *)
  | Oand, r1 :: r2 :: nil => (* Oand *)
  | Oor, r1 :: r2 :: nil => (* Oor *)
  | Oxor, r1 :: r2 :: nil => (* Oxor *)
  | Oshl, r1 :: r2 :: nil => (* Oshl *)
  | Oshr, r1 :: r2 :: nil => (* Oshr *)
  | Oshru, r1 :: r2 :: nil => (* Oshru *)
  | Olea addr, args => (* Olea *)
  | Ocmp c, args => (* Ocmp *)
  | _, _ => (* default *)
  end.
*)

Inductive op_strength_reduction_cases: forall (op: operation) (args: list reg), Type :=
  | op_strength_reduction_case2:
      forall r1 r2,
      op_strength_reduction_cases (Osub) (r1 :: r2 :: nil)
  | op_strength_reduction_case3:
      forall r1 r2,
      op_strength_reduction_cases (Omul) (r1 :: r2 :: nil)
  | op_strength_reduction_case4:
      forall r1 r2,
      op_strength_reduction_cases (Odiv) (r1 :: r2 :: nil)
  | op_strength_reduction_case5:
      forall r1 r2,
      op_strength_reduction_cases (Odivu) (r1 :: r2 :: nil)
  | op_strength_reduction_case7:
      forall r1 r2,
      op_strength_reduction_cases (Omodu) (r1 :: r2 :: nil)
  | op_strength_reduction_case8:
      forall r1 r2,
      op_strength_reduction_cases (Oand) (r1 :: r2 :: nil)
  | op_strength_reduction_case9:
      forall r1 r2,
      op_strength_reduction_cases (Oor) (r1 :: r2 :: nil)
  | op_strength_reduction_case10:
      forall r1 r2,
      op_strength_reduction_cases (Oxor) (r1 :: r2 :: nil)
  | op_strength_reduction_case11:
      forall r1 r2,
      op_strength_reduction_cases (Oshl) (r1 :: r2 :: nil)
  | op_strength_reduction_case12:
      forall r1 r2,
      op_strength_reduction_cases (Oshr) (r1 :: r2 :: nil)
  | op_strength_reduction_case13:
      forall r1 r2,
      op_strength_reduction_cases (Oshru) (r1 :: r2 :: nil)
  | op_strength_reduction_case14:
      forall addr args,
      op_strength_reduction_cases (Olea addr) (args)
  | op_strength_reduction_case15:
      forall c args,
      op_strength_reduction_cases (Ocmp c) (args)
  | op_strength_reduction_default:
      forall (op: operation) (args: list reg),
      op_strength_reduction_cases op args.

Definition op_strength_reduction_match (op: operation) (args: list reg) :=
  match op as z1, args as z2 return op_strength_reduction_cases z1 z2 with
  | Osub, r1 :: r2 :: nil =>
      op_strength_reduction_case2 r1 r2
  | Omul, r1 :: r2 :: nil =>
      op_strength_reduction_case3 r1 r2
  | Odiv, r1 :: r2 :: nil =>
      op_strength_reduction_case4 r1 r2
  | Odivu, r1 :: r2 :: nil =>
      op_strength_reduction_case5 r1 r2
  | Omodu, r1 :: r2 :: nil =>
      op_strength_reduction_case7 r1 r2
  | Oand, r1 :: r2 :: nil =>
      op_strength_reduction_case8 r1 r2
  | Oor, r1 :: r2 :: nil =>
      op_strength_reduction_case9 r1 r2
  | Oxor, r1 :: r2 :: nil =>
      op_strength_reduction_case10 r1 r2
  | Oshl, r1 :: r2 :: nil =>
      op_strength_reduction_case11 r1 r2
  | Oshr, r1 :: r2 :: nil =>
      op_strength_reduction_case12 r1 r2
  | Oshru, r1 :: r2 :: nil =>
      op_strength_reduction_case13 r1 r2
  | Olea addr, args =>
      op_strength_reduction_case14 addr args
  | Ocmp c, args =>
      op_strength_reduction_case15 c args
  | op, args =>
      op_strength_reduction_default op args
  end.

(** We must be careful to preserve 2-address constraints over the
    RTL code, which means that commutative operations cannot
    be specialized if their first argument is a constant. *)

Definition op_strength_reduction (op: operation) (args: list reg) :=
  match op_strength_reduction_match op args with
  | op_strength_reduction_case2 r1 r2 =>
      (* Osub *)
      match intval r2 with
      | Some n => make_addimm (Int.neg n) r1
      | _ => (op, args)
      end
  | op_strength_reduction_case3 r1 r2 =>
      (* Omul *)
      match intval r2 with
      | Some n => make_mulimm n r1
      | _ => (op, args)
      end
  | op_strength_reduction_case4 r1 r2 =>
      (* Odiv *)
      match intval r2 with
      | Some n =>
          match Int.is_power2 n with
          | Some l => if Int.ltu l (Int.repr 31)
                      then (Oshrximm l, r1 :: nil)
                      else (op, args)
          | None   => (op, args)
          end
      | None =>
          (op, args)
      end
  | op_strength_reduction_case5 r1 r2 =>
      (* Odivu *)
      match intval r2 with
      | Some n =>
          match Int.is_power2 n with
          | Some l => make_shruimm l r1
          | None   => (op, args)
          end
      | None =>
          (op, args)
      end
  | op_strength_reduction_case7 r1 r2 =>
      (* Omodu *)
      match intval r2 with
      | Some n =>
          match Int.is_power2 n with
          | Some l => (Oandimm (Int.sub n Int.one), r1 :: nil)
          | None   => (op, args)
          end
      | None =>
          (op, args)
      end
  | op_strength_reduction_case8 r1 r2 =>
      (* Oand *)
      match intval r2 with
      | Some n => make_andimm n r1
      | _ => (op, args)
      end
  | op_strength_reduction_case9 r1 r2 =>
      (* Oor *)
      match intval r2 with
      | Some n => make_orimm n r1
      | _ => (op, args)
      end
  | op_strength_reduction_case10 r1 r2 =>
      (* Oxor *)
      match intval r2 with
      | Some n => make_xorimm n r1
      | _ => (op, args)
      end
  | op_strength_reduction_case11 r1 r2 =>
      (* Oshl *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shlimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case12 r1 r2 =>
      (* Oshr *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shrimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case13 r1 r2 =>
      (* Oshru *)
      match intval r2 with
      | Some n =>
          if Int.ltu n Int.iwordsize
          then make_shruimm n r1
          else (op, args)
      | _ => (op, args)
      end
  | op_strength_reduction_case14 addr args =>
      (* Olea *)
      let (addr', args') := addr_strength_reduction addr args in
      (Olea addr', args')
  | op_strength_reduction_case15 c args =>
      (* Ocmp *)
      let (c', args') := cond_strength_reduction c args in
      (Ocmp c', args')
  | op_strength_reduction_default op args =>
      (* default *)
      (op, args)
  end.

End STRENGTH_REDUCTION.

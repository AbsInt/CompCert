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

(** Instruction selection for operators *)

(** The instruction selection pass recognizes opportunities for using
  combined arithmetic and logical operations and addressing modes
  offered by the target processor.  For instance, the expression [x + 1]
  can take advantage of the "immediate add" instruction of the processor,
  and on the PowerPC, the expression [(x >> 6) & 0xFF] can be turned
  into a "rotate and mask" instruction.

  This file defines functions for building CminorSel expressions and
  statements, especially expressions consisting of operator
  applications.  These functions examine their arguments to choose
  cheaper forms of operators whenever possible.

  For instance, [add e1 e2] will return a CminorSel expression semantically
  equivalent to [Eop Oadd (e1 ::: e2 ::: Enil)], but will use a
  [Oaddimm] operator if one of the arguments is an integer constant,
  or suppress the addition altogether if one of the arguments is the
  null integer.  In passing, we perform operator reassociation
  ([(e + c1) * c2] becomes [(e * c2) + (c1 * c2)]) and a small amount
  of constant propagation.

  On top of the "smart constructor" functions defined below,
  module [Selection] implements the actual instruction selection pass.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Cminor.
Require Import Op.
Require Import CminorSel.

Open Local Scope cminorsel_scope.

(** ** Constants **)

Definition addrsymbol (id: ident) (ofs: int) :=
  Eop (Olea (Aglobal id ofs)) Enil.

Definition addrstack (ofs: int) :=
  Eop (Olea (Ainstack ofs)) Enil.

(** ** Boolean negation *)

Definition notbool_base (e: expr) :=
  Eop (Ocmp (Ccompimm Ceq Int.zero)) (e ::: Enil).

Fixpoint notbool (e: expr) {struct e} : expr :=
  match e with
  | Eop (Ointconst n) Enil =>
      Eop (Ointconst (if Int.eq n Int.zero then Int.one else Int.zero)) Enil
  | Eop (Ocmp cond) args =>
      Eop (Ocmp (negate_condition cond)) args
  | Econdition e1 e2 e3 =>
      Econdition e1 (notbool e2) (notbool e3)
  | _ =>
      notbool_base e
  end.

(** ** Integer addition and pointer addition *)

Definition offset_addressing (a: addressing) (ofs: int) : addressing :=
  match a with
  | Aindexed n => Aindexed (Int.add n ofs)
  | Aindexed2 n => Aindexed2 (Int.add n ofs)
  | Ascaled sc n => Ascaled sc (Int.add n ofs)
  | Aindexed2scaled sc n => Aindexed2scaled sc (Int.add n ofs)
  | Aglobal id n => Aglobal id (Int.add n ofs)
  | Abased id n => Abased id (Int.add n ofs)
  | Abasedscaled sc id n => Abasedscaled sc id (Int.add n ofs)
  | Ainstack n => Ainstack (Int.add n ofs)
  end.

(** Addition of an integer constant *)

(*
Definition addimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e else
  match e with
  | Eop (Ointconst m) Enil       => Eop (Ointconst(Int.add n m)) Enil
  | Eop (Olea addr) args         => Eop (Olea (offset_addressing addr n)) args
  | _                            => Eop (Olea (Aindexed n)) (e ::: Enil)
  end.
*)

Inductive addimm_cases: forall (e: expr), Type :=
  | addimm_case1:
      forall m,
      addimm_cases (Eop (Ointconst m) Enil)
  | addimm_case2:
      forall addr args,
      addimm_cases (Eop (Olea addr) args)
  | addimm_default:
      forall (e: expr),
      addimm_cases e.

Definition addimm_match (e: expr) :=
  match e as z1 return addimm_cases z1 with
  | Eop (Ointconst m) Enil =>
      addimm_case1 m
  | Eop (Olea addr) args =>
      addimm_case2 addr args
  | e =>
      addimm_default e
  end.

Definition addimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e else
  match addimm_match e with
  | addimm_case1 m =>
      Eop (Ointconst(Int.add n m)) Enil
  | addimm_case2 addr args =>
      Eop (Olea (offset_addressing addr n)) args
  | addimm_default e =>
      Eop (Olea (Aindexed n)) (e ::: Enil)
  end.

(** Addition of two integer or pointer expressions *)

(*
Definition add (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => addimm n1 t2
  | t1, Eop (Ointconst n2) Enil => addimm n2 t1
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) => Eop (Olea (Aindexed2 (Int.add n1 n2))) (t1:::t2:::Enil)
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Ascaled sc n2)) (t2:::Enil) => Eop (Olea (Aindexed2scaled sc (Int.add n1 n2))) (t1:::t2:::Enil)
  | Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) => Eop (Olea (Aindexed2scaled sc (Int.add n1 n2))) (t2:::t1:::Enil)
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil) => Eop (Olea (Abased id (Int.add ofs n1))) (t1:::Enil)
  | Eop (Olea (Aglobal id ofs)) Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) => Eop (Olea (Abased id (Int.add ofs n2))) (t2:::Enil)
  | Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil) => Eop (Olea (Abasedscaled sc id (Int.add ofs n1))) (t1:::Enil)
  | Eop (Olea (Aglobal id ofs)) Enil), Eop (Olea (Ascaled sc n2)) (t2:::Enil) => Eop (Olea (Abasedscaled sc id (Int.add ofs n2))) (t2:::Enil)
  | Eop (Olea (Ascaled sc n)) (t1:::Enil), t2 => Eop (Olea (Aindexed2scaled sc n)) (t2:::t1:::Enil)
  | t1, Eop (Olea (Ascaled sc n)) (t2:::Enil) => Eop (Olea (Aindexed2scaled sc n)) (t1:::t2:::Enil)
  | Eop (Olea (Aindexed n)) (t1:::Enil), t2 => Eop (Olea (Aindexed2 n)) (t1:::t2:::Enil)
  | t1, Eop (Olea (Aindexed n)) (t2:::Enil) => Eop (Olea (Aindexed2 n)) (t1:::t2:::Enil)
  | _, _ => Eop (Olea (Aindexed2 Int.zero)) (e1:::e2:::Enil)
  end.
*)

Inductive add_cases: forall (e1: expr) (e2: expr), Type :=
  | add_case1:
      forall n1 t2,
      add_cases (Eop (Ointconst n1) Enil) (t2)
  | add_case2:
      forall t1 n2,
      add_cases (t1) (Eop (Ointconst n2) Enil)
  | add_case3:
      forall n1 t1 n2 t2,
      add_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | add_case4:
      forall n1 t1 sc n2 t2,
      add_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (Eop (Olea (Ascaled sc n2)) (t2:::Enil))
  | add_case5:
      forall sc n1 t1 n2 t2,
      add_cases (Eop (Olea (Ascaled sc n1)) (t1:::Enil)) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | add_case6:
      forall n1 t1 id ofs,
      add_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (Eop (Olea (Aglobal id ofs)) Enil)
  | add_case7:
      forall id ofs n2 t2,
      add_cases (Eop (Olea (Aglobal id ofs)) Enil) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | add_case8:
      forall sc n1 t1 id ofs,
      add_cases (Eop (Olea (Ascaled sc n1)) (t1:::Enil)) (Eop (Olea (Aglobal id ofs)) Enil)
  | add_case9:
      forall id ofs sc n2 t2,
      add_cases (Eop (Olea (Aglobal id ofs)) Enil) (Eop (Olea (Ascaled sc n2)) (t2:::Enil))
  | add_case10:
      forall sc n t1 t2,
      add_cases (Eop (Olea (Ascaled sc n)) (t1:::Enil)) (t2)
  | add_case11:
      forall t1 sc n t2,
      add_cases (t1) (Eop (Olea (Ascaled sc n)) (t2:::Enil))
  | add_case12:
      forall n t1 t2,
      add_cases (Eop (Olea (Aindexed n)) (t1:::Enil)) (t2)
  | add_case13:
      forall t1 n t2,
      add_cases (t1) (Eop (Olea (Aindexed n)) (t2:::Enil))
  | add_default:
      forall (e1: expr) (e2: expr),
      add_cases e1 e2.

Definition add_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return add_cases z1 z2 with
  | Eop (Ointconst n1) Enil, t2 =>
      add_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil =>
      add_case2 t1 n2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      add_case3 n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Ascaled sc n2)) (t2:::Enil) =>
      add_case4 n1 t1 sc n2 t2
  | Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      add_case5 sc n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil =>
      add_case6 n1 t1 id ofs
  | Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      add_case7 id ofs n2 t2
  | Eop (Olea (Ascaled sc n1)) (t1:::Enil), Eop (Olea (Aglobal id ofs)) Enil =>
      add_case8 sc n1 t1 id ofs
  | Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Ascaled sc n2)) (t2:::Enil) =>
      add_case9 id ofs sc n2 t2
  | Eop (Olea (Ascaled sc n)) (t1:::Enil), t2 =>
      add_case10 sc n t1 t2
  | t1, Eop (Olea (Ascaled sc n)) (t2:::Enil) =>
      add_case11 t1 sc n t2
  | Eop (Olea (Aindexed n)) (t1:::Enil), t2 =>
      add_case12 n t1 t2
  | t1, Eop (Olea (Aindexed n)) (t2:::Enil) =>
      add_case13 t1 n t2
  | e1, e2 =>
      add_default e1 e2
  end.

Definition add (e1: expr) (e2: expr) :=
  match add_match e1 e2 with
  | add_case1 n1 t2 =>
      addimm n1 t2
  | add_case2 t1 n2 =>
      addimm n2 t1
  | add_case3 n1 t1 n2 t2 =>
      Eop (Olea (Aindexed2 (Int.add n1 n2))) (t1:::t2:::Enil)
  | add_case4 n1 t1 sc n2 t2 =>
      Eop (Olea (Aindexed2scaled sc (Int.add n1 n2))) (t1:::t2:::Enil)
  | add_case5 sc n1 t1 n2 t2 =>
      Eop (Olea (Aindexed2scaled sc (Int.add n1 n2))) (t2:::t1:::Enil)
  | add_case6 n1 t1 id ofs =>
      Eop (Olea (Abased id (Int.add ofs n1))) (t1:::Enil)
  | add_case7 id ofs n2 t2 =>
      Eop (Olea (Abased id (Int.add ofs n2))) (t2:::Enil)
  | add_case8 sc n1 t1 id ofs =>
      Eop (Olea (Abasedscaled sc id (Int.add ofs n1))) (t1:::Enil)
  | add_case9 id ofs sc n2 t2 =>
      Eop (Olea (Abasedscaled sc id (Int.add ofs n2))) (t2:::Enil)
  | add_case10 sc n t1 t2 =>
      Eop (Olea (Aindexed2scaled sc n)) (t2:::t1:::Enil)
  | add_case11 t1 sc n t2 =>
      Eop (Olea (Aindexed2scaled sc n)) (t1:::t2:::Enil)
  | add_case12 n t1 t2 =>
      Eop (Olea (Aindexed2 n)) (t1:::t2:::Enil)
  | add_case13 t1 n t2 =>
      Eop (Olea (Aindexed2 n)) (t1:::t2:::Enil)
  | add_default e1 e2 =>
      Eop (Olea (Aindexed2 Int.zero)) (e1:::e2:::Enil)
  end.

(** ** Integer and pointer subtraction *)

(*
Definition sub (e1: expr) (e2: expr) :=
  match e1, e2 with
  | t1, Eop (Ointconst n2) Enil => addimm (Int.neg n2) t1
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) => addimm (Int.sub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | Eop (Olea (Aindexed n1)) (t1:::Enil), t2 => addimm n1 (Eop Osub (t1:::t2:::Enil))
  | t1, Eop (Olea (Aindexed n2)) (t2:::Enil) => addimm (Int.neg n2) (Eop Osub (t1:::t2:::Enil))
  | _, _ => Eop Osub (e1:::e2:::Enil)
  end.
*)

Inductive sub_cases: forall (e1: expr) (e2: expr), Type :=
  | sub_case1:
      forall t1 n2,
      sub_cases (t1) (Eop (Ointconst n2) Enil)
  | sub_case2:
      forall n1 t1 n2 t2,
      sub_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | sub_case3:
      forall n1 t1 t2,
      sub_cases (Eop (Olea (Aindexed n1)) (t1:::Enil)) (t2)
  | sub_case4:
      forall t1 n2 t2,
      sub_cases (t1) (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | sub_default:
      forall (e1: expr) (e2: expr),
      sub_cases e1 e2.

Definition sub_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return sub_cases z1 z2 with
  | t1, Eop (Ointconst n2) Enil =>
      sub_case1 t1 n2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      sub_case2 n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (t1:::Enil), t2 =>
      sub_case3 n1 t1 t2
  | t1, Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      sub_case4 t1 n2 t2
  | e1, e2 =>
      sub_default e1 e2
  end.

Definition sub (e1: expr) (e2: expr) :=
  match sub_match e1 e2 with
  | sub_case1 t1 n2 =>
      addimm (Int.neg n2) t1
  | sub_case2 n1 t1 n2 t2 =>
      addimm (Int.sub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | sub_case3 n1 t1 t2 =>
      addimm n1 (Eop Osub (t1:::t2:::Enil))
  | sub_case4 t1 n2 t2 =>
      addimm (Int.neg n2) (Eop Osub (t1:::t2:::Enil))
  | sub_default e1 e2 =>
      Eop Osub (e1:::e2:::Enil)
  end.

(** ** Immediate shifts *)

Definition shift_is_scale (n: int) : bool :=
  Int.eq n (Int.repr 1) || Int.eq n (Int.repr 2) || Int.eq n (Int.repr 3).

(*
Definition shlimm (e1: expr) :=
  if Int.eq n Int.zero then e1 else
  match e1 with
  | Eop (Ointconst n1) Enil => Eop (Ointconst(Int.shl n1 n))
  | Eop (Oshlimm n1) (t1:::Enil) => if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshlimm (Int.add n n1)) (t1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  | Eop (Olea (Aindexed n1)) (t1:::Enil) => if shift_is_scale n then Eop (Olea (Ascaled (Int.shl Int.one n) (Int.shl n1 n))) (t1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  | _ => if shift_is_scale n then Eop (Olea (Ascaled (Int.shl Int.one n) Int.zero) (t1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  end.
*)

Inductive shlimm_cases: forall (e1: expr), Type :=
  | shlimm_case1:
      forall n1,
      shlimm_cases (Eop (Ointconst n1) Enil)
  | shlimm_case2:
      forall n1 t1,
      shlimm_cases (Eop (Oshlimm n1) (t1:::Enil))
  | shlimm_case3:
      forall n1 t1,
      shlimm_cases (Eop (Olea (Aindexed n1)) (t1:::Enil))
  | shlimm_default:
      forall (e1: expr),
      shlimm_cases e1.

Definition shlimm_match (e1: expr) :=
  match e1 as z1 return shlimm_cases z1 with
  | Eop (Ointconst n1) Enil =>
      shlimm_case1 n1
  | Eop (Oshlimm n1) (t1:::Enil) =>
      shlimm_case2 n1 t1
  | Eop (Olea (Aindexed n1)) (t1:::Enil) =>
      shlimm_case3 n1 t1
  | e1 =>
      shlimm_default e1
  end.

Definition shlimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  match shlimm_match e1 with
  | shlimm_case1 n1 =>
      Eop (Ointconst(Int.shl n1 n)) Enil
  | shlimm_case2 n1 t1 =>
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshlimm (Int.add n n1)) (t1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  | shlimm_case3 n1 t1 =>
      if shift_is_scale n then Eop (Olea (Ascaled (Int.shl Int.one n) (Int.shl n1 n))) (t1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  | shlimm_default e1 =>
      if shift_is_scale n then Eop (Olea (Ascaled (Int.shl Int.one n) Int.zero)) (e1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  end.

(*
Definition shruimm (e1: expr) :=
  if Int.eq n Int.zero then e1 else
  match e1 with
  | Eop (Ointconst n1) Enil => Eop (Ointconst(Int.shru n1 n))
  | Eop (Oshruimm n1) (t1:::Enil) => if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshruimm (Int.add n n1)) (t1:::Enil) else Eop (Oshruimm n) (e1:::Enil)
  | _ => Eop (Oshruimm n) (e1:::Enil)
  end.
*)

Inductive shruimm_cases: forall (e1: expr), Type :=
  | shruimm_case1:
      forall n1,
      shruimm_cases (Eop (Ointconst n1) Enil)
  | shruimm_case2:
      forall n1 t1,
      shruimm_cases (Eop (Oshruimm n1) (t1:::Enil))
  | shruimm_default:
      forall (e1: expr),
      shruimm_cases e1.

Definition shruimm_match (e1: expr) :=
  match e1 as z1 return shruimm_cases z1 with
  | Eop (Ointconst n1) Enil =>
      shruimm_case1 n1
  | Eop (Oshruimm n1) (t1:::Enil) =>
      shruimm_case2 n1 t1
  | e1 =>
      shruimm_default e1
  end.

Definition shruimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  match shruimm_match e1 with
  | shruimm_case1 n1 =>
      Eop (Ointconst(Int.shru n1 n)) Enil
  | shruimm_case2 n1 t1 =>
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshruimm (Int.add n n1)) (t1:::Enil) else Eop (Oshruimm n) (e1:::Enil)
  | shruimm_default e1 =>
      Eop (Oshruimm n) (e1:::Enil)
  end.

(*
Definition shrimm (e1: expr) :=
  if Int.eq n Int.zero then e1 else
  match e1 with
  | Eop (Ointconst n1) Enil => Eop (Ointconst(Int.shr n1 n)) Enil
  | Eop (Oshrimm n1) (t1:::Enil) => if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshrimm (Int.add n n1)) (t1:::Enil) else Eop (Oshrimm n) (e1:::Enil)
  | _ => Eop (Oshrimm n) (e1:::Enil)
  end.
*)

Inductive shrimm_cases: forall (e1: expr), Type :=
  | shrimm_case1:
      forall n1,
      shrimm_cases (Eop (Ointconst n1) Enil)
  | shrimm_case2:
      forall n1 t1,
      shrimm_cases (Eop (Oshrimm n1) (t1:::Enil))
  | shrimm_default:
      forall (e1: expr),
      shrimm_cases e1.

Definition shrimm_match (e1: expr) :=
  match e1 as z1 return shrimm_cases z1 with
  | Eop (Ointconst n1) Enil =>
      shrimm_case1 n1
  | Eop (Oshrimm n1) (t1:::Enil) =>
      shrimm_case2 n1 t1
  | e1 =>
      shrimm_default e1
  end.

Definition shrimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else 
  match shrimm_match e1 with
  | shrimm_case1 n1 =>
      Eop (Ointconst(Int.shr n1 n)) Enil
  | shrimm_case2 n1 t1 =>
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshrimm (Int.add n n1)) (t1:::Enil) else Eop (Oshrimm n) (e1:::Enil)
  | shrimm_default e1 =>
      Eop (Oshrimm n) (e1:::Enil)
  end.

(** ** Integer multiply *)

Definition mulimm_base (n1: int) (e2: expr) :=
  match Int.one_bits n1 with
  | i :: nil =>
      shlimm e2 i
  | i :: j :: nil =>
      Elet e2 (add (shlimm (Eletvar 0) i) (shlimm (Eletvar 0) j))
  | _ =>
      Eop (Omulimm n1) (e2:::Enil)
  end.

(*
Definition mulimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then 
   Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.one then
    e2
  else match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst(intmul n1 n2)) Enil
  | Eop (Olea (Aindexed n2)) (t2:::Enil) => if mul_is_scale n1 then Eop (Olea (Ascaled n1 (Int.mul n1 n2))) (t2:::Enil) else addimm (Int.mul n1 n2) (mulimm_base n1 t2)
  | _ => mulimm_base n1 e2
  end.

Definition mulimm (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst(intmul n1 n2)) Enil
  | Eop (Olea (Aindexed n2)) (t2:::Enil) => if mul_is_scale n1 then Eop (Olea (Ascaled n1 (Int.mul n1 n2))) (t2:::Enil) else addimm (Int.mul n1 n2) (mulimm_base n1 t2)
  | _ => mulimm_base n1 e2
  end.
*)

Inductive mulimm_cases: forall (e2: expr), Type :=
  | mulimm_case1:
      forall n2,
      mulimm_cases (Eop (Ointconst n2) Enil)
  | mulimm_case2:
      forall n2 t2,
      mulimm_cases (Eop (Olea (Aindexed n2)) (t2:::Enil))
  | mulimm_default:
      forall (e2: expr),
      mulimm_cases e2.

Definition mulimm_match (e2: expr) :=
  match e2 as z1 return mulimm_cases z1 with
  | Eop (Ointconst n2) Enil =>
      mulimm_case1 n2
  | Eop (Olea (Aindexed n2)) (t2:::Enil) =>
      mulimm_case2 n2 t2
  | e2 =>
      mulimm_default e2
  end.

Definition mulimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then 
   Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.one then
    e2
  else match mulimm_match e2 with
  | mulimm_case1 n2 =>
      Eop (Ointconst(Int.mul n1 n2)) Enil
  | mulimm_case2 n2 t2 =>
      addimm (Int.mul n1 n2) (mulimm_base n1 t2)
  | mulimm_default e2 =>
      mulimm_base n1 e2
  end.

(*
Definition mul (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => mulimm n1 t2
  | t1, Eop (Ointconst n2) Enil => mulimm n2 t1
  | _, _ => Eop Omul (e1:::e2:::Enil)
  end.
*)

Inductive mul_cases: forall (e1: expr) (e2: expr), Type :=
  | mul_case1:
      forall (n1: int) (t2: expr),
      mul_cases (Eop (Ointconst n1) Enil) (t2)
  | mul_case2:
      forall (t1: expr) (n2: int),
      mul_cases (t1) (Eop (Ointconst n2) Enil)
  | mul_default:
      forall (e1: expr) (e2: expr),
      mul_cases e1 e2.

Definition mul_match_aux (e1: expr) (e2: expr) :=
  match e2 as z2 return mul_cases e1 z2 with
  | Eop (Ointconst n2) Enil =>
      mul_case2 e1 n2
  | e2 =>
      mul_default e1 e2
  end.

Definition mul_match (e1: expr) (e2: expr) :=
  match e1 as z1 return mul_cases z1 e2 with
  | Eop (Ointconst n1) Enil =>
      mul_case1 n1 e2
  | e1 =>
      mul_match_aux e1 e2
  end.

Definition mul (e1: expr) (e2: expr) :=
  match mul_match e1 e2 with
  | mul_case1 n1 t2 =>
      mulimm n1 t2
  | mul_case2 t1 n2 =>
      mulimm n2 t1
  | mul_default e1 e2 =>
      Eop Omul (e1:::e2:::Enil)
  end.

(** ** Bitwise and, or, xor *)

Definition orimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e
  else if Int.eq n Int.mone then Eop (Ointconst Int.mone) Enil
  else Eop (Oorimm n) (e:::Enil).

Definition same_expr_pure (e1 e2: expr) :=
  match e1, e2 with
  | Evar v1, Evar v2 => if ident_eq v1 v2 then true else false
  | _, _ => false
  end.

(*
Definition or (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => orimm n1 t2
  | t1, Eop (Ointconst n2) Enil => orimm n2 t1
  | Eop (Oshlimm n1) (t1:::Enil), Eop (Oshruimm n2) (t2:::Enil)) => ...
  | Eop (Oshruimm n2) (t2:::Enil)), Eop (Oshlimm n1) (t1:::Enil) => ...
  | _, _ => Eop Oor (e1:::e2:::Enil)
  end.
*)

Inductive or_cases: forall (e1: expr) (e2: expr), Type :=
  | or_case1:
      forall n1 t2,
      or_cases (Eop (Ointconst n1) Enil) (t2)
  | or_case2:
      forall t1 n2,
      or_cases (t1) (Eop (Ointconst n2) Enil)
  | or_case3:
      forall n1 t1 n2 t2,
      or_cases (Eop (Oshlimm n1) (t1:::Enil)) (Eop (Oshruimm n2) (t2:::Enil))
  | or_case4:
      forall n2 t2 n1 t1,
      or_cases (Eop (Oshruimm n2) (t2:::Enil)) (Eop (Oshlimm n1) (t1:::Enil))
  | or_default:
      forall (e1: expr) (e2: expr),
      or_cases e1 e2.

Definition or_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return or_cases z1 z2 with
  | Eop (Ointconst n1) Enil, t2 =>
      or_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil =>
      or_case2 t1 n2
  | Eop (Oshlimm n1) (t1:::Enil), Eop (Oshruimm n2) (t2:::Enil) =>
      or_case3 n1 t1 n2 t2
  | Eop (Oshruimm n2) (t2:::Enil), Eop (Oshlimm n1) (t1:::Enil) =>
      or_case4 n2 t2 n1 t1
  | e1, e2 =>
      or_default e1 e2
  end.

Definition or (e1: expr) (e2: expr) :=
  match or_match e1 e2 with
  | or_case1 n1 t2 =>
      orimm n1 t2
  | or_case2 t1 n2 =>
      orimm n2 t1
  | or_case3 n1 t1 n2 t2 =>
      if Int.eq (Int.add n1 n2) Int.iwordsize
      && same_expr_pure t1 t2
      then Eop (Ororimm n2) (t1:::Enil)
      else Eop Oor (e1:::e2:::Enil)
  | or_case4 n2 t2 n1 t1 =>
      if Int.eq (Int.add n1 n2) Int.iwordsize
      && same_expr_pure t1 t2
      then Eop (Ororimm n2) (t1:::Enil)
      else Eop Oor (e1:::e2:::Enil)
  | or_default e1 e2 =>
      Eop Oor (e1:::e2:::Enil)
  end.

Definition andimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then Eop (Ointconst Int.zero) Enil
  else if Int.eq n Int.mone then e
  else Eop (Oandimm n) (e:::Enil).

Definition and (e1: expr) (e2: expr) :=
  match mul_match e1 e2 with
  | mul_case1 n1 t2 =>
      andimm n1 t2
  | mul_case2 t1 n2 =>
      andimm n2 t1
  | mul_default e1 e2 =>
      Eop Oand (e1:::e2:::Enil)
  end.

Definition xorimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e
  else Eop (Oxorimm n) (e:::Enil).

Definition xor (e1: expr) (e2: expr) :=
  match mul_match e1 e2 with
  | mul_case1 n1 t2 =>
      xorimm n1 t2
  | mul_case2 t1 n2 =>
      xorimm n2 t1
  | mul_default e1 e2 =>
      Eop Oxor (e1:::e2:::Enil)
  end.

(** ** General shifts *)

Inductive shift_cases: forall (e1: expr), Type :=
  | shift_case1:
      forall (n2: int),
      shift_cases (Eop (Ointconst n2) Enil)
  | shift_default:
      forall (e1: expr),
      shift_cases e1.

Definition shift_match (e1: expr) :=
  match e1 as z1 return shift_cases z1 with
  | Eop (Ointconst n2) Enil =>
      shift_case1 n2
  | e1 =>
      shift_default e1
  end.

Definition shl (e1: expr) (e2: expr) :=
  match shift_match e2 with
  | shift_case1 n2 =>
      shlimm e1 n2
  | shift_default e2 =>
      Eop Oshl (e1:::e2:::Enil)
  end.

Definition shru (e1: expr) (e2: expr) :=
  match shift_match e2 with
  | shift_case1 n2 =>
      shruimm e1 n2
  | shift_default e2 =>
      Eop Oshru (e1:::e2:::Enil)
  end.

Definition shr (e1: expr) (e2: expr) :=
  match shift_match e2 with
  | shift_case1 n2 =>
      shrimm e1 n2
  | shift_default e2 =>
      Eop Oshr (e1:::e2:::Enil)
  end.

(** ** Comparisons *)

Inductive comp_cases: forall (e1: expr) (e2: expr), Type :=
  | comp_case1:
      forall n1 t2,
      comp_cases (Eop (Ointconst n1) Enil) (t2)
  | comp_case2:
      forall t1 n2,
      comp_cases (t1) (Eop (Ointconst n2) Enil)
  | comp_default:
      forall (e1: expr) (e2: expr),
      comp_cases e1 e2.

Definition comp_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return comp_cases z1 z2 with
  | Eop (Ointconst n1) Enil, t2 =>
      comp_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil =>
      comp_case2 t1 n2
  | e1, e2 =>
      comp_default e1 e2
  end.

Definition comp (c: comparison) (e1: expr) (e2: expr) :=
  match comp_match e1 e2 with
  | comp_case1 n1 t2 =>
      Eop (Ocmp (Ccompimm (swap_comparison c) n1)) (t2 ::: Enil)
  | comp_case2 t1 n2 =>
      Eop (Ocmp (Ccompimm c n2)) (t1 ::: Enil)
  | comp_default e1 e2 =>
      Eop (Ocmp (Ccomp c)) (e1 ::: e2 ::: Enil)
  end.

Definition compu (c: comparison) (e1: expr) (e2: expr) :=
  match comp_match e1 e2 with
  | comp_case1 n1 t2 =>
      Eop (Ocmp (Ccompuimm (swap_comparison c) n1)) (t2 ::: Enil)
  | comp_case2 t1 n2 =>
      Eop (Ocmp (Ccompuimm c n2)) (t1 ::: Enil)
  | comp_default e1 e2 =>
      Eop (Ocmp (Ccompu c)) (e1 ::: e2 ::: Enil)
  end.

Definition compf (c: comparison) (e1: expr) (e2: expr) :=
  Eop (Ocmp (Ccompf c)) (e1 ::: e2 ::: Enil).

(** ** Other operators, not optimized. *)

Definition cast8unsigned (e: expr) := Eop Ocast8unsigned (e ::: Enil).
Definition cast8signed (e: expr) := Eop Ocast8signed (e ::: Enil).
Definition cast16unsigned (e: expr) := Eop Ocast16unsigned (e ::: Enil).
Definition cast16signed (e: expr) := Eop Ocast16signed (e ::: Enil).
Definition divu (e1: expr) (e2: expr) := Eop Odivu (e1:::e2:::Enil).
Definition modu (e1: expr) (e2: expr) := Eop Omodu (e1:::e2:::Enil).
Definition divs (e1: expr) (e2: expr) := Eop Odiv (e1:::e2:::Enil).
Definition mods (e1: expr) (e2: expr) := Eop Omod (e1:::e2:::Enil).
Definition negint (e: expr) := Eop Oneg (e ::: Enil).
Definition notint (e: expr) := Eop (Oxorimm Int.mone) (e ::: Enil).
Definition negf (e: expr) :=  Eop Onegf (e ::: Enil).
Definition absf (e: expr) :=  Eop Oabsf (e ::: Enil).
Definition singleoffloat (e: expr) := Eop Osingleoffloat (e ::: Enil).
Definition intoffloat (e: expr) := Eop Ointoffloat (e ::: Enil).
Definition floatofint (e: expr) := Eop Ofloatofint (e ::: Enil).
Definition addf (e1 e2: expr) :=  Eop Oaddf (e1 ::: e2 ::: Enil).
Definition subf (e1 e2: expr) :=  Eop Osubf (e1 ::: e2 ::: Enil).
Definition mulf (e1 e2: expr) :=  Eop Omulf (e1 ::: e2 ::: Enil).
Definition divf (e1 e2: expr) :=  Eop Odivf (e1 ::: e2 ::: Enil).

(** ** Conversions between unsigned ints and floats *)

Definition intuoffloat (e: expr) :=
  let f := Eop (Ofloatconst (Float.floatofintu Float.ox8000_0000)) Enil in
  Elet e
    (Econdition (CEcond (Ccompf Clt) (Eletvar O ::: f ::: Enil))
      (intoffloat (Eletvar O))
      (addimm Float.ox8000_0000 (intoffloat (subf (Eletvar O) f)))).

Definition floatofintu (e: expr) :=
  let f := Eop (Ofloatconst (Float.floatofintu Float.ox8000_0000)) Enil in
  Elet e
    (Econdition (CEcond (Ccompuimm Clt Float.ox8000_0000) (Eletvar O ::: Enil))
      (floatofint (Eletvar O))
      (addf (floatofint (addimm (Int.neg Float.ox8000_0000) (Eletvar O))) f)).

(** ** Addressing modes *)

(*
Definition addressing (e: expr) :=
  match e with
  | Eop (Olea addr) args => (addr, args)
  | _ => (Aindexed Int.zero, e:::Enil)
  end.
*)

Inductive addressing_cases: forall (e: expr), Type :=
  | addressing_case1:
      forall addr args,
      addressing_cases (Eop (Olea addr) args)
  | addressing_default:
      forall (e: expr),
      addressing_cases e.

Definition addressing_match (e: expr) :=
  match e as z1 return addressing_cases z1 with
  | Eop (Olea addr) args =>
      addressing_case1 addr args
  | e =>
      addressing_default e
  end.

Definition addressing (chunk: memory_chunk) (e: expr) :=
  match addressing_match e with
  | addressing_case1 addr args =>
      (addr, args)
  | addressing_default e =>
      (Aindexed Int.zero, e:::Enil)
  end.


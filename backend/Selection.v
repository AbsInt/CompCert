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

(** Instruction selection *)

(** The instruction selection pass recognizes opportunities for using
  combined arithmetic and logical operations and addressing modes
  offered by the target processor.  For instance, the expression [x + 1]
  can take advantage of the "immediate add" instruction of the processor,
  and on the PowerPC, the expression [(x >> 6) & 0xFF] can be turned
  into a "rotate and mask" instruction.

  Instruction selection proceeds by bottom-up rewriting over expressions.
  The source language is Cminor and the target language is CminorSel. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Cminor.
Require Import Op.
Require Import CminorSel.

Infix ":::" := Econs (at level 60, right associativity) : selection_scope.

Open Local Scope selection_scope.

(** * Lifting of let-bound variables *)

(** Some of the instruction functions generate [Elet] constructs to
  share the evaluation of a subexpression.  Owing to the use of de
  Bruijn indices for let-bound variables, we need to shift de Bruijn
  indices when an expression [b] is put in a [Elet a b] context. *)

Fixpoint lift_expr (p: nat) (a: expr) {struct a}: expr :=
  match a with
  | Evar id => Evar id
  | Eop op bl => Eop op (lift_exprlist p bl)
  | Eload chunk addr bl => Eload chunk addr (lift_exprlist p bl)
  | Econdition b c d =>
      Econdition (lift_condexpr p b) (lift_expr p c) (lift_expr p d)
  | Elet b c => Elet (lift_expr p b) (lift_expr (S p) c)
  | Eletvar n =>
      if le_gt_dec p n then Eletvar (S n) else Eletvar n
  end

with lift_condexpr (p: nat) (a: condexpr) {struct a}: condexpr :=
  match a with
  | CEtrue => CEtrue
  | CEfalse => CEfalse
  | CEcond cond bl => CEcond cond (lift_exprlist p bl)
  | CEcondition b c d =>
      CEcondition (lift_condexpr p b) (lift_condexpr p c) (lift_condexpr p d)
  end

with lift_exprlist (p: nat) (a: exprlist) {struct a}: exprlist :=
  match a with
  | Enil => Enil
  | Econs b cl => Econs (lift_expr p b) (lift_exprlist p cl)
  end.

Definition lift (a: expr): expr := lift_expr O a.

(** * Smart constructors for operators *)

(** This section defines functions for building CminorSel expressions
  and statements, especially expressions consisting of operator
  applications.  These functions examine their arguments to choose
  cheaper forms of operators whenever possible.

  For instance, [add e1 e2] will return a CminorSel expression semantically
  equivalent to [Eop Oadd (e1 ::: e2 ::: Enil)], but will use a
  [Oaddimm] operator if one of the arguments is an integer constant,
  or suppress the addition altogether if one of the arguments is the
  null integer.  In passing, we perform operator reassociation
  ([(e + c1) * c2] becomes [(e * c2) + (c1 * c2)]) and a small amount
  of constant propagation.
*)

(** ** Integer logical negation *)

(** The natural way to write smart constructors is by pattern-matching
  on their arguments, recognizing cases where cheaper operators
  or combined operators are applicable.  For instance, integer logical
  negation has three special cases (not-and, not-or and not-xor),
  along with a default case that uses not-or over its arguments and itself.
  This is written naively as follows:
<<
Definition notint (e: expr) :=
  match e with
  | Eop Oand (t1:::t2:::Enil) => Eop Onand (t1:::t2:::Enil)
  | Eop Oor (t1:::t2:::Enil) => Eop Onor (t1:::t2:::Enil)
  | Eop Oxor (t1:::t2:::Enil) => Eop Onxor (t1:::t2:::Enil)
  | _ => Elet(e, Eop Onor (Eletvar O ::: Eletvar O ::: Enil)
  end.
>>
  However, Coq expands complex pattern-matchings like the above into
  elementary matchings over all constructors of an inductive type,
  resulting in much duplication of the final catch-all case.
  Such duplications generate huge executable code and duplicate
  cases in the correctness proofs.

  To limit this duplication, we use the following trick due to
  Yves Bertot.  We first define a dependent inductive type that
  characterizes the expressions that match each of the 4 cases of interest.
*)

Inductive notint_cases: forall (e: expr), Set :=
  | notint_case1:
      forall (t1: expr) (t2: expr),
      notint_cases (Eop Oand (t1:::t2:::Enil))
  | notint_case2:
      forall (t1: expr) (t2: expr),
      notint_cases (Eop Oor (t1:::t2:::Enil))
  | notint_case3:
      forall (t1: expr) (t2: expr),
      notint_cases (Eop Oxor (t1:::t2:::Enil))
  | notint_default:
      forall (e: expr),
      notint_cases e.

(** We then define a classification function that takes an expression
  and return the case in which it falls.  Note that the catch-all case
  [notint_default] does not state that it is mutually exclusive with
  the first three, more specific cases.  The classification function
  nonetheless chooses the specific cases in preference to the catch-all
  case. *)

Definition notint_match (e: expr) :=
  match e as z1 return notint_cases z1 with
  | Eop Oand (t1:::t2:::Enil) =>
      notint_case1 t1 t2
  | Eop Oor (t1:::t2:::Enil) =>
      notint_case2 t1 t2
  | Eop Oxor (t1:::t2:::Enil) =>
      notint_case3 t1 t2
  | e =>
      notint_default e
  end.

(** Finally, the [notint] function we need is defined by a 4-case match
  over the result of the classification function.  Thus, no duplication
  of the right-hand sides of this match occur, and the proof has only
  4 cases to consider (it proceeds by case over [notint_match e]).
  Since the default case is not obviously exclusive with the three
  specific cases, it is important that its right-hand side is
  semantically correct for all possible values of [e], which is the
  case here and for all other smart constructors. *)

Definition notint (e: expr) :=
  match notint_match e with
  | notint_case1 t1 t2 =>
      Eop Onand (t1:::t2:::Enil)
  | notint_case2 t1 t2 =>
      Eop Onor (t1:::t2:::Enil)
  | notint_case3 t1 t2 =>
      Eop Onxor (t1:::t2:::Enil)
  | notint_default e =>
      Elet e (Eop Onor (Eletvar O ::: Eletvar O ::: Enil))
  end.

(** This programming pattern will be applied systematically for the
  other smart constructors in this file. *)

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

(*
Definition addimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e else
  match e with
  | Eop (Ointconst m) Enil       => Eop (Ointconst(Int.add n m)) Enil
  | Eop (Oaddrsymbol s m) Enil   => Eop (Oaddrsymbol s (Int.add n m)) Enil
  | Eop (Oaddrstack m) Enil      => Eop (Oaddrstack (Int.add n m)) Enil
  | Eop (Oaddimm m) (t ::: Enil) => Eop (Oaddimm(Int.add n m)) (t ::: Enil)
  | _                            => Eop (Oaddimm n) (e ::: Enil)
  end.
*)

(** Addition of an integer constant. *)

Inductive addimm_cases: forall (e: expr), Set :=
  | addimm_case1:
      forall (m: int),
      addimm_cases (Eop (Ointconst m) Enil)
  | addimm_case2:
      forall (s: ident) (m: int),
      addimm_cases (Eop (Oaddrsymbol s m) Enil)
  | addimm_case3:
      forall (m: int),
      addimm_cases (Eop (Oaddrstack m) Enil)
  | addimm_case4:
      forall (m: int) (t: expr),
      addimm_cases (Eop (Oaddimm m) (t ::: Enil))
  | addimm_default:
      forall (e: expr),
      addimm_cases e.

Definition addimm_match (e: expr) :=
  match e as z1 return addimm_cases z1 with
  | Eop (Ointconst m) Enil =>
      addimm_case1 m
  | Eop (Oaddrsymbol s m) Enil =>
      addimm_case2 s m
  | Eop (Oaddrstack m) Enil =>
      addimm_case3 m
  | Eop (Oaddimm m) (t ::: Enil) =>
      addimm_case4 m t
  | e =>
      addimm_default e
  end.

Definition addimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e else
  match addimm_match e with
  | addimm_case1 m =>
      Eop (Ointconst(Int.add n m)) Enil
  | addimm_case2 s m =>
      Eop (Oaddrsymbol s (Int.add n m)) Enil
  | addimm_case3 m =>
      Eop (Oaddrstack (Int.add n m)) Enil
  | addimm_case4 m t =>
      Eop (Oaddimm(Int.add n m)) (t ::: Enil)
  | addimm_default e =>
      Eop (Oaddimm n) (e ::: Enil)
  end.

(** Addition of two integer or pointer expressions. *)

(*
Definition add (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => addimm n1 t2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) => addimm (Int.add n1 n2) (Eop Oadd (t1:::t2:::Enil))
  | Eop(Oaddimm n1) (t1:::Enil)), t2 => addimm n1 (Eop Oadd (t1:::t2:::Enil))
  | t1, Eop (Ointconst n2) Enil => addimm n2 t1
  | t1, Eop (Oaddimm n2) (t2:::Enil) => addimm n2 (Eop Oadd (t1:::t2:::Enil))
  | _, _ => Eop Oadd (e1:::e2:::Enil)
  end.
*)

Inductive add_cases: forall (e1: expr) (e2: expr), Set :=
  | add_case1:
      forall (n1: int) (t2: expr),
      add_cases (Eop (Ointconst n1) Enil) (t2)
  | add_case2:
      forall (n1: int) (t1: expr) (n2: int) (t2: expr),
      add_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case3:
      forall (n1: int) (t1: expr) (t2: expr),
      add_cases (Eop(Oaddimm n1) (t1:::Enil)) (t2)
  | add_case4:
      forall (t1: expr) (n2: int),
      add_cases (t1) (Eop (Ointconst n2) Enil)
  | add_case5:
      forall (t1: expr) (n2: int) (t2: expr),
      add_cases (t1) (Eop (Oaddimm n2) (t2:::Enil))
  | add_default:
      forall (e1: expr) (e2: expr),
      add_cases e1 e2.

Definition add_match_aux (e1: expr) (e2: expr) :=
  match e2 as z2 return add_cases e1 z2 with
  | Eop (Ointconst n2) Enil =>
      add_case4 e1 n2
  | Eop (Oaddimm n2) (t2:::Enil) =>
      add_case5 e1 n2 t2
  | e2 =>
      add_default e1 e2
  end.

Definition add_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return add_cases z1 z2 with
  | Eop (Ointconst n1) Enil, t2 =>
      add_case1 n1 t2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) =>
      add_case2 n1 t1 n2 t2
  | Eop(Oaddimm n1) (t1:::Enil), t2 =>
      add_case3 n1 t1 t2
  | e1, e2 =>
      add_match_aux e1 e2
  end.

Definition add (e1: expr) (e2: expr) :=
  match add_match e1 e2 with
  | add_case1 n1 t2 =>
      addimm n1 t2
  | add_case2 n1 t1 n2 t2 =>
      addimm (Int.add n1 n2) (Eop Oadd (t1:::t2:::Enil))
  | add_case3 n1 t1 t2 =>
      addimm n1 (Eop Oadd (t1:::t2:::Enil))
  | add_case4 t1 n2 =>
      addimm n2 t1
  | add_case5 t1 n2 t2 =>
      addimm n2 (Eop Oadd (t1:::t2:::Enil))
  | add_default e1 e2 =>
      Eop Oadd (e1:::e2:::Enil)
  end.

(** ** Integer and pointer subtraction *)

(*
Definition sub (e1: expr) (e2: expr) :=
  match e1, e2 with
  | t1, Eop (Ointconst n2) Enil => addimm (Int.neg n2) t1
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) => addimm 
(intsub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | Eop (Oaddimm n1) (t1:::Enil), t2 => addimm n1 (Eop Osub (t1:::t2:::Rni
l))
  | t1, Eop (Oaddimm n2) (t2:::Enil) => addimm (Int.neg n2) (Eop Osub (t1:::
:t2:::Enil))
  | _, _ => Eop Osub (e1:::e2:::Enil)
  end.
*)

Inductive sub_cases: forall (e1: expr) (e2: expr), Set :=
  | sub_case1:
      forall (t1: expr) (n2: int),
      sub_cases (t1) (Eop (Ointconst n2) Enil)
  | sub_case2:
      forall (n1: int) (t1: expr) (n2: int) (t2: expr),
      sub_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddimm n2) (t2:::Enil))
  | sub_case3:
      forall (n1: int) (t1: expr) (t2: expr),
      sub_cases (Eop (Oaddimm n1) (t1:::Enil)) (t2)
  | sub_case4:
      forall (t1: expr) (n2: int) (t2: expr),
      sub_cases (t1) (Eop (Oaddimm n2) (t2:::Enil))
  | sub_default:
      forall (e1: expr) (e2: expr),
      sub_cases e1 e2.

Definition sub_match_aux (e1: expr) (e2: expr) :=
  match e1 as z1 return sub_cases z1 e2 with
  | Eop (Oaddimm n1) (t1:::Enil) =>
      sub_case3 n1 t1 e2
  | e1 =>
      sub_default e1 e2
  end.

Definition sub_match (e1: expr) (e2: expr) :=
  match e2 as z2, e1 as z1 return sub_cases z1 z2 with
  | Eop (Ointconst n2) Enil, t1 =>
      sub_case1 t1 n2
  | Eop (Oaddimm n2) (t2:::Enil), Eop (Oaddimm n1) (t1:::Enil) =>
      sub_case2 n1 t1 n2 t2
  | Eop (Oaddimm n2) (t2:::Enil), t1 =>
      sub_case4 t1 n2 t2
  | e2, e1 =>
      sub_match_aux e1 e2
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

(** ** Rotates and immediate shifts *)

(*
Definition rolm (e1: expr) :=
  match e1 with
  | Eop (Ointconst n1) Enil =>
      Eop (Ointconst(Int.and (Int.rol n1 amount2) mask2)) Enil
  | Eop (Orolm amount1 mask1) (t1:::Enil) =>
      let amount := Int.and (Int.add amount1 amount2) Ox1Fl in
      let mask := Int.and (Int.rol mask1 amount2) mask2 in
      if Int.is_rlw_mask mask
      then Eop (Orolm amount mask) (t1:::Enil)
      else Eop (Orolm amount2 mask2) (e1:::Enil)
  | _ => Eop (Orolm amount2 mask2) (e1:::Enil)
  end
*)

Inductive rolm_cases: forall (e1: expr), Set :=
  | rolm_case1:
      forall (n1: int),
      rolm_cases (Eop (Ointconst n1) Enil)
  | rolm_case2:
      forall (amount1: int) (mask1: int) (t1: expr),
      rolm_cases (Eop (Orolm amount1 mask1) (t1:::Enil))
  | rolm_default:
      forall (e1: expr),
      rolm_cases e1.

Definition rolm_match (e1: expr) :=
  match e1 as z1 return rolm_cases z1 with
  | Eop (Ointconst n1) Enil =>
      rolm_case1 n1
  | Eop (Orolm amount1 mask1) (t1:::Enil) =>
      rolm_case2 amount1 mask1 t1
  | e1 =>
      rolm_default e1
  end.

Definition rolm (e1: expr) (amount2 mask2: int) :=
  match rolm_match e1 with
  | rolm_case1 n1 =>
      Eop (Ointconst(Int.and (Int.rol n1 amount2) mask2)) Enil
  | rolm_case2 amount1 mask1 t1 =>
      let amount := Int.and (Int.add amount1 amount2) (Int.repr 31) in
      let mask := Int.and (Int.rol mask1 amount2) mask2 in
      if Int.is_rlw_mask mask
      then Eop (Orolm amount mask) (t1:::Enil)
      else Eop (Orolm amount2 mask2) (e1:::Enil)
  | rolm_default e1 =>
      Eop (Orolm amount2 mask2) (e1:::Enil)
  end.

Definition shlimm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then
    e1
  else if Int.ltu n2 (Int.repr 32) then
    rolm e1 n2 (Int.shl Int.mone n2)
  else
    Eop Oshl (e1:::Eop (Ointconst n2) Enil:::Enil).

Definition shruimm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then
    e1
  else if Int.ltu n2 (Int.repr 32) then
    rolm e1 (Int.sub (Int.repr 32) n2) (Int.shru Int.mone n2)
  else
    Eop Oshru (e1:::Eop (Ointconst n2) Enil:::Enil).

(** ** Integer multiply *)

Definition mulimm_base (n1: int) (e2: expr) :=
  match Int.one_bits n1 with
  | i :: nil =>
      shlimm e2 i
  | i :: j :: nil =>
      Elet e2
        (Eop Oadd (shlimm (Eletvar 0) i :::
                   shlimm (Eletvar 0) j ::: Enil))
  | _ =>
      Eop (Omulimm n1) (e2:::Enil)
  end.

(*
Definition mulimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then 
    Elet e2 (Eop (Ointconst Int.zero) Enil)
  else if Int.eq n1 Int.one then
    e2
  else match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst(intmul n1 n2)) Enil
  | Eop (Oaddimm n2) (t2:::Enil) => addimm (intmul n1 n2) (mulimm_base n1 t2)
  | _ => mulimm_base n1 e2
  end.
*)

Inductive mulimm_cases: forall (e2: expr), Set :=
  | mulimm_case1:
      forall (n2: int),
      mulimm_cases (Eop (Ointconst n2) Enil)
  | mulimm_case2:
      forall (n2: int) (t2: expr),
      mulimm_cases (Eop (Oaddimm n2) (t2:::Enil))
  | mulimm_default:
      forall (e2: expr),
      mulimm_cases e2.

Definition mulimm_match (e2: expr) :=
  match e2 as z1 return mulimm_cases z1 with
  | Eop (Ointconst n2) Enil =>
      mulimm_case1 n2
  | Eop (Oaddimm n2) (t2:::Enil) =>
      mulimm_case2 n2 t2
  | e2 =>
      mulimm_default e2
  end.

Definition mulimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then 
    Elet e2 (Eop (Ointconst Int.zero) Enil)
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

Inductive mul_cases: forall (e1: expr) (e2: expr), Set :=
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

(** ** Integer division and modulus *)

Definition divs (e1: expr) (e2: expr) := Eop Odiv (e1:::e2:::Enil).

Definition mod_aux (divop: operation) (e1 e2: expr) :=
  Elet e1
    (Elet (lift e2)
      (Eop Osub (Eletvar 1 :::
                 Eop Omul (Eop divop (Eletvar 1 ::: Eletvar 0 ::: Enil) :::
                           Eletvar 0 :::
                           Enil) :::
                 Enil))).

Definition mods := mod_aux Odiv.

Inductive divu_cases: forall (e2: expr), Set :=
  | divu_case1:
      forall (n2: int),
      divu_cases (Eop (Ointconst n2) Enil)
  | divu_default:
      forall (e2: expr),
      divu_cases e2.

Definition divu_match (e2: expr) :=
  match e2 as z1 return divu_cases z1 with
  | Eop (Ointconst n2) Enil =>
      divu_case1 n2
  | e2 =>
      divu_default e2
  end.

Definition divu (e1: expr) (e2: expr) :=
  match divu_match e2 with
  | divu_case1 n2 =>
      match Int.is_power2 n2 with
      | Some l2 => shruimm e1 l2
      | None    => Eop Odivu (e1:::e2:::Enil)
      end
  | divu_default e2 =>
      Eop Odivu (e1:::e2:::Enil)
  end.

Definition modu (e1: expr) (e2: expr) :=
  match divu_match e2 with
  | divu_case1 n2 =>
      match Int.is_power2 n2 with
      | Some l2 => rolm e1 Int.zero (Int.sub n2 Int.one)
      | None    => mod_aux Odivu e1 e2
      end
  | divu_default e2 =>
      mod_aux Odivu e1 e2
  end.

(** ** Bitwise and, or, xor *)

Definition andimm (n1: int) (e2: expr) :=
  if Int.is_rlw_mask n1
  then rolm e2 Int.zero n1
  else Eop (Oandimm n1) (e2:::Enil).

Definition and (e1: expr) (e2: expr) :=
  match mul_match e1 e2 with
  | mul_case1 n1 t2 =>
      andimm n1 t2
  | mul_case2 t1 n2 =>
      andimm n2 t1
  | mul_default e1 e2 =>
      Eop Oand (e1:::e2:::Enil)
  end.

Definition same_expr_pure (e1 e2: expr) :=
  match e1, e2 with
  | Evar v1, Evar v2 => if ident_eq v1 v2 then true else false
  | _, _ => false
  end.

Inductive or_cases: forall (e1: expr) (e2: expr), Set :=
  | or_case1:
      forall (amount1: int) (mask1: int) (t1: expr)
             (amount2: int) (mask2: int) (t2: expr),
      or_cases (Eop (Orolm amount1  mask1) (t1:::Enil)) 
               (Eop (Orolm amount2 mask2) (t2:::Enil))
  | or_default:
      forall (e1: expr) (e2: expr),
      or_cases e1 e2.

Definition or_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return or_cases z1 z2 with
  | Eop (Orolm amount1  mask1) (t1:::Enil),
    Eop (Orolm amount2 mask2) (t2:::Enil) =>
      or_case1 amount1 mask1 t1 amount2 mask2 t2
  | e1, e2 =>
      or_default e1 e2
  end.

Definition or (e1: expr) (e2: expr) :=
  match or_match e1 e2 with
  | or_case1 amount1 mask1 t1 amount2 mask2 t2 =>
      if Int.eq amount1 amount2
      && Int.is_rlw_mask (Int.or mask1 mask2)
      && same_expr_pure t1 t2
      then Eop (Orolm amount1 (Int.or mask1 mask2)) (t1:::Enil)
      else Eop Oor (e1:::e2:::Enil)
  | or_default e1 e2 =>
      Eop Oor (e1:::e2:::Enil)
  end.

(** ** General shifts *)

Inductive shift_cases: forall (e1: expr), Set :=
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

(** ** Floating-point arithmetic *)

(*
Definition addf (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop Omulf (t1:::t2:::Enil), t3 => Eop Omuladdf (t1:::t2:::t3:::Enil)
  | t1, Eop Omulf (t2:::t3:::Enil) => Elet t1 (Eop Omuladdf (t2:::t3:::Rvar 0:::Enil))
  | _, _ => Eop Oaddf (e1:::e2:::Enil)
  end.
*)

Inductive addf_cases: forall (e1: expr) (e2: expr), Set :=
  | addf_case1:
      forall (t1: expr) (t2: expr) (t3: expr),
      addf_cases (Eop Omulf (t1:::t2:::Enil)) (t3)
  | addf_case2:
      forall (t1: expr) (t2: expr) (t3: expr),
      addf_cases (t1) (Eop Omulf (t2:::t3:::Enil))
  | addf_default:
      forall (e1: expr) (e2: expr),
      addf_cases e1 e2.

Definition addf_match_aux (e1: expr) (e2: expr) :=
  match e2 as z2 return addf_cases e1 z2 with
  | Eop Omulf (t2:::t3:::Enil) =>
      addf_case2 e1 t2 t3
  | e2 =>
      addf_default e1 e2
  end.

Definition addf_match (e1: expr) (e2: expr) :=
  match e1 as z1 return addf_cases z1 e2 with
  | Eop Omulf (t1:::t2:::Enil) =>
      addf_case1 t1 t2 e2
  | e1 =>
      addf_match_aux e1 e2
  end.

Definition addf (e1: expr) (e2: expr) :=
  match addf_match e1 e2 with
  | addf_case1 t1 t2 t3 =>
      Eop Omuladdf (t1:::t2:::t3:::Enil)
  | addf_case2 t1 t2 t3 =>
      Elet t1 (Eop Omuladdf (lift t2:::lift t3:::Eletvar 0:::Enil))
  | addf_default e1 e2 =>
      Eop Oaddf (e1:::e2:::Enil)
  end.

(*
Definition subf (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop Omulfloat (t1:::t2:::Enil), t3 => Eop Omulsubf (t1:::t2:::t3:::Enil)
  | _, _ => Eop Osubf (e1:::e2:::Enil)
  end.
*)

Inductive subf_cases: forall (e1: expr) (e2: expr), Set :=
  | subf_case1:
      forall (t1: expr) (t2: expr) (t3: expr),
      subf_cases (Eop Omulf (t1:::t2:::Enil)) (t3)
  | subf_default:
      forall (e1: expr) (e2: expr),
      subf_cases e1 e2.

Definition subf_match (e1: expr) (e2: expr) :=
  match e1 as z1 return subf_cases z1 e2 with
  | Eop Omulf (t1:::t2:::Enil) =>
      subf_case1 t1 t2 e2
  | e1 =>
      subf_default e1 e2
  end.

Definition subf (e1: expr) (e2: expr) :=
  match subf_match e1 e2 with
  | subf_case1 t1 t2 t3 =>
      Eop Omulsubf (t1:::t2:::t3:::Enil)
  | subf_default e1 e2 =>
      Eop Osubf (e1:::e2:::Enil)
  end.

(** ** Truncations and sign extensions *)

Inductive cast8signed_cases: forall (e1: expr), Set :=
  | cast8signed_case1:
      forall (e2: expr),
      cast8signed_cases (Eop Ocast8signed (e2 ::: Enil))
  | cast8signed_default:
      forall (e1: expr),
      cast8signed_cases e1.

Definition cast8signed_match (e1: expr) :=
  match e1 as z1 return cast8signed_cases z1 with
  | Eop Ocast8signed (e2 ::: Enil) =>
      cast8signed_case1 e2
  | e1 =>
      cast8signed_default e1
  end.

Definition cast8signed (e: expr) := 
  match cast8signed_match e with
  | cast8signed_case1 e1 => e
  | cast8signed_default e1 => Eop Ocast8signed (e1 ::: Enil)
  end.

Inductive cast8unsigned_cases: forall (e1: expr), Set :=
  | cast8unsigned_case1:
      forall (e2: expr),
      cast8unsigned_cases (Eop Ocast8unsigned (e2 ::: Enil))
  | cast8unsigned_default:
      forall (e1: expr),
      cast8unsigned_cases e1.

Definition cast8unsigned_match (e1: expr) :=
  match e1 as z1 return cast8unsigned_cases z1 with
  | Eop Ocast8unsigned (e2 ::: Enil) =>
      cast8unsigned_case1 e2
  | e1 =>
      cast8unsigned_default e1
  end.

Definition cast8unsigned (e: expr) := 
  match cast8unsigned_match e with
  | cast8unsigned_case1 e1 => e
  | cast8unsigned_default e1 => Eop Ocast8unsigned (e1 ::: Enil)
  end.

Inductive cast16signed_cases: forall (e1: expr), Set :=
  | cast16signed_case1:
      forall (e2: expr),
      cast16signed_cases (Eop Ocast16signed (e2 ::: Enil))
  | cast16signed_default:
      forall (e1: expr),
      cast16signed_cases e1.

Definition cast16signed_match (e1: expr) :=
  match e1 as z1 return cast16signed_cases z1 with
  | Eop Ocast16signed (e2 ::: Enil) =>
      cast16signed_case1 e2
  | e1 =>
      cast16signed_default e1
  end.

Definition cast16signed (e: expr) := 
  match cast16signed_match e with
  | cast16signed_case1 e1 => e
  | cast16signed_default e1 => Eop Ocast16signed (e1 ::: Enil)
  end.

Inductive cast16unsigned_cases: forall (e1: expr), Set :=
  | cast16unsigned_case1:
      forall (e2: expr),
      cast16unsigned_cases (Eop Ocast16unsigned (e2 ::: Enil))
  | cast16unsigned_default:
      forall (e1: expr),
      cast16unsigned_cases e1.

Definition cast16unsigned_match (e1: expr) :=
  match e1 as z1 return cast16unsigned_cases z1 with
  | Eop Ocast16unsigned (e2 ::: Enil) =>
      cast16unsigned_case1 e2
  | e1 =>
      cast16unsigned_default e1
  end.

Definition cast16unsigned (e: expr) := 
  match cast16unsigned_match e with
  | cast16unsigned_case1 e1 => e
  | cast16unsigned_default e1 => Eop Ocast16unsigned (e1 ::: Enil)
  end.

Inductive singleoffloat_cases: forall (e1: expr), Set :=
  | singleoffloat_case1:
      forall (e2: expr),
      singleoffloat_cases (Eop Osingleoffloat (e2 ::: Enil))
  | singleoffloat_default:
      forall (e1: expr),
      singleoffloat_cases e1.

Definition singleoffloat_match (e1: expr) :=
  match e1 as z1 return singleoffloat_cases z1 with
  | Eop Osingleoffloat (e2 ::: Enil) =>
      singleoffloat_case1 e2
  | e1 =>
      singleoffloat_default e1
  end.

Definition singleoffloat (e: expr) := 
  match singleoffloat_match e with
  | singleoffloat_case1 e1 => e
  | singleoffloat_default e1 => Eop Osingleoffloat (e1 ::: Enil)
  end.

(** ** Comparisons *)

Inductive comp_cases: forall (e1: expr) (e2: expr), Set :=
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

(** ** Conditional expressions *)

Fixpoint negate_condexpr (e: condexpr): condexpr :=
  match e with
  | CEtrue => CEfalse
  | CEfalse => CEtrue
  | CEcond c el => CEcond (negate_condition c) el
  | CEcondition e1 e2 e3 =>
      CEcondition e1 (negate_condexpr e2) (negate_condexpr e3)
  end.


Definition is_compare_neq_zero (c: condition) : bool :=
  match c with
  | Ccompimm Cne n => Int.eq n Int.zero
  | Ccompuimm Cne n => Int.eq n Int.zero
  | _ => false
  end.

Definition is_compare_eq_zero (c: condition) : bool :=
  match c with
  | Ccompimm Ceq n => Int.eq n Int.zero
  | Ccompuimm Ceq n => Int.eq n Int.zero
  | _ => false
  end.

Fixpoint condexpr_of_expr (e: expr) : condexpr :=
  match e with
  | Eop (Ointconst n) Enil =>
      if Int.eq n Int.zero then CEfalse else CEtrue
  | Eop (Ocmp c) (e1 ::: Enil) =>
      if is_compare_neq_zero c then
        condexpr_of_expr e1
      else if is_compare_eq_zero c then
        negate_condexpr (condexpr_of_expr e1)
      else
        CEcond c (e1 ::: Enil)
  | Eop (Ocmp c) el =>
      CEcond c el
  | Econdition ce e1 e2 =>
      CEcondition ce (condexpr_of_expr e1) (condexpr_of_expr e2)
  | _ =>
      CEcond (Ccompimm Cne Int.zero) (e:::Enil)
  end.

(** ** Recognition of addressing modes for load and store operations *)

(*
Definition addressing (e: expr) :=
  match e with
  | Eop (Oaddrsymbol s n) Enil => (Aglobal s n, Enil)
  | Eop (Oaddrstack n) Enil => (Ainstack n, Enil)
  | Eop Oadd (Eop (Oaddrsymbol s n) Enil) e2 => (Abased(s, n), e2:::Enil)
  | Eop (Oaddimm n) (e1:::Enil) => (Aindexed n, e1:::Enil)
  | Eop Oadd (e1:::e2:::Enil) => (Aindexed2, e1:::e2:::Enil)
  | _ => (Aindexed Int.zero, e:::Enil)
  end.
*)

Inductive addressing_cases: forall (e: expr), Set :=
  | addressing_case1:
      forall (s: ident) (n: int),
      addressing_cases (Eop (Oaddrsymbol s n) Enil)
  | addressing_case2:
      forall (n: int),
      addressing_cases (Eop (Oaddrstack n) Enil)
  | addressing_case3:
      forall (s: ident) (n: int) (e2: expr),
      addressing_cases
        (Eop Oadd (Eop (Oaddrsymbol s n) Enil:::e2:::Enil))
  | addressing_case4:
      forall (n: int) (e1: expr),
      addressing_cases (Eop (Oaddimm n) (e1:::Enil))
  | addressing_case5:
      forall (e1: expr) (e2: expr),
      addressing_cases (Eop Oadd (e1:::e2:::Enil))
  | addressing_default:
      forall (e: expr),
      addressing_cases e.

Definition addressing_match (e: expr) :=
  match e as z1 return addressing_cases z1 with
  | Eop (Oaddrsymbol s n) Enil =>
      addressing_case1 s n
  | Eop (Oaddrstack n) Enil =>
      addressing_case2 n
  | Eop Oadd (Eop (Oaddrsymbol s n) Enil:::e2:::Enil) =>
      addressing_case3 s n e2
  | Eop (Oaddimm n) (e1:::Enil) =>
      addressing_case4 n e1
  | Eop Oadd (e1:::e2:::Enil) =>
      addressing_case5 e1 e2
  | e =>
      addressing_default e
  end.

Definition addressing (e: expr) :=
  match addressing_match e with
  | addressing_case1 s n =>
      (Aglobal s n, Enil)
  | addressing_case2 n =>
      (Ainstack n, Enil)
  | addressing_case3 s n e2 =>
      (Abased s n, e2:::Enil)
  | addressing_case4 n e1 =>
      (Aindexed n, e1:::Enil)
  | addressing_case5 e1 e2 =>
      (Aindexed2, e1:::e2:::Enil)
  | addressing_default e =>
      (Aindexed Int.zero, e:::Enil)
  end.

Definition load (chunk: memory_chunk) (e1: expr) :=
  match addressing e1 with
  | (mode, args) => Eload chunk mode args
  end.

Definition store (chunk: memory_chunk) (e1 e2: expr) :=
  match addressing e1 with
  | (mode, args) => Sstore chunk mode args e2
  end.

(** * Translation from Cminor to CminorSel *)

(** Instruction selection for operator applications *)

Definition sel_constant (cst: Cminor.constant) : expr :=
  match cst with
  | Cminor.Ointconst n => Eop (Ointconst n) Enil
  | Cminor.Ofloatconst f => Eop (Ofloatconst f) Enil
  | Cminor.Oaddrsymbol id ofs => Eop (Oaddrsymbol id ofs) Enil
  | Cminor.Oaddrstack ofs => Eop (Oaddrstack ofs) Enil
  end.

Definition sel_unop (op: Cminor.unary_operation) (arg: expr) : expr :=
  match op with
  | Cminor.Ocast8unsigned => cast8unsigned arg 
  | Cminor.Ocast8signed => cast8signed arg 
  | Cminor.Ocast16unsigned => cast16unsigned arg 
  | Cminor.Ocast16signed => cast16signed arg 
  | Cminor.Onegint => Eop (Osubimm Int.zero) (arg ::: Enil)
  | Cminor.Onotbool => notbool arg
  | Cminor.Onotint => notint arg
  | Cminor.Onegf => Eop Onegf (arg ::: Enil)
  | Cminor.Oabsf => Eop Oabsf (arg ::: Enil)
  | Cminor.Osingleoffloat => singleoffloat arg
  | Cminor.Ointoffloat => Eop Ointoffloat (arg ::: Enil)
  | Cminor.Ointuoffloat => Eop Ointuoffloat (arg ::: Enil)
  | Cminor.Ofloatofint => Eop Ofloatofint (arg ::: Enil)
  | Cminor.Ofloatofintu => Eop Ofloatofintu (arg ::: Enil)
  end.

Definition sel_binop (op: Cminor.binary_operation) (arg1 arg2: expr) : expr :=
  match op with
  | Cminor.Oadd => add arg1 arg2
  | Cminor.Osub => sub arg1 arg2
  | Cminor.Omul => mul arg1 arg2
  | Cminor.Odiv => divs arg1 arg2
  | Cminor.Odivu => divu arg1 arg2
  | Cminor.Omod => mods arg1 arg2
  | Cminor.Omodu => modu arg1 arg2
  | Cminor.Oand => and arg1 arg2
  | Cminor.Oor => or arg1 arg2
  | Cminor.Oxor => Eop Oxor (arg1 ::: arg2 ::: Enil)
  | Cminor.Oshl => shl arg1 arg2
  | Cminor.Oshr => Eop Oshr (arg1 ::: arg2 ::: Enil)
  | Cminor.Oshru => shru arg1 arg2
  | Cminor.Oaddf => addf arg1 arg2
  | Cminor.Osubf => subf arg1 arg2
  | Cminor.Omulf => Eop Omulf (arg1 ::: arg2 ::: Enil)
  | Cminor.Odivf => Eop Odivf (arg1 ::: arg2 ::: Enil)
  | Cminor.Ocmp c => comp c arg1 arg2
  | Cminor.Ocmpu c => compu c arg1 arg2
  | Cminor.Ocmpf c => compf c arg1 arg2
  end.

(** Conversion from Cminor expression to Cminorsel expressions *)

Fixpoint sel_expr (a: Cminor.expr) : expr :=
  match a with
  | Cminor.Evar id => Evar id
  | Cminor.Econst cst => sel_constant cst
  | Cminor.Eunop op arg => sel_unop op (sel_expr arg)
  | Cminor.Ebinop op arg1 arg2 => sel_binop op (sel_expr arg1) (sel_expr arg2)
  | Cminor.Eload chunk addr => load chunk (sel_expr addr)
  | Cminor.Econdition cond ifso ifnot =>
      Econdition (condexpr_of_expr (sel_expr cond))
                 (sel_expr ifso) (sel_expr ifnot)
  end.

Fixpoint sel_exprlist (al: list Cminor.expr) : exprlist :=
  match al with
  | nil => Enil
  | a :: bl => Econs (sel_expr a) (sel_exprlist bl)
  end.

(** Conversion from Cminor statements to Cminorsel statements. *)

Fixpoint sel_stmt (s: Cminor.stmt) : stmt :=
  match s with
  | Cminor.Sskip => Sskip
  | Cminor.Sassign id e => Sassign id (sel_expr e)
  | Cminor.Sstore chunk addr rhs => store chunk (sel_expr addr) (sel_expr rhs)
  | Cminor.Scall optid sg fn args =>
      Scall optid sg (sel_expr fn) (sel_exprlist args)
  | Cminor.Stailcall sg fn args => 
      Stailcall sg (sel_expr fn) (sel_exprlist args)
  | Cminor.Salloc id b => Salloc id (sel_expr b)
  | Cminor.Sseq s1 s2 => Sseq (sel_stmt s1) (sel_stmt s2)
  | Cminor.Sifthenelse e ifso ifnot =>
      Sifthenelse (condexpr_of_expr (sel_expr e))
                  (sel_stmt ifso) (sel_stmt ifnot)
  | Cminor.Sloop body => Sloop (sel_stmt body)
  | Cminor.Sblock body => Sblock (sel_stmt body)
  | Cminor.Sexit n => Sexit n
  | Cminor.Sswitch e cases dfl => Sswitch (sel_expr e) cases dfl
  | Cminor.Sreturn None => Sreturn None
  | Cminor.Sreturn (Some e) => Sreturn (Some (sel_expr e))
  | Cminor.Slabel lbl body => Slabel lbl (sel_stmt body)
  | Cminor.Sgoto lbl => Sgoto lbl
  end.

(** Conversion of functions and programs. *)

Definition sel_function (f: Cminor.function) : function :=
  mkfunction
    f.(Cminor.fn_sig)
    f.(Cminor.fn_params)
    f.(Cminor.fn_vars)
    f.(Cminor.fn_stackspace)
    (sel_stmt f.(Cminor.fn_body)).

Definition sel_fundef (f: Cminor.fundef) : fundef :=
  transf_fundef sel_function f.

Definition sel_program (p: Cminor.program) : program :=
  transform_program sel_fundef p.




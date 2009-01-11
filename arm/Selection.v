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
  | Eop (Oshift s) (t1:::Enil) => Eop (Onotshift s) (t1:::Enil)
  | Eop Onot (t1:::Enil) => t1
  | Eop (Onotshift s) (t1:::Enil) => Eop (Oshift s) (t1:::Enil)
  | _ => Eop Onot (e:::Enil)
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
      forall s t1,
      notint_cases (Eop (Oshift s) (t1:::Enil))
  | notint_case2:
      forall t1,
      notint_cases (Eop Onot (t1:::Enil))
  | notint_case3:
      forall s t1,
      notint_cases (Eop (Onotshift s) (t1:::Enil))
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
  | Eop (Oshift s) (t1:::Enil) =>
      notint_case1 s t1
  | Eop Onot (t1:::Enil) =>
      notint_case2 t1
  | Eop (Onotshift s) (t1:::Enil) =>
      notint_case3 s t1
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
  | notint_case1 s t1 =>
      Eop (Onotshift s) (t1:::Enil)
  | notint_case2 t1 =>
      t1
  | notint_case3 s t1 =>
      Eop (Oshift s) (t1:::Enil)
  | notint_default e =>
      Eop Onot (e:::Enil)
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

(** Addition of an integer constant. *)

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

Inductive addimm_cases: forall (e: expr), Set :=
  | addimm_case1:
      forall m,
      addimm_cases (Eop (Ointconst m) Enil)
  | addimm_case2:
      forall s m,
      addimm_cases (Eop (Oaddrsymbol s m) Enil)
  | addimm_case3:
      forall m,
      addimm_cases (Eop (Oaddrstack m) Enil)
  | addimm_case4:
      forall m t,
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
  | Eop (Oshift s) (t1:::Enil), t2 => Eop (Oaddshift s) (t2:::t1:::Enil)
  | t1, Eop (Oshift s) (t2:::Enil) => Eop (Oaddshift s) (t1:::t2:::Enil)
  | _, _ => Eop Oadd (e1:::e2:::Enil)
  end.
*)

Inductive add_cases: forall (e1: expr) (e2: expr), Set :=
  | add_case1:
      forall n1 t2,
      add_cases (Eop (Ointconst n1) Enil) (t2)
  | add_case2:
      forall n1 t1 n2 t2,
      add_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case3:
      forall n1 t1 t2,
      add_cases (Eop (Oaddimm n1) (t1:::Enil)) (t2)
  | add_case4:
      forall t1 n2,
      add_cases (t1) (Eop (Ointconst n2) Enil)
  | add_case5:
      forall t1 n2 t2,
      add_cases (t1) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case6:
      forall s t1 t2,
      add_cases (Eop (Oshift s) (t1:::Enil)) (t2)
  | add_case7:
      forall t1 s t2,
      add_cases (t1) (Eop (Oshift s) (t2:::Enil))
  | add_default:
      forall (e1: expr) (e2: expr),
      add_cases e1 e2.

Definition add_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return add_cases z1 z2 with
  | Eop (Ointconst n1) Enil, t2 =>
      add_case1 n1 t2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) =>
      add_case2 n1 t1 n2 t2
  | Eop(Oaddimm n1) (t1:::Enil), t2 =>
      add_case3 n1 t1 t2
  | t1, Eop (Ointconst n2) Enil =>
      add_case4 t1 n2
  | t1, Eop (Oaddimm n2) (t2:::Enil) =>
      add_case5 t1 n2 t2
  | Eop (Oshift s) (t1:::Enil), t2 =>
      add_case6 s t1 t2
  | t1, Eop (Oshift s) (t2:::Enil) =>
      add_case7 t1 s t2
  | e1, e2 =>
      add_default e1 e2
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
  | add_case6 s t1 t2 =>
      Eop (Oaddshift s) (t2:::t1:::Enil)
  | add_case7 t1 s t2 =>
      Eop (Oaddshift s) (t1:::t2:::Enil)
  | add_default e1 e2 =>
      Eop Oadd (e1:::e2:::Enil)
  end.

(** ** Integer and pointer subtraction *)

(*
Definition sub (e1: expr) (e2: expr) :=
  match e1, e2 with
  | t1, Eop (Ointconst n2) Enil => addimm (Int.neg n2) t1
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) => addimm (intsub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | Eop (Oaddimm n1) (t1:::Enil), t2 => addimm n1 (Eop Osub (t1:::t2:::Rnil))
  | t1, Eop (Oaddimm n2) (t2:::Enil) => addimm (Int.neg n2) (Eop Osub (t1::::t2:::Enil))
  | Eop (Ointconst n1) Enil, t2 => Eop (Orsubimm n1) (t2:::Enil)
  | Eop (Oshift s) (t1:::Enil), t2 => Eop (Orsubshift s) (t2:::t1:::Enil)
  | t1, Eop (Oshift s) (t2:::Enil) => Eop (Osubshift s) (t1:::t2:::Enil)
  | _, _ => Eop Osub (e1:::e2:::Enil)
  end.
*)

Inductive sub_cases: forall (e1: expr) (e2: expr), Set :=
  | sub_case1:
      forall t1 n2,
      sub_cases (t1) (Eop (Ointconst n2) Enil)
  | sub_case2:
      forall n1 t1 n2 t2,
      sub_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddimm n2) (t2:::Enil))
  | sub_case3:
      forall n1 t1 t2,
      sub_cases (Eop (Oaddimm n1) (t1:::Enil)) (t2)
  | sub_case4:
      forall t1 n2 t2,
      sub_cases (t1) (Eop (Oaddimm n2) (t2:::Enil))
  | sub_case5:
      forall n1 t2,
      sub_cases (Eop (Ointconst n1) Enil) (t2)
  | sub_case6:
      forall s t1 t2,
      sub_cases (Eop (Oshift s) (t1:::Enil)) (t2)
  | sub_case7:
      forall t1 s t2,
      sub_cases (t1) (Eop (Oshift s) (t2:::Enil))
  | sub_default:
      forall (e1: expr) (e2: expr),
      sub_cases e1 e2.

Definition sub_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return sub_cases z1 z2 with
  | t1, Eop (Ointconst n2) Enil =>
      sub_case1 t1 n2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) =>
      sub_case2 n1 t1 n2 t2
  | Eop (Oaddimm n1) (t1:::Enil), t2 =>
      sub_case3 n1 t1 t2
  | t1, Eop (Oaddimm n2) (t2:::Enil) =>
      sub_case4 t1 n2 t2
  | Eop (Ointconst n1) Enil, t2 =>
      sub_case5 n1 t2
  | Eop (Oshift s) (t1:::Enil), t2 =>
      sub_case6 s t1 t2
  | t1, Eop (Oshift s) (t2:::Enil) =>
      sub_case7 t1 s t2
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
  | sub_case5 n1 t2 =>
      Eop (Orsubimm n1) (t2:::Enil)
  | sub_case6 s t1 t2 =>
      Eop (Orsubshift s) (t2:::t1:::Enil)
  | sub_case7 t1 s t2 =>
      Eop (Osubshift s) (t1:::t2:::Enil)
  | sub_default e1 e2 =>
      Eop Osub (e1:::e2:::Enil)
  end.

(** ** Immediate shifts *)

(*
Definition shlimm (e1: expr) :=
  if Int.eq n Int.zero then e1 else 
  match e1 with
  | Eop (Ointconst n1) Enil => Eop (Ointconst(Int.shl n1 n))
  | Eop (Oshift (Olsl n1)) (t1:::Enil) => if Int.ltu (Int.add n n1) (Int.repr 32) then Eop (Oshift (Olsl (Int.add n n1))) (t1:::Enil) else Eop (Oshift (Olsl n)) (e1:::Enil)
  | _ => Eop (Oshift (Olsl n)) (e1:::Enil)
  end.
*)

Inductive shlimm_cases: forall (e1: expr), Set :=
  | shlimm_case1:
      forall n1,
      shlimm_cases (Eop (Ointconst n1) Enil)
  | shlimm_case2:
      forall n1 t1,
      shlimm_cases (Eop (Oshift (Slsl n1)) (t1:::Enil))
  | shlimm_default:
      forall (e1: expr),
      shlimm_cases e1.

Definition shlimm_match (e1: expr) :=
  match e1 as z1 return shlimm_cases z1 with
  | Eop (Ointconst n1) Enil =>
      shlimm_case1 n1
  | Eop (Oshift (Slsl n1)) (t1:::Enil) =>
      shlimm_case2 n1 t1
  | e1 =>
      shlimm_default e1
  end.

Definition shlimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  match is_shift_amount n with
  | None => Eop Oshl (e1 ::: Eop (Ointconst n) Enil ::: Enil)
  | Some n' =>
    match shlimm_match e1 with
    | shlimm_case1 n1 =>
        Eop (Ointconst(Int.shl n1 n)) Enil
    | shlimm_case2 n1 t1 =>
        match is_shift_amount (Int.add n (s_amount n1)) with
        | None =>
            Eop (Oshift (Slsl n')) (e1:::Enil)
        | Some n'' =>
            Eop (Oshift (Slsl n'')) (t1:::Enil)
        end
    | shlimm_default e1 =>
        Eop (Oshift (Slsl n')) (e1:::Enil)
    end
  end.

(*
Definition shruimm (e1: expr) :=
  if Int.eq n Int.zero then e1 else
  match e1 with
  | Eop (Ointconst n1) Enil => Eop (Ointconst(Int.shru n1 n))
  | Eop (Oshift (Olsr n1)) (t1:::Enil) => if Int.ltu (Int.add n n1) (Int.repr 32) then Eop (Oshift (Olsr (Int.add n n1))) (t1:::Enil) else Eop (Oshift (Olsr n)) (e1:::Enil)
  | _ => Eop (Oshift (Olsr n)) (e1:::Enil)
  end.
*)

Inductive shruimm_cases: forall (e1: expr), Set :=
  | shruimm_case1:
      forall n1,
      shruimm_cases (Eop (Ointconst n1) Enil)
  | shruimm_case2:
      forall n1 t1,
      shruimm_cases (Eop (Oshift (Slsr n1)) (t1:::Enil))
  | shruimm_default:
      forall (e1: expr),
      shruimm_cases e1.

Definition shruimm_match (e1: expr) :=
  match e1 as z1 return shruimm_cases z1 with
  | Eop (Ointconst n1) Enil =>
      shruimm_case1 n1
  | Eop (Oshift (Slsr n1)) (t1:::Enil) =>
      shruimm_case2 n1 t1
  | e1 =>
      shruimm_default e1
  end.

Definition shruimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  match is_shift_amount n with
  | None => Eop Oshru (e1 ::: Eop (Ointconst n) Enil ::: Enil)
  | Some n' =>
    match shruimm_match e1 with
    | shruimm_case1 n1 =>
        Eop (Ointconst(Int.shru n1 n)) Enil
    | shruimm_case2 n1 t1 =>
        match is_shift_amount (Int.add n (s_amount n1)) with
        | None =>
            Eop (Oshift (Slsr n')) (e1:::Enil)
        | Some n'' =>
            Eop (Oshift (Slsr n'')) (t1:::Enil)
        end
    | shruimm_default e1 =>
        Eop (Oshift (Slsr n')) (e1:::Enil)
    end
  end.

(*
Definition shrimm (e1: expr) :=
  match e1 with
  | Eop (Ointconst n1) Enil => Eop (Ointconst(Int.shr n1 n))
  | Eop (Oshift (Oasr n1)) (t1:::Enil) => if Int.ltu (Int.add n n1) (Int.repr 32) then Eop (Oshift (Oasr (Int.add n n1))) (t1:::Enil) else Eop (Oshift (Oasr n)) (e1:::Enil)
  | _ => Eop (Oshift (Oasr n)) (e1:::Enil)
  end.
*)

Inductive shrimm_cases: forall (e1: expr), Set :=
  | shrimm_case1:
      forall n1,
      shrimm_cases (Eop (Ointconst n1) Enil)
  | shrimm_case2:
      forall n1 t1,
      shrimm_cases (Eop (Oshift (Sasr n1)) (t1:::Enil))
  | shrimm_default:
      forall (e1: expr),
      shrimm_cases e1.

Definition shrimm_match (e1: expr) :=
  match e1 as z1 return shrimm_cases z1 with
  | Eop (Ointconst n1) Enil =>
      shrimm_case1 n1
  | Eop (Oshift (Sasr n1)) (t1:::Enil) =>
      shrimm_case2 n1 t1
  | e1 =>
      shrimm_default e1
  end.

Definition shrimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then e1 else
  match is_shift_amount n with
  | None => Eop Oshr (e1 ::: Eop (Ointconst n) Enil ::: Enil)
  | Some n' =>
    match shrimm_match e1 with
    | shrimm_case1 n1 =>
        Eop (Ointconst(Int.shr n1 n)) Enil
    | shrimm_case2 n1 t1 =>
        match is_shift_amount (Int.add n (s_amount n1)) with
        | None =>
            Eop (Oshift (Sasr n')) (e1:::Enil)
        | Some n'' =>
            Eop (Oshift (Sasr n'')) (t1:::Enil)
        end
    | shrimm_default e1 =>
        Eop (Oshift (Sasr n')) (e1:::Enil)
    end
  end.

(** ** Integer multiply *)

Definition mulimm_base (n1: int) (e2: expr) :=
  match Int.one_bits n1 with
  | i :: nil =>
      shlimm e2 i
  | i :: j :: nil =>
      Elet e2
        (add (shlimm (Eletvar 0) i) (shlimm (Eletvar 0) j))
  | _ =>
      Eop Omul (Eop (Ointconst n1) Enil ::: e2 ::: Enil)
  end.

(*
Definition mulimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then 
    Eop (Ointconst Int.zero) Enil
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

Definition mod_aux (divop: operation) (e1 e2: expr) :=
  Elet e1
    (Elet (lift e2)
      (Eop Osub (Eletvar 1 :::
                 Eop Omul (Eop divop (Eletvar 1 ::: Eletvar 0 ::: Enil) :::
                           Eletvar 0 :::
                           Enil) :::
                 Enil))).

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
      | Some l2 => Eop (Oandimm (Int.sub n2 Int.one)) (e1:::Enil)
      | None    => mod_aux Odivu e1 e2
      end
  | divu_default e2 =>
      mod_aux Odivu e1 e2
  end.

Definition divs (e1: expr) (e2: expr) :=
  match divu_match e2 with
  | divu_case1 n2 =>
      match Int.is_power2 n2 with
      | Some l2 => if Int.ltu l2 (Int.repr 31)
                   then Eop (Oshrximm l2) (e1:::Enil)
                   else Eop Odiv (e1:::e2:::Enil)
      | None    => Eop Odiv (e1:::e2:::Enil)
      end
  | divu_default e2 =>
      Eop Odiv (e1:::e2:::Enil)
  end.

Definition mods := mod_aux Odiv.  (* could be improved *)


(** ** Bitwise and, or, xor *)

(*
Definition and (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Oshift s) (t1:::Enil), t2 => Eop (Oandshift s) (t2:::t1:::Enil)
  | t1, Eop (Oshift s) (t2:::Enil) => Eop (Oandshift s) (t1:::t2:::Enil)
  | Eop (Onotshift s) (t1:::Enil), t2 => Eop (Obicshift s) (t2:::t1:::Enil)
  | t1, Eop (Onotshift s) (t2:::Enil) => Eop (Obicshift s) (t1:::t2:::Enil)
  | Eop Onot (t1:::Enil), t2 => Eop Obic (t2:::t1:::Enil)
  | t1, Eop Onot (t2:::Enil) => Eop Obic (t1:::t2:::Enil)
  | _, _ => Eop Oand (e1:::e2:::Enil)
  end.
*)

Inductive and_cases: forall (e1: expr) (e2: expr), Set :=
  | and_case1:
      forall s t1 t2,
      and_cases (Eop (Oshift s) (t1:::Enil)) (t2)
  | and_case2:
      forall t1 s t2,
      and_cases (t1) (Eop (Oshift s) (t2:::Enil))
  | and_case3:
      forall s t1 t2,
      and_cases (Eop (Onotshift s) (t1:::Enil)) (t2)
  | and_case4:
      forall t1 s t2,
      and_cases (t1) (Eop (Onotshift s) (t2:::Enil))
  | and_case5:
      forall t1 t2,
      and_cases (Eop Onot (t1:::Enil)) (t2)
  | and_case6:
      forall t1 t2,
      and_cases (t1) (Eop Onot (t2:::Enil))
  | and_default:
      forall (e1: expr) (e2: expr),
      and_cases e1 e2.

Definition and_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return and_cases z1 z2 with
  | Eop (Oshift s) (t1:::Enil), t2 =>
      and_case1 s t1 t2
  | t1, Eop (Oshift s) (t2:::Enil) =>
      and_case2 t1 s t2
  | Eop (Onotshift s) (t1:::Enil), t2 =>
      and_case3 s t1 t2
  | t1, Eop (Onotshift s) (t2:::Enil) =>
      and_case4 t1 s t2
  | Eop Onot (t1:::Enil), t2 =>
      and_case5 t1 t2
  | t1, Eop Onot (t2:::Enil) =>
      and_case6 t1 t2
  | e1, e2 =>
      and_default e1 e2
  end.

Definition and (e1: expr) (e2: expr) :=
  match and_match e1 e2 with
  | and_case1 s t1 t2 =>
      Eop (Oandshift s) (t2:::t1:::Enil)
  | and_case2 t1 s t2 =>
      Eop (Oandshift s) (t1:::t2:::Enil)
  | and_case3 s t1 t2 =>
      Eop (Obicshift s) (t2:::t1:::Enil)
  | and_case4 t1 s t2 =>
      Eop (Obicshift s) (t1:::t2:::Enil)
  | and_case5 t1 t2 =>
      Eop Obic (t2:::t1:::Enil)
  | and_case6 t1 t2 =>
      Eop Obic (t1:::t2:::Enil)
  | and_default e1 e2 =>
      Eop Oand (e1:::e2:::Enil)
  end.

Definition same_expr_pure (e1 e2: expr) :=
  match e1, e2 with
  | Evar v1, Evar v2 => if ident_eq v1 v2 then true else false
  | _, _ => false
  end.

(*
Definition or (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Oshift (Olsl n1) (t1:::Enil), Eop (Oshift (Olsr n2) (t2:::Enil)) => ...
  | Eop (Oshift s) (t1:::Enil), t2 => Eop (Oorshift s) (t2:::t1:::Enil)
  | t1, Eop (Oshift s) (t2:::Enil) => Eop (Oorshift s) (t1:::t2:::Enil)
  | _, _ => Eop Oor (e1:::e2:::Enil)
  end.
*)

(* TODO: symmetric of first case *)

Inductive or_cases: forall (e1: expr) (e2: expr), Set :=
  | or_case1:
      forall n1 t1 n2 t2,
      or_cases (Eop (Oshift (Slsl n1)) (t1:::Enil)) (Eop (Oshift (Slsr n2)) (t2:::Enil))
  | or_case2:
      forall s t1 t2,
      or_cases (Eop (Oshift s) (t1:::Enil)) (t2)
  | or_case3:
      forall t1 s t2,
      or_cases (t1) (Eop (Oshift s) (t2:::Enil))
  | or_default:
      forall (e1: expr) (e2: expr),
      or_cases e1 e2.

Definition or_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return or_cases z1 z2 with
  | Eop (Oshift (Slsl n1)) (t1:::Enil), Eop (Oshift (Slsr n2)) (t2:::Enil) =>
      or_case1 n1 t1 n2 t2
  | Eop (Oshift s) (t1:::Enil), t2 =>
      or_case2 s t1 t2
  | t1, Eop (Oshift s) (t2:::Enil) =>
      or_case3 t1 s t2
  | e1, e2 =>
      or_default e1 e2
  end.

Definition or (e1: expr) (e2: expr) :=
  match or_match e1 e2 with
  | or_case1 n1 t1 n2 t2 =>
      if Int.eq (Int.add (s_amount n1) (s_amount n2)) (Int.repr 32)
      && same_expr_pure t1 t2
      then Eop (Oshift (Sror n2)) (t1:::Enil)
      else Eop (Oorshift (Slsr n2)) (e1:::t2:::Enil)
  | or_case2 s t1 t2 =>
      Eop (Oorshift s) (t2:::t1:::Enil)
  | or_case3 t1 s t2 =>
      Eop (Oorshift s) (t1:::t2:::Enil)
  | or_default e1 e2 =>
      Eop Oor (e1:::e2:::Enil)
  end.

(*
Definition xor (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Oshift s) (t1:::Enil), t2 => Eop (Oxorshift s) (t2:::t1:::Enil)
  | t1, Eop (Oshift s) (t2:::Enil) => Eop (Oxorshift s) (t1:::t2:::Enil)
  | _, _ => Eop Oxor (e1:::e2:::Enil)
  end.
*)

Inductive xor_cases: forall (e1: expr) (e2: expr), Set :=
  | xor_case1:
      forall s t1 t2,
      xor_cases (Eop (Oshift s) (t1:::Enil)) (t2)
  | xor_case2:
      forall t1 s t2,
      xor_cases (t1) (Eop (Oshift s) (t2:::Enil))
  | xor_default:
      forall (e1: expr) (e2: expr),
      xor_cases e1 e2.

Definition xor_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return xor_cases z1 z2 with
  | Eop (Oshift s) (t1:::Enil), t2 =>
      xor_case1 s t1 t2
  | t1, Eop (Oshift s) (t2:::Enil) =>
      xor_case2 t1 s t2
  | e1, e2 =>
      xor_default e1 e2
  end.

Definition xor (e1: expr) (e2: expr) :=
  match xor_match e1 e2 with
  | xor_case1 s t1 t2 =>
      Eop (Oxorshift s) (t2:::t1:::Enil)
  | xor_case2 t1 s t2 =>
      Eop (Oxorshift s) (t1:::t2:::Enil)
  | xor_default e1 e2 =>
      Eop Oxor (e1:::e2:::Enil)
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

Definition shr (e1: expr) (e2: expr) :=
  match shift_match e2 with
  | shift_case1 n2 =>
      shrimm e1 n2
  | shift_default e2 =>
      Eop Oshr (e1:::e2:::Enil)
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

(*
Definition comp (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => Eop (Ocmp (Ccompimm (swap_comparison c) n1)) (t2:::Enil)
  | t1, Eop (Ointconst n2) Enil => Eop (Ocmp (Ccompimm c n1)) (t1:::Enil)
  | Eop (Oshift s) (t1:::Enil), t2 => Eop (Ocmp (Ccompshift (swap_comparison c) s)) (t2:::t1:::Enil)
  | t1, Eop (Oshift s) (t2:::Enil) => Eop (Ocmp (Ccompshift c s)) (t1:::t2:::Enil)
  | _, _ => Eop (Ocmp (Ccomp c)) (e1:::e2:::Enil)
  end.
*)
  
Inductive comp_cases: forall (e1: expr) (e2: expr), Set :=
  | comp_case1:
      forall n1 t2,
      comp_cases (Eop (Ointconst n1) Enil) (t2)
  | comp_case2:
      forall t1 n2,
      comp_cases (t1) (Eop (Ointconst n2) Enil)
  | comp_case3:
      forall s t1 t2,
      comp_cases (Eop (Oshift s) (t1:::Enil)) (t2)
  | comp_case4:
      forall t1 s t2,
      comp_cases (t1) (Eop (Oshift s) (t2:::Enil))
  | comp_default:
      forall (e1: expr) (e2: expr),
      comp_cases e1 e2.

Definition comp_match (e1: expr) (e2: expr) :=
  match e1 as z1, e2 as z2 return comp_cases z1 z2 with
  | Eop (Ointconst n1) Enil, t2 =>
      comp_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil =>
      comp_case2 t1 n2
  | Eop (Oshift s) (t1:::Enil), t2 =>
      comp_case3 s t1 t2
  | t1, Eop (Oshift s) (t2:::Enil) =>
      comp_case4 t1 s t2
  | e1, e2 =>
      comp_default e1 e2
  end.

Definition comp (c: comparison) (e1: expr) (e2: expr) :=
  match comp_match e1 e2 with
  | comp_case1 n1 t2 =>
      Eop (Ocmp (Ccompimm (swap_comparison c) n1)) (t2:::Enil)
  | comp_case2 t1 n2 =>
      Eop (Ocmp (Ccompimm c n2)) (t1:::Enil)
  | comp_case3 s t1 t2 =>
      Eop (Ocmp (Ccompshift (swap_comparison c) s)) (t2:::t1:::Enil)
  | comp_case4 t1 s t2 =>
      Eop (Ocmp (Ccompshift c s)) (t1:::t2:::Enil)
  | comp_default e1 e2 =>
      Eop (Ocmp (Ccomp c)) (e1:::e2:::Enil)
  end.

Definition compu (c: comparison) (e1: expr) (e2: expr) :=
  match comp_match e1 e2 with
  | comp_case1 n1 t2 =>
      Eop (Ocmp (Ccompuimm (swap_comparison c) n1)) (t2:::Enil)
  | comp_case2 t1 n2 =>
      Eop (Ocmp (Ccompuimm c n2)) (t1:::Enil)
  | comp_case3 s t1 t2 =>
      Eop (Ocmp (Ccompushift (swap_comparison c) s)) (t2:::t1:::Enil)
  | comp_case4 t1 s t2 =>
      Eop (Ocmp (Ccompushift c s)) (t1:::t2:::Enil)
  | comp_default e1 e2 =>
      Eop (Ocmp (Ccompu c)) (e1:::e2:::Enil)
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
  | Eop (Oaddrstack n) Enil => (Ainstack n, Enil)
  | Eop (Oaddimm n) (e1:::Enil) => (Aindexed n, e1:::Enil)
  | Eop (Oaddshift s) (e1:::e2:::Enil) => (Aindexed2shift s, e1:::e2:::Enil)
  | Eop Oadd (e1:::e2:::Enil) => (Aindexed2, e1:::e2:::Enil)
  | _ => (Aindexed Int.zero, e:::Enil)
  end.
*)

Inductive addressing_cases: forall (e: expr), Set :=
  | addressing_case2:
      forall n,
      addressing_cases (Eop (Oaddrstack n) Enil)
  | addressing_case3:
      forall n e1,
      addressing_cases (Eop (Oaddimm n) (e1:::Enil))
  | addressing_case4:
      forall s e1 e2,
      addressing_cases (Eop (Oaddshift s) (e1:::e2:::Enil))
  | addressing_case5:
      forall e1 e2,
      addressing_cases (Eop Oadd (e1:::e2:::Enil))
  | addressing_default:
      forall (e: expr),
      addressing_cases e.

Definition addressing_match (e: expr) :=
  match e as z1 return addressing_cases z1 with
  | Eop (Oaddrstack n) Enil =>
      addressing_case2 n
  | Eop (Oaddimm n) (e1:::Enil) =>
      addressing_case3 n e1
  | Eop (Oaddshift s) (e1:::e2:::Enil) =>
      addressing_case4 s e1 e2
  | Eop Oadd (e1:::e2:::Enil) =>
      addressing_case5 e1 e2
  | e =>
      addressing_default e
  end.

(** We do not recognize the [Aindexed2] and [Aindexed2shift] modes
    for floating-point accesses, since these are not supported
    by the hardware and emulated inefficiently in [ARMgen]. *)

Definition is_float_addressing (chunk: memory_chunk): bool :=
  match chunk with
  | Mfloat32 => true
  | Mfloat64 => true
  | _ => false
  end.

Definition addressing (chunk: memory_chunk) (e: expr) :=
  match addressing_match e with
  | addressing_case2 n =>
      (Ainstack n, Enil)
  | addressing_case3 n e1 =>
      (Aindexed n, e1:::Enil)
  | addressing_case4 s e1 e2 =>
      if is_float_addressing chunk
      then (Aindexed Int.zero, Eop (Oaddshift s) (e1:::e2:::Enil) ::: Enil)
      else (Aindexed2shift s, e1:::e2:::Enil)
  | addressing_case5 e1 e2 =>
      if is_float_addressing chunk
      then (Aindexed Int.zero, Eop Oadd (e1:::e2:::Enil) ::: Enil)
      else (Aindexed2, e1:::e2:::Enil)
  | addressing_default e =>
      (Aindexed Int.zero, e:::Enil)
  end.

Definition load (chunk: memory_chunk) (e1: expr) :=
  match addressing chunk e1 with
  | (mode, args) => Eload chunk mode args
  end.

Definition store (chunk: memory_chunk) (e1 e2: expr) :=
  match addressing chunk e1 with
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
  | Cminor.Onegint => Eop (Orsubimm Int.zero) (arg ::: Enil)
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
  | Cminor.Oxor => xor arg1 arg2
  | Cminor.Oshl => shl arg1 arg2
  | Cminor.Oshr => shr arg1 arg2
  | Cminor.Oshru => shru arg1 arg2
  | Cminor.Oaddf => Eop Oaddf (arg1 ::: arg2 ::: Enil)
  | Cminor.Osubf => Eop Osubf (arg1 ::: arg2 ::: Enil)
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

(** For compatibility with PowerPC *)

Parameter use_fused_mul: unit -> bool.

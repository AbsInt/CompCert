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
  Eop (Oaddrsymbol id ofs) Enil.

Definition addrstack (ofs: int) :=
  Eop (Oaddrstack ofs) Enil.

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

Inductive notint_cases: forall (e: expr), Type :=
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

Inductive addimm_cases: forall (e: expr), Type :=
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
  | Eop (Oaddrsymbol s n1) Enil, Eop (Oaddimm n2) (t2:::Enil) => Eop Oadd (Eop (Oaddrsymbol s (Int.add n1 n2)) Enil ::: t2 ::: Enil)
  | Eop (Oaddrstack n1) Enil, Eop (Oaddimm n2) (t2:::Enil) => Eop Oadd (Eop (Oaddstack (Int.add n1 n2)) Enil ::: t2 ::: Enil)
  | _, _ => Eop Oadd (e1:::e2:::Enil)
  end.
*)

Inductive add_cases: forall (e1: expr) (e2: expr), Type :=
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
  | add_case6:
      forall s n1 n2 t2,
      add_cases (Eop (Oaddrsymbol s n1) Enil) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case7:
      forall n1 n2 t2,
      add_cases (Eop (Oaddrstack n1) Enil) (Eop (Oaddimm n2) (t2:::Enil))
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
  | Eop (Oaddrsymbol s n1) Enil, Eop (Oaddimm n2) (t2:::Enil) => 
      add_case6 s n1 n2 t2
  | Eop (Oaddrstack n1) Enil, Eop (Oaddimm n2) (t2:::Enil) =>
      add_case7 n1 n2 t2
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
  | add_case6 s n1 n2 t2 =>
      Eop Oadd (Eop (Oaddrsymbol s (Int.add n1 n2)) Enil ::: t2 ::: Enil)
  | add_case7 n1 n2 t2 =>
      Eop Oadd (Eop (Oaddrstack (Int.add n1 n2)) Enil ::: t2 ::: Enil)
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

Inductive sub_cases: forall (e1: expr) (e2: expr), Type :=
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

(** Recognition of integers that are acceptable as immediate operands
  to the [rlwim] PowerPC instruction.  These integers are of the form
  [000011110000] or [111100001111], that is, a run of one bits
  surrounded by zero bits, or conversely.  We recognize these integers by
  running the following automaton on the bits.  The accepting states are
  2, 3, 4, 5, and 6.
<<
               0          1          0
              / \        / \        / \
              \ /        \ /        \ /
        -0--> [1] --1--> [2] --0--> [3]
       /     
     [0]
       \
        -1--> [4] --0--> [5] --1--> [6]
              / \        / \        / \
              \ /        \ /        \ /
               1          0          1
>>
*)

Inductive rlw_state: Type :=
  | RLW_S0 : rlw_state
  | RLW_S1 : rlw_state
  | RLW_S2 : rlw_state
  | RLW_S3 : rlw_state
  | RLW_S4 : rlw_state
  | RLW_S5 : rlw_state
  | RLW_S6 : rlw_state
  | RLW_Sbad : rlw_state.

Definition rlw_transition (s: rlw_state) (b: bool) : rlw_state :=
  match s, b with
  | RLW_S0, false => RLW_S1
  | RLW_S0, true  => RLW_S4
  | RLW_S1, false => RLW_S1
  | RLW_S1, true  => RLW_S2
  | RLW_S2, false => RLW_S3
  | RLW_S2, true  => RLW_S2
  | RLW_S3, false => RLW_S3
  | RLW_S3, true  => RLW_Sbad
  | RLW_S4, false => RLW_S5
  | RLW_S4, true  => RLW_S4
  | RLW_S5, false => RLW_S5
  | RLW_S5, true  => RLW_S6
  | RLW_S6, false => RLW_Sbad
  | RLW_S6, true  => RLW_S6
  | RLW_Sbad, _ => RLW_Sbad
  end.

Definition rlw_accepting (s: rlw_state) : bool :=
  match s with
  | RLW_S0 => false
  | RLW_S1 => false
  | RLW_S2 => true
  | RLW_S3 => true
  | RLW_S4 => true
  | RLW_S5 => true
  | RLW_S6 => true
  | RLW_Sbad => false
  end.

Fixpoint is_rlw_mask_rec (n: nat) (s: rlw_state) (x: Z) {struct n} : bool :=
  match n with
  | O =>
      rlw_accepting s
  | S m =>
      let (b, y) := Int.Z_bin_decomp x in
      is_rlw_mask_rec m (rlw_transition s b) y
  end.

Definition is_rlw_mask (x: int) : bool :=
  is_rlw_mask_rec Int.wordsize RLW_S0 (Int.unsigned x).

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

Inductive rolm_cases: forall (e1: expr), Type :=
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
      let amount := Int.modu (Int.add amount1 amount2) Int.iwordsize in
      let mask := Int.and (Int.rol mask1 amount2) mask2 in
      if is_rlw_mask mask
      then Eop (Orolm amount mask) (t1:::Enil)
      else Eop (Orolm amount2 mask2) (e1:::Enil)
  | rolm_default e1 =>
      Eop (Orolm amount2 mask2) (e1:::Enil)
  end.

Definition shlimm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then
    e1
  else if Int.ltu n2 Int.iwordsize then
    rolm e1 n2 (Int.shl Int.mone n2)
  else
    Eop Oshl (e1:::Eop (Ointconst n2) Enil:::Enil).

Definition shruimm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then
    e1
  else if Int.ltu n2 Int.iwordsize then
    rolm e1 (Int.sub Int.iwordsize n2) (Int.shru Int.mone n2)
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

Inductive mulimm_cases: forall (e2: expr), Type :=
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

Definition andimm (n1: int) (e2: expr) :=
  if is_rlw_mask n1
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

Inductive or_cases: forall (e1: expr) (e2: expr), Type :=
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
      && is_rlw_mask (Int.or mask1 mask2)
      && same_expr_pure t1 t2
      then Eop (Orolm amount1 (Int.or mask1 mask2)) (t1:::Enil)
      else Eop Oor (e1:::e2:::Enil)
  | or_default e1 e2 =>
      Eop Oor (e1:::e2:::Enil)
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

Inductive divu_cases: forall (e2: expr), Type :=
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
      | Some l2 => andimm (Int.sub n2 Int.one) e1
      | None    => mod_aux Odivu e1 e2
      end
  | divu_default e2 =>
      mod_aux Odivu e1 e2
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

(** ** Floating-point arithmetic *)

Parameter use_fused_mul : unit -> bool.

(*
Definition addf (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop Omulf (t1:::t2:::Enil), t3 => Eop Omuladdf (t1:::t2:::t3:::Enil)
  | t1, Eop Omulf (t2:::t3:::Enil) => Elet t1 (Eop Omuladdf (t2:::t3:::Rvar 0:::Enil))
  | _, _ => Eop Oaddf (e1:::e2:::Enil)
  end.
*)

Inductive addf_cases: forall (e1: expr) (e2: expr), Type :=
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
  if use_fused_mul tt then
    match addf_match e1 e2 with
    | addf_case1 t1 t2 t3 =>
        Eop Omuladdf (t1:::t2:::t3:::Enil)
    | addf_case2 t1 t2 t3 =>
        Eop Omuladdf (t2:::t3:::t1:::Enil)
    | addf_default e1 e2 =>
        Eop Oaddf (e1:::e2:::Enil)
    end
  else Eop Oaddf (e1:::e2:::Enil).

(*
Definition subf (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop Omulfloat (t1:::t2:::Enil), t3 => Eop Omulsubf (t1:::t2:::t3:::Enil)
  | _, _ => Eop Osubf (e1:::e2:::Enil)
  end.
*)

Inductive subf_cases: forall (e1: expr) (e2: expr), Type :=
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
  if use_fused_mul tt then
    match subf_match e1 e2 with
    | subf_case1 t1 t2 t3 =>
        Eop Omulsubf (t1:::t2:::t3:::Enil)
    | subf_default e1 e2 =>
        Eop Osubf (e1:::e2:::Enil)
    end
  else Eop Osubf (e1:::e2:::Enil).

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

(** ** Floating-point conversions *)

Definition intoffloat (e: expr) := Eop Ointoffloat (e ::: Enil).

Definition intuoffloat (e: expr) :=
  let f := Eop (Ofloatconst (Float.floatofintu Float.ox8000_0000)) Enil in
  Elet e
    (Econdition (CEcond (Ccompf Clt) (Eletvar O ::: f ::: Enil))
      (intoffloat (Eletvar O))
      (addimm Float.ox8000_0000 (intoffloat (subf (Eletvar O) f)))).

Definition floatofintu (e: expr) :=
  subf (Eop Ofloatofwords (Eop (Ointconst Float.ox4330_0000) Enil ::: e ::: Enil))
       (Eop (Ofloatconst (Float.from_words Float.ox4330_0000 Int.zero)) Enil).

Definition floatofint (e: expr) :=
  subf (Eop Ofloatofwords (Eop (Ointconst Float.ox4330_0000) Enil
                           ::: addimm Float.ox8000_0000 e ::: Enil))
       (Eop (Ofloatconst (Float.from_words Float.ox4330_0000 Float.ox8000_0000)) Enil).

(** ** Other operators, not optimized. *)

Definition cast8unsigned (e: expr) := Eop Ocast8unsigned (e ::: Enil).
Definition cast8signed (e: expr) := Eop Ocast8signed (e ::: Enil).
Definition cast16unsigned (e: expr) := Eop Ocast16unsigned (e ::: Enil).
Definition cast16signed (e: expr) := Eop Ocast16signed (e ::: Enil).
Definition singleoffloat (e: expr) := Eop Osingleoffloat (e ::: Enil).
Definition negint (e: expr) := Eop (Osubimm Int.zero) (e ::: Enil).
Definition negf (e: expr) :=  Eop Onegf (e ::: Enil).
Definition absf (e: expr) :=  Eop Oabsf (e ::: Enil).
Definition xor (e1 e2: expr) :=  Eop Oxor (e1 ::: e2 ::: Enil).
Definition shr (e1 e2: expr) :=  Eop Oshr (e1 ::: e2 ::: Enil).
Definition mulf (e1 e2: expr) :=  Eop Omulf (e1 ::: e2 ::: Enil).
Definition divf (e1 e2: expr) :=  Eop Odivf (e1 ::: e2 ::: Enil).

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

Inductive addressing_cases: forall (e: expr), Type :=
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

Definition addressing (chunk: memory_chunk) (e: expr) :=
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

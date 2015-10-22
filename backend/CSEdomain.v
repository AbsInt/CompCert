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

(** The abstract domain for value numbering, used in common
    subexpression elimination. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Op.
Require Import Registers.
Require Import RTL.

(** Value numbers are represented by positive integers.  Equations are
  of the form [valnum = rhs] or [valnum >= rhs], where the right-hand
  sides [rhs] are either arithmetic operations or memory loads, [=] is
  strict equality of values, and [>=] is the "more defined than" relation
  over values. *)

Definition valnum := positive.

Inductive rhs : Type :=
  | Op: operation -> list valnum -> rhs
  | Load: memory_chunk -> addressing -> list valnum -> rhs.

Inductive equation : Type :=
  | Eq (v: valnum) (strict: bool) (r: rhs).

Definition eq_valnum: forall (x y: valnum), {x=y}+{x<>y} := peq.

Definition eq_list_valnum: forall (x y: list valnum), {x=y}+{x<>y} := list_eq_dec peq.

Definition eq_rhs (x y: rhs) : {x=y}+{x<>y}.
Proof.
  generalize chunk_eq eq_operation eq_addressing eq_valnum eq_list_valnum.
  decide equality.
Defined.

(** A value numbering is a collection of equations between value numbers
  plus a partial map from registers to value numbers.  Additionally,
  we maintain the next unused value number, so as to easily generate
  fresh value numbers.  We also maintain a reverse mapping from value
  numbers to registers, redundant with the mapping from registers to
  value numbers, in order to speed up some operations. *)

Record numbering : Type := mknumbering {
  num_next: valnum;                  (**r first unused value number *)
  num_eqs: list equation;            (**r valid equations *)
  num_reg: PTree.t valnum;           (**r mapping register to valnum *)
  num_val: PMap.t (list reg)         (**r reverse mapping valnum to regs containing it *)
}.

Definition empty_numbering :=
  {| num_next := 1%positive;
     num_eqs  := nil;
     num_reg  := PTree.empty _;
     num_val  := PMap.init nil |}.

(** A numbering is well formed if all value numbers mentioned are below
  [num_next].  Moreover, the [num_val] reverse mapping must be consistent
  with the [num_reg] direct mapping. *)

Definition valnums_rhs (r: rhs): list valnum :=
  match r with
  | Op op vl => vl
  | Load chunk addr vl => vl
  end.

Definition wf_rhs (next: valnum) (r: rhs) : Prop :=
forall v, In v (valnums_rhs r) -> Plt v next.

Definition wf_equation (next: valnum) (e: equation) : Prop :=
  match e with Eq l str r => Plt l next /\ wf_rhs next r end.

Record wf_numbering (n: numbering) : Prop := {
  wf_num_eqs: forall e,
      In e n.(num_eqs) -> wf_equation n.(num_next) e;
  wf_num_reg: forall r v,
      PTree.get r n.(num_reg) = Some v -> Plt v n.(num_next);
  wf_num_val: forall r v,
      In r (PMap.get v n.(num_val)) -> PTree.get r n.(num_reg) = Some v
}.

Hint Resolve wf_num_eqs wf_num_reg wf_num_val: cse.

(** Satisfiability of numberings.  A numbering holds in a concrete
  execution state if there exists a valuation assigning values to
  value numbers that satisfies the equations and register mapping
  of the numbering. *)

Definition valuation := valnum -> val.

Inductive rhs_eval_to (valu: valuation) (ge: genv) (sp: val) (m: mem):
                                                     rhs -> val -> Prop :=
  | op_eval_to: forall op vl v,
      eval_operation ge sp op (map valu vl) m = Some v ->
      rhs_eval_to valu ge sp m (Op op vl) v
  | load_eval_to: forall chunk addr vl a v,
      eval_addressing ge sp addr (map valu vl) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rhs_eval_to valu ge sp m (Load chunk addr vl) v.

Inductive equation_holds (valu: valuation) (ge: genv) (sp: val) (m: mem):
                                                      equation -> Prop :=
  | eq_holds_strict: forall l r,
      rhs_eval_to valu ge sp m r (valu l) ->
      equation_holds valu ge sp m (Eq l true r)
  | eq_holds_lessdef: forall l r v,
      rhs_eval_to valu ge sp m r v -> Val.lessdef v (valu l) ->
      equation_holds valu ge sp m (Eq l false r).

Record numbering_holds (valu: valuation) (ge: genv) (sp: val)
                       (rs: regset) (m: mem) (n: numbering) : Prop := {
  num_holds_wf:
     wf_numbering n;
  num_holds_eq: forall eq,
     In eq n.(num_eqs) -> equation_holds valu ge sp m eq;
  num_holds_reg: forall r v,
     n.(num_reg)!r = Some v -> rs#r = valu v
}.

Hint Resolve num_holds_wf num_holds_eq num_holds_reg: cse.

Lemma empty_numbering_holds:
  forall valu ge sp rs m,
  numbering_holds valu ge sp rs m empty_numbering.
Proof.
  intros; split; simpl; intros.
- split; simpl; intros.
  + contradiction.
  + rewrite PTree.gempty in H; discriminate.
  + rewrite PMap.gi in H; contradiction.
- contradiction.
- rewrite PTree.gempty in H; discriminate.
Qed.


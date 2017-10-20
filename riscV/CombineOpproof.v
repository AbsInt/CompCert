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

(** Recognition of combined operations, addressing modes and conditions
  during the [CSE] phase. *)

Require Import FunInd.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import CSEdomain.
Require Import CombineOp.

Section COMBINE.

Variable ge: genv.
Variable sp: val.
Variable m: mem.
Variable get: valnum -> option rhs.
Variable valu: valnum -> val.
Hypothesis get_sound: forall v rhs, get v = Some rhs -> rhs_eval_to valu ge sp m rhs (valu v).

Lemma get_op_sound:
  forall v op vl, get v = Some (Op op vl) -> eval_operation ge sp op (map valu vl) m = Some (valu v).
Proof.
  intros. exploit get_sound; eauto. intros REV; inv REV; auto.
Qed.

Ltac UseGetSound :=
  match goal with
  | [ H: get _ = Some _ |- _ ] =>
      let x := fresh "EQ" in (generalize (get_op_sound _ _ _ H); intros x; simpl in x; FuncInv)
  end.

Lemma combine_compimm_ne_0_sound:
  forall x cond args,
  combine_compimm_ne_0 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Cne (valu x) (Vint Int.zero) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Cne (valu x) (Vint Int.zero).
Proof.
  intros until args. functional induction (combine_compimm_ne_0 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite <- H.
  destruct (eval_condition cond (map valu args) m); simpl; auto. destruct b; auto.
Qed.

Lemma combine_compimm_eq_0_sound:
  forall x cond args,
  combine_compimm_eq_0 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Ceq (valu x) (Vint Int.zero) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Ceq (valu x) (Vint Int.zero).
Proof.
  intros until args. functional induction (combine_compimm_eq_0 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite <- H.
  rewrite eval_negate_condition.
  destruct (eval_condition c (map valu args) m); simpl; auto. destruct b; auto.
Qed.

Lemma combine_compimm_eq_1_sound:
  forall x cond args,
  combine_compimm_eq_1 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Ceq (valu x) (Vint Int.one) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Ceq (valu x) (Vint Int.one).
Proof.
  intros until args. functional induction (combine_compimm_eq_1 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite <- H.
  destruct (eval_condition cond (map valu args) m); simpl; auto. destruct b; auto.
Qed.

Lemma combine_compimm_ne_1_sound:
  forall x cond args,
  combine_compimm_ne_1 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Cne (valu x) (Vint Int.one) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Cne (valu x) (Vint Int.one).
Proof.
  intros until args. functional induction (combine_compimm_ne_1 get x); intros EQ; inv EQ.
  (* of cmp *)
  UseGetSound. rewrite <- H.
  rewrite eval_negate_condition.
  destruct (eval_condition c (map valu args) m); simpl; auto. destruct b; auto.
Qed.

Theorem combine_cond_sound:
  forall cond args cond' args',
  combine_cond get cond args = Some(cond', args') ->
  eval_condition cond' (map valu args') m = eval_condition cond (map valu args) m.
Proof.
  intros. functional inversion H; subst.
  (* compimm ne zero *)
  - simpl; eapply combine_compimm_ne_0_sound; eauto.
  (* compimm ne one *)
  - simpl; eapply combine_compimm_ne_1_sound; eauto.
  (* compimm eq zero *)
  - simpl; eapply combine_compimm_eq_0_sound; eauto.
  (* compimm eq one *)
  - simpl; eapply combine_compimm_eq_1_sound; eauto.
  (* compuimm ne zero *)
  - simpl; eapply combine_compimm_ne_0_sound; eauto.
  (* compuimm ne one *)
  - simpl; eapply combine_compimm_ne_1_sound; eauto.
  (* compuimm eq zero *)
  - simpl; eapply combine_compimm_eq_0_sound; eauto.
  (* compuimm eq one *)
  - simpl; eapply combine_compimm_eq_1_sound; eauto.
Qed.

Theorem combine_addr_sound:
  forall addr args addr' args',
  combine_addr get addr args = Some(addr', args') ->
  eval_addressing ge sp addr' (map valu args') = eval_addressing ge sp addr (map valu args).
Proof.
  intros. functional inversion H; subst.
- (* indexed - addimm *)
  UseGetSound. simpl. rewrite <- H0. destruct v; auto. simpl; rewrite H7; simpl.
  rewrite Ptrofs.add_assoc. auto.
- (* indexed - addimml *)
  UseGetSound. simpl. rewrite <- H0. destruct v; auto. simpl; rewrite H7; simpl.
  rewrite Ptrofs.add_assoc. auto.
Qed.

Theorem combine_op_sound:
  forall op args op' args',
  combine_op get op args = Some(op', args') ->
  eval_operation ge sp op' (map valu args') m = eval_operation ge sp op (map valu args) m.
Proof.
  intros. functional inversion H; subst.
  (* addimm - addimm *)
  - UseGetSound. FuncInv. simpl.
    rewrite <- H0. rewrite Val.add_assoc. auto.
  (* andimm - andimm *)
  - UseGetSound; simpl.
    generalize (Int.eq_spec p m0); rewrite H7; intros.
    rewrite <- H0. rewrite Val.and_assoc. simpl. fold p. rewrite H1. auto.
  - UseGetSound; simpl.
    rewrite <- H0. rewrite Val.and_assoc. auto.
  (* orimm - orimm *)
  - UseGetSound. simpl. rewrite <- H0. rewrite Val.or_assoc. auto.
  (* xorimm - xorimm *)
  - UseGetSound. simpl. rewrite <- H0. rewrite Val.xor_assoc. auto.
  (* addlimm - addlimm *)
  - UseGetSound. FuncInv. simpl.
    rewrite <- H0. rewrite Val.addl_assoc. auto.
  (* andlimm - andlimm *)
  - UseGetSound; simpl.
    generalize (Int64.eq_spec p m0); rewrite H7; intros.
    rewrite <- H0. rewrite Val.andl_assoc. simpl. fold p. rewrite H1. auto.
  - UseGetSound; simpl.
    rewrite <- H0. rewrite Val.andl_assoc. auto.
  (* orlimm - orlimm *)
  - UseGetSound. simpl. rewrite <- H0. rewrite Val.orl_assoc. auto.
  (* xorlimm - xorlimm *)
  - UseGetSound. simpl. rewrite <- H0. rewrite Val.xorl_assoc. auto.
  (* cmp *)
  - simpl. decEq; decEq. eapply combine_cond_sound; eauto.
Qed.

End COMBINE.

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

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import CombineOp.
Require Import CSE.

Section COMBINE.

Variable ge: genv.
Variable sp: val.
Variable m: mem.
Variable get: valnum -> option rhs.
Variable valu: valnum -> val.
Hypothesis get_sound: forall v rhs, get v = Some rhs -> equation_holds valu ge sp m v rhs.

Lemma combine_compimm_ne_0_sound:
  forall x cond args,
  combine_compimm_ne_0 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Cne (valu x) (Vint Int.zero) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Cne (valu x) (Vint Int.zero).
Proof.
  intros until args. functional induction (combine_compimm_ne_0 get x); intros EQ; inv EQ.
  (* of cmp *)
  exploit get_sound; eauto. unfold equation_holds. simpl. intro EQ; inv EQ. 
  destruct (eval_condition cond (map valu args) m); simpl; auto. destruct b; auto.
  (* of and *)
  exploit get_sound; eauto. unfold equation_holds; simpl. 
  destruct args; try discriminate. destruct args; try discriminate. simpl. 
  intros EQ; inv EQ. destruct (valu v); simpl; auto. 
Qed.

Lemma combine_compimm_eq_0_sound:
  forall x cond args,
  combine_compimm_eq_0 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Ceq (valu x) (Vint Int.zero) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Ceq (valu x) (Vint Int.zero).
Proof.
  intros until args. functional induction (combine_compimm_eq_0 get x); intros EQ; inv EQ.
  (* of cmp *)
  exploit get_sound; eauto. unfold equation_holds. simpl. intro EQ; inv EQ. 
  rewrite eval_negate_condition. 
  destruct (eval_condition c (map valu args) m); simpl; auto. destruct b; auto.
  (* of and *)
  exploit get_sound; eauto. unfold equation_holds; simpl. 
  destruct args; try discriminate. destruct args; try discriminate. simpl. 
  intros EQ; inv EQ. destruct (valu v); simpl; auto. 
Qed.

Lemma combine_compimm_eq_1_sound:
  forall x cond args,
  combine_compimm_eq_1 get x = Some(cond, args) ->
  eval_condition cond (map valu args) m = Val.cmp_bool Ceq (valu x) (Vint Int.one) /\
  eval_condition cond (map valu args) m = Val.cmpu_bool (Mem.valid_pointer m) Ceq (valu x) (Vint Int.one).
Proof.
  intros until args. functional induction (combine_compimm_eq_1 get x); intros EQ; inv EQ.
  (* of cmp *)
  exploit get_sound; eauto. unfold equation_holds. simpl. intro EQ; inv EQ. 
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
  exploit get_sound; eauto. unfold equation_holds. simpl. intro EQ; inv EQ. 
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
  simpl; eapply combine_compimm_ne_0_sound; eauto.
  (* compimm ne one *)
  simpl; eapply combine_compimm_ne_1_sound; eauto.
  (* compimm eq zero *)
  simpl; eapply combine_compimm_eq_0_sound; eauto.
  (* compimm eq one *)
  simpl; eapply combine_compimm_eq_1_sound; eauto.
  (* compuimm ne zero *)
  simpl; eapply combine_compimm_ne_0_sound; eauto.
  (* compuimm ne one *)
  simpl; eapply combine_compimm_ne_1_sound; eauto.
  (* compuimm eq zero *)
  simpl; eapply combine_compimm_eq_0_sound; eauto.
  (* compuimm eq one *)
  simpl; eapply combine_compimm_eq_1_sound; eauto.
Qed.

Theorem combine_addr_sound:
  forall addr args addr' args',
  combine_addr get addr args = Some(addr', args') ->
  eval_addressing ge sp addr' (map valu args') = eval_addressing ge sp addr (map valu args).
Proof.
  intros. functional inversion H; subst.
  (* indexed - addimm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intro EQ. FuncInv.
  rewrite <- H0. rewrite Val.add_assoc. auto. 
Qed.

Theorem combine_op_sound:
  forall op args op' args',
  combine_op get op args = Some(op', args') ->
  eval_operation ge sp op' (map valu args') m = eval_operation ge sp op (map valu args) m.
Proof.
  intros. functional inversion H; subst.
(* addimm - addimm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1. rewrite Val.add_assoc. auto.
(* addimm - subimm *)
Opaque Val.sub.
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1. change (Vint (Int.add m0 n)) with (Val.add (Vint m0) (Vint n)).
  rewrite Val.sub_add_l. auto.
(* subimm - addimm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1.
Transparent Val.sub.
  destruct v; simpl; auto. repeat rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite Int.neg_add_distr. decEq. decEq. decEq. apply Int.add_commut.
(* andimm - andimm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1. rewrite Val.and_assoc. auto.
(* andimm - rolm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1. destruct v; simpl; auto. unfold Int.rolm. rewrite Int.and_assoc. auto.
(* orimm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1. rewrite Val.or_assoc. auto.
(* xorimm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1. rewrite Val.xor_assoc. auto.
(* rolm - andimm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1. rewrite <- Val.rolm_zero. rewrite Val.rolm_rolm. 
  rewrite (Int.add_commut Int.zero). rewrite Int.add_zero. auto.
(* rolm - rolm *)
  exploit get_sound; eauto. unfold equation_holds; simpl; intros. FuncInv.
  rewrite <- H1. rewrite Val.rolm_rolm. auto. 
(* cmp *)
  simpl. decEq; decEq. eapply combine_cond_sound; eauto.
Qed.

End COMBINE.

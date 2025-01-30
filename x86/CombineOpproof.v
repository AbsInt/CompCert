(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition of combined operations, addressing modes and conditions
  during the [CSE] phase. *)

From Coq Require Import FunInd.
Require Import Coqlib.
Require Import Integers Values Memory.
Require Import Op RTL CSEdomain.
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
  (* of and *)
  UseGetSound. rewrite <- H.
  destruct v; simpl; auto.
  (* of xorimm *)
  UseGetSound. rewrite <- H.
  destruct v; simpl; auto. rewrite Int.xor_is_zero; auto.
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
  (* of and *)
  UseGetSound. rewrite <- H. destruct v; auto.
  (* of xorimm *)
  UseGetSound. rewrite <- H.
  destruct v; simpl; auto. rewrite Int.xor_is_zero; auto.
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

Theorem combine_cond'_sound:
  forall cond args res res',
  combine_cond' cond args = Some res' ->
  eval_condition cond (map valu args) m = Some res ->
  res = res'.
Proof.
  intros.  unfold combine_cond' in *.
  destruct cond; inv H; destruct args; inv H2; destruct args; inv H1; destruct args; inv H2.
  apply (combine_comparison_cmp_sound valu c v v0 res res'); auto.
  apply (combine_comparison_cmpu_sound valu m c v v0 res res'); auto.
  apply (combine_comparison_cmpl_sound valu c v v0 res res'); auto.
  apply (combine_comparison_cmplu_sound valu m c v v0 res res'); auto.
Qed.

Theorem combine_addr_32_sound:
  forall addr args addr' args',
  combine_addr_32 get addr args = Some(addr', args') ->
  eval_addressing32 ge sp addr' (map valu args') = eval_addressing32 ge sp addr (map valu args).
Proof.
  intros. functional inversion H; subst.
  (* indexed - lea *)
  UseGetSound. simpl. unfold offset_addressing in H7. destruct (addressing_valid (offset_addressing_total a n)); inv H7.
  eapply eval_offset_addressing_total_32; eauto.
Qed.

Theorem combine_addr_64_sound:
  forall addr args addr' args',
  combine_addr_64 get addr args = Some(addr', args') ->
  eval_addressing64 ge sp addr' (map valu args') = eval_addressing64 ge sp addr (map valu args).
Proof.
  intros. functional inversion H; subst.
  (* indexed - leal *)
  UseGetSound. simpl. unfold offset_addressing in H7. destruct (addressing_valid (offset_addressing_total a n)); inv H7.
  eapply eval_offset_addressing_total_64; eauto.
Qed.

Theorem combine_addr_sound:
  forall addr args addr' args',
  combine_addr get addr args = Some(addr', args') ->
  eval_addressing ge sp addr' (map valu args') = eval_addressing ge sp addr (map valu args).
Proof.
  unfold combine_addr, eval_addressing; intros; destruct Archi.ptr64.
  apply combine_addr_64_sound; auto.
  apply combine_addr_32_sound; auto.
Qed.

Theorem combine_op_sound:
  forall op args op' args' r,
  combine_op get op args = Some(op', args') ->
  eval_operation ge sp op (map valu args) m = Some r ->
  exists r', eval_operation ge sp op' (map valu args') m = Some r' /\ Val.lessdef r r'.
Proof.
  intros. functional inversion H; subst.
(* lea-lea *)
 - exists r; split; auto. rewrite <- H0. eapply combine_addr_32_sound; eauto.
(* leal-leal *)
 - exists r; split; auto.  rewrite <- H0. eapply combine_addr_64_sound; eauto.
(* andimm - andimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.and_assoc. auto.
(* orimm - orimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.or_assoc. auto.
(* xorimm - xorimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.xor_assoc. auto.
(* andimm - andimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.andl_assoc. auto.
(* orimm - orimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.orl_assoc. auto.
(* xorimm - xorimm *)
 - UseGetSound. exists r; split; auto. rewrite <- H0. simpl. rewrite <- H1. rewrite Val.xorl_assoc. auto.
 (* cmp true *)
 - exists Vtrue; split; auto. inv H0. destruct (eval_condition cond (map valu args) m) eqn:?; auto.
   rewrite (combine_cond'_sound cond args b true); eauto.
 (* cmp false *)
 - exists Vfalse; split; auto. inv H0. destruct (eval_condition cond (map valu args) m) eqn:?; auto.
   rewrite (combine_cond'_sound cond args b false); eauto.
 (* cmp reduce *)
 - exists r; split; auto. decEq; decEq. simpl. erewrite combine_cond_sound; eauto.
 (* sel cond true *)
 - exists (valu x). simpl in H0.
   destruct (eval_condition cond (map valu args1) m) eqn:?; simpl; split; auto; inv H0; auto.
   rewrite (combine_cond'_sound cond args1 b true); eauto.  destruct (valu x), ty; auto.
 (* sel cond false *)
 - exists (valu y). simpl in H0.
   destruct (eval_condition cond (map valu args1) m) eqn:?; simpl; split; auto; inv H0; auto.
   rewrite (combine_cond'_sound cond args1 b false); eauto.  destruct (valu y), ty; auto.
 (* sel cond same *)
 - exists (valu y); split; auto. inv H0. destruct (eval_condition cond (map valu args1) m); auto.
   simpl. destruct b, (valu y), ty; auto.
 - exists r; split; auto. rewrite <- H0.
   simpl. erewrite combine_cond_sound; eauto.
Qed.

End COMBINE.

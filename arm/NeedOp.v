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

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import NeedDomain.
Require Import RTL.

(** Neededness analysis for ARM operators *)

Definition needs_of_condition (cond: condition): list nval := nil.

Definition needs_of_shift (s: shift) (nv: nval): nval :=
  match s with
  | Slsl x => shlimm nv x
  | Slsr x => shruimm nv x
  | Sasr x => shrimm nv x
  | Sror x => ror nv x
  end.

Definition op1 (nv: nval) := nv :: nil.
Definition op2 (nv: nval) := nv :: nv :: nil.
Definition op2shift (s: shift) (nv: nval) := nv :: needs_of_shift s nv :: nil.

Definition needs_of_operation (op: operation) (nv: nval): list nval :=
  match op with
  | Omove => nv::nil
  | Ointconst n => nil
  | Ofloatconst n => nil
  | Osingleconst n => nil
  | Oaddrsymbol id ofs => nil
  | Oaddrstack ofs => nil
  | Ocast8signed => op1 (sign_ext 8 nv)
  | Ocast16signed => op1 (sign_ext 16 nv)
  | Oadd => op2 (modarith nv)
  | Oaddshift s => op2shift s (modarith nv)
  | Oaddimm _ => op1 (modarith nv)
  | Osub => op2 (default nv)
  | Osubshift s => op2shift s (default nv)
  | Orsubshift s => op2shift s (default nv)
  | Orsubimm _ => op1 (default nv)
  | Omul => op2 (modarith nv)
  | Omla => let n := modarith nv in let n2 := modarith n in n2::n2::n::nil
  | Omulhu | Omulhs | Odiv | Odivu => let n := default nv in n::n::nil
  | Oand => op2 (bitwise nv)
  | Oandshift s => op2shift s (bitwise nv)
  | Oandimm n => op1 (andimm nv n)
  | Oor => op2 (bitwise nv)
  | Oorshift s => op2shift s (bitwise nv)
  | Oorimm n => op1 (orimm nv n)
  | Oxor => op2 (bitwise nv)
  | Oxorshift s => op2shift s (bitwise nv)
  | Oxorimm n => op1 (bitwise nv)
  | Obic => let n := bitwise nv in n::bitwise n::nil
  | Obicshift s => let n := bitwise nv in n::needs_of_shift s (bitwise n)::nil
  | Onot => op1 (bitwise nv)
  | Onotshift s => op1 (needs_of_shift s (bitwise nv))
  | Oshl | Oshr | Oshru => op2 (default nv)
  | Oshift s => op1 (needs_of_shift s nv)
  | Oshrximm _ => op1 (default nv)
  | Onegf | Oabsf => op1 (default nv)
  | Oaddf | Osubf | Omulf | Odivf => op2 (default nv)
  | Onegfs | Oabsfs => op1 (default nv)
  | Oaddfs | Osubfs | Omulfs | Odivfs => op2 (default nv)
  | Ofloatofsingle | Osingleoffloat => op1 (default nv)
  | Ointoffloat | Ointuoffloat | Ofloatofint | Ofloatofintu => op1 (default nv)
  | Ointofsingle | Ointuofsingle | Osingleofint | Osingleofintu => op1 (default nv)
  | Omakelong => op2 (default nv)
  | Olowlong | Ohighlong => op1 (default nv)
  | Ocmp c => needs_of_condition c
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Ocast8signed => sign_ext_redundant 8 nv
  | Ocast16signed => sign_ext_redundant 16 nv
  | Oandimm n => andimm_redundant nv n
  | Oorimm n => orimm_redundant nv n
  | _ => false
  end.

Ltac InvAgree :=
  match goal with
  | [H: vagree_list nil _ _ |- _ ] => inv H; InvAgree
  | [H: vagree_list (_::_) _ _ |- _ ] => inv H; InvAgree
  | _ => idtac
  end.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Section SOUNDNESS.

Variable ge: genv.
Variable sp: block.
Variables m m': mem.
Hypothesis PERM: forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p.

Lemma needs_of_condition_sound:
  forall cond args b args',
  eval_condition cond args m = Some b ->
  vagree_list args args' (needs_of_condition cond) ->
  eval_condition cond args' m' = Some b.
Proof.
  intros. unfold needs_of_condition in H0.
  eapply default_needs_of_condition_sound; eauto.
Qed.

Lemma needs_of_shift_sound:
  forall v v' s nv,
  vagree v v' (needs_of_shift s nv) ->
  vagree (eval_shift s v) (eval_shift s v') nv.
Proof.
  intros. destruct s; simpl in *.
  apply shlimm_sound; auto.
  apply shruimm_sound; auto.
  apply shrimm_sound; auto.
  apply ror_sound; auto.
Qed.

Lemma val_sub_lessdef:
  forall v1 v1' v2 v2',
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Val.lessdef (Val.sub v1 v2) (Val.sub v1' v2').
Proof.
  intros. inv H. inv H0. auto. destruct v1'; simpl; auto. simpl; auto.
Qed.

Lemma needs_of_operation_sound:
  forall op args v nv args',
  eval_operation ge (Vptr sp Ptrofs.zero) op args m = Some v ->
  vagree_list args args' (needs_of_operation op nv) ->
  nv <> Nothing ->
  exists v',
     eval_operation ge (Vptr sp Ptrofs.zero) op args' m' = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_operation; intros; destruct op; try (eapply default_needs_of_operation_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree; TrivialExists.
- apply sign_ext_sound; auto. compute; auto.
- apply sign_ext_sound; auto. compute; auto.
- apply add_sound; auto.
- apply add_sound; auto. apply needs_of_shift_sound; auto.
- apply add_sound; auto with na.
- replace (default nv) with All in *.
  apply vagree_lessdef. apply val_sub_lessdef; auto with na.
  apply lessdef_vagree. apply needs_of_shift_sound; auto with na.
  destruct nv; simpl; congruence.
- replace (default nv) with All in *.
  apply vagree_lessdef. apply val_sub_lessdef; auto with na.
  apply lessdef_vagree. apply needs_of_shift_sound; auto with na.
  destruct nv; simpl; congruence.
- apply mul_sound; auto.
- apply add_sound; auto. apply mul_sound; auto.
- apply and_sound; auto.
- apply and_sound; auto. apply needs_of_shift_sound; auto.
- apply andimm_sound; auto.
- apply or_sound; auto.
- apply or_sound; auto. apply needs_of_shift_sound; auto.
- apply orimm_sound; auto.
- apply xor_sound; auto.
- apply xor_sound; auto. apply needs_of_shift_sound; auto.
- apply xor_sound; auto with na.
- apply and_sound; auto. apply notint_sound; auto.
- apply and_sound; auto. apply notint_sound. apply needs_of_shift_sound; auto.
- apply notint_sound; auto.
- apply notint_sound. apply needs_of_shift_sound; auto.
- apply needs_of_shift_sound; auto.
Qed.

Lemma operation_is_redundant_sound:
  forall op nv arg1 args v arg1' args',
  operation_is_redundant op nv = true ->
  eval_operation ge (Vptr sp Ptrofs.zero) op (arg1 :: args) m = Some v ->
  vagree_list (arg1 :: args) (arg1' :: args') (needs_of_operation op nv) ->
  vagree v arg1' nv.
Proof.
  intros. destruct op; simpl in *; try discriminate; inv H1; FuncInv; subst.
- apply sign_ext_redundant_sound; auto. omega.
- apply sign_ext_redundant_sound; auto. omega.
- apply andimm_redundant_sound; auto.
- apply orimm_redundant_sound; auto.
Qed.

End SOUNDNESS.




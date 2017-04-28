(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import AST Integers Floats.
Require Import Values Memory Globalenvs.
Require Import Op RTL.
Require Import NeedDomain.

(** Neededness analysis for RISC-V operators *)

Definition op1 (nv: nval) := nv :: nil.
Definition op2 (nv: nval) := nv :: nv :: nil.

Definition needs_of_condition (cond: condition): list nval := nil.

Definition needs_of_operation (op: operation) (nv: nval): list nval :=
  match op with
  | Omove => op1 nv
  | Ointconst n => nil
  | Olongconst n => nil
  | Ofloatconst n => nil
  | Osingleconst n => nil
  | Oaddrsymbol id ofs => nil
  | Oaddrstack ofs => nil
  | Ocast8signed => op1 (sign_ext 8 nv)
  | Ocast16signed => op1 (sign_ext 16 nv)
  | Oadd => op2 (modarith nv)
  | Oaddimm n => op1 (modarith nv)
  | Oneg => op1 (modarith nv)
  | Osub => op2 (default nv)
  | Omul => op2 (modarith nv)
  | Omulhs | Omulhu | Odiv | Odivu | Omod | Omodu => op2 (default nv)
  | Oand => op2 (bitwise nv)
  | Oandimm n => op1 (andimm nv n)
  | Oor => op2 (bitwise nv)
  | Oorimm n => op1 (orimm nv n)
  | Oxor => op2 (bitwise nv)
  | Oxorimm n => op1 (bitwise nv)
  | Oshl | Oshr | Oshru => op2 (default nv)
  | Oshlimm n => op1 (shlimm nv n)
  | Oshrimm n => op1 (shrimm nv n)
  | Oshruimm n => op1 (shruimm nv n)
  | Oshrximm n => op1 (default nv)
  | Omakelong => op2 (default nv)
  | Olowlong | Ohighlong => op1 (default nv)
  | Ocast32signed => op1 (default nv)
  | Ocast32unsigned => op1 (default nv)
  | Oaddl => op2 (default nv)
  | Oaddlimm n => op1 (default nv)
  | Onegl => op1 (default nv)
  | Osubl => op2 (default nv)
  | Omull => op2 (default nv)
  | Omullhs | Omullhu | Odivl | Odivlu | Omodl | Omodlu => op2 (default nv)
  | Oandl => op2 (default nv)
  | Oandlimm n => op1 (default nv)
  | Oorl => op2 (default nv)
  | Oorlimm n => op1 (default nv)
  | Oxorl => op2 (default nv)
  | Oxorlimm n => op1 (default nv)
  | Oshll | Oshrl | Oshrlu => op2 (default nv)
  | Oshllimm n => op1 (default nv)
  | Oshrlimm n => op1 (default nv)
  | Oshrluimm n => op1 (default nv)
  | Oshrxlimm n => op1 (default nv)
  | Onegf | Oabsf => op1 (default nv)
  | Oaddf | Osubf | Omulf | Odivf => op2 (default nv)
  | Onegfs | Oabsfs => op1 (default nv)
  | Oaddfs | Osubfs | Omulfs | Odivfs => op2 (default nv)
  | Ofloatofsingle | Osingleoffloat => op1 (default nv)
  | Ointoffloat | Ointuoffloat | Ofloatofint | Ofloatofintu => op1 (default nv)
  | Olongoffloat | Olonguoffloat | Ofloatoflong | Ofloatoflongu => op1 (default nv)
  | Ointofsingle | Ointuofsingle | Osingleofint | Osingleofintu => op1 (default nv)
  | Olongofsingle | Olonguofsingle | Osingleoflong | Osingleoflongu => op1 (default nv)
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
- apply add_sound; auto with na.
- apply neg_sound; auto.
- apply mul_sound; auto.
- apply and_sound; auto.
- apply andimm_sound; auto.
- apply or_sound; auto.
- apply orimm_sound; auto.
- apply xor_sound; auto.
- apply xor_sound; auto with na.
- apply shlimm_sound; auto.
- apply shrimm_sound; auto.
- apply shruimm_sound; auto.
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

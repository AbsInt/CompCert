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

(** Neededness analysis for x86_64 operators *)

Require Import Coqlib.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Op NeedDomain RTL.

Definition op1 (nv: nval) := nv :: nil.
Definition op2 (nv: nval) := nv :: nv :: nil.

Definition needs_of_condition (cond: condition): list nval :=
  match cond with
  | Cmaskzero n | Cmasknotzero n => op1 (maskzero n)
  | _ => nil
  end.

Definition needs_of_addressing_32 (addr: addressing) (nv: nval): list nval :=
  match addr with
  | Aindexed n => op1 (modarith nv)
  | Aindexed2 n => op2 (modarith nv)
  | Ascaled sc ofs => op1 (modarith (modarith nv))
  | Aindexed2scaled sc ofs => op2 (modarith nv)
  | Aglobal s ofs => nil
  | Abased s ofs => op1 (modarith nv)
  | Abasedscaled sc s ofs => op1 (modarith (modarith nv))
  | Ainstack ofs => nil
  end.

Definition needs_of_addressing_64 (addr: addressing) (nv: nval): list nval :=
  match addr with
  | Aindexed n => op1 (default nv)
  | Aindexed2 n => op2 (default nv)
  | Ascaled sc ofs => op1 (default nv)
  | Aindexed2scaled sc ofs => op2 (default nv)
  | Aglobal s ofs => nil
  | Abased s ofs => op1 (default nv)
  | Abasedscaled sc s ofs => op1 (default nv)
  | Ainstack ofs => nil
  end.

Definition needs_of_addressing (addr: addressing) (nv: nval): list nval :=
  if Archi.ptr64 then needs_of_addressing_64 addr nv else needs_of_addressing_32 addr nv.

Definition needs_of_operation (op: operation) (nv: nval): list nval :=
  match op with
  | Omove => op1 nv
  | Ointconst n => nil
  | Olongconst n => nil
  | Ofloatconst n => nil
  | Osingleconst n => nil
  | Oindirectsymbol id => nil
  | Ocast8signed => op1 (sign_ext 8 nv)
  | Ocast8unsigned => op1 (zero_ext 8 nv)
  | Ocast16signed => op1 (sign_ext 16 nv)
  | Ocast16unsigned => op1 (zero_ext 16 nv)
  | Oneg => op1 (modarith nv)
  | Osub => op2 (default nv)
  | Omul => op2 (modarith nv)
  | Omulimm n => op1 (modarith nv)
  | Omulhs | Omulhu | Odiv | Odivu | Omod | Omodu => op2 (default nv)
  | Oand => op2 (bitwise nv)
  | Oandimm n => op1 (andimm nv n)
  | Oor => op2 (bitwise nv)
  | Oorimm n => op1 (orimm nv n)
  | Oxor => op2 (bitwise nv)
  | Oxorimm n => op1 (bitwise nv)
  | Onot => op1 (bitwise nv)
  | Oshl => op2 (default nv)
  | Oshlimm n => op1 (shlimm nv n)
  | Oshr => op2 (default nv)
  | Oshrimm n => op1 (shrimm nv n)
  | Oshrximm n => op1 (default nv)
  | Oshru => op2 (default nv)
  | Oshruimm n => op1 (shruimm nv n)
  | Ororimm n => op1 (ror nv n)
  | Oshldimm n => op1 (default nv)
  | Olea addr => needs_of_addressing_32 addr nv
  | Omakelong => op2 (default nv)
  | Olowlong | Ohighlong => op1 (default nv)
  | Ocast32signed => op1 (default nv)
  | Ocast32unsigned => op1 (default nv)
  | Onegl => op1 (default nv)
  | Oaddlimm _ => op1 (default nv)
  | Osubl => op2 (default nv)
  | Omull => op2 (default nv)
  | Omullimm _ => op1 (default nv)
  | Omullhs | Omullhu | Odivl | Odivlu | Omodl | Omodlu => op2 (default nv)
  | Oandl => op2 (default nv)
  | Oandlimm _ => op1 (default nv)
  | Oorl => op2 (default nv)
  | Oorlimm _ => op1 (default nv)
  | Oxorl => op2 (default nv)
  | Oxorlimm _ => op1 (default nv)
  | Onotl => op1 (default nv)
  | Oshll => op2 (default nv)
  | Oshllimm _ => op1 (default nv)
  | Oshrl => op2 (default nv)
  | Oshrlimm _ => op1 (default nv)
  | Oshrxlimm n => op1 (default nv)
  | Oshrlu => op2 (default nv)
  | Oshrluimm _ => op1 (default nv)
  | Ororlimm _ => op1 (default nv)
  | Oleal addr => needs_of_addressing_64 addr nv
  | Onegf | Oabsf => op1 (default nv)
  | Oaddf | Osubf | Omulf | Odivf => op2 (default nv)
  | Onegfs | Oabsfs => op1 (default nv)
  | Oaddfs | Osubfs | Omulfs | Odivfs => op2 (default nv)
  | Osingleoffloat | Ofloatofsingle => op1 (default nv)
  | Ointoffloat | Ofloatofint | Ointofsingle | Osingleofint => op1 (default nv)
  | Olongoffloat | Ofloatoflong | Olongofsingle | Osingleoflong => op1 (default nv)
  | Ocmp c => needs_of_condition c
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Ocast8signed => sign_ext_redundant 8 nv
  | Ocast8unsigned => zero_ext_redundant 8 nv
  | Ocast16signed => sign_ext_redundant 16 nv
  | Ocast16unsigned => zero_ext_redundant 16 nv
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
  intros. destruct cond; simpl in H;
  try (eapply default_needs_of_condition_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree.
- eapply maskzero_sound; eauto.
- destruct (Val.maskzero_bool v n) as [b'|] eqn:MZ; try discriminate.
  erewrite maskzero_sound; eauto.
Qed.

Lemma needs_of_addressing_32_sound:
  forall sp addr args v nv args',
  eval_addressing32 ge (Vptr sp Ptrofs.zero) addr args = Some v ->
  vagree_list args args' (needs_of_addressing_32 addr nv) ->
  exists v',
     eval_addressing32 ge (Vptr sp Ptrofs.zero) addr args' = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_addressing_32; intros.
  destruct addr; simpl in *; FuncInv; InvAgree; TrivialExists;
  auto using add_sound, mul_sound with na.
  apply add_sound; auto with na. apply add_sound; rewrite modarith_idem; auto.
  apply add_sound; auto. apply add_sound; rewrite modarith_idem; auto with na.
  apply mul_sound; rewrite modarith_idem; auto with na.
Qed.

(*
Lemma needs_of_addressing_64_sound:
  forall sp addr args v nv args',
  eval_addressing64 ge (Vptr sp Ptrofs.zero) addr args = Some v ->
  vagree_list args args' (needs_of_addressing_64 addr nv) ->
  exists v',
     eval_addressing64 ge (Vptr sp Ptrofs.zero) addr args' = Some v'
  /\ vagree v v' nv.
*)

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
- apply zero_ext_sound; auto. omega.
- apply sign_ext_sound; auto. compute; auto.
- apply zero_ext_sound; auto. omega.
- apply neg_sound; auto.
- apply mul_sound; auto.
- apply mul_sound; auto with na.
- apply and_sound; auto.
- apply andimm_sound; auto.
- apply or_sound; auto.
- apply orimm_sound; auto.
- apply xor_sound; auto.
- apply xor_sound; auto with na.
- apply notint_sound; auto.
- apply shlimm_sound; auto.
- apply shrimm_sound; auto.
- apply shruimm_sound; auto.
- apply ror_sound; auto.
- eapply needs_of_addressing_32_sound; eauto.
- change (eval_addressing64 ge (Vptr sp Ptrofs.zero) a args')
    with (eval_operation ge (Vptr sp Ptrofs.zero) (Oleal a) args' m').
  eapply default_needs_of_operation_sound; eauto.
  destruct a; simpl in H0; auto.
- destruct (eval_condition cond args m) as [b|] eqn:EC; simpl in H2.
  erewrite needs_of_condition_sound by eauto.
  subst v; simpl. auto with na.
  subst v; auto with na.
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
- apply zero_ext_redundant_sound; auto. omega.
- apply sign_ext_redundant_sound; auto. omega.
- apply zero_ext_redundant_sound; auto. omega.
- apply andimm_redundant_sound; auto.
- apply orimm_redundant_sound; auto.
Qed.

End SOUNDNESS.



(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import AST Integers Floats.
Require Import Values Memory Globalenvs.
Require Import Op RTL.
Require Import NeedDomain.

(** Neededness analysis for AArch64 operators *)

Definition needs_of_shift (s: shift) (a: amount32) (nv: nval) :=
  match s with
  | Slsl => shlimm nv a
  | Sasr => shrimm nv a
  | Slsr => shruimm nv a
  | Sror => ror nv a
  end.

Definition needs_of_shiftl (s: shift) (a: amount64) (nv: nval) :=
  match s with
  | Slsl => shllimm nv a
  | Sasr => shrlimm nv a
  | Slsr => shrluimm nv a
  | Sror => rorl nv a
  end.

Definition needs_of_extend (x: extension) (a: amount64) (nv: nval) :=
  match x with
  | Xuns32 => longofintu (shllimm nv a)
  | Xsgn32 => longofint (shllimm nv a)
  end.

Definition zero_ext' (s: Z) (nv: nval) :=
  if zle 0 s then zero_ext s nv else default nv.
Definition sign_ext' (s: Z) (nv: nval) :=
  if zlt 0 s then sign_ext s nv else default nv.

Definition op1 (nv: nval) := nv :: nil.
Definition op2 (nv: nval) := nv :: nv :: nil.
Definition op1shift (s: shift) (a: amount32) (nv: nval) :=
  needs_of_shift s a nv :: nil.
Definition op1shiftl (s: shift) (a: amount64) (nv: nval) :=
  needs_of_shiftl s a nv :: nil.
Definition op2shift (s: shift) (a: amount32) (nv: nval) :=
  nv :: needs_of_shift s a nv :: nil.
Definition op2shiftl (s: shift) (a: amount64) (nv: nval) :=
  nv :: needs_of_shiftl s a nv :: nil.
Definition op2extl (x: extension) (a: amount64) (nv: nval) :=
  nv :: needs_of_extend x a nv :: nil.

Definition needs_of_condition (cond: condition): list nval := nil.

Definition needs_of_operation (op: operation) (nv: nval): list nval :=
  match op with
  | Omove => nv :: nil
  | Ointconst _ => nil
  | Olongconst _ => nil
  | Ofloatconst _ => nil
  | Osingleconst _ => nil
  | Oaddrsymbol _ _ => nil
  | Oaddrstack _ => nil
  | Oshift s a => op1shift s a nv
  | Oadd | Osub | Omul => op2 (modarith nv)
  | Oaddshift s a | Osubshift s a => op2shift s a (modarith nv)
  | Oaddimm _ => op1 (modarith nv)
  | Oneg => op1 (modarith nv)
  | Onegshift s a => op1shift s a (modarith nv)
  | Omuladd | Omulsub => 
      let n := modarith nv in n :: n :: n :: nil
  | Odiv | Odivu => op2 (default nv)
  | Oand | Oor | Oxor => op2 (bitwise nv)
  | Oandshift s a | Oorshift s a | Oxorshift s a =>  op2shift s a (bitwise nv)
  | Oandimm  n => op1 (andimm nv n)
  | Oorimm n => op1 (orimm nv n)
  | Oxorimm n => op1 (bitwise nv)
  | Onot => op1 (bitwise nv)
  | Onotshift s a => needs_of_shift s a (bitwise nv) :: nil
  | Obic | Oorn | Oeqv => 
      let n := bitwise nv in n :: bitwise n :: nil
  | Obicshift s a | Oornshift s a | Oeqvshift s a =>
      let n := bitwise nv in n :: needs_of_shift s a (bitwise n) :: nil
  | Oshl | Oshr | Oshru => op2 (default nv)
  | Oshrximm _ => op1 (default nv)
  | Ozext s => op1 (zero_ext' s nv)
  | Osext s => op1 (sign_ext' s nv)
  | Oshlzext s a => op1 (zero_ext' s (shlimm nv a))
  | Oshlsext s a => op1 (sign_ext' s (shlimm nv a))
  | Ozextshr a s => op1 (shruimm (zero_ext' s nv) a)
  | Osextshr a s => op1 (shrimm (sign_ext' s nv) a)

  | Oshiftl s a => op1shiftl s a nv
  | Oextend x a => op1 (needs_of_extend x a nv)
  | Omakelong => makelong_hi nv :: makelong_lo nv :: nil
  | Olowlong => op1 (loword nv)
  | Ohighlong => op1 (hiword nv)
  | Oaddl | Omull => op2 (modarith nv)
  | Osubl => op2 (default nv)
  | Oaddlshift s a => op2shiftl s a (modarith nv)
  | Oaddlext x a => op2extl x a (modarith nv)
  | Osublshift _ _ | Osublext _ _ => op2 (default nv)
  | Oaddlimm _ => op1 (modarith nv)
  | Onegl => op1 (modarith nv)
  | Oneglshift s a => op1shiftl s a (modarith nv)
  | Omulladd => let n := modarith nv in n :: n :: n :: nil
  | Omullsub | Omullhs | Omullhu | Odivl | Odivlu => op2 (default nv)
  | Oandl | Oorl | Oxorl | Obicl | Oornl | Oeqvl => op2 (bitwise nv)
  | Oandlshift s a | Oorlshift s a  | Oxorlshift s a => op2shiftl s a (bitwise nv)
  | Obiclshift s a | Oornlshift s a | Oeqvlshift s a =>
      let n := bitwise nv in n :: needs_of_shiftl s a (bitwise n) :: nil
  | Oandlimm n => op1 (andlimm nv n)
  | Oorlimm n => op1 (orlimm nv n)
  | Oxorlimm n => op1 (bitwise nv)

  | Onotl => op1 (bitwise nv)
  | Onotlshift s a => needs_of_shiftl s a (bitwise nv) :: nil
  | Oshll | Oshrl | Oshrlu => op2 (default nv)
  | Oshrlximm _ => op1 (default nv)
  | Ozextl _ | Osextl _
  | Oshllzext _ _ | Oshllsext _ _ | Ozextshrl _ _ | Osextshrl _ _ => op1 (default nv)
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
  | Osel c ty => nv :: nv :: needs_of_condition c
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Ozext s => zle 0 s && zero_ext_redundant s nv
  | Osext s => zlt 0 s && sign_ext_redundant s nv
  | Oandimm n => andimm_redundant nv n
  | Oorimm n => orimm_redundant nv n
  | Oandlimm n => andlimm_redundant nv n
  | Oorlimm n => orlimm_redundant nv n
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

Lemma shift_sound:
  forall v w s a x,
  vagree v w (needs_of_shift s a x) ->
  vagree (eval_shift s v a) (eval_shift s w a) x.
Proof.
  intros until x; destruct s; simpl; intros.
- apply shlimm_sound; auto.
- apply shruimm_sound; auto.
- apply shrimm_sound; auto.
- apply ror_sound; auto.
Qed.

Lemma shiftl_sound:
  forall v w s a x,
  vagree v w (needs_of_shiftl s a x) ->
  vagree (eval_shiftl s v a) (eval_shiftl s w a) x.
Proof.
  intros until x; destruct s; simpl; intros.
- apply shllimm_sound; auto.
- apply shrluimm_sound; auto.
- apply shrlimm_sound; auto.
- apply rorl_sound; auto.
Qed.

Lemma extend_sound:
  forall v w ext a x,
  vagree v w (needs_of_extend ext a x) ->
  vagree (eval_extend ext v a) (eval_extend ext w a) x.
Proof.
  unfold needs_of_extend, eval_extend; intros.
  destruct ext; auto using longofint_sound, longofintu_sound, shllimm_sound.
Qed.

Lemma zero_ext'_sound:
  forall v w x n,
  vagree v w (zero_ext' n x) ->
  vagree (Val.zero_ext n v) (Val.zero_ext n w) x.
Proof.
  unfold zero_ext'; intros. destruct (zle 0 n).
- apply zero_ext_sound; auto.
- assert (E: x = Nothing \/ Val.lessdef v w) by (destruct x; auto).
  destruct E. subst x; simpl; auto. apply vagree_lessdef; apply Val.zero_ext_lessdef; auto.
Qed.

Lemma sign_ext'_sound:
  forall v w x n,
  vagree v w (sign_ext' n x) ->
  vagree (Val.sign_ext n v) (Val.sign_ext n w) x.
Proof.
  unfold sign_ext'; intros. destruct (zlt 0 n).
- apply sign_ext_sound; auto.
- assert (E: x = Nothing \/ Val.lessdef v w) by (destruct x; auto).
  destruct E. subst x; simpl; auto. apply vagree_lessdef; apply Val.sign_ext_lessdef; auto.
Qed.

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
- apply shift_sound; auto.
- apply add_sound; auto.
- apply add_sound; auto using shift_sound.
- apply add_sound; auto with na.
- apply neg_sound; auto.
- apply neg_sound; auto using shift_sound.
- apply sub_sound; auto.
- apply sub_sound; auto using shift_sound.
- apply mul_sound; auto.
- apply add_sound; auto. apply mul_sound; rewrite modarith_idem; auto. 
- apply sub_sound; auto. apply mul_sound; rewrite modarith_idem; auto. 
- apply and_sound; auto.
- apply and_sound; auto using shift_sound.
- apply andimm_sound; auto.
- apply or_sound; auto.
- apply or_sound; auto using shift_sound.
- apply orimm_sound; auto.
- apply xor_sound; auto.
- apply xor_sound; auto using shift_sound.
- apply xor_sound; auto with na.
- apply notint_sound; auto.
- apply notint_sound; auto using shift_sound.
- apply and_sound; auto. apply notint_sound; rewrite bitwise_idem; auto.
- apply and_sound; auto. apply notint_sound; rewrite bitwise_idem; auto using shift_sound.
- apply or_sound; auto. apply notint_sound; rewrite bitwise_idem; auto.
- apply or_sound; auto. apply notint_sound; rewrite bitwise_idem; auto using shift_sound.
- apply xor_sound; auto. apply notint_sound; rewrite bitwise_idem; auto.
- apply xor_sound; auto. apply notint_sound; rewrite bitwise_idem; auto using shift_sound.
- apply zero_ext'_sound; auto.
- apply sign_ext'_sound; auto.
- apply shlimm_sound; apply zero_ext'_sound; auto.
- apply shlimm_sound; apply sign_ext'_sound; auto.
- apply zero_ext'_sound; apply shruimm_sound; auto.
- apply sign_ext'_sound; apply shrimm_sound; auto.
- apply shiftl_sound; auto.
- apply extend_sound; auto.
- apply makelong_sound; auto.
- apply loword_sound; auto.
- apply hiword_sound; auto.
- apply addl_sound; auto.
- apply addl_sound; auto using shiftl_sound.
- apply addl_sound; auto using extend_sound.
- apply addl_sound; auto with na.
- apply negl_sound; auto.
- apply negl_sound; auto using shiftl_sound.
- apply mull_sound; auto.
- apply addl_sound; auto. apply mull_sound; rewrite modarith_idem; auto.
- apply andl_sound; auto.
- apply andl_sound; auto using shiftl_sound.
- apply andlimm_sound; auto.
- apply orl_sound; auto.
- apply orl_sound; auto using shiftl_sound.
- apply orlimm_sound; auto.
- apply xorl_sound; auto.
- apply xorl_sound; auto using shiftl_sound.
- apply xorl_sound; auto with na.
- apply notl_sound; auto.
- apply notl_sound; auto using shiftl_sound.
- apply andl_sound; auto using notl_sound.
- apply andl_sound; auto using notl_sound, shiftl_sound.
- apply orl_sound; auto using notl_sound.
- apply orl_sound; auto using notl_sound, shiftl_sound.
- apply xorl_sound; auto using notl_sound.
- apply xorl_sound; auto using notl_sound, shiftl_sound.
- destruct (eval_condition cond args m) as [b|] eqn:EC.
  erewrite needs_of_condition_sound by eauto.
  apply select_sound; auto.
  simpl; auto with na.
Qed.

Lemma operation_is_redundant_sound:
  forall op nv arg1 args v arg1' args',
  operation_is_redundant op nv = true ->
  eval_operation ge (Vptr sp Ptrofs.zero) op (arg1 :: args) m = Some v ->
  vagree_list (arg1 :: args) (arg1' :: args') (needs_of_operation op nv) ->
  vagree v arg1' nv.
Proof.
  intros. destruct op; simpl in *; try discriminate; inv H1; FuncInv; subst.
- apply andimm_redundant_sound; auto.
- apply orimm_redundant_sound; auto.
- InvBooleans. unfold zero_ext' in H5; rewrite zle_true in H5 by auto. 
  apply zero_ext_redundant_sound; auto.
- InvBooleans. unfold sign_ext' in H5; rewrite zlt_true in H5 by auto. 
  apply sign_ext_redundant_sound; auto.
- apply andlimm_redundant_sound; auto.
- apply orlimm_redundant_sound; auto.
Qed.

End SOUNDNESS.

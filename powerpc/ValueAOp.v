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
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import ValueDomain.
Require Import RTL.

(** Value analysis for PowerPC operators *)

Definition eval_static_condition (cond: condition) (vl: list aval): abool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => cmpu_bool c v1 v2
  | Ccompimm c n, v1 :: nil => cmp_bool c v1 (I n)
  | Ccompuimm c n, v1 :: nil => cmpu_bool c v1 (I n)
  | Ccompf c, v1 :: v2 :: nil => cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => cnot (cmpf_bool c v1 v2)
  | Cmaskzero n, v1 :: nil => maskzero v1 n
  | Cmasknotzero n, v1 :: nil => cnot (maskzero v1 n)
  | Ccompl c, v1 :: v2 :: nil => cmpl_bool c v1 v2
  | Ccomplu c, v1 :: v2 :: nil => cmplu_bool c v1 v2
  | Ccomplimm c n, v1 :: nil => cmpl_bool c v1 (L n)
  | Ccompluimm c n, v1 :: nil => cmplu_bool c v1 (L n)
  | _, _ => Bnone
  end.

Definition eval_static_addressing (addr: addressing) (vl: list aval): aval :=
  match addr, vl with
  | Aindexed n, v1::nil => add v1 (I n)
  | Aindexed2, v1::v2::nil => add v1 v2
  | Aglobal s ofs, nil => Ptr (Gl s ofs)
  | Abased s ofs, v1::nil => add (Ptr (Gl s ofs)) v1
  | Ainstack ofs, nil => Ptr(Stk ofs)
  | _, _ => Vbot
  end.

Definition eval_static_operation (op: operation) (vl: list aval): aval :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Ofloatconst n, nil => if propagate_float_constants tt then F n else ntop
  | Osingleconst n, nil => if propagate_float_constants tt then FS n else ntop
  | Oaddrsymbol id ofs, nil => Ptr (Gl id ofs)
  | Oaddrstack ofs, nil => Ptr (Stk ofs)
  | Ocast8signed, v1 :: nil => sign_ext 8 v1
  | Ocast16signed, v1 :: nil => sign_ext 16 v1
  | Oadd, v1::v2::nil => add v1 v2
  | Oaddimm n, v1::nil => add v1 (I n)
  | Oaddsymbol id ofs, v1::nil => add (Ptr (Gl id ofs)) v1
  | Osub, v1::v2::nil => sub v1 v2
  | Osubimm n, v1::nil => sub (I n) v1
  | Omul, v1::v2::nil => mul v1 v2
  | Omulimm n, v1::nil => mul v1 (I n)
  | Omulhs, v1::v2::nil => mulhs v1 v2
  | Omulhu, v1::v2::nil => mulhu v1 v2
  | Odiv, v1::v2::nil => divs v1 v2
  | Odivu, v1::v2::nil => divu v1 v2
  | Oand, v1::v2::nil => and v1 v2
  | Oandimm n, v1::nil => and v1 (I n)
  | Oor, v1::v2::nil => or v1 v2
  | Oorimm n, v1::nil => or v1 (I n)
  | Oxor, v1::v2::nil => xor v1 v2
  | Oxorimm n, v1::nil => xor v1 (I n)
  | Onot, v1::nil => notint v1
  | Onand, v1::v2::nil => notint(and v1 v2)
  | Onor, v1::v2::nil => notint(or v1 v2)
  | Onxor, v1::v2::nil => notint(xor v1 v2)
  | Oandc, v1::v2::nil => and v1 (notint v2)
  | Oorc, v1::v2::nil => or v1 (notint v2)
  | Oshl, v1::v2::nil => shl v1 v2
  | Oshr, v1::v2::nil => shr v1 v2
  | Oshrimm n, v1::nil => shr v1 (I n)
  | Oshrximm n, v1::nil => shrx v1 (I n)
  | Oshru, v1::v2::nil => shru v1 v2
  | Orolm amount mask, v1::nil => rolm v1 amount mask
  | Oroli amount mask, v1::v2::nil => or (and v1 (I (Int.not mask))) (rolm v2 amount mask)
  | Olongconst n, nil => L n
  | Ocast32signed, v1::nil => longofint v1
  | Ocast32unsigned, v1::nil => longofintu v1
  | Oaddl, v1::v2::nil => addl v1 v2
  | Oaddlimm n, v1::nil => addl v1 (L n)
  | Osubl, v1::v2::nil => subl v1 v2
  | Onegl, v1::nil => negl v1
  | Omull, v1::v2::nil => mull v1 v2
  | Omullhs, v1::v2::nil => mullhs v1 v2
  | Omullhu, v1::v2::nil => mullhu v1 v2
  | Odivl, v1::v2::nil => divls v1 v2
  | Odivlu, v1::v2::nil => divlu v1 v2
  | Oandl, v1::v2::nil => andl v1 v2
  | Oandlimm n, v1::nil => andl v1 (L n)
  | Oorl, v1::v2::nil => orl v1 v2
  | Oorlimm n, v1::nil => orl v1 (L n)
  | Oxorl, v1::v2::nil => xorl v1 v2
  | Oxorlimm n, v1::nil => xorl v1 (L n)
  | Onotl, v1::nil => notl v1
  | Oshll, v1::v2::nil => shll v1 v2
  | Oshrl, v1::v2::nil => shrl v1 v2
  | Oshrlimm n, v1::nil => shrl v1 (I n)
  | Oshrxlimm n, v1::nil => shrxl v1 (I n)
  | Oshrlu, v1::v2::nil => shrlu v1 v2
  | Orolml amount mask, v1::nil => rolml v1 amount mask
  | Olongoffloat, v1::nil => longoffloat v1
  | Ofloatoflong, v1::nil => floatoflong v1
  | Onegf, v1::nil => negf v1
  | Oabsf, v1::nil => absf v1
  | Oaddf, v1::v2::nil => addf v1 v2
  | Osubf, v1::v2::nil => subf v1 v2
  | Omulf, v1::v2::nil => mulf v1 v2
  | Odivf, v1::v2::nil => divf v1 v2
  | Onegfs, v1::nil => negfs v1
  | Oabsfs, v1::nil => absfs v1
  | Oaddfs, v1::v2::nil => addfs v1 v2
  | Osubfs, v1::v2::nil => subfs v1 v2
  | Omulfs, v1::v2::nil => mulfs v1 v2
  | Odivfs, v1::v2::nil => divfs v1 v2
  | Osingleoffloat, v1::nil => singleoffloat v1
  | Ofloatofsingle, v1::nil => floatofsingle v1
  | Ointoffloat, v1::nil => intoffloat v1
  | Ointuoffloat, v1::nil => intuoffloat v1
  | Ofloatofint, v1::nil => floatofint v1
  | Ofloatofintu, v1::nil => floatofintu v1
  | Ofloatofwords, v1::v2::nil => floatofwords v1 v2
  | Omakelong, v1::v2::nil => longofwords v1 v2
  | Olowlong, v1::nil => loword v1
  | Ohighlong, v1::nil => hiword v1
  | Ocmp c, _ => of_optbool (eval_static_condition c vl)
  | _, _ => Vbot
  end.

Section SOUNDNESS.

Variable bc: block_classification.
Variable ge: genv.
Hypothesis GENV: genv_match bc ge.
Variable sp: block.
Hypothesis STACK: bc sp = BCstack.

Theorem eval_static_condition_sound:
  forall cond vargs m aargs,
  list_forall2 (vmatch bc) vargs aargs ->
  cmatch (eval_condition cond vargs m) (eval_static_condition cond aargs).
Proof.
  intros until aargs; intros VM.
  inv VM.
  destruct cond; auto with va.
  inv H0.
  destruct cond; simpl; eauto with va.
  inv H2.
  destruct cond; simpl; eauto with va.
  destruct cond; auto with va.
Qed.

Lemma symbol_address_sound:
  forall id ofs,
  vmatch bc (Genv.symbol_address ge id ofs) (Ptr (Gl id ofs)).
Proof.
  intros; apply symbol_address_sound; apply GENV.
Qed.

Hint Resolve symbol_address_sound: va.

Ltac InvHyps :=
  match goal with
  | [H: None = Some _ |- _ ] => discriminate
  | [H: Some _ = Some _ |- _] => inv H
  | [H1: match ?vl with nil => _ | _ :: _ => _ end = Some _ ,
     H2: list_forall2 _ ?vl _ |- _ ] => inv H2; InvHyps
  | _ => idtac
  end.

Theorem eval_static_addressing_sound:
  forall addr vargs vres aargs,
  eval_addressing ge (Vptr sp Ptrofs.zero) addr vargs = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_addressing addr aargs).
Proof.
  unfold eval_addressing, eval_static_addressing; intros;
  destruct addr; InvHyps; eauto with va.
  rewrite Ptrofs.add_zero_l; auto with va.
Qed.

Theorem eval_static_operation_sound:
  forall op vargs m vres aargs,
  eval_operation ge (Vptr sp Ptrofs.zero) op vargs m = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_operation op aargs).
Proof.
  unfold eval_operation, eval_static_operation; intros;
  destruct op; InvHyps; eauto with va.
  destruct (propagate_float_constants tt); constructor.
  destruct (propagate_float_constants tt); constructor.
  rewrite Ptrofs.add_zero_l; eauto with va.
  fold (Val.sub (Vint i) a1). auto with va.
  apply rolml_sound; auto.
  apply floatofwords_sound; auto.
  apply of_optbool_sound. eapply eval_static_condition_sound; eauto.
Qed.

End SOUNDNESS.

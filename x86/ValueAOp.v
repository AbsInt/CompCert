(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                Xavier Leroy, INRIA Paris                            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Compopts.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Op RTL ValueDomain.

(** Value analysis for x86_64 operators *)

Definition eval_static_condition (cond: condition) (vl: list aval): abool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => cmpu_bool c v1 v2
  | Ccompimm c n, v1 :: nil => cmp_bool c v1 (I n)
  | Ccompuimm c n, v1 :: nil => cmpu_bool c v1 (I n)
  | Ccompl c, v1 :: v2 :: nil => cmpl_bool c v1 v2
  | Ccomplu c, v1 :: v2 :: nil => cmplu_bool c v1 v2
  | Ccomplimm c n, v1 :: nil => cmpl_bool c v1 (L n)
  | Ccompluimm c n, v1 :: nil => cmplu_bool c v1 (L n)
  | Ccompf c, v1 :: v2 :: nil => cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => cnot (cmpf_bool c v1 v2)
  | Ccompfs c, v1 :: v2 :: nil => cmpfs_bool c v1 v2
  | Cnotcompfs c, v1 :: v2 :: nil => cnot (cmpfs_bool c v1 v2)
  | Cmaskzero n, v1 :: nil => maskzero v1 n
  | Cmasknotzero n, v1 :: nil => cnot (maskzero v1 n)
  | _, _ => Bnone
  end.

Definition eval_static_addressing_32 (addr: addressing) (vl: list aval): aval :=
  match addr, vl with
  | Aindexed n, v1::nil => add v1 (I (Int.repr n))
  | Aindexed2 n, v1::v2::nil => add (add v1 v2) (I (Int.repr n))
  | Ascaled sc ofs, v1::nil => add (mul v1 (I (Int.repr sc))) (I (Int.repr ofs))
  | Aindexed2scaled sc ofs, v1::v2::nil => add v1 (add (mul v2 (I (Int.repr sc))) (I (Int.repr ofs)))
  | Aglobal s ofs, nil => Ptr (Gl s ofs)
  | Abased s ofs, v1::nil => add (Ptr (Gl s ofs)) v1
  | Abasedscaled sc s ofs, v1::nil => add (Ptr (Gl s ofs)) (mul v1 (I (Int.repr sc)))
  | Ainstack ofs, nil => Ptr(Stk ofs)
  | _, _ => Vbot
  end.

Definition eval_static_addressing_64 (addr: addressing) (vl: list aval): aval :=
  match addr, vl with
  | Aindexed n, v1::nil => addl v1 (L (Int64.repr n))
  | Aindexed2 n, v1::v2::nil => addl (addl v1 v2) (L (Int64.repr n))
  | Ascaled sc ofs, v1::nil => addl (mull v1 (L (Int64.repr sc))) (L (Int64.repr ofs))
  | Aindexed2scaled sc ofs, v1::v2::nil => addl v1 (addl (mull v2 (L (Int64.repr sc))) (L (Int64.repr ofs)))
  | Aglobal s ofs, nil => Ptr (Gl s ofs)
  | Abased s ofs, v1::nil => addl (Ptr (Gl s ofs)) v1
  | Abasedscaled sc s ofs, v1::nil => addl (Ptr (Gl s ofs)) (mull v1 (L (Int64.repr sc)))
  | Ainstack ofs, nil => Ptr(Stk ofs)
  | _, _ => Vbot
  end.

Definition eval_static_addressing (addr: addressing) (vl: list aval): aval :=
  if Archi.ptr64
  then eval_static_addressing_64 addr vl
  else eval_static_addressing_32 addr vl.

Definition eval_static_operation (op: operation) (vl: list aval): aval :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Olongconst n, nil => L n
  | Ofloatconst n, nil => if propagate_float_constants tt then F n else ntop
  | Osingleconst n, nil => if propagate_float_constants tt then FS n else ntop
  | Oindirectsymbol id, nil => Ifptr (Gl id Ptrofs.zero)
  | Ocast8signed, v1 :: nil => sign_ext 8 v1
  | Ocast8unsigned, v1 :: nil => zero_ext 8 v1
  | Ocast16signed, v1 :: nil => sign_ext 16 v1
  | Ocast16unsigned, v1 :: nil => zero_ext 16 v1
  | Oneg, v1::nil => neg v1
  | Osub, v1::v2::nil => sub v1 v2
  | Omul, v1::v2::nil => mul v1 v2
  | Omulimm n, v1::nil => mul v1 (I n)
  | Omulhs, v1::v2::nil => mulhs v1 v2
  | Omulhu, v1::v2::nil => mulhu v1 v2
  | Odiv, v1::v2::nil => divs v1 v2
  | Odivu, v1::v2::nil => divu v1 v2
  | Omod, v1::v2::nil => mods v1 v2
  | Omodu, v1::v2::nil => modu v1 v2
  | Oand, v1::v2::nil => and v1 v2
  | Oandimm n, v1::nil => and v1 (I n)
  | Oor, v1::v2::nil => or v1 v2
  | Oorimm n, v1::nil => or v1 (I n)
  | Oxor, v1::v2::nil => xor v1 v2
  | Oxorimm n, v1::nil => xor v1 (I n)
  | Onot, v1::nil => notint v1
  | Oshl, v1::v2::nil => shl v1 v2
  | Oshlimm n, v1::nil => shl v1 (I n)
  | Oshr, v1::v2::nil => shr v1 v2
  | Oshrimm n, v1::nil => shr v1 (I n)
  | Oshrximm n, v1::nil => shrx v1 (I n)
  | Oshru, v1::v2::nil => shru v1 v2
  | Oshruimm n, v1::nil => shru v1 (I n)
  | Ororimm n, v1::nil => ror v1 (I n)
  | Oshldimm n, v1::v2::nil => or (shl v1 (I n)) (shru v2 (I (Int.sub Int.iwordsize n)))
  | Olea addr, _ => eval_static_addressing_32 addr vl
  | Omakelong, v1::v2::nil => longofwords v1 v2
  | Olowlong, v1::nil => loword v1
  | Ohighlong, v1::nil => hiword v1
  | Ocast32signed, v1::nil => longofint v1
  | Ocast32unsigned, v1::nil => longofintu v1
  | Onegl, v1::nil => negl v1
  | Oaddlimm n, v1::nil => addl v1 (L n)
  | Osubl, v1::v2::nil => subl v1 v2
  | Omull, v1::v2::nil => mull v1 v2
  | Omullimm n, v1::nil => mull v1 (L n)
  | Omullhs, v1::v2::nil => mullhs v1 v2
  | Omullhu, v1::v2::nil => mullhu v1 v2
  | Odivl, v1::v2::nil => divls v1 v2
  | Odivlu, v1::v2::nil => divlu v1 v2
  | Omodl, v1::v2::nil => modls v1 v2
  | Omodlu, v1::v2::nil => modlu v1 v2
  | Oandl, v1::v2::nil => andl v1 v2
  | Oandlimm n, v1::nil => andl v1 (L n)
  | Oorl, v1::v2::nil => orl v1 v2
  | Oorlimm n, v1::nil => orl v1 (L n)
  | Oxorl, v1::v2::nil => xorl v1 v2
  | Oxorlimm n, v1::nil => xorl v1 (L n)
  | Onotl, v1::nil => notl v1
  | Oshll, v1::v2::nil => shll v1 v2
  | Oshllimm n, v1::nil => shll v1 (I n)
  | Oshrl, v1::v2::nil => shrl v1 v2
  | Oshrlimm n, v1::nil => shrl v1 (I n)
  | Oshrxlimm n, v1::nil => shrxl v1 (I n)
  | Oshrlu, v1::v2::nil => shrlu v1 v2
  | Oshrluimm n, v1::nil => shrlu v1 (I n)
  | Ororlimm n, v1::nil => rorl v1 (I n)
  | Oleal addr, _ => eval_static_addressing_64 addr vl
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
  | Ofloatofint, v1::nil => floatofint v1
  | Ointofsingle, v1::nil => intofsingle v1
  | Osingleofint, v1::nil => singleofint v1
  | Olongoffloat, v1::nil => longoffloat v1
  | Ofloatoflong, v1::nil => floatoflong v1
  | Olongofsingle, v1::nil => longofsingle v1
  | Osingleoflong, v1::nil => singleoflong v1
  | Ocmp c, _ => of_optbool (eval_static_condition c vl)
  | Osel c ty, v1::v2::vl => select (eval_static_condition c vl) v1 v2
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
  intros until aargs; intros VM. inv VM.
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

Lemma symbol_address_sound_2:
  forall id ofs,
  vmatch bc (Genv.symbol_address ge id ofs) (Ifptr (Gl id ofs)).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:F.
  constructor. constructor. apply GENV; auto.
  constructor.
Qed.

Hint Resolve symbol_address_sound symbol_address_sound_2: va.

Ltac InvHyps :=
  match goal with
  | [H: None = Some _ |- _ ] => discriminate
  | [H: Some _ = Some _ |- _] => inv H
  | [H1: match ?vl with nil => _ | _ :: _ => _ end = Some _ ,
     H2: list_forall2 _ ?vl _ |- _ ] => inv H2; InvHyps
  | [H: (if Archi.ptr64 then _ else _) = Some _ |- _] => destruct Archi.ptr64 eqn:?; InvHyps
  | _ => idtac
  end.

Theorem eval_static_addressing_32_sound:
  forall addr vargs vres aargs,
  eval_addressing32 ge (Vptr sp Ptrofs.zero) addr vargs = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_addressing_32 addr aargs).
Proof.
  unfold eval_addressing32, eval_static_addressing_32; intros;
  destruct addr; InvHyps; eauto with va.
  rewrite Ptrofs.add_zero_l; eauto with va.
Qed.

Theorem eval_static_addressing_64_sound:
  forall addr vargs vres aargs,
  eval_addressing64 ge (Vptr sp Ptrofs.zero) addr vargs = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_addressing_64 addr aargs).
Proof.
  unfold eval_addressing64, eval_static_addressing_64; intros;
  destruct addr; InvHyps; eauto with va.
  rewrite Ptrofs.add_zero_l; eauto with va.
Qed.

Theorem eval_static_addressing_sound:
  forall addr vargs vres aargs,
  eval_addressing ge (Vptr sp Ptrofs.zero) addr vargs = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_addressing addr aargs).
Proof.
  unfold eval_addressing, eval_static_addressing; intros.
  destruct Archi.ptr64; eauto using eval_static_addressing_32_sound, eval_static_addressing_64_sound.
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
  eapply eval_static_addressing_32_sound; eauto.
  eapply eval_static_addressing_64_sound; eauto.
  apply of_optbool_sound. eapply eval_static_condition_sound; eauto.
  apply select_sound; auto. eapply eval_static_condition_sound; eauto.
Qed.

End SOUNDNESS.


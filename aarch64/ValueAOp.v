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

Require Import Coqlib Compopts.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Op RTL ValueDomain.

(** Value analysis for AArch64 operators *)

Definition eval_static_shift (s: shift) (v: aval) (n: amount32) : aval :=
  match s with
  | Slsl => shl v (I n)
  | Slsr => shru v (I n)
  | Sasr => shr v (I n)
  | Sror => ror v (I n)
  end.

Definition eval_static_shiftl (s: shift) (v: aval) (n: amount64) : aval :=
  match s with
  | Slsl => shll v (I n)
  | Slsr => shrlu v (I n)
  | Sasr => shrl v (I n)
  | Sror => rorl v (I n)
  end.

Definition eval_static_extend (x: extension) (v: aval) (n: amount64) : aval :=
  shll (match x with Xsgn32 => longofint v | Xuns32 => longofintu v end) (I n).

Definition eval_static_condition (cond: condition) (vl: list aval): abool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => cmpu_bool c v1 v2
  | Ccompimm c n, v1 :: nil => cmp_bool c v1 (I n)
  | Ccompuimm c n, v1 :: nil => cmpu_bool c v1 (I n)
  | Ccompshift c s a, v1 :: v2 :: nil => cmp_bool c v1 (eval_static_shift s v2 a)
  | Ccompushift c s a, v1 :: v2 :: nil => cmpu_bool c v1 (eval_static_shift s v2 a)
  | Cmaskzero m, v1 :: nil => maskzero v1 m
  | Cmasknotzero m, v1 :: nil => cnot (maskzero v1 m)
  | Ccompl c, v1 :: v2 :: nil => cmpl_bool c v1 v2
  | Ccomplu c, v1 :: v2 :: nil => cmplu_bool c v1 v2
  | Ccomplimm c n, v1 :: nil => cmpl_bool c v1 (L n)
  | Ccompluimm c n, v1 :: nil => cmplu_bool c v1 (L n)
  | Ccomplshift c s a, v1 :: v2 :: nil => cmpl_bool c v1 (eval_static_shiftl s v2 a)
  | Ccomplushift c s a, v1 :: v2 :: nil => cmplu_bool c v1 (eval_static_shiftl s v2 a)
  | Cmasklzero m, v1 :: nil => cmpl_bool Ceq (andl v1 (L m)) (L Int64.zero)
  | Cmasklnotzero m, v1 :: nil => cmpl_bool Cne (andl v1 (L m)) (L Int64.zero)
  | Ccompf c, v1 :: v2 :: nil => cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => cnot (cmpf_bool c v1 v2)
  | Ccompfzero c, v1 :: nil => cmpf_bool c v1 (F Float.zero)
  | Cnotcompfzero c, v1 :: nil => cnot (cmpf_bool c v1 (F Float.zero))
  | Ccompfs c, v1 :: v2 :: nil => cmpfs_bool c v1 v2
  | Cnotcompfs c, v1 :: v2 :: nil => cnot (cmpfs_bool c v1 v2)
  | Ccompfszero c, v1 :: nil => cmpfs_bool c v1 (FS Float32.zero)
  | Cnotcompfszero c, v1 :: nil => cnot (cmpfs_bool c v1 (FS Float32.zero))
  | _, _ => Bnone
  end.

Definition eval_static_addressing (addr: addressing) (vl: list aval): aval :=
  match addr, vl with
  | Aindexed n, v1 :: nil => addl v1 (L n)
  | Aindexed2, v1 :: v2 :: nil => addl v1 v2
  | Aindexed2shift a, v1 :: v2 :: nil => addl v1 (shll v2 (I a))
  | Aindexed2ext x a, v1 :: v2 :: nil => addl v1 (eval_static_extend x v2 a)
  | Aglobal s ofs, nil => Ptr (Gl s ofs)
  | Ainstack ofs, nil => Ptr (Stk ofs)
  | _, _ => Vbot
  end.

Definition eval_static_operation (op: operation) (vl: list aval): aval :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => I n
  | Olongconst n, nil => L n
  | Ofloatconst n, nil => if propagate_float_constants tt then F n else ntop
  | Osingleconst n, nil => if propagate_float_constants tt then FS n else ntop
  | Oaddrsymbol id ofs, nil => Ptr (Gl id ofs)
  | Oaddrstack ofs, nil => Ptr (Stk ofs)

  | Oshift s a, v1::nil => eval_static_shift s v1 a  
  | Oadd, v1::v2::nil => add v1 v2
  | Oaddshift s a, v1::v2::nil => add v1 (eval_static_shift s v2 a)
  | Oaddimm n, v1::nil => add v1 (I n)
  | Oneg, v1::nil => neg v1
  | Onegshift s a, v1::nil => neg (eval_static_shift s v1 a)
  | Osub, v1::v2::nil => sub v1 v2
  | Osubshift s a, v1::v2::nil => sub v1 (eval_static_shift s v2 a)
  | Omul, v1::v2::nil => mul v1 v2
  | Omuladd, v1::v2::v3::nil => add v1 (mul v2 v3)
  | Omulsub, v1::v2::v3::nil => sub v1 (mul v2 v3)
  | Odiv, v1::v2::nil => divs v1 v2
  | Odivu, v1::v2::nil => divu v1 v2
  | Oand, v1::v2::nil => and v1 v2
  | Oandshift s a, v1::v2::nil => and v1 (eval_static_shift s v2 a)
  | Oandimm n, v1::nil => and v1 (I n)
  | Oor, v1::v2::nil => or v1 v2
  | Oorshift s a, v1::v2::nil => or v1 (eval_static_shift s v2 a)
  | Oorimm n, v1::nil => or v1 (I n)
  | Oxor, v1::v2::nil => xor v1 v2
  | Oxorshift s a, v1::v2::nil => xor v1 (eval_static_shift s v2 a)
  | Oxorimm n, v1::nil => xor v1 (I n)
  | Onot, v1::nil => notint v1
  | Onotshift s a, v1::nil => notint (eval_static_shift s v1 a)
  | Obic, v1::v2::nil => and v1 (notint v2)
  | Obicshift s a, v1::v2::nil => and v1 (notint (eval_static_shift s v2 a))
  | Oorn, v1::v2::nil => or v1 (notint v2)
  | Oornshift s a, v1::v2::nil => or v1 (notint (eval_static_shift s v2 a))
  | Oeqv, v1::v2::nil => xor v1 (notint v2)
  | Oeqvshift s a, v1::v2::nil => xor v1 (notint (eval_static_shift s v2 a))
  | Oshl, v1::v2::nil => shl v1 v2
  | Oshr, v1::v2::nil => shr v1 v2
  | Oshru, v1::v2::nil => shru v1 v2
  | Oshrximm n, v1::nil => shrx v1 (I n)
  | Ozext s, v1::nil => zero_ext s v1
  | Osext s, v1::nil => sign_ext s v1
  | Oshlzext s a, v1::nil => shl (zero_ext s v1) (I a)
  | Oshlsext s a, v1::nil => shl (sign_ext s v1) (I a)
  | Ozextshr a s, v1::nil => zero_ext s (shru v1 (I a))
  | Osextshr a s, v1::nil => sign_ext s (shr v1 (I a))

  | Oshiftl s a, v1::nil => eval_static_shiftl s v1 a  
  | Oextend x a, v1::nil => eval_static_extend x v1 a
  | Omakelong, v1::v2::nil => longofwords v1 v2
  | Olowlong, v1::nil => loword v1
  | Ohighlong, v1::nil => hiword v1
  | Oaddl, v1::v2::nil => addl v1 v2
  | Oaddlshift s a, v1::v2::nil => addl v1 (eval_static_shiftl s v2 a)
  | Oaddlext x a, v1::v2::nil => addl v1 (eval_static_extend x v2 a)
  | Oaddlimm n, v1::nil => addl v1 (L n)
  | Onegl, v1::nil => negl v1
  | Oneglshift s a, v1::nil => negl (eval_static_shiftl s v1 a)
  | Osubl, v1::v2::nil => subl v1 v2
  | Osublshift s a, v1::v2::nil => subl v1 (eval_static_shiftl s v2 a)
  | Osublext x a, v1::v2::nil => subl v1 (eval_static_extend x v2 a)
  | Omull, v1::v2::nil => mull v1 v2
  | Omulladd, v1::v2::v3::nil => addl v1 (mull v2 v3)
  | Omullsub, v1::v2::v3::nil => subl v1 (mull v2 v3)
  | Omullhs, v1::v2::nil => mullhs v1 v2
  | Omullhu, v1::v2::nil => mullhu v1 v2
  | Odivl, v1::v2::nil => divls v1 v2
  | Odivlu, v1::v2::nil => divlu v1 v2
  | Oandl, v1::v2::nil => andl v1 v2
  | Oandlshift s a, v1::v2::nil => andl v1 (eval_static_shiftl s v2 a)
  | Oandlimm n, v1::nil => andl v1 (L n)
  | Oorl, v1::v2::nil => orl v1 v2
  | Oorlshift s a, v1::v2::nil => orl v1 (eval_static_shiftl s v2 a)
  | Oorlimm n, v1::nil => orl v1 (L n)
  | Oxorl, v1::v2::nil => xorl v1 v2
  | Oxorlshift s a, v1::v2::nil => xorl v1 (eval_static_shiftl s v2 a)
  | Oxorlimm n, v1::nil => xorl v1 (L n)
  | Onotl, v1::nil => notl v1
  | Onotlshift s a, v1::nil => notl (eval_static_shiftl s v1 a)
  | Obicl, v1::v2::nil => andl v1 (notl v2)
  | Obiclshift s a, v1::v2::nil => andl v1 (notl (eval_static_shiftl s v2 a))
  | Oornl, v1::v2::nil => orl v1 (notl v2)
  | Oornlshift s a, v1::v2::nil => orl v1 (notl (eval_static_shiftl s v2 a))
  | Oeqvl, v1::v2::nil => xorl v1 (notl v2)
  | Oeqvlshift s a, v1::v2::nil => xorl v1 (notl (eval_static_shiftl s v2 a))
  | Oshll, v1::v2::nil => shll v1 v2
  | Oshrl, v1::v2::nil => shrl v1 v2
  | Oshrlu, v1::v2::nil => shrlu v1 v2
  | Oshrlximm n, v1::nil => shrxl v1 (I n)
  | Ozextl s, v1::nil => zero_ext_l s v1
  | Osextl s, v1::nil => sign_ext_l s v1
  | Oshllzext s a, v1::nil => shll (zero_ext_l s v1) (I a)
  | Oshllsext s a, v1::nil => shll (sign_ext_l s v1) (I a)
  | Ozextshrl a s, v1::nil => zero_ext_l s (shrlu v1 (I a))
  | Osextshrl a s, v1::nil => sign_ext_l s (shrl v1 (I a))

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
  | Ointofsingle, v1::nil => intofsingle v1
  | Ointuofsingle, v1::nil => intuofsingle v1
  | Osingleofint, v1::nil => singleofint v1
  | Osingleofintu, v1::nil => singleofintu v1
  | Olongoffloat, v1::nil => longoffloat v1
  | Olonguoffloat, v1::nil => longuoffloat v1
  | Ofloatoflong, v1::nil => floatoflong v1
  | Ofloatoflongu, v1::nil => floatoflongu v1
  | Olongofsingle, v1::nil => longofsingle v1
  | Olonguofsingle, v1::nil => longuofsingle v1
  | Osingleoflong, v1::nil => singleoflong v1
  | Osingleoflongu, v1::nil => singleoflongu v1

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

Ltac InvHyps :=
  match goal with
  | [H: None = Some _ |- _ ] => discriminate
  | [H: Some _ = Some _ |- _] => inv H
  | [H1: match ?vl with nil => _ | _ :: _ => _ end = Some _ ,
     H2: list_forall2 _ ?vl _ |- _ ] => inv H2; InvHyps
  | _ => idtac
  end.

Lemma eval_static_shift_sound: forall v av s n,
  vmatch bc v av -> vmatch bc (eval_shift s v n) (eval_static_shift s av n).
Proof.
  intros. unfold eval_shift, eval_static_shift; destruct s; auto with va.
Qed.

Lemma eval_static_shiftl_sound: forall v av s n,
  vmatch bc v av -> vmatch bc (eval_shiftl s v n) (eval_static_shiftl s av n).
Proof.
  intros. unfold eval_shiftl, eval_static_shiftl; destruct s; auto with va.
Qed.

Lemma eval_static_extend_sound: forall v av x n,
  vmatch bc v av -> vmatch bc (eval_extend x v n) (eval_static_extend x av n).
Proof.
  intros. unfold eval_extend, eval_static_extend; destruct x; auto with va.
Qed.

Hint Resolve eval_static_shift_sound eval_static_shiftl_sound eval_static_extend_sound: va.

Theorem eval_static_condition_sound:
  forall cond vargs m aargs,
  list_forall2 (vmatch bc) vargs aargs ->
  cmatch (eval_condition cond vargs m) (eval_static_condition cond aargs).
Proof.
  intros until aargs; intros VM. inv VM.
  destruct cond; auto with va.
  inv H0.
  destruct cond; simpl; eauto with va.
  replace (Val.cmp_bool Ceq (Val.and a1 (Vint n)) (Vint Int.zero))
     with (Val.maskzero_bool a1 n) by (destruct a1; auto).
  eauto with va.
  replace (Val.cmp_bool Cne (Val.and a1 (Vint n)) (Vint Int.zero))
     with (option_map negb (Val.maskzero_bool a1 n)) by (destruct a1; auto).
  eauto with va.
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

Theorem eval_static_addressing_sound:
  forall addr vargs vres aargs,
  eval_addressing ge (Vptr sp Ptrofs.zero) addr vargs = Some vres ->
  list_forall2 (vmatch bc) vargs aargs ->
  vmatch bc vres (eval_static_addressing addr aargs).
Proof.
  unfold eval_addressing, eval_static_addressing; intros;
  destruct addr; InvHyps; eauto with va.
  rewrite Ptrofs.add_zero_l; eauto with va.
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
  apply of_optbool_sound. eapply eval_static_condition_sound; eauto.
  apply select_sound; eauto using eval_static_condition_sound.
Qed.

End SOUNDNESS.


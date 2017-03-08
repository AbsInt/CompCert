(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010-2013 Sylvie Boldo
#<br />#
Copyright (C) 2010-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Basic properties of floating-point formats: lemmas about mantissa, exponent... *)
Require Import Fcore_Raux.
Require Import Fcore_defs.

Section Float_prop.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Theorem Rcompare_F2R :
  forall e m1 m2 : Z,
  Rcompare (F2R (Float beta m1 e)) (F2R (Float beta m2 e)) = Zcompare m1 m2.
Proof.
intros e m1 m2.
unfold F2R. simpl.
rewrite Rcompare_mult_r.
apply Rcompare_Z2R.
apply bpow_gt_0.
Qed.

(** Basic facts *)
Theorem F2R_le_reg :
  forall e m1 m2 : Z,
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R ->
  (m1 <= m2)%Z.
Proof.
intros e m1 m2 H.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow e).
apply bpow_gt_0.
exact H.
Qed.

Theorem F2R_le_compat :
  forall m1 m2 e : Z,
  (m1 <= m2)%Z ->
  (F2R (Float beta m1 e) <= F2R (Float beta m2 e))%R.
Proof.
intros m1 m2 e H.
unfold F2R. simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply Z2R_le.
Qed.

Theorem F2R_lt_reg :
  forall e m1 m2 : Z,
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R ->
  (m1 < m2)%Z.
Proof.
intros e m1 m2 H.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow e).
apply bpow_gt_0.
exact H.
Qed.

Theorem F2R_lt_compat :
  forall e m1 m2 : Z,
  (m1 < m2)%Z ->
  (F2R (Float beta m1 e) < F2R (Float beta m2 e))%R.
Proof.
intros e m1 m2 H.
unfold F2R. simpl.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
now apply Z2R_lt.
Qed.

Theorem F2R_eq_compat :
  forall e m1 m2 : Z,
  (m1 = m2)%Z ->
  (F2R (Float beta m1 e) = F2R (Float beta m2 e))%R.
Proof.
intros e m1 m2 H.
now apply (f_equal (fun m => F2R (Float beta m e))).
Qed.

Theorem F2R_eq_reg :
  forall e m1 m2 : Z,
  F2R (Float beta m1 e) = F2R (Float beta m2 e) ->
  m1 = m2.
Proof.
intros e m1 m2 H.
apply Zle_antisym ;
  apply F2R_le_reg with e ;
  rewrite H ;
  apply Rle_refl.
Qed.

Theorem F2R_Zabs:
  forall m e : Z,
   F2R (Float beta (Zabs m) e) = Rabs (F2R (Float beta m e)).
Proof.
intros m e.
unfold F2R.
rewrite Rabs_mult.
rewrite <- Z2R_abs.
simpl.
apply f_equal.
apply sym_eq; apply Rabs_right.
apply Rle_ge.
apply bpow_ge_0.
Qed.

Theorem F2R_Zopp :
  forall m e : Z,
  F2R (Float beta (Zopp m) e) = Ropp (F2R (Float beta m e)).
Proof.
intros m e.
unfold F2R. simpl.
rewrite <- Ropp_mult_distr_l_reverse.
now rewrite Z2R_opp.
Qed.

(** Sign facts *)
Theorem F2R_0 :
  forall e : Z,
  F2R (Float beta 0 e) = 0%R.
Proof.
intros e.
unfold F2R. simpl.
apply Rmult_0_l.
Qed.

Theorem F2R_eq_0_reg :
  forall m e : Z,
  F2R (Float beta m e) = 0%R ->
  m = Z0.
Proof.
intros m e H.
apply F2R_eq_reg with e.
now rewrite F2R_0.
Qed.

Theorem F2R_ge_0_reg :
  forall m e : Z,
  (0 <= F2R (Float beta m e))%R ->
  (0 <= m)%Z.
Proof.
intros m e H.
apply F2R_le_reg with e.
now rewrite F2R_0.
Qed.

Theorem F2R_le_0_reg :
  forall m e : Z,
  (F2R (Float beta m e) <= 0)%R ->
  (m <= 0)%Z.
Proof.
intros m e H.
apply F2R_le_reg with e.
now rewrite F2R_0.
Qed.

Theorem F2R_gt_0_reg :
  forall m e : Z,
  (0 < F2R (Float beta m e))%R ->
  (0 < m)%Z.
Proof.
intros m e H.
apply F2R_lt_reg with e.
now rewrite F2R_0.
Qed.

Theorem F2R_lt_0_reg :
  forall m e : Z,
  (F2R (Float beta m e) < 0)%R ->
  (m < 0)%Z.
Proof.
intros m e H.
apply F2R_lt_reg with e.
now rewrite F2R_0.
Qed.

Theorem F2R_ge_0_compat :
  forall f : float beta,
  (0 <= Fnum f)%Z ->
  (0 <= F2R f)%R.
Proof.
intros f H.
rewrite <- F2R_0 with (Fexp f).
now apply F2R_le_compat.
Qed.

Theorem F2R_le_0_compat :
  forall f : float beta,
  (Fnum f <= 0)%Z ->
  (F2R f <= 0)%R.
Proof.
intros f H.
rewrite <- F2R_0 with (Fexp f).
now apply F2R_le_compat.
Qed.

Theorem F2R_gt_0_compat :
  forall f : float beta,
  (0 < Fnum f)%Z ->
  (0 < F2R f)%R.
Proof.
intros f H.
rewrite <- F2R_0 with (Fexp f).
now apply F2R_lt_compat.
Qed.

Theorem F2R_lt_0_compat :
  forall f : float beta,
  (Fnum f < 0)%Z ->
  (F2R f < 0)%R.
Proof.
intros f H.
rewrite <- F2R_0 with (Fexp f).
now apply F2R_lt_compat.
Qed.

Theorem F2R_neq_0_compat :
 forall f : float beta,
  (Fnum f <> 0)%Z ->
  (F2R f <> 0)%R.
Proof.
intros f H H1.
apply H.
now apply F2R_eq_0_reg with (Fexp f).
Qed.


Lemma Fnum_ge_0_compat: forall (f : float beta),
  (0 <= F2R f)%R -> (0 <= Fnum f)%Z.
Proof.
intros f H.
case (Zle_or_lt 0 (Fnum f)); trivial.
intros H1; contradict H.
apply Rlt_not_le.
now apply F2R_lt_0_compat.
Qed.

Lemma Fnum_le_0_compat: forall (f : float beta),
  (F2R f <= 0)%R -> (Fnum f <= 0)%Z.
Proof.
intros f H.
case (Zle_or_lt (Fnum f) 0); trivial.
intros H1; contradict H.
apply Rlt_not_le.
now apply F2R_gt_0_compat.
Qed.

(** Floats and bpow *)
Theorem F2R_bpow :
  forall e : Z,
  F2R (Float beta 1 e) = bpow e.
Proof.
intros e.
unfold F2R. simpl.
apply Rmult_1_l.
Qed.

Theorem bpow_le_F2R :
  forall m e : Z,
  (0 < m)%Z ->
  (bpow e <= F2R (Float beta m e))%R.
Proof.
intros m e H.
rewrite <- F2R_bpow.
apply F2R_le_compat.
now apply (Zlt_le_succ 0).
Qed.

Theorem F2R_p1_le_bpow :
  forall m e1 e2 : Z,
  (0 < m)%Z ->
  (F2R (Float beta m e1) < bpow e2)%R ->
  (F2R (Float beta (m + 1) e1) <= bpow e2)%R.
Proof.
intros m e1 e2 Hm.
intros H.
assert (He : (e1 <= e2)%Z).
(* . *)
apply (le_bpow beta).
apply Rle_trans with (F2R (Float beta m e1)).
unfold F2R. simpl.
rewrite <- (Rmult_1_l (bpow e1)) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply (Z2R_le 1).
now apply (Zlt_le_succ 0).
now apply Rlt_le.
(* . *)
revert H.
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite bpow_plus.
unfold F2R. simpl.
rewrite <- (Z2R_Zpower beta (e2 - e1)).
intros H.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_lt_reg_r in H.
apply Z2R_le.
apply Zlt_le_succ.
now apply lt_Z2R.
apply bpow_gt_0.
now apply Zle_minus_le_0.
Qed.

Theorem bpow_le_F2R_m1 :
  forall m e1 e2 : Z,
  (1 < m)%Z ->
  (bpow e2 < F2R (Float beta m e1))%R ->
  (bpow e2 <= F2R (Float beta (m - 1) e1))%R.
Proof.
intros m e1 e2 Hm.
case (Zle_or_lt e1 e2); intros He.
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite bpow_plus.
unfold F2R. simpl.
rewrite <- (Z2R_Zpower beta (e2 - e1)).
intros H.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_lt_reg_r in H.
apply Z2R_le.
rewrite (Zpred_succ (Zpower _ _)).
apply Zplus_le_compat_r.
apply Zlt_le_succ.
now apply lt_Z2R.
apply bpow_gt_0.
now apply Zle_minus_le_0.
intros H.
apply Rle_trans with (1*bpow e1)%R.
rewrite Rmult_1_l.
apply bpow_le.
now apply Zlt_le_weak.
unfold F2R. simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 1%R with (Z2R 1) by reflexivity.
apply Z2R_le.
omega.
Qed.

Theorem F2R_lt_bpow :
  forall f : float beta, forall e',
  (Zabs (Fnum f) < Zpower beta (e' - Fexp f))%Z ->
  (Rabs (F2R f) < bpow e')%R.
Proof.
intros (m, e) e' Hm.
rewrite <- F2R_Zabs.
destruct (Zle_or_lt e e') as [He|He].
unfold F2R. simpl.
apply Rmult_lt_reg_r with (bpow (-e)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- 2!bpow_plus, Zplus_opp_r, Rmult_1_r.
rewrite <-Z2R_Zpower. 2: now apply Zle_left.
now apply Z2R_lt.
elim Zlt_not_le with (1 := Hm).
simpl.
cut (e' - e < 0)%Z. 2: omega.
clear.
case (e' - e)%Z ; try easy.
intros p _.
apply Zabs_pos.
Qed.

Theorem F2R_change_exp :
  forall e' m e : Z,
  (e' <= e)%Z ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e')) e').
Proof.
intros e' m e He.
unfold F2R. simpl.
rewrite Z2R_mult, Z2R_Zpower, Rmult_assoc.
apply f_equal.
pattern e at 1 ; replace e with (e - e' + e')%Z by ring.
apply bpow_plus.
now apply Zle_minus_le_0.
Qed.

Theorem F2R_prec_normalize :
  forall m e e' p : Z,
  (Zabs m < Zpower beta p)%Z ->
  (bpow (e' - 1)%Z <= Rabs (F2R (Float beta m e)))%R ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e' + p)) (e' - p)).
Proof.
intros m e e' p Hm Hf.
assert (Hp: (0 <= p)%Z).
destruct p ; try easy.
now elim (Zle_not_lt _ _ (Zabs_pos m)).
(* . *)
replace (e - e' + p)%Z with (e - (e' - p))%Z by ring.
apply F2R_change_exp.
cut (e' - 1 < e + p)%Z. omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := Hf).
rewrite <- F2R_Zabs, Zplus_comm, bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- Z2R_Zpower.
now apply Z2R_lt.
exact Hp.
Qed.

(** Floats and ln_beta *)
Theorem ln_beta_F2R_bounds :
  forall x m e, (0 < m)%Z ->
  (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R ->
  ln_beta beta x = ln_beta beta (F2R (Float beta m e)) :> Z.
Proof.
intros x m e Hp (Hx,Hx2).
destruct (ln_beta beta (F2R (Float beta m e))) as (ex, He).
simpl.
apply ln_beta_unique.
assert (Hp1: (0 < F2R (Float beta m e))%R).
now apply F2R_gt_0_compat.
specialize (He (Rgt_not_eq _ _ Hp1)).
rewrite Rabs_pos_eq in He. 2: now apply Rlt_le.
destruct He as (He1, He2).
assert (Hx1: (0 < x)%R).
now apply Rlt_le_trans with (2 := Hx).
rewrite Rabs_pos_eq. 2: now apply Rlt_le.
split.
now apply Rle_trans with (1 := He1).
apply Rlt_le_trans with (1 := Hx2).
now apply F2R_p1_le_bpow.
Qed.

Theorem ln_beta_F2R :
  forall m e : Z,
  m <> Z0 ->
  (ln_beta beta (F2R (Float beta m e)) = ln_beta beta (Z2R m) + e :> Z)%Z.
Proof.
intros m e H.
unfold F2R ; simpl.
apply ln_beta_mult_bpow.
exact (Z2R_neq m 0 H).
Qed.

Theorem float_distribution_pos :
  forall m1 e1 m2 e2 : Z,
  (0 < m1)%Z ->
  (F2R (Float beta m1 e1) < F2R (Float beta m2 e2) < F2R (Float beta (m1 + 1) e1))%R ->
  (e2 < e1)%Z /\ (e1 + ln_beta beta (Z2R m1) = e2 + ln_beta beta (Z2R m2))%Z.
Proof.
intros m1 e1 m2 e2 Hp1 (H12, H21).
assert (He: (e2 < e1)%Z).
(* . *)
apply Znot_ge_lt.
intros H0.
elim Rlt_not_le with (1 := H21).
apply Zge_le in H0.
apply (F2R_change_exp e1 m2 e2) in H0.
rewrite H0.
apply F2R_le_compat.
apply Zlt_le_succ.
apply (F2R_lt_reg e1).
now rewrite <- H0.
(* . *)
split.
exact He.
rewrite (Zplus_comm e1), (Zplus_comm e2).
assert (Hp2: (0 < m2)%Z).
apply (F2R_gt_0_reg m2 e2).
apply Rlt_trans with (2 := H12).
now apply F2R_gt_0_compat.
rewrite <- 2!ln_beta_F2R.
destruct (ln_beta beta (F2R (Float beta m1 e1))) as (e1', H1).
simpl.
apply sym_eq.
apply ln_beta_unique.
assert (H2 : (bpow (e1' - 1) <= F2R (Float beta m1 e1) < bpow e1')%R).
rewrite <- (Zabs_eq m1), F2R_Zabs.
apply H1.
apply Rgt_not_eq.
apply Rlt_gt.
now apply F2R_gt_0_compat.
now apply Zlt_le_weak.
clear H1.
rewrite <- F2R_Zabs, Zabs_eq.
split.
apply Rlt_le.
apply Rle_lt_trans with (2 := H12).
apply H2.
apply Rlt_le_trans with (1 := H21).
now apply F2R_p1_le_bpow.
now apply Zlt_le_weak.
apply sym_not_eq.
now apply Zlt_not_eq.
apply sym_not_eq.
now apply Zlt_not_eq.
Qed.

Theorem F2R_cond_Zopp :
  forall b m e,
  F2R (Float beta (cond_Zopp b m) e) = cond_Ropp b (F2R (Float beta m e)).
Proof.
intros [|] m e ; unfold F2R ; simpl.
now rewrite Z2R_opp, Ropp_mult_distr_l_reverse.
apply refl_equal.
Qed.

End Float_prop.

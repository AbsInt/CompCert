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

(** * Rounding to nearest, ties to even: existence, unicity... *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_ulp.

Notation ZnearestE := (Znearest (fun x => negb (Zeven x))).

Section Fcore_rnd_NE.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Context { valid_exp : Valid_exp fexp }.

Notation format := (generic_format beta fexp).
Notation canonic := (canonic beta fexp).

Definition NE_prop (_ : R) f :=
  exists g : float beta, f = F2R g /\ canonic g /\ Zeven (Fnum g) = true.

Definition Rnd_NE_pt :=
  Rnd_NG_pt format NE_prop.

Definition DN_UP_parity_pos_prop :=
  forall x xd xu,
  (0 < x)%R ->
  ~ format x ->
  canonic xd ->
  canonic xu ->
  F2R xd = round beta fexp Zfloor x ->
  F2R xu = round beta fexp Zceil x ->
  Zeven (Fnum xu) = negb (Zeven (Fnum xd)).

Definition DN_UP_parity_prop :=
  forall x xd xu,
  ~ format x ->
  canonic xd ->
  canonic xu ->
  F2R xd = round beta fexp Zfloor x ->
  F2R xu = round beta fexp Zceil x ->
  Zeven (Fnum xu) = negb (Zeven (Fnum xd)).

Lemma DN_UP_parity_aux :
  DN_UP_parity_pos_prop ->
  DN_UP_parity_prop.
Proof.
intros Hpos x xd xu Hfx Hd Hu Hxd Hxu.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
(* . *)
exact (Hpos x xd xu Hx Hfx Hd Hu Hxd Hxu).
elim Hfx.
rewrite <- Hx.
apply generic_format_0.
(* . *)
assert (Hx': (0 < -x)%R).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive, Ropp_0.
destruct xd as (md, ed).
destruct xu as (mu, eu).
simpl.
rewrite <- (Bool.negb_involutive (Zeven mu)).
apply f_equal.
apply sym_eq.
rewrite <- (Zeven_opp mu), <- (Zeven_opp md).
change (Zeven (Fnum (Float beta (-md) ed)) = negb (Zeven (Fnum (Float beta (-mu) eu)))).
apply (Hpos (-x)%R _ _ Hx').
intros H.
apply Hfx.
rewrite <- Ropp_involutive.
now apply generic_format_opp.
now apply canonic_opp.
now apply canonic_opp.
rewrite round_DN_opp, F2R_Zopp.
now apply f_equal.
rewrite round_UP_opp, F2R_Zopp.
now apply f_equal.
Qed.

Class Exists_NE :=
  exists_NE : Zeven beta = false \/ forall e,
  ((fexp e < e)%Z -> (fexp (e + 1) < e)%Z) /\ ((e <= fexp e)%Z -> fexp (fexp e + 1) = fexp e).

Context { exists_NE_ : Exists_NE }.

Theorem DN_UP_parity_generic_pos :
  DN_UP_parity_pos_prop.
Proof with auto with typeclass_instances.
intros x xd xu H0x Hfx Hd Hu Hxd Hxu.
destruct (ln_beta beta x) as (ex, Hexa).
specialize (Hexa (Rgt_not_eq _ _ H0x)).
generalize Hexa. intros Hex.
rewrite (Rabs_pos_eq _ (Rlt_le _ _ H0x)) in Hex.
destruct (Zle_or_lt ex (fexp ex)) as [Hxe|Hxe].
(* small x *)
assert (Hd3 : Fnum xd = Z0).
apply F2R_eq_0_reg with beta (Fexp xd).
change (F2R xd = R0).
rewrite Hxd.
apply round_DN_small_pos with (1 := Hex) (2 := Hxe).
assert (Hu3 : xu = Float beta (1 * Zpower beta (fexp ex - fexp (fexp ex + 1))) (fexp (fexp ex + 1))).
apply canonic_unicity with (1 := Hu).
apply (f_equal fexp).
rewrite <- F2R_change_exp.
now rewrite F2R_bpow, ln_beta_bpow.
now apply valid_exp.
rewrite <- F2R_change_exp.
rewrite F2R_bpow.
apply sym_eq.
rewrite Hxu.
apply sym_eq.
apply round_UP_small_pos with (1 := Hex) (2 := Hxe).
now apply valid_exp.
rewrite Hd3, Hu3.
rewrite Zmult_1_l.
simpl.
destruct exists_NE_ as [H|H].
apply Zeven_Zpower_odd with (2 := H).
apply Zle_minus_le_0.
now apply valid_exp.
rewrite (proj2 (H ex)).
now rewrite Zminus_diag.
exact Hxe.
(* large x *)
assert (Hd4: (bpow (ex - 1) <= Rabs (F2R xd) < bpow ex)%R).
rewrite Rabs_pos_eq.
rewrite Hxd.
split.
apply (round_DN_pt beta fexp x).
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
omega.
apply Hex.
apply Rle_lt_trans with (2 := proj2 Hex).
apply (round_DN_pt beta fexp x).
rewrite Hxd.
apply (round_DN_pt beta fexp x).
apply generic_format_0.
now apply Rlt_le.
assert (Hxe2 : (fexp (ex + 1) <= ex)%Z) by now apply valid_exp.
assert (Hud: (F2R xu = F2R xd + ulp beta fexp x)%R).
rewrite Hxu, Hxd.
now apply round_UP_DN_ulp.
destruct (total_order_T (bpow ex) (F2R xu)) as [[Hu2|Hu2]|Hu2].
(* - xu > bpow ex  *)
elim (Rlt_not_le _ _ Hu2).
rewrite Hxu.
apply round_bounded_large_pos...
(* - xu = bpow ex *)
assert (Hu3: xu = Float beta (1 * Zpower beta (ex - fexp (ex + 1))) (fexp (ex + 1))).
apply canonic_unicity with (1 := Hu).
apply (f_equal fexp).
rewrite <- F2R_change_exp.
now rewrite F2R_bpow, ln_beta_bpow.
now apply valid_exp.
rewrite <- Hu2.
apply sym_eq.
rewrite <- F2R_change_exp.
apply F2R_bpow.
exact Hxe2.
assert (Hd3: xd = Float beta (Zpower beta (ex - fexp ex) - 1) (fexp ex)).
assert (H: F2R xd = F2R (Float beta (Zpower beta (ex - fexp ex) - 1) (fexp ex))).
unfold F2R. simpl.
rewrite Z2R_minus.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Z2R_Zpower, <- bpow_plus.
ring_simplify (ex - fexp ex + fexp ex)%Z.
rewrite Hu2, Hud.
rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
unfold canonic_exp.
rewrite ln_beta_unique with beta x ex.
unfold F2R.
simpl. ring.
rewrite Rabs_pos_eq.
exact Hex.
now apply Rlt_le.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
apply canonic_unicity with (1 := Hd) (3 := H).
apply (f_equal fexp).
rewrite <- H.
apply sym_eq.
now apply ln_beta_unique.
rewrite Hd3, Hu3.
unfold Fnum.
rewrite Zeven_mult. simpl.
unfold Zminus at 2.
rewrite Zeven_plus.
rewrite eqb_sym. simpl.
fold (negb (Zeven (beta ^ (ex - fexp ex)))).
rewrite Bool.negb_involutive.
rewrite (Zeven_Zpower beta (ex - fexp ex)). 2: omega.
destruct exists_NE_.
rewrite H.
apply Zeven_Zpower_odd with (2 := H).
now apply Zle_minus_le_0.
apply Zeven_Zpower.
specialize (H ex).
omega.
(* - xu < bpow ex *)
revert Hud.
rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
unfold F2R.
rewrite Hd, Hu.
unfold canonic_exp.
rewrite ln_beta_unique with beta (F2R xu) ex.
rewrite ln_beta_unique with (1 := Hd4).
rewrite ln_beta_unique with (1 := Hexa).
intros H.
replace (Fnum xu) with (Fnum xd + 1)%Z.
rewrite Zeven_plus.
now apply eqb_sym.
apply sym_eq.
apply eq_Z2R.
rewrite Z2R_plus.
apply Rmult_eq_reg_r with (bpow (fexp ex)).
rewrite H.
simpl. ring.
apply Rgt_not_eq.
apply bpow_gt_0.
rewrite Rabs_pos_eq.
split.
apply Rle_trans with (1 := proj1 Hex).
rewrite Hxu.
apply (round_UP_pt beta fexp x).
exact Hu2.
apply Rlt_le.
apply Rlt_le_trans with (1 := H0x).
rewrite Hxu.
apply (round_UP_pt beta fexp x).
Qed.

Theorem DN_UP_parity_generic :
  DN_UP_parity_prop.
Proof.
apply DN_UP_parity_aux.
apply DN_UP_parity_generic_pos.
Qed.

Theorem Rnd_NE_pt_total :
  round_pred_total Rnd_NE_pt.
Proof.
apply satisfies_any_imp_NG.
now apply generic_format_satisfies_any.
intros x d u Hf Hd Hu.
generalize (proj1 Hd).
unfold generic_format.
set (ed := canonic_exp beta fexp d).
set (md := Ztrunc (scaled_mantissa beta fexp d)).
intros Hd1.
case_eq (Zeven md) ; [ intros He | intros Ho ].
right.
exists (Float beta md ed).
unfold Fcore_generic_fmt.canonic.
rewrite <- Hd1.
now repeat split.
left.
generalize (proj1 Hu).
unfold generic_format.
set (eu := canonic_exp beta fexp u).
set (mu := Ztrunc (scaled_mantissa beta fexp u)).
intros Hu1.
rewrite Hu1.
eexists ; repeat split.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hu1.
rewrite (DN_UP_parity_generic x (Float beta md ed) (Float beta mu eu)).
simpl.
now rewrite Ho.
exact Hf.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hd1.
unfold Fcore_generic_fmt.canonic.
now rewrite <- Hu1.
rewrite <- Hd1.
apply Rnd_DN_pt_unicity with (1 := Hd).
now apply round_DN_pt.
rewrite <- Hu1.
apply Rnd_UP_pt_unicity with (1 := Hu).
now apply round_UP_pt.
Qed.

Theorem Rnd_NE_pt_monotone :
  round_pred_monotone Rnd_NE_pt.
Proof.
apply Rnd_NG_pt_monotone.
intros x d u Hd Hdn Hu Hun (cd, (Hd1, Hd2)) (cu, (Hu1, Hu2)).
destruct (Req_dec x d) as [Hx|Hx].
rewrite <- Hx.
apply sym_eq.
apply Rnd_UP_pt_idempotent with (1 := Hu).
rewrite Hx.
apply Hd.
rewrite (DN_UP_parity_aux DN_UP_parity_generic_pos x cd cu) in Hu2 ; try easy.
now rewrite (proj2 Hd2) in Hu2.
intros Hf.
apply Hx.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
rewrite <- Hd1.
apply Rnd_DN_pt_unicity with (1 := Hd).
now apply round_DN_pt.
rewrite <- Hu1.
apply Rnd_UP_pt_unicity with (1 := Hu).
now apply round_UP_pt.
Qed.

Theorem Rnd_NE_pt_round :
  round_pred Rnd_NE_pt.
split.
apply Rnd_NE_pt_total.
apply Rnd_NE_pt_monotone.
Qed.

Lemma round_NE_pt_pos :
  forall x,
  (0 < x)%R ->
  Rnd_NE_pt x (round beta fexp ZnearestE x).
Proof with auto with typeclass_instances.
intros x Hx.
split.
now apply round_N_pt.
unfold NE_prop.
set (mx := scaled_mantissa beta fexp x).
set (xr := round beta fexp ZnearestE x).
destruct (Req_dec (mx - Z2R (Zfloor mx)) (/2)) as [Hm|Hm].
(* midpoint *)
left.
exists (Float beta (Ztrunc (scaled_mantissa beta fexp xr)) (canonic_exp beta fexp xr)).
split.
apply round_N_pt...
split.
unfold Fcore_generic_fmt.canonic. simpl.
apply f_equal.
apply round_N_pt...
simpl.
unfold xr, round, Znearest.
fold mx.
rewrite Hm.
rewrite Rcompare_Eq. 2: apply refl_equal.
case_eq (Zeven (Zfloor mx)) ; intros Hmx.
(* . even floor *)
change (Zeven (Ztrunc (scaled_mantissa beta fexp (round beta fexp Zfloor x))) = true).
destruct (Rle_or_lt (round beta fexp Zfloor x) 0) as [Hr|Hr].
rewrite (Rle_antisym _ _ Hr).
unfold scaled_mantissa.
rewrite Rmult_0_l.
change 0%R with (Z2R 0).
now rewrite (Ztrunc_Z2R 0).
rewrite <- (round_0 beta fexp Zfloor).
apply round_le...
now apply Rlt_le.
rewrite scaled_mantissa_DN...
now rewrite Ztrunc_Z2R.
(* . odd floor *)
change (Zeven (Ztrunc (scaled_mantissa beta fexp (round beta fexp Zceil x))) = true).
destruct (ln_beta beta x) as (ex, Hex).
specialize (Hex (Rgt_not_eq _ _ Hx)).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hx)) in Hex.
destruct (Z_lt_le_dec (fexp ex) ex) as [He|He].
(* .. large pos *)
assert (Hu := round_bounded_large_pos _ _ Zceil _ _ He Hex).
assert (Hfc: Zceil mx = (Zfloor mx + 1)%Z).
apply Zceil_floor_neq.
intros H.
rewrite H in Hm.
unfold Rminus in Hm.
rewrite Rplus_opp_r in Hm.
elim (Rlt_irrefl 0).
rewrite Hm at 2.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
destruct (proj2 Hu) as [Hu'|Hu'].
(* ... u <> bpow *)
unfold scaled_mantissa.
rewrite canonic_exp_fexp_pos with (1 := conj (proj1 Hu) Hu').
unfold round, F2R. simpl.
rewrite canonic_exp_fexp_pos with (1 := Hex).
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
rewrite Ztrunc_Z2R.
fold mx.
rewrite Hfc.
now rewrite Zeven_plus, Hmx.
(* ... u = bpow *)
rewrite Hu'.
unfold scaled_mantissa, canonic_exp.
rewrite ln_beta_bpow.
rewrite <- bpow_plus, <- Z2R_Zpower.
rewrite Ztrunc_Z2R.
case_eq (Zeven beta) ; intros Hr.
destruct exists_NE_ as [Hs|Hs].
now rewrite Hs in Hr.
destruct (Hs ex) as (H,_).
rewrite Zeven_Zpower.
exact Hr.
omega.
assert (Zeven (Zfloor mx) = true). 2: now rewrite H in Hmx.
replace (Zfloor mx) with (Zceil mx + -1)%Z by omega.
rewrite Zeven_plus.
apply eqb_true.
unfold mx.
replace (Zceil (scaled_mantissa beta fexp x)) with (Zpower beta (ex - fexp ex)).
rewrite Zeven_Zpower_odd with (2 := Hr).
easy.
omega.
apply eq_Z2R.
rewrite Z2R_Zpower. 2: omega.
apply Rmult_eq_reg_r with (bpow (fexp ex)).
unfold Zminus.
rewrite bpow_plus.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_l, Rmult_1_r.
pattern (fexp ex) ; rewrite <- canonic_exp_fexp_pos with (1 := Hex).
now apply sym_eq.
apply Rgt_not_eq.
apply bpow_gt_0.
generalize (proj1 (valid_exp ex) He).
omega.
(* .. small pos *)
assert (Zeven (Zfloor mx) = true). 2: now rewrite H in Hmx.
unfold mx, scaled_mantissa.
rewrite canonic_exp_fexp_pos with (1 := Hex).
now rewrite mantissa_DN_small_pos.
(* not midpoint *)
right.
intros g Hg.
destruct (Req_dec x g) as [Hxg|Hxg].
rewrite <- Hxg.
apply sym_eq.
apply round_generic...
rewrite Hxg.
apply Hg.
set (d := round beta fexp Zfloor x).
set (u := round beta fexp Zceil x).
apply Rnd_N_pt_unicity with (d := d) (u := u) (4 := Hg).
now apply round_DN_pt.
now apply round_UP_pt.
2: now apply round_N_pt.
rewrite <- (scaled_mantissa_mult_bpow beta fexp x).
unfold d, u, round, F2R. simpl. fold mx.
rewrite <- 2!Rmult_minus_distr_r.
intros H.
apply Rmult_eq_reg_r in H.
apply Hm.
apply Rcompare_Eq_inv.
rewrite Rcompare_floor_ceil_mid.
now apply Rcompare_Eq.
contradict Hxg.
apply sym_eq.
apply Rnd_N_pt_idempotent with (1 := Hg).
rewrite <- (scaled_mantissa_mult_bpow beta fexp x).
fold mx.
rewrite <- Hxg.
change (Z2R (Zfloor mx) * bpow (canonic_exp beta fexp x))%R with d.
now eapply round_DN_pt.
apply Rgt_not_eq.
apply bpow_gt_0.
Qed.

Theorem round_NE_opp :
  forall x,
  round beta fexp ZnearestE (-x) = (- round beta fexp ZnearestE x)%R.
Proof.
intros x.
unfold round. simpl.
rewrite scaled_mantissa_opp, canonic_exp_opp.
rewrite Znearest_opp.
rewrite <- F2R_Zopp.
apply (f_equal (fun v => F2R (Float beta (-v) _))).
set (m := scaled_mantissa beta fexp x).
unfold Znearest.
case Rcompare ; trivial.
apply (f_equal (fun (b : bool) => if b then Zceil m else Zfloor m)).
rewrite Bool.negb_involutive.
rewrite Zeven_opp.
rewrite Zeven_plus.
now rewrite eqb_sym.
Qed.

Lemma round_NE_abs:
  forall x : R,
  round beta fexp ZnearestE (Rabs x) = Rabs (round beta fexp ZnearestE x).
Proof with auto with typeclass_instances.
intros x.
apply sym_eq.
unfold Rabs at 2.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite round_NE_opp.
apply Rabs_left1.
rewrite <- (round_0 beta fexp ZnearestE).
apply round_le...
now apply Rlt_le.
apply Rabs_pos_eq.
rewrite <- (round_0 beta fexp ZnearestE).
apply round_le...
now apply Rge_le.
Qed.

Theorem round_NE_pt :
  forall x,
  Rnd_NE_pt x (round beta fexp ZnearestE x).
Proof with auto with typeclass_instances.
intros x.
destruct (total_order_T x 0) as [[Hx|Hx]|Hx].
apply Rnd_NG_pt_sym.
apply generic_format_opp.
unfold NE_prop.
intros _ f ((mg,eg),(H1,(H2,H3))).
exists (Float beta (- mg) eg).
repeat split.
rewrite H1.
now rewrite F2R_Zopp.
now apply canonic_opp.
simpl.
now rewrite Zeven_opp.
rewrite <- round_NE_opp.
apply round_NE_pt_pos.
now apply Ropp_0_gt_lt_contravar.
rewrite Hx, round_0...
apply Rnd_NG_pt_refl.
apply generic_format_0.
now apply round_NE_pt_pos.
Qed.

End Fcore_rnd_NE.

(** Notations for backward-compatibility with Flocq 1.4. *)
Notation rndNE := ZnearestE (only parsing).

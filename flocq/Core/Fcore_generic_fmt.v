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

(** * What is a real number belonging to a format, and many properties. *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_float_prop.

Section Generic.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Section Format.

Variable fexp : Z -> Z.

(** To be a good fexp *)

Class Valid_exp :=
  valid_exp :
  forall k : Z,
  ( (fexp k < k)%Z -> (fexp (k + 1) <= k)%Z ) /\
  ( (k <= fexp k)%Z ->
    (fexp (fexp k + 1) <= fexp k)%Z /\
    forall l : Z, (l <= fexp k)%Z -> fexp l = fexp k ).

Context { valid_exp_ : Valid_exp }.

Theorem valid_exp_large :
  forall k l,
  (fexp k < k)%Z -> (k <= l)%Z ->
  (fexp l < l)%Z.
Proof.
intros k l Hk H.
apply Znot_ge_lt.
intros Hl.
apply Zge_le in Hl.
assert (H' := proj2 (proj2 (valid_exp l) Hl) k).
omega.
Qed.

Theorem valid_exp_large' :
  forall k l,
  (fexp k < k)%Z -> (l <= k)%Z ->
  (fexp l < k)%Z.
Proof.
intros k l Hk H.
apply Znot_ge_lt.
intros H'.
apply Zge_le in H'.
assert (Hl := Zle_trans _ _ _ H H').
apply valid_exp in Hl.
assert (H1 := proj2 Hl k H').
omega.
Qed.

Definition canonic_exp x :=
  fexp (ln_beta beta x).

Definition canonic (f : float beta) :=
  Fexp f = canonic_exp (F2R f).

Definition scaled_mantissa x :=
  (x * bpow (- canonic_exp x))%R.

Definition generic_format (x : R) :=
  x = F2R (Float beta (Ztrunc (scaled_mantissa x)) (canonic_exp x)).

(** Basic facts *)
Theorem generic_format_0 :
  generic_format 0.
Proof.
unfold generic_format, scaled_mantissa.
rewrite Rmult_0_l.
change (Ztrunc 0) with (Ztrunc (Z2R 0)).
now rewrite Ztrunc_Z2R, F2R_0.
Qed.

Theorem canonic_exp_opp :
  forall x,
  canonic_exp (-x) = canonic_exp x.
Proof.
intros x.
unfold canonic_exp.
now rewrite ln_beta_opp.
Qed.

Theorem canonic_exp_abs :
  forall x,
  canonic_exp (Rabs x) = canonic_exp x.
Proof.
intros x.
unfold canonic_exp.
now rewrite ln_beta_abs.
Qed.

Theorem generic_format_bpow :
  forall e, (fexp (e + 1) <= e)%Z ->
  generic_format (bpow e).
Proof.
intros e H.
unfold generic_format, scaled_mantissa, canonic_exp.
rewrite ln_beta_bpow.
rewrite <- bpow_plus.
rewrite <- (Z2R_Zpower beta (e + - fexp (e + 1))).
rewrite Ztrunc_Z2R.
rewrite <- F2R_bpow.
rewrite F2R_change_exp with (1 := H).
now rewrite Zmult_1_l.
now apply Zle_minus_le_0.
Qed.

Theorem generic_format_bpow' :
  forall e, (fexp e <= e)%Z ->
  generic_format (bpow e).
Proof.
intros e He.
apply generic_format_bpow.
destruct (Zle_lt_or_eq _ _ He).
now apply valid_exp_.
rewrite <- H.
apply valid_exp.
rewrite H.
apply Zle_refl.
Qed.

Theorem generic_format_F2R :
  forall m e,
  ( m <> 0 -> canonic_exp (F2R (Float beta m e)) <= e )%Z ->
  generic_format (F2R (Float beta m e)).
Proof.
intros m e.
destruct (Z_eq_dec m 0) as [Zm|Zm].
intros _.
rewrite Zm, F2R_0.
apply generic_format_0.
unfold generic_format, scaled_mantissa.
set (e' := canonic_exp (F2R (Float beta m e))).
intros He.
specialize (He Zm).
unfold F2R at 3. simpl.
rewrite  F2R_change_exp with (1 := He).
apply F2R_eq_compat.
rewrite Rmult_assoc, <- bpow_plus, <- Z2R_Zpower, <- Z2R_mult.
now rewrite Ztrunc_Z2R.
now apply Zle_left.
Qed.

Lemma generic_format_F2R': forall (x:R) (f:float beta),
       F2R f = x -> ((x <> 0)%R ->
       (canonic_exp x <= Fexp f)%Z) ->
       generic_format x.
Proof.
intros x f H1 H2.
rewrite <- H1; destruct f as (m,e).
apply  generic_format_F2R.
simpl in *; intros H3.
rewrite H1; apply H2.
intros Y; apply H3.
apply F2R_eq_0_reg with beta e.
now rewrite H1.
Qed.


Theorem canonic_opp :
  forall m e,
  canonic (Float beta m e) ->
  canonic (Float beta (-m) e).
Proof.
intros m e H.
unfold canonic.
now rewrite F2R_Zopp, canonic_exp_opp.
Qed.

Theorem canonic_abs :
  forall m e,
  canonic (Float beta m e) ->
  canonic (Float beta (Zabs m) e).
Proof.
intros m e H.
unfold canonic.
now rewrite F2R_Zabs, canonic_exp_abs.
Qed.

Theorem canonic_0: canonic (Float beta 0 (fexp (ln_beta beta 0%R))).
Proof.
unfold canonic; simpl; unfold canonic_exp.
replace (F2R {| Fnum := 0; Fexp := fexp (ln_beta beta 0) |}) with 0%R.
reflexivity.
unfold F2R; simpl; ring.
Qed.



Theorem canonic_unicity :
  forall f1 f2,
  canonic f1 ->
  canonic f2 ->
  F2R f1 = F2R f2 ->
  f1 = f2.
Proof.
intros (m1, e1) (m2, e2).
unfold canonic. simpl.
intros H1 H2 H.
rewrite H in H1.
rewrite <- H2 in H1. clear H2.
rewrite H1 in H |- *.
apply (f_equal (fun m => Float beta m e2)).
apply F2R_eq_reg with (1 := H).
Qed.

Theorem scaled_mantissa_generic :
  forall x,
  generic_format x ->
  scaled_mantissa x = Z2R (Ztrunc (scaled_mantissa x)).
Proof.
intros x Hx.
unfold scaled_mantissa.
pattern x at 1 3 ; rewrite Hx.
unfold F2R. simpl.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
now rewrite Ztrunc_Z2R.
Qed.

Theorem scaled_mantissa_mult_bpow :
  forall x,
  (scaled_mantissa x * bpow (canonic_exp x))%R = x.
Proof.
intros x.
unfold scaled_mantissa.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_l.
apply Rmult_1_r.
Qed.

Theorem scaled_mantissa_0 :
  scaled_mantissa 0 = 0%R.
Proof.
apply Rmult_0_l.
Qed.

Theorem scaled_mantissa_opp :
  forall x,
  scaled_mantissa (-x) = (-scaled_mantissa x)%R.
Proof.
intros x.
unfold scaled_mantissa.
rewrite canonic_exp_opp.
now rewrite Ropp_mult_distr_l_reverse.
Qed.

Theorem scaled_mantissa_abs :
  forall x,
  scaled_mantissa (Rabs x) = Rabs (scaled_mantissa x).
Proof.
intros x.
unfold scaled_mantissa.
rewrite canonic_exp_abs, Rabs_mult.
apply f_equal.
apply sym_eq.
apply Rabs_pos_eq.
apply bpow_ge_0.
Qed.

Theorem generic_format_opp :
  forall x, generic_format x -> generic_format (-x).
Proof.
intros x Hx.
unfold generic_format.
rewrite scaled_mantissa_opp, canonic_exp_opp.
rewrite Ztrunc_opp.
rewrite F2R_Zopp.
now apply f_equal.
Qed.

Theorem generic_format_abs :
  forall x, generic_format x -> generic_format (Rabs x).
Proof.
intros x Hx.
unfold generic_format.
rewrite scaled_mantissa_abs, canonic_exp_abs.
rewrite Ztrunc_abs.
rewrite F2R_Zabs.
now apply f_equal.
Qed.

Theorem generic_format_abs_inv :
  forall x, generic_format (Rabs x) -> generic_format x.
Proof.
intros x.
unfold generic_format, Rabs.
case Rcase_abs ; intros _.
rewrite scaled_mantissa_opp, canonic_exp_opp, Ztrunc_opp.
intros H.
rewrite <- (Ropp_involutive x) at 1.
rewrite H, F2R_Zopp.
apply Ropp_involutive.
easy.
Qed.

Theorem canonic_exp_fexp :
  forall x ex,
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
  canonic_exp x = fexp ex.
Proof.
intros x ex Hx.
unfold canonic_exp.
now rewrite ln_beta_unique with (1 := Hx).
Qed.

Theorem canonic_exp_fexp_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  canonic_exp x = fexp ex.
Proof.
intros x ex Hx.
apply canonic_exp_fexp.
rewrite Rabs_pos_eq.
exact Hx.
apply Rle_trans with (2 := proj1 Hx).
apply bpow_ge_0.
Qed.

(** Properties when the real number is "small" (kind of subnormal) *)
Theorem mantissa_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  (0 < x * bpow (- fexp ex) < 1)%R.
Proof.
intros x ex Hx He.
split.
apply Rmult_lt_0_compat.
apply Rlt_le_trans with (2 := proj1 Hx).
apply bpow_gt_0.
apply bpow_gt_0.
apply Rmult_lt_reg_r with (bpow (fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_l.
rewrite Rmult_1_r, Rmult_1_l.
apply Rlt_le_trans with (1 := proj2 Hx).
now apply bpow_le.
Qed.

Theorem scaled_mantissa_small :
  forall x ex,
  (Rabs x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  (Rabs (scaled_mantissa x) < 1)%R.
Proof.
intros x ex Ex He.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, scaled_mantissa_0, Rabs_R0.
now apply (Z2R_lt 0 1).
rewrite <- scaled_mantissa_abs.
unfold scaled_mantissa.
rewrite canonic_exp_abs.
unfold canonic_exp.
destruct (ln_beta beta x) as (ex', Ex').
simpl.
specialize (Ex' Zx).
apply (mantissa_small_pos _ _ Ex').
assert (ex' <= fexp ex)%Z.
apply Zle_trans with (2 := He).
apply bpow_lt_bpow with beta.
now apply Rle_lt_trans with (2 := Ex).
now rewrite (proj2 (proj2 (valid_exp _) He)).
Qed.

Theorem abs_scaled_mantissa_lt_bpow :
  forall x,
  (Rabs (scaled_mantissa x) < bpow (ln_beta beta x - canonic_exp x))%R.
Proof.
intros x.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, scaled_mantissa_0, Rabs_R0.
apply bpow_gt_0.
apply Rlt_le_trans with (1 := bpow_ln_beta_gt beta _).
apply bpow_le.
unfold scaled_mantissa.
rewrite ln_beta_mult_bpow with (1 := Zx).
apply Zle_refl.
Qed.

Theorem ln_beta_generic_gt :
  forall x, (x <> 0)%R ->
  generic_format x ->
  (canonic_exp x < ln_beta beta x)%Z.
Proof.
intros x Zx Gx.
apply Znot_ge_lt.
unfold canonic_exp.
destruct (ln_beta beta x) as (ex,Ex) ; simpl.
specialize (Ex Zx).
intros H.
apply Zge_le in H.
generalize (scaled_mantissa_small x ex (proj2 Ex) H).
contradict Zx.
rewrite Gx.
replace (Ztrunc (scaled_mantissa x)) with Z0.
apply F2R_0.
cut (Zabs (Ztrunc (scaled_mantissa x)) < 1)%Z.
clear ; zify ; omega.
apply lt_Z2R.
rewrite Z2R_abs.
now rewrite <- scaled_mantissa_generic.
Qed.

Theorem mantissa_DN_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Zfloor (x * bpow (- fexp ex)) = Z0.
Proof.
intros x ex Hx He.
apply Zfloor_imp. simpl.
assert (H := mantissa_small_pos x ex Hx He).
split ; try apply Rlt_le ; apply H.
Qed.

Theorem mantissa_UP_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  Zceil (x * bpow (- fexp ex)) = 1%Z.
Proof.
intros x ex Hx He.
apply Zceil_imp. simpl.
assert (H := mantissa_small_pos x ex Hx He).
split ; try apply Rlt_le ; apply H.
Qed.

(** Generic facts about any format *)
Theorem generic_format_discrete :
  forall x m,
  let e := canonic_exp x in
  (F2R (Float beta m e) < x < F2R (Float beta (m + 1) e))%R ->
  ~ generic_format x.
Proof.
intros x m e (Hx,Hx2) Hf.
apply Rlt_not_le with (1 := Hx2). clear Hx2.
rewrite Hf.
fold e.
apply F2R_le_compat.
apply Zlt_le_succ.
apply lt_Z2R.
rewrite <- scaled_mantissa_generic with (1 := Hf).
apply Rmult_lt_reg_r with (bpow e).
apply bpow_gt_0.
now rewrite scaled_mantissa_mult_bpow.
Qed.

Theorem generic_format_canonic :
  forall f, canonic f ->
  generic_format (F2R f).
Proof.
intros (m, e) Hf.
unfold canonic in Hf. simpl in Hf.
unfold generic_format, scaled_mantissa.
rewrite <- Hf.
apply F2R_eq_compat.
unfold F2R. simpl.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
now rewrite Ztrunc_Z2R.
Qed.

Theorem generic_format_ge_bpow :
  forall emin,
  ( forall e, (emin <= fexp e)%Z ) ->
  forall x,
  (0 < x)%R ->
  generic_format x ->
  (bpow emin <= x)%R.
Proof.
intros emin Emin x Hx Fx.
rewrite Fx.
apply Rle_trans with (bpow (fexp (ln_beta beta x))).
now apply bpow_le.
apply bpow_le_F2R.
apply F2R_gt_0_reg with beta (canonic_exp x).
now rewrite <- Fx.
Qed.

Theorem abs_lt_bpow_prec:
  forall prec,
  (forall e, (e - prec <= fexp e)%Z) ->
  (* OK with FLX, FLT and FTZ *)
  forall x,
  (Rabs x < bpow (prec + canonic_exp x))%R.
intros prec Hp x.
case (Req_dec x 0); intros Hxz.
rewrite Hxz, Rabs_R0.
apply bpow_gt_0.
unfold canonic_exp.
destruct (ln_beta beta x) as (ex,Ex) ; simpl.
specialize (Ex Hxz).
apply Rlt_le_trans with (1 := proj2 Ex).
apply bpow_le.
specialize (Hp ex).
omega.
Qed.

Theorem generic_format_bpow_inv' :
  forall e,
  generic_format (bpow e) ->
  (fexp (e + 1) <= e)%Z.
Proof.
intros e He.
apply Znot_gt_le.
contradict He.
unfold generic_format, scaled_mantissa, canonic_exp, F2R. simpl.
rewrite ln_beta_bpow, <- bpow_plus.
apply Rgt_not_eq.
rewrite Ztrunc_floor.
2: apply bpow_ge_0.
rewrite Zfloor_imp with (n := Z0).
rewrite Rmult_0_l.
apply bpow_gt_0.
split.
apply bpow_ge_0.
apply (bpow_lt _ _ 0).
clear -He ; omega.
Qed.

Theorem generic_format_bpow_inv :
  forall e,
  generic_format (bpow e) ->
  (fexp e <= e)%Z.
Proof.
intros e He.
apply generic_format_bpow_inv' in He.
assert (H := valid_exp_large' (e + 1) e).
omega.
Qed.

Section Fcore_generic_round_pos.

(** Rounding functions: R -> Z *)

Variable rnd : R -> Z.

Class Valid_rnd := {
  Zrnd_le : forall x y, (x <= y)%R -> (rnd x <= rnd y)%Z ;
  Zrnd_Z2R : forall n, rnd (Z2R n) = n
}.

Context { valid_rnd : Valid_rnd }.

Theorem Zrnd_DN_or_UP :
  forall x, rnd x = Zfloor x \/ rnd x = Zceil x.
Proof.
intros x.
destruct (Zle_or_lt (rnd x) (Zfloor x)) as [Hx|Hx].
left.
apply Zle_antisym with (1 := Hx).
rewrite <- (Zrnd_Z2R (Zfloor x)).
apply Zrnd_le.
apply Zfloor_lb.
right.
apply Zle_antisym.
rewrite <- (Zrnd_Z2R (Zceil x)).
apply Zrnd_le.
apply Zceil_ub.
rewrite Zceil_floor_neq.
omega.
intros H.
rewrite <- H in Hx.
rewrite Zfloor_Z2R, Zrnd_Z2R in Hx.
apply Zlt_irrefl with (1 := Hx).
Qed.

Theorem Zrnd_ZR_or_AW :
  forall x, rnd x = Ztrunc x \/ rnd x = Zaway x.
Proof.
intros x.
unfold Ztrunc, Zaway.
destruct (Zrnd_DN_or_UP x) as [Hx|Hx] ;
  case Rlt_bool.
now right.
now left.
now left.
now right.
Qed.

(** the most useful one: R -> F *)
Definition round x :=
  F2R (Float beta (rnd (scaled_mantissa x)) (canonic_exp x)).

Theorem round_bounded_large_pos :
  forall x ex,
  (fexp ex < ex)%Z ->
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (bpow (ex - 1) <= round x <= bpow ex)%R.
Proof.
intros x ex He Hx.
unfold round, scaled_mantissa.
rewrite (canonic_exp_fexp_pos _ _ Hx).
unfold F2R. simpl.
destruct (Zrnd_DN_or_UP (x * bpow (- fexp ex))) as [Hr|Hr] ; rewrite Hr.
(* DN *)
split.
replace (ex - 1)%Z with (ex - 1 + - fexp ex + fexp ex)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (Hf: Z2R (Zpower beta (ex - 1 - fexp ex)) = bpow (ex - 1 + - fexp ex)).
apply Z2R_Zpower.
omega.
rewrite <- Hf.
apply Z2R_le.
apply Zfloor_lub.
rewrite Hf.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Hx.
apply Rle_trans with (2 := Rlt_le _ _ (proj2 Hx)).
apply Rmult_le_reg_r with (bpow (- fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
apply Zfloor_lb.
(* UP *)
split.
apply Rle_trans with (1 := proj1 Hx).
apply Rmult_le_reg_r with (bpow (- fexp ex)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
apply Zceil_ub.
pattern ex at 3 ; replace ex with (ex - fexp ex + fexp ex)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (Hf: Z2R (Zpower beta (ex - fexp ex)) = bpow (ex - fexp ex)).
apply Z2R_Zpower.
omega.
rewrite <- Hf.
apply Z2R_le.
apply Zceil_glb.
rewrite Hf.
unfold Zminus.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rlt_le.
apply Hx.
Qed.

Theorem round_bounded_small_pos :
  forall x ex,
  (ex <= fexp ex)%Z ->
  (bpow (ex - 1) <= x < bpow ex)%R ->
  round x = 0%R \/ round x = bpow (fexp ex).
Proof.
intros x ex He Hx.
unfold round, scaled_mantissa.
rewrite (canonic_exp_fexp_pos _ _ Hx).
unfold F2R. simpl.
destruct (Zrnd_DN_or_UP (x * bpow (-fexp ex))) as [Hr|Hr] ; rewrite Hr.
(* DN *)
left.
apply Rmult_eq_0_compat_r.
apply (@f_equal _ _ Z2R _ Z0).
apply Zfloor_imp.
refine (let H := _ in conj (Rlt_le _ _ (proj1 H)) (proj2 H)).
now apply mantissa_small_pos.
(* UP *)
right.
pattern (bpow (fexp ex)) at 2 ; rewrite <- Rmult_1_l.
apply (f_equal (fun m => (m * bpow (fexp ex))%R)).
apply (@f_equal _ _ Z2R _ 1%Z).
apply Zceil_imp.
refine (let H := _ in conj (proj1 H) (Rlt_le _ _ (proj2 H))).
now apply mantissa_small_pos.
Qed.

Theorem round_le_pos :
  forall x y, (0 < x)%R -> (x <= y)%R -> (round x <= round y)%R.
Proof.
intros x y Hx Hxy.
destruct (ln_beta beta x) as [ex Hex].
destruct (ln_beta beta y) as [ey Hey].
specialize (Hex (Rgt_not_eq _ _ Hx)).
specialize (Hey (Rgt_not_eq _ _ (Rlt_le_trans _ _ _ Hx Hxy))).
rewrite Rabs_pos_eq in Hex.
2: now apply Rlt_le.
rewrite Rabs_pos_eq in Hey.
2: apply Rle_trans with (2:=Hxy); now apply Rlt_le.
assert (He: (ex <= ey)%Z).
  apply bpow_lt_bpow with beta.
  apply Rle_lt_trans with (1 := proj1 Hex).
  now apply Rle_lt_trans with y.
assert (Heq: fexp ex = fexp ey -> (round x <= round y)%R).
  intros H.
  unfold round, scaled_mantissa, canonic_exp.
  rewrite ln_beta_unique_pos with (1 := Hex).
  rewrite ln_beta_unique_pos with (1 := Hey).
  rewrite H.
  apply F2R_le_compat.
  apply Zrnd_le.
  apply Rmult_le_compat_r with (2 := Hxy).
  apply bpow_ge_0.
destruct (Zle_or_lt ey (fexp ey)) as [Hy1|Hy1].
  apply Heq.
  apply valid_exp with (1 := Hy1).
  now apply Zle_trans with ey.
destruct (Zle_lt_or_eq _ _ He) as [He'|He'].
2: now apply Heq, f_equal.
apply Rle_trans with (bpow (ey - 1)).
2: now apply round_bounded_large_pos.
destruct (Zle_or_lt ex (fexp ex)) as [Hx1|Hx1].
  destruct (round_bounded_small_pos _ _ Hx1 Hex) as [-> | ->].
  apply bpow_ge_0.
  apply bpow_le.
  apply valid_exp, proj2 in Hx1.
  specialize (Hx1 ey).
  omega.
apply Rle_trans with (bpow ex).
now apply round_bounded_large_pos.
apply bpow_le.
now apply Z.lt_le_pred.
Qed.

Theorem round_generic :
  forall x,
  generic_format x ->
  round x = x.
Proof.
intros x Hx.
unfold round.
rewrite scaled_mantissa_generic with (1 := Hx).
rewrite Zrnd_Z2R.
now apply sym_eq.
Qed.

Theorem round_0 :
  round 0 = 0%R.
Proof.
unfold round, scaled_mantissa.
rewrite Rmult_0_l.
change 0%R with (Z2R 0).
rewrite Zrnd_Z2R.
apply F2R_0.
Qed.

Theorem exp_small_round_0_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  round x = 0%R -> (ex <= fexp ex)%Z .
Proof.
intros x ex H H1.
case (Zle_or_lt ex (fexp ex)); trivial; intros V.
contradict H1.
apply Rgt_not_eq.
apply Rlt_le_trans with (bpow (ex-1)).
apply bpow_gt_0.
apply (round_bounded_large_pos); assumption.
Qed.

Theorem generic_format_round_pos :
  forall x,
  (0 < x)%R ->
  generic_format (round x).
Proof.
intros x Hx0.
destruct (ln_beta beta x) as (ex, Hex).
specialize (Hex (Rgt_not_eq _ _ Hx0)).
rewrite Rabs_pos_eq in Hex. 2: now apply Rlt_le.
destruct (Zle_or_lt ex (fexp ex)) as [He|He].
(* small *)
destruct (round_bounded_small_pos _ _ He Hex) as [Hr|Hr] ; rewrite Hr.
apply generic_format_0.
apply generic_format_bpow.
now apply valid_exp.
(* large *)
generalize (round_bounded_large_pos _ _ He Hex).
intros (Hr1, Hr2).
destruct (Rle_or_lt (bpow ex) (round x)) as [Hr|Hr].
rewrite <- (Rle_antisym _ _ Hr Hr2).
apply generic_format_bpow.
now apply valid_exp.
apply generic_format_F2R.
intros _.
rewrite (canonic_exp_fexp_pos (F2R _) _ (conj Hr1 Hr)).
rewrite (canonic_exp_fexp_pos _ _ Hex).
now apply Zeq_le.
Qed.

End Fcore_generic_round_pos.

Theorem round_ext :
  forall rnd1 rnd2,
  ( forall x, rnd1 x = rnd2 x ) ->
  forall x,
  round rnd1 x = round rnd2 x.
Proof.
intros rnd1 rnd2 Hext x.
unfold round.
now rewrite Hext.
Qed.

Section Zround_opp.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Definition Zrnd_opp x := Zopp (rnd (-x)).

Global Instance valid_rnd_opp : Valid_rnd Zrnd_opp.
Proof with auto with typeclass_instances.
split.
(* *)
intros x y Hxy.
unfold Zrnd_opp.
apply Zopp_le_cancel.
rewrite 2!Zopp_involutive.
apply Zrnd_le...
now apply Ropp_le_contravar.
(* *)
intros n.
unfold Zrnd_opp.
rewrite <- Z2R_opp, Zrnd_Z2R...
apply Zopp_involutive.
Qed.

Theorem round_opp :
  forall x,
  round rnd (- x) = Ropp (round Zrnd_opp x).
Proof.
intros x.
unfold round.
rewrite <- F2R_Zopp, canonic_exp_opp, scaled_mantissa_opp.
apply F2R_eq_compat.
apply sym_eq.
exact (Zopp_involutive _).
Qed.

End Zround_opp.

(** IEEE-754 roundings: up, down and to zero *)

Global Instance valid_rnd_DN : Valid_rnd Zfloor.
Proof.
split.
apply Zfloor_le.
apply Zfloor_Z2R.
Qed.

Global Instance valid_rnd_UP : Valid_rnd Zceil.
Proof.
split.
apply Zceil_le.
apply Zceil_Z2R.
Qed.

Global Instance valid_rnd_ZR : Valid_rnd Ztrunc.
Proof.
split.
apply Ztrunc_le.
apply Ztrunc_Z2R.
Qed.

Global Instance valid_rnd_AW : Valid_rnd Zaway.
Proof.
split.
apply Zaway_le.
apply Zaway_Z2R.
Qed.

Section monotone.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_DN_or_UP :
  forall x,
  round rnd x = round Zfloor x \/ round rnd x = round Zceil x.
Proof.
intros x.
unfold round.
destruct (Zrnd_DN_or_UP rnd (scaled_mantissa x)) as [Hx|Hx].
left. now rewrite Hx.
right. now rewrite Hx.
Qed.

Theorem round_ZR_or_AW :
  forall x,
  round rnd x = round Ztrunc x \/ round rnd x = round Zaway x.
Proof.
intros x.
unfold round.
destruct (Zrnd_ZR_or_AW rnd (scaled_mantissa x)) as [Hx|Hx].
left. now rewrite Hx.
right. now rewrite Hx.
Qed.

Theorem round_le :
  forall x y, (x <= y)%R -> (round rnd x <= round rnd y)%R.
Proof with auto with typeclass_instances.
intros x y Hxy.
destruct (total_order_T x 0) as [[Hx|Hx]|Hx].
3: now apply round_le_pos.
(* x < 0 *)
unfold round.
destruct (Rlt_or_le y 0) as [Hy|Hy].
(* . y < 0 *)
rewrite <- (Ropp_involutive x), <- (Ropp_involutive y).
rewrite (scaled_mantissa_opp (-x)), (scaled_mantissa_opp (-y)).
rewrite (canonic_exp_opp (-x)), (canonic_exp_opp (-y)).
apply Ropp_le_cancel.
rewrite <- 2!F2R_Zopp.
apply (round_le_pos (Zrnd_opp rnd) (-y) (-x)).
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
now apply Ropp_le_contravar.
(* . 0 <= y *)
apply Rle_trans with 0%R.
apply F2R_le_0_compat. simpl.
rewrite <- (Zrnd_Z2R rnd 0).
apply Zrnd_le...
simpl.
rewrite <- (Rmult_0_l (bpow (- fexp (ln_beta beta x)))).
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply Rlt_le.
apply F2R_ge_0_compat. simpl.
rewrite <- (Zrnd_Z2R rnd 0).
apply Zrnd_le...
apply Rmult_le_pos.
exact Hy.
apply bpow_ge_0.
(* x = 0 *)
rewrite Hx.
rewrite round_0...
apply F2R_ge_0_compat.
simpl.
rewrite <- (Zrnd_Z2R rnd 0).
apply Zrnd_le...
apply Rmult_le_pos.
now rewrite <- Hx.
apply bpow_ge_0.
Qed.

Theorem round_ge_generic :
  forall x y, generic_format x -> (x <= y)%R -> (x <= round rnd y)%R.
Proof.
intros x y Hx Hxy.
rewrite <- (round_generic rnd x Hx).
now apply round_le.
Qed.

Theorem round_le_generic :
  forall x y, generic_format y -> (x <= y)%R -> (round rnd x <= y)%R.
Proof.
intros x y Hy Hxy.
rewrite <- (round_generic rnd y Hy).
now apply round_le.
Qed.

End monotone.

Theorem round_abs_abs :
  forall P : R -> R -> Prop,
  ( forall rnd (Hr : Valid_rnd rnd) x, (0 <= x)%R -> P x (round rnd x) ) ->
  forall rnd {Hr : Valid_rnd rnd} x, P (Rabs x) (Rabs (round rnd x)).
Proof with auto with typeclass_instances.
intros P HP rnd Hr x.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
(* . *)
rewrite 2!Rabs_pos_eq.
now apply HP.
rewrite <- (round_0 rnd).
now apply round_le.
exact Hx.
(* . *)
rewrite (Rabs_left _ Hx).
rewrite Rabs_left1.
pattern x at 2 ; rewrite <- Ropp_involutive.
rewrite round_opp.
rewrite Ropp_involutive.
apply HP...
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite <- (round_0 rnd).
apply round_le...
now apply Rlt_le.
Qed.

Theorem round_bounded_large :
  forall rnd {Hr : Valid_rnd rnd} x ex,
  (fexp ex < ex)%Z ->
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
  (bpow (ex - 1) <= Rabs (round rnd x) <= bpow ex)%R.
Proof with auto with typeclass_instances.
intros rnd Hr x ex He.
apply round_abs_abs...
clear rnd Hr x.
intros rnd' Hr x _.
apply round_bounded_large_pos...
Qed.

Theorem exp_small_round_0 :
  forall rnd {Hr : Valid_rnd rnd} x ex,
  (bpow (ex - 1) <= Rabs x < bpow ex)%R ->
   round rnd x = 0%R -> (ex <= fexp ex)%Z .
Proof.
intros rnd Hr x ex H1 H2.
generalize Rabs_R0.
rewrite <- H2 at 1.
apply (round_abs_abs (fun t rt => forall (ex : Z),
(bpow (ex - 1) <= t < bpow ex)%R ->
rt = 0%R -> (ex <= fexp ex)%Z)); trivial.
clear; intros rnd Hr x Hx.
now apply exp_small_round_0_pos.
Qed.




Section monotone_abs.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem abs_round_ge_generic :
  forall x y, generic_format x -> (x <= Rabs y)%R -> (x <= Rabs (round rnd y))%R.
Proof with auto with typeclass_instances.
intros x y.
apply round_abs_abs...
clear rnd valid_rnd y.
intros rnd' Hrnd y Hy.
apply round_ge_generic...
Qed.

Theorem abs_round_le_generic :
  forall x y, generic_format y -> (Rabs x <= y)%R -> (Rabs (round rnd x) <= y)%R.
Proof with auto with typeclass_instances.
intros x y.
apply round_abs_abs...
clear rnd valid_rnd x.
intros rnd' Hrnd x Hx.
apply round_le_generic...
Qed.

End monotone_abs.

Theorem round_DN_opp :
  forall x,
  round Zfloor (-x) = (- round Zceil x)%R.
Proof.
intros x.
unfold round.
rewrite scaled_mantissa_opp.
rewrite <- F2R_Zopp.
unfold Zceil.
rewrite Zopp_involutive.
now rewrite canonic_exp_opp.
Qed.

Theorem round_UP_opp :
  forall x,
  round Zceil (-x) = (- round Zfloor x)%R.
Proof.
intros x.
unfold round.
rewrite scaled_mantissa_opp.
rewrite <- F2R_Zopp.
unfold Zceil.
rewrite Ropp_involutive.
now rewrite canonic_exp_opp.
Qed.

Theorem round_ZR_opp :
  forall x,
  round Ztrunc (- x) = Ropp (round Ztrunc x).
Proof.
intros x.
unfold round.
rewrite scaled_mantissa_opp, canonic_exp_opp, Ztrunc_opp.
apply F2R_Zopp.
Qed.

Theorem round_ZR_abs :
  forall x,
  round Ztrunc (Rabs x) = Rabs (round Ztrunc x).
Proof with auto with typeclass_instances.
intros x.
apply sym_eq.
unfold Rabs at 2.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite round_ZR_opp.
apply Rabs_left1.
rewrite <- (round_0 Ztrunc).
apply round_le...
now apply Rlt_le.
apply Rabs_pos_eq.
rewrite <- (round_0 Ztrunc).
apply round_le...
now apply Rge_le.
Qed.

Theorem round_AW_opp :
  forall x,
  round Zaway (- x) = Ropp (round Zaway x).
Proof.
intros x.
unfold round.
rewrite scaled_mantissa_opp, canonic_exp_opp, Zaway_opp.
apply F2R_Zopp.
Qed.

Theorem round_AW_abs :
  forall x,
  round Zaway (Rabs x) = Rabs (round Zaway x).
Proof with auto with typeclass_instances.
intros x.
apply sym_eq.
unfold Rabs at 2.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite round_AW_opp.
apply Rabs_left1.
rewrite <- (round_0 Zaway).
apply round_le...
now apply Rlt_le.
apply Rabs_pos_eq.
rewrite <- (round_0 Zaway).
apply round_le...
now apply Rge_le.
Qed.

Theorem round_ZR_pos :
  forall x,
  (0 <= x)%R ->
  round Ztrunc x = round Zfloor x.
Proof.
intros x Hx.
unfold round, Ztrunc.
case Rlt_bool_spec.
intros H.
elim Rlt_not_le with (1 := H).
rewrite <- (Rmult_0_l (bpow (- canonic_exp x))).
apply Rmult_le_compat_r with (2 := Hx).
apply bpow_ge_0.
easy.
Qed.

Theorem round_ZR_neg :
  forall x,
  (x <= 0)%R ->
  round Ztrunc x = round Zceil x.
Proof.
intros x Hx.
unfold round, Ztrunc.
case Rlt_bool_spec.
easy.
intros [H|H].
elim Rlt_not_le with (1 := H).
rewrite <- (Rmult_0_l (bpow (- canonic_exp x))).
apply Rmult_le_compat_r with (2 := Hx).
apply bpow_ge_0.
rewrite <- H.
change 0%R with (Z2R 0).
now rewrite Zfloor_Z2R, Zceil_Z2R.
Qed.

Theorem round_AW_pos :
  forall x,
  (0 <= x)%R ->
  round Zaway x = round Zceil x.
Proof.
intros x Hx.
unfold round, Zaway.
case Rlt_bool_spec.
intros H.
elim Rlt_not_le with (1 := H).
rewrite <- (Rmult_0_l (bpow (- canonic_exp x))).
apply Rmult_le_compat_r with (2 := Hx).
apply bpow_ge_0.
easy.
Qed.

Theorem round_AW_neg :
  forall x,
  (x <= 0)%R ->
  round Zaway x = round Zfloor x.
Proof.
intros x Hx.
unfold round, Zaway.
case Rlt_bool_spec.
easy.
intros [H|H].
elim Rlt_not_le with (1 := H).
rewrite <- (Rmult_0_l (bpow (- canonic_exp x))).
apply Rmult_le_compat_r with (2 := Hx).
apply bpow_ge_0.
rewrite <- H.
change 0%R with (Z2R 0).
now rewrite Zfloor_Z2R, Zceil_Z2R.
Qed.

Theorem generic_format_round :
  forall rnd { Hr : Valid_rnd rnd } x,
  generic_format (round rnd x).
Proof with auto with typeclass_instances.
intros rnd Zrnd x.
destruct (total_order_T x 0) as [[Hx|Hx]|Hx].
rewrite <- (Ropp_involutive x).
destruct (round_DN_or_UP rnd (- - x)) as [Hr|Hr] ; rewrite Hr.
rewrite round_DN_opp.
apply generic_format_opp.
apply generic_format_round_pos...
now apply Ropp_0_gt_lt_contravar.
rewrite round_UP_opp.
apply generic_format_opp.
apply generic_format_round_pos...
now apply Ropp_0_gt_lt_contravar.
rewrite Hx.
rewrite round_0...
apply generic_format_0.
now apply generic_format_round_pos.
Qed.

Theorem round_DN_pt :
  forall x,
  Rnd_DN_pt generic_format x (round Zfloor x).
Proof with auto with typeclass_instances.
intros x.
split.
apply generic_format_round...
split.
pattern x at 2 ; rewrite <- scaled_mantissa_mult_bpow.
unfold round, F2R. simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Zfloor_lb.
intros g Hg Hgx.
apply round_ge_generic...
Qed.

Theorem generic_format_satisfies_any :
  satisfies_any generic_format.
Proof.
split.
(* symmetric set *)
exact generic_format_0.
exact generic_format_opp.
(* round down *)
intros x.
eexists.
apply round_DN_pt.
Qed.

Theorem round_UP_pt :
  forall x,
  Rnd_UP_pt generic_format x (round Zceil x).
Proof.
intros x.
rewrite <- (Ropp_involutive x).
rewrite round_UP_opp.
apply Rnd_DN_UP_pt_sym.
apply generic_format_opp.
apply round_DN_pt.
Qed.

Theorem round_ZR_pt :
  forall x,
  Rnd_ZR_pt generic_format x (round Ztrunc x).
Proof.
intros x.
split ; intros Hx.
rewrite round_ZR_pos with (1 := Hx).
apply round_DN_pt.
rewrite round_ZR_neg with (1 := Hx).
apply round_UP_pt.
Qed.

Theorem round_DN_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  round Zfloor x = 0%R.
Proof.
intros x ex Hx He.
rewrite <- (F2R_0 beta (canonic_exp x)).
rewrite <- mantissa_DN_small_pos with (1 := Hx) (2 := He).
now rewrite <- canonic_exp_fexp_pos with (1 := Hx).
Qed.


Theorem round_DN_UP_lt :
  forall x, ~ generic_format x ->
  (round Zfloor x < x < round Zceil x)%R.
Proof with auto with typeclass_instances.
intros x Fx.
assert (Hx:(round  Zfloor x <= x <= round Zceil x)%R).
split.
apply round_DN_pt.
apply round_UP_pt.
split.
  destruct Hx as [Hx _].
  apply Rnot_le_lt; intro Hle.
  assert (x = round Zfloor x) by now apply Rle_antisym.
  rewrite H in Fx.
  contradict Fx.
  apply generic_format_round...
destruct Hx as [_ Hx].
apply Rnot_le_lt; intro Hle.
assert (x = round Zceil x) by now apply Rle_antisym.
rewrite H in Fx.
contradict Fx.
apply generic_format_round...
Qed.

Theorem round_UP_small_pos :
  forall x ex,
  (bpow (ex - 1) <= x < bpow ex)%R ->
  (ex <= fexp ex)%Z ->
  round Zceil x = (bpow (fexp ex)).
Proof.
intros x ex Hx He.
rewrite <- F2R_bpow.
rewrite <- mantissa_UP_small_pos with (1 := Hx) (2 := He).
now rewrite <- canonic_exp_fexp_pos with (1 := Hx).
Qed.

Theorem generic_format_EM :
  forall x,
  generic_format x \/ ~generic_format x.
Proof with auto with typeclass_instances.
intros x.
destruct (Req_dec (round Zfloor x) x) as [Hx|Hx].
left.
rewrite <- Hx.
apply generic_format_round...
right.
intros H.
apply Hx.
apply round_generic...
Qed.

Section round_large.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_large_pos_ge_pow :
  forall x e,
  (0 < round rnd x)%R ->
  (bpow e <= x)%R ->
  (bpow e <= round rnd x)%R.
Proof.
intros x e Hd Hex.
destruct (ln_beta beta x) as (ex, He).
assert (Hx: (0 < x)%R).
apply Rlt_le_trans with (2 := Hex).
apply bpow_gt_0.
specialize (He (Rgt_not_eq _ _ Hx)).
rewrite Rabs_pos_eq in He. 2: now apply Rlt_le.
apply Rle_trans with (bpow (ex - 1)).
apply bpow_le.
cut (e < ex)%Z. omega.
apply (lt_bpow beta).
now apply Rle_lt_trans with (2 := proj2 He).
destruct (Zle_or_lt ex (fexp ex)).
destruct (round_bounded_small_pos rnd x ex H He) as [Hr|Hr].
rewrite Hr in Hd.
elim Rlt_irrefl with (1 := Hd).
rewrite Hr.
apply bpow_le.
omega.
apply (round_bounded_large_pos rnd x ex H He).
Qed.

End round_large.

Theorem ln_beta_round_ZR :
  forall x,
  (round Ztrunc x <> 0)%R ->
  (ln_beta beta (round Ztrunc x) = ln_beta beta x :> Z).
Proof with auto with typeclass_instances.
intros x Zr.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, round_0...
apply ln_beta_unique.
destruct (ln_beta beta x) as (ex, Ex) ; simpl.
specialize (Ex Zx).
rewrite <- round_ZR_abs.
split.
apply round_large_pos_ge_pow...
rewrite round_ZR_abs.
now apply Rabs_pos_lt.
apply Ex.
apply Rle_lt_trans with (2 := proj2 Ex).
rewrite round_ZR_pos.
apply round_DN_pt.
apply Rabs_pos.
Qed.

Theorem ln_beta_round :
  forall rnd {Hrnd : Valid_rnd rnd} x,
  (round rnd x <> 0)%R ->
  (ln_beta beta (round rnd x) = ln_beta beta x :> Z) \/
  Rabs (round rnd x) = bpow (Zmax (ln_beta beta x) (fexp (ln_beta beta x))).
Proof with auto with typeclass_instances.
intros rnd Hrnd x.
destruct (round_ZR_or_AW rnd x) as [Hr|Hr] ; rewrite Hr ; clear Hr rnd Hrnd.
left.
now apply ln_beta_round_ZR.
intros Zr.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, round_0...
destruct (ln_beta beta x) as (ex, Ex) ; simpl.
specialize (Ex Zx).
rewrite <- ln_beta_abs.
rewrite <- round_AW_abs.
destruct (Zle_or_lt ex (fexp ex)) as [He|He].
right.
rewrite Zmax_r with (1 := He).
rewrite round_AW_pos with (1 := Rabs_pos _).
now apply round_UP_small_pos.
destruct (round_bounded_large_pos Zaway _ ex He Ex) as (H1,[H2|H2]).
left.
apply ln_beta_unique.
rewrite <- round_AW_abs, Rabs_Rabsolu.
now split.
right.
now rewrite Zmax_l with (1 := Zlt_le_weak _ _ He).
Qed.

Theorem ln_beta_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  (ln_beta beta (round Zfloor x) = ln_beta beta x :> Z).
Proof.
intros x Hd.
assert (0 < x)%R.
apply Rlt_le_trans with (1 := Hd).
apply round_DN_pt.
revert Hd.
rewrite <- round_ZR_pos.
intros Hd.
apply ln_beta_round_ZR.
now apply Rgt_not_eq.
now apply Rlt_le.
Qed.

Theorem canonic_exp_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  canonic_exp (round Zfloor x) = canonic_exp x.
Proof.
intros x Hd.
apply (f_equal fexp).
now apply ln_beta_DN.
Qed.

Theorem scaled_mantissa_DN :
  forall x,
  (0 < round Zfloor x)%R ->
  scaled_mantissa (round Zfloor x) = Z2R (Zfloor (scaled_mantissa x)).
Proof.
intros x Hd.
unfold scaled_mantissa.
rewrite canonic_exp_DN with (1 := Hd).
unfold round, F2R. simpl.
now rewrite Rmult_assoc, <- bpow_plus, Zplus_opp_r, Rmult_1_r.
Qed.

Theorem generic_N_pt_DN_or_UP :
  forall x f,
  Rnd_N_pt generic_format x f ->
  f = round Zfloor x \/ f = round Zceil x.
Proof.
intros x f Hxf.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf).
left.
apply Rnd_DN_pt_unicity with (1 := H).
apply round_DN_pt.
right.
apply Rnd_UP_pt_unicity with (1 := H).
apply round_UP_pt.
Qed.

Section not_FTZ.

Class Exp_not_FTZ :=
  exp_not_FTZ : forall e, (fexp (fexp e + 1) <= fexp e)%Z.

Context { exp_not_FTZ_ : Exp_not_FTZ }.

Theorem subnormal_exponent :
  forall e x,
  (e <= fexp e)%Z ->
  generic_format x ->
  x = F2R (Float beta (Ztrunc (x * bpow (- fexp e))) (fexp e)).
Proof.
intros e x He Hx.
pattern x at 2 ; rewrite Hx.
unfold F2R at 2. simpl.
rewrite Rmult_assoc, <- bpow_plus.
assert (H: Z2R (Zpower beta (canonic_exp x + - fexp e)) = bpow (canonic_exp x + - fexp e)).
apply Z2R_Zpower.
unfold canonic_exp.
set (ex := ln_beta beta x).
generalize (exp_not_FTZ ex).
generalize (proj2 (proj2 (valid_exp _) He) (fexp ex + 1)%Z).
omega.
rewrite <- H.
rewrite <- Z2R_mult, Ztrunc_Z2R.
unfold F2R. simpl.
rewrite Z2R_mult.
rewrite H.
rewrite Rmult_assoc, <- bpow_plus.
now ring_simplify (canonic_exp x + - fexp e + fexp e)%Z.
Qed.

End not_FTZ.

Section monotone_exp.

Class Monotone_exp :=
  monotone_exp : forall ex ey, (ex <= ey)%Z -> (fexp ex <= fexp ey)%Z.

Context { monotone_exp_ : Monotone_exp }.

Global Instance monotone_exp_not_FTZ : Exp_not_FTZ.
Proof.
intros e.
destruct (Z_lt_le_dec (fexp e) e) as [He|He].
apply monotone_exp.
now apply Zlt_le_succ.
now apply valid_exp.
Qed.

Lemma canonic_exp_le_bpow :
  forall (x : R) (e : Z),
  x <> 0%R ->
  (Rabs x < bpow e)%R ->
  (canonic_exp x <= fexp e)%Z.
Proof.
intros x e Zx Hx.
apply monotone_exp.
now apply ln_beta_le_bpow.
Qed.

Lemma canonic_exp_ge_bpow :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= Rabs x)%R ->
  (fexp e <= canonic_exp x)%Z.
Proof.
intros x e Hx.
apply monotone_exp.
rewrite (Zsucc_pred e).
apply Zlt_le_succ.
now apply ln_beta_gt_bpow.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem ln_beta_round_ge :
  forall x,
  round rnd x <> 0%R ->
  (ln_beta beta x <= ln_beta beta (round rnd x))%Z.
Proof with auto with typeclass_instances.
intros x.
destruct (round_ZR_or_AW rnd x) as [H|H] ; rewrite H ; clear H ; intros Zr.
rewrite ln_beta_round_ZR with (1 := Zr).
apply Zle_refl.
apply ln_beta_le_abs.
contradict Zr.
rewrite Zr.
apply round_0...
rewrite <- round_AW_abs.
rewrite round_AW_pos.
apply round_UP_pt.
apply Rabs_pos.
Qed.

Theorem canonic_exp_round_ge :
  forall x,
  round rnd x <> 0%R ->
  (canonic_exp x <= canonic_exp (round rnd x))%Z.
Proof with auto with typeclass_instances.
intros x Zr.
unfold canonic_exp.
apply monotone_exp.
now apply ln_beta_round_ge.
Qed.

End monotone_exp.

Section Znearest.

(** Roundings to nearest: when in the middle, use the choice function *)
Variable choice : Z -> bool.

Definition Znearest x :=
  match Rcompare (x - Z2R (Zfloor x)) (/2) with
  | Lt => Zfloor x
  | Eq => if choice (Zfloor x) then Zceil x else Zfloor x
  | Gt => Zceil x
  end.

Theorem Znearest_DN_or_UP :
  forall x,
  Znearest x = Zfloor x \/ Znearest x = Zceil x.
Proof.
intros x.
unfold Znearest.
case Rcompare_spec ; intros _.
now left.
case choice.
now right.
now left.
now right.
Qed.

Theorem Znearest_ge_floor :
  forall x,
  (Zfloor x <= Znearest x)%Z.
Proof.
intros x.
destruct (Znearest_DN_or_UP x) as [Hx|Hx] ; rewrite Hx.
apply Zle_refl.
apply le_Z2R.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
Qed.

Theorem Znearest_le_ceil :
  forall x,
  (Znearest x <= Zceil x)%Z.
Proof.
intros x.
destruct (Znearest_DN_or_UP x) as [Hx|Hx] ; rewrite Hx.
apply le_Z2R.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
apply Zle_refl.
Qed.

Global Instance valid_rnd_N : Valid_rnd Znearest.
Proof.
split.
(* *)
intros x y Hxy.
destruct (Rle_or_lt (Z2R (Zceil x)) y) as [H|H].
apply Zle_trans with (1 := Znearest_le_ceil x).
apply Zle_trans with (2 := Znearest_ge_floor y).
now apply Zfloor_lub.
(* . *)
assert (Hf: Zfloor y = Zfloor x).
apply Zfloor_imp.
split.
apply Rle_trans with (2 := Zfloor_lb y).
apply Z2R_le.
now apply Zfloor_le.
apply Rlt_le_trans with (1 := H).
apply Z2R_le.
apply Zceil_glb.
apply Rlt_le.
rewrite Z2R_plus.
apply Zfloor_ub.
(* . *)
unfold Znearest at 1.
case Rcompare_spec ; intro Hx.
(* .. *)
rewrite <- Hf.
apply Znearest_ge_floor.
(* .. *)
unfold Znearest.
rewrite Hf.
case Rcompare_spec ; intro Hy.
elim Rlt_not_le with (1 := Hy).
rewrite <- Hx.
now apply Rplus_le_compat_r.
replace y with x.
apply Zle_refl.
apply Rplus_eq_reg_l with (- Z2R (Zfloor x))%R.
rewrite 2!(Rplus_comm (- (Z2R (Zfloor x)))).
change (x - Z2R (Zfloor x) = y - Z2R (Zfloor x))%R.
now rewrite Hy.
apply Zle_trans with (Zceil x).
case choice.
apply Zle_refl.
apply le_Z2R.
apply Rle_trans with x.
apply Zfloor_lb.
apply Zceil_ub.
now apply Zceil_le.
(* .. *)
unfold Znearest.
rewrite Hf.
rewrite Rcompare_Gt.
now apply Zceil_le.
apply Rlt_le_trans with (1 := Hx).
now apply Rplus_le_compat_r.
(* *)
intros n.
unfold Znearest.
rewrite Zfloor_Z2R.
rewrite Rcompare_Lt.
easy.
unfold Rminus.
rewrite Rplus_opp_r.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
Qed.

Theorem Rcompare_floor_ceil_mid :
  forall x,
  Z2R (Zfloor x) <> x ->
  Rcompare (x - Z2R (Zfloor x)) (/ 2) = Rcompare (x - Z2R (Zfloor x)) (Z2R (Zceil x) - x).
Proof.
intros x Hx.
rewrite Zceil_floor_neq with (1 := Hx).
rewrite Z2R_plus. simpl.
destruct (Rcompare_spec (x - Z2R (Zfloor x)) (/ 2)) as [H1|H1|H1] ; apply sym_eq.
(* . *)
apply Rcompare_Lt.
apply Rplus_lt_reg_l with (x - Z2R (Zfloor x))%R.
replace (x - Z2R (Zfloor x) + (x - Z2R (Zfloor x)))%R with ((x - Z2R (Zfloor x)) * 2)%R by ring.
replace (x - Z2R (Zfloor x) + (Z2R (Zfloor x) + 1 - x))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply (Z2R_lt 0 2).
(* . *)
apply Rcompare_Eq.
replace (Z2R (Zfloor x) + 1 - x)%R with (1 - (x - Z2R (Zfloor x)))%R by ring.
rewrite H1.
field.
(* . *)
apply Rcompare_Gt.
apply Rplus_lt_reg_l with (x - Z2R (Zfloor x))%R.
replace (x - Z2R (Zfloor x) + (x - Z2R (Zfloor x)))%R with ((x - Z2R (Zfloor x)) * 2)%R by ring.
replace (x - Z2R (Zfloor x) + (Z2R (Zfloor x) + 1 - x))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply (Z2R_lt 0 2).
Qed.

Theorem Rcompare_ceil_floor_mid :
  forall x,
  Z2R (Zfloor x) <> x ->
  Rcompare (Z2R (Zceil x) - x) (/ 2) = Rcompare (Z2R (Zceil x) - x) (x - Z2R (Zfloor x)).
Proof.
intros x Hx.
rewrite Zceil_floor_neq with (1 := Hx).
rewrite Z2R_plus. simpl.
destruct (Rcompare_spec (Z2R (Zfloor x) + 1 - x) (/ 2)) as [H1|H1|H1] ; apply sym_eq.
(* . *)
apply Rcompare_Lt.
apply Rplus_lt_reg_l with (Z2R (Zfloor x) + 1 - x)%R.
replace (Z2R (Zfloor x) + 1 - x + (Z2R (Zfloor x) + 1 - x))%R with ((Z2R (Zfloor x) + 1 - x) * 2)%R by ring.
replace (Z2R (Zfloor x) + 1 - x + (x - Z2R (Zfloor x)))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply (Z2R_lt 0 2).
(* . *)
apply Rcompare_Eq.
replace (x - Z2R (Zfloor x))%R with (1 - (Z2R (Zfloor x) + 1 - x))%R by ring.
rewrite H1.
field.
(* . *)
apply Rcompare_Gt.
apply Rplus_lt_reg_l with (Z2R (Zfloor x) + 1 - x)%R.
replace (Z2R (Zfloor x) + 1 - x + (Z2R (Zfloor x) + 1 - x))%R with ((Z2R (Zfloor x) + 1 - x) * 2)%R by ring.
replace (Z2R (Zfloor x) + 1 - x + (x - Z2R (Zfloor x)))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply (Z2R_lt 0 2).
Qed.

Theorem Znearest_N_strict :
  forall x,
  (x - Z2R (Zfloor x) <> /2)%R ->
  (Rabs (x - Z2R (Znearest x)) < /2)%R.
Proof.
intros x Hx.
unfold Znearest.
case Rcompare_spec ; intros H.
rewrite Rabs_pos_eq.
exact H.
apply Rle_0_minus.
apply Zfloor_lb.
now elim Hx.
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
rewrite Zceil_floor_neq.
rewrite Z2R_plus.
simpl.
apply Ropp_lt_cancel.
apply Rplus_lt_reg_l with 1%R.
replace (1 + -/2)%R with (/2)%R by field.
now replace (1 + - (Z2R (Zfloor x) + 1 - x))%R with (x - Z2R (Zfloor x))%R by ring.
apply Rlt_not_eq.
apply Rplus_lt_reg_l with (- Z2R (Zfloor x))%R.
apply Rlt_trans with (/2)%R.
rewrite Rplus_opp_l.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
now rewrite <- (Rplus_comm x).
apply Rle_minus.
apply Zceil_ub.
Qed.

Theorem Znearest_N :
  forall x,
  (Rabs (x - Z2R (Znearest x)) <= /2)%R.
Proof.
intros x.
destruct (Req_dec (x - Z2R (Zfloor x)) (/2)) as [Hx|Hx].
assert (K: (Rabs (/2) <= /2)%R).
apply Req_le.
apply Rabs_pos_eq.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
destruct (Znearest_DN_or_UP x) as [H|H] ; rewrite H ; clear H.
now rewrite Hx.
rewrite Zceil_floor_neq.
rewrite Z2R_plus.
simpl.
replace (x - (Z2R (Zfloor x) + 1))%R with (x - Z2R (Zfloor x) - 1)%R by ring.
rewrite Hx.
rewrite Rabs_minus_sym.
now replace (1 - /2)%R with (/2)%R by field.
apply Rlt_not_eq.
apply Rplus_lt_reg_l with (- Z2R (Zfloor x))%R.
rewrite Rplus_opp_l, Rplus_comm.
fold (x - Z2R (Zfloor x))%R.
rewrite Hx.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply Rlt_le.
now apply Znearest_N_strict.
Qed.

Theorem Znearest_imp :
  forall x n,
  (Rabs (x - Z2R n) < /2)%R ->
  Znearest x = n.
Proof.
intros x n Hd.
cut (Zabs (Znearest x - n) < 1)%Z.
clear ; zify ; omega.
apply lt_Z2R.
rewrite Z2R_abs, Z2R_minus.
replace (Z2R (Znearest x) - Z2R n)%R with (- (x - Z2R (Znearest x)) + (x - Z2R n))%R by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
simpl.
replace 1%R with (/2 + /2)%R by field.
apply Rplus_le_lt_compat with (2 := Hd).
rewrite Rabs_Ropp.
apply Znearest_N.
Qed.

Theorem round_N_pt :
  forall x,
  Rnd_N_pt generic_format x (round Znearest x).
Proof.
intros x.
set (d := round Zfloor x).
set (u := round Zceil x).
set (mx := scaled_mantissa x).
set (bx := bpow (canonic_exp x)).
(* . *)
assert (H: (Rabs (round Znearest x - x) <= Rmin (x - d) (u - x))%R).
pattern x at -1 ; rewrite <- scaled_mantissa_mult_bpow.
unfold d, u, round, F2R. simpl.
fold mx bx.
rewrite <- 3!Rmult_minus_distr_r.
rewrite Rabs_mult, (Rabs_pos_eq bx). 2: apply bpow_ge_0.
rewrite <- Rmult_min_distr_r. 2: apply bpow_ge_0.
apply Rmult_le_compat_r.
apply bpow_ge_0.
unfold Znearest.
destruct (Req_dec (Z2R (Zfloor mx)) mx) as [Hm|Hm].
(* .. *)
rewrite Hm.
unfold Rminus at 2.
rewrite Rplus_opp_r.
rewrite Rcompare_Lt.
rewrite Hm.
unfold Rminus at -3.
rewrite Rplus_opp_r.
rewrite Rabs_R0.
unfold Rmin.
destruct (Rle_dec 0 (Z2R (Zceil mx) - mx)) as [H|H].
apply Rle_refl.
apply Rle_0_minus.
apply Zceil_ub.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
(* .. *)
rewrite Rcompare_floor_ceil_mid with (1 := Hm).
rewrite Rmin_compare.
assert (H: (Rabs (mx - Z2R (Zfloor mx)) <= mx - Z2R (Zfloor mx))%R).
rewrite Rabs_pos_eq.
apply Rle_refl.
apply Rle_0_minus.
apply Zfloor_lb.
case Rcompare_spec ; intros Hm'.
now rewrite Rabs_minus_sym.
case choice.
rewrite <- Hm'.
exact H.
now rewrite Rabs_minus_sym.
rewrite Rabs_pos_eq.
apply Rle_refl.
apply Rle_0_minus.
apply Zceil_ub.
(* . *)
apply Rnd_DN_UP_pt_N with d u.
apply generic_format_round.
auto with typeclass_instances.
now apply round_DN_pt.
now apply round_UP_pt.
apply Rle_trans with (1 := H).
apply Rmin_l.
apply Rle_trans with (1 := H).
apply Rmin_r.
Qed.

Theorem round_N_middle :
  forall x,
  (x - round Zfloor x = round Zceil x - x)%R ->
  round Znearest x = if choice (Zfloor (scaled_mantissa x)) then round Zceil x else round Zfloor x.
Proof.
intros x.
pattern x at 1 4 ; rewrite <- scaled_mantissa_mult_bpow.
unfold round, Znearest, F2R. simpl.
destruct (Req_dec (Z2R (Zfloor (scaled_mantissa x))) (scaled_mantissa x)) as [Fx|Fx].
(* *)
intros _.
rewrite <- Fx.
rewrite Zceil_Z2R, Zfloor_Z2R.
set (m := Zfloor (scaled_mantissa x)).
now case (Rcompare (Z2R m - Z2R m) (/ 2)) ; case (choice m).
(* *)
intros H.
rewrite Rcompare_floor_ceil_mid with (1 := Fx).
rewrite Rcompare_Eq.
now case choice.
apply Rmult_eq_reg_r with (bpow (canonic_exp x)).
now rewrite 2!Rmult_minus_distr_r.
apply Rgt_not_eq.
apply bpow_gt_0.
Qed.

Lemma round_N_really_small_pos :
  forall x,
  forall ex,
  (Fcore_Raux.bpow beta (ex - 1) <= x < Fcore_Raux.bpow beta ex)%R ->
  (ex < fexp ex)%Z ->
  (round Znearest x = 0)%R.
Proof.
intros x ex Hex Hf.
unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
apply (Rmult_eq_reg_r (bpow (- fexp (ln_beta beta x))));
  [|now apply Rgt_not_eq; apply bpow_gt_0].
rewrite Rmult_0_l, Rmult_assoc, <- bpow_plus.
replace (_ + - _)%Z with 0%Z by ring; simpl; rewrite Rmult_1_r.
change 0%R with (Z2R 0); apply f_equal.
apply Znearest_imp.
simpl; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
assert (H : (x >= 0)%R).
{ apply Rle_ge; apply Rle_trans with (bpow (ex - 1)); [|exact (proj1 Hex)].
  now apply bpow_ge_0. }
assert (H' : (x * bpow (- fexp (ln_beta beta x)) >= 0)%R).
{ apply Rle_ge; apply Rmult_le_pos.
  - now apply Rge_le.
  - now apply bpow_ge_0. }
rewrite Rabs_right; [|exact H'].
apply (Rmult_lt_reg_r (bpow (fexp (ln_beta beta x)))); [now apply bpow_gt_0|].
rewrite Rmult_assoc, <- bpow_plus.
replace (- _ + _)%Z with 0%Z by ring; simpl; rewrite Rmult_1_r.
apply (Rlt_le_trans _ _ _ (proj2 Hex)).
apply Rle_trans with (bpow (fexp (ln_beta beta x) - 1)).
- apply bpow_le.
  rewrite (ln_beta_unique beta x ex); [omega|].
  now rewrite Rabs_right.
- unfold Zminus; rewrite bpow_plus.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r; [now apply bpow_ge_0|].
  unfold Fcore_Raux.bpow, Z.pow_pos; simpl.
  rewrite Zmult_1_r.
  apply Rinv_le; [exact Rlt_0_2|].
  change 2%R with (Z2R 2); apply Z2R_le.
  destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le.
Qed.

End Znearest.

Section rndNA.

Global Instance valid_rnd_NA : Valid_rnd (Znearest (Zle_bool 0)) := valid_rnd_N _.

Theorem round_NA_pt :
  forall x,
  Rnd_NA_pt generic_format x (round (Znearest (Zle_bool 0)) x).
Proof.
intros x.
generalize (round_N_pt (Zle_bool 0) x).
set (f := round (Znearest (Zle_bool 0)) x).
intros Rxf.
destruct (Req_dec (x - round Zfloor x) (round Zceil x - x)) as [Hm|Hm].
(* *)
apply Rnd_NA_N_pt.
exact generic_format_0.
exact Rxf.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
(* . *)
rewrite Rabs_pos_eq with (1 := Hx).
rewrite Rabs_pos_eq.
unfold f.
rewrite round_N_middle with (1 := Hm).
rewrite Zle_bool_true.
apply (round_UP_pt x).
apply Zfloor_lub.
apply Rmult_le_pos with (1 := Hx).
apply bpow_ge_0.
apply Rnd_N_pt_pos with (2 := Hx) (3 := Rxf).
exact generic_format_0.
(* . *)
rewrite Rabs_left with (1 := Hx).
rewrite Rabs_left1.
apply Ropp_le_contravar.
unfold f.
rewrite round_N_middle with (1 := Hm).
rewrite Zle_bool_false.
apply (round_DN_pt x).
apply lt_Z2R.
apply Rle_lt_trans with (scaled_mantissa x).
apply Zfloor_lb.
simpl.
rewrite <- (Rmult_0_l (bpow (- canonic_exp x))).
apply Rmult_lt_compat_r with (2 := Hx).
apply bpow_gt_0.
apply Rnd_N_pt_neg with (3 := Rxf).
exact generic_format_0.
now apply Rlt_le.
(* *)
split.
apply Rxf.
intros g Rxg.
rewrite Rnd_N_pt_unicity with (3 := Hm) (4 := Rxf) (5 := Rxg).
apply Rle_refl.
apply round_DN_pt.
apply round_UP_pt.
Qed.

End rndNA.

Section rndN_opp.

Theorem Znearest_opp :
  forall choice x,
  Znearest choice (- x) = (- Znearest (fun t => negb (choice (- (t + 1))%Z)) x)%Z.
Proof with auto with typeclass_instances.
intros choice x.
destruct (Req_dec (Z2R (Zfloor x)) x) as [Hx|Hx].
rewrite <- Hx.
rewrite <- Z2R_opp.
rewrite 2!Zrnd_Z2R...
unfold Znearest.
replace (- x - Z2R (Zfloor (-x)))%R with (Z2R (Zceil x) - x)%R.
rewrite Rcompare_ceil_floor_mid with (1 := Hx).
rewrite Rcompare_floor_ceil_mid with (1 := Hx).
rewrite Rcompare_sym.
rewrite <- Zceil_floor_neq with (1 := Hx).
unfold Zceil.
rewrite Ropp_involutive.
case Rcompare ; simpl ; trivial.
rewrite Zopp_involutive.
case (choice (Zfloor (- x))) ; simpl ; trivial.
now rewrite Zopp_involutive.
now rewrite Zopp_involutive.
unfold Zceil.
rewrite Z2R_opp.
apply Rplus_comm.
Qed.

Theorem round_N_opp :
  forall choice,
  forall x,
  round (Znearest choice) (-x) = (- round (Znearest (fun t => negb (choice (- (t + 1))%Z))) x)%R.
Proof.
intros choice x.
unfold round, F2R. simpl.
rewrite canonic_exp_opp.
rewrite scaled_mantissa_opp.
rewrite Znearest_opp.
rewrite Z2R_opp.
now rewrite Ropp_mult_distr_l_reverse.
Qed.

End rndN_opp.

End Format.

(** Inclusion of a format into an extended format *)
Section Inclusion.

Variables fexp1 fexp2 : Z -> Z.

Context { valid_exp1 : Valid_exp fexp1 }.
Context { valid_exp2 : Valid_exp fexp2 }.

Theorem generic_inclusion_ln_beta :
  forall x,
  ( x <> R0 -> (fexp2 (ln_beta beta x) <= fexp1 (ln_beta beta x))%Z ) ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof.
intros x He Fx.
rewrite Fx.
apply generic_format_F2R.
intros Zx.
rewrite <- Fx.
apply He.
contradict Zx.
rewrite Zx, scaled_mantissa_0.
apply (Ztrunc_Z2R 0).
Qed.

Theorem generic_inclusion_lt_ge :
  forall e1 e2,
  ( forall e, (e1 < e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x < bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof.
intros e1 e2 He x (Hx1,Hx2).
apply generic_inclusion_ln_beta.
intros Zx.
apply He.
split.
now apply ln_beta_gt_bpow.
now apply ln_beta_le_bpow.
Qed.

Theorem generic_inclusion :
  forall e,
  (fexp2 e <= fexp1 e)%Z ->
  forall x,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof with auto with typeclass_instances.
intros e He x (Hx1,[Hx2|Hx2]).
apply generic_inclusion_ln_beta.
now rewrite ln_beta_unique with (1 := conj Hx1 Hx2).
intros Fx.
apply generic_format_abs_inv.
rewrite Hx2.
apply generic_format_bpow'...
apply Zle_trans with (1 := He).
apply generic_format_bpow_inv...
rewrite <- Hx2.
now apply generic_format_abs.
Qed.

Theorem generic_inclusion_le_ge :
  forall e1 e2,
  (e1 < e2)%Z ->
  ( forall e, (e1 < e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x <= bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof.
intros e1 e2 He' He x (Hx1,[Hx2|Hx2]).
(* *)
apply generic_inclusion_ln_beta.
intros Zx.
apply He.
split.
now apply ln_beta_gt_bpow.
now apply ln_beta_le_bpow.
(* *)
apply generic_inclusion with (e := e2).
apply He.
split.
apply He'.
apply Zle_refl.
rewrite Hx2.
split.
apply bpow_le.
apply Zle_pred.
apply Rle_refl.
Qed.

Theorem generic_inclusion_le :
  forall e2,
  ( forall e, (e <= e2)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (Rabs x <= bpow e2)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof.
intros e2 He x [Hx|Hx].
apply generic_inclusion_ln_beta.
intros Zx.
apply He.
now apply ln_beta_le_bpow.
apply generic_inclusion with (e := e2).
apply He.
apply Zle_refl.
rewrite Hx.
split.
apply bpow_le.
apply Zle_pred.
apply Rle_refl.
Qed.

Theorem generic_inclusion_ge :
  forall e1,
  ( forall e, (e1 < e)%Z -> (fexp2 e <= fexp1 e)%Z ) ->
  forall x,
  (bpow e1 <= Rabs x)%R ->
  generic_format fexp1 x ->
  generic_format fexp2 x.
Proof.
intros e1 He x Hx.
apply generic_inclusion_ln_beta.
intros Zx.
apply He.
now apply ln_beta_gt_bpow.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem generic_round_generic :
  forall x,
  generic_format fexp1 x ->
  generic_format fexp1 (round fexp2 rnd x).
Proof with auto with typeclass_instances.
intros x Gx.
apply generic_format_abs_inv.
apply generic_format_abs in Gx.
revert rnd valid_rnd x Gx.
refine (round_abs_abs _ (fun x y => generic_format fexp1 x -> generic_format fexp1 y) _).
intros rnd valid_rnd x [Hx|Hx] Gx.
(* x > 0 *)
generalize (ln_beta_generic_gt _ x (Rgt_not_eq _ _ Hx) Gx).
unfold canonic_exp.
destruct (ln_beta beta x) as (ex,Ex) ; simpl.
specialize (Ex (Rgt_not_eq _ _ Hx)).
intros He'.
rewrite Rabs_pos_eq in Ex by now apply Rlt_le.
destruct (Zle_or_lt ex (fexp2 ex)) as [He|He].
(* - x near 0 for fexp2 *)
destruct (round_bounded_small_pos fexp2 rnd x ex He Ex) as [Hr|Hr].
rewrite Hr.
apply generic_format_0.
rewrite Hr.
apply generic_format_bpow'...
apply Zlt_le_weak.
apply valid_exp_large with ex...
(* - x large for fexp2 *)
destruct (Zle_or_lt (canonic_exp fexp2 x) (canonic_exp fexp1 x)) as [He''|He''].
(* - - round fexp2 x is representable for fexp1 *)
rewrite round_generic...
rewrite Gx.
apply generic_format_F2R.
fold (round fexp1 Ztrunc x).
intros Zx.
unfold canonic_exp at 1.
rewrite ln_beta_round_ZR...
contradict Zx.
apply F2R_eq_0_reg with (1 := Zx).
(* - - round fexp2 x has too many digits for fexp1 *)
destruct (round_bounded_large_pos fexp2 rnd x ex He Ex) as (Hr1,[Hr2|Hr2]).
apply generic_format_F2R.
intros Zx.
fold (round fexp2 rnd x).
unfold canonic_exp at 1.
rewrite ln_beta_unique_pos with (1 := conj Hr1 Hr2).
rewrite <- ln_beta_unique_pos with (1 := Ex).
now apply Zlt_le_weak.
rewrite Hr2.
apply generic_format_bpow'...
now apply Zlt_le_weak.
(* x = 0 *)
rewrite <- Hx, round_0...
apply generic_format_0.
Qed.

End Inclusion.

End Generic.

Notation ZnearestA := (Znearest (Zle_bool 0)).

Section rndNA_opp.

Lemma round_NA_opp :
  forall beta : radix,
  forall (fexp : Z -> Z),
  forall x,
  (round beta fexp ZnearestA (- x) = - round beta fexp ZnearestA x)%R.
Proof.
intros beta fexp x.
rewrite round_N_opp.
apply Ropp_eq_compat.
apply round_ext.
clear x; intro x.
unfold Znearest.
case_eq (Rcompare (x - Z2R (Zfloor x)) (/ 2)); intro C;
[|reflexivity|reflexivity].
apply Rcompare_Eq_inv in C.
assert (H : negb (0 <=? - (Zfloor x + 1))%Z = (0 <=? Zfloor x)%Z);
  [|now rewrite H].
rewrite negb_Zle_bool.
case_eq (0 <=? Zfloor x)%Z; intro C'.
- apply Zle_bool_imp_le in C'.
  apply Zlt_bool_true.
  omega.
- rewrite Z.leb_gt in C'.
  apply Zlt_bool_false.
  omega.
Qed.

End rndNA_opp.

(** Notations for backward-compatibility with Flocq 1.4. *)
Notation rndDN := Zfloor (only parsing).
Notation rndUP := Zceil (only parsing).
Notation rndZR := Ztrunc (only parsing).
Notation rndNA := ZnearestA (only parsing).

(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2009-2018 Sylvie Boldo
#<br />#
Copyright (C) 2009-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Floating-point format with gradual underflow *)

From Coq Require Import ZArith Reals Psatz.

Require Import Zaux Raux Defs Round_pred Generic_fmt Float_prop FLX FIX Ulp Round_NE.

Section RND_FLT.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable emin prec : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Inductive FLT_format (x : R) : Prop :=
  FLT_spec (f : float beta) :
    x = F2R f -> (Z.abs (Fnum f) < Zpower beta prec)%Z ->
    (emin <= Fexp f)%Z -> FLT_format x.

Definition FLT_exp e := Z.max (e - prec) emin.

(** Properties of the FLT format *)
Global Instance FLT_exp_valid : Valid_exp FLT_exp.
Proof.
intros k.
unfold FLT_exp.
generalize (prec_gt_0 prec).
repeat split ;
  intros ; zify ; lia.
Qed.

Theorem generic_format_FLT :
  forall x, FLT_format x -> generic_format beta FLT_exp x.
Proof.
clear prec_gt_0_.
intros x [[mx ex] H1 H2 H3].
simpl in H2, H3.
rewrite H1.
apply generic_format_F2R.
intros Zmx.
unfold cexp, FLT_exp.
rewrite mag_F2R with (1 := Zmx).
apply Z.max_lub with (2 := H3).
apply Zplus_le_reg_r with (prec - ex)%Z.
ring_simplify.
now apply mag_le_Zpower.
Qed.

Theorem FLT_format_generic :
  forall x, generic_format beta FLT_exp x -> FLT_format x.
Proof.
intros x.
unfold generic_format.
set (ex := cexp beta FLT_exp x).
set (mx := Ztrunc (scaled_mantissa beta FLT_exp x)).
intros Hx.
rewrite Hx.
eexists ; repeat split ; simpl.
apply lt_IZR.
rewrite IZR_Zpower. 2: now apply Zlt_le_weak.
apply Rmult_lt_reg_r with (bpow ex).
apply bpow_gt_0.
rewrite <- bpow_plus.
change (F2R (Float beta (Z.abs mx) ex) < bpow (prec + ex))%R.
rewrite F2R_Zabs.
rewrite <- Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
unfold cexp in ex.
destruct (mag beta x) as (ex', He).
simpl in ex.
specialize (He Hx0).
apply Rlt_le_trans with (1 := proj2 He).
apply bpow_le.
cut (ex' - prec <= ex)%Z. lia.
unfold ex, FLT_exp.
apply Z.le_max_l.
apply Z.le_max_r.
Qed.

Theorem generic_format_FLT_bpow :
  forall e, (emin <= e)%Z -> generic_format beta FLT_exp (bpow e).
Proof.
intros e He.
apply generic_format_bpow; unfold FLT_exp.
apply Z.max_case; try assumption.
unfold Prec_gt_0 in prec_gt_0_; lia.
Qed.

Theorem FLT_format_bpow :
  forall e, (emin <= e)%Z -> FLT_format (bpow e).
Proof.
intros e He.
apply FLT_format_generic.
now apply generic_format_FLT_bpow.
Qed.

Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLT_exp)).
intros x.
split.
apply FLT_format_generic.
apply generic_format_FLT.
Qed.

Theorem cexp_FLT_FLX :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  cexp beta FLT_exp x = cexp beta (FLX_exp prec) x.
Proof.
intros x Hx.
assert (Hx0: x <> 0%R).
intros H1; rewrite H1, Rabs_R0 in Hx.
contradict Hx; apply Rlt_not_le, bpow_gt_0.
unfold cexp.
apply Zmax_left.
destruct (mag beta x) as (ex, He).
unfold FLX_exp. simpl.
specialize (He Hx0).
cut (emin + prec - 1 < ex)%Z. lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := Hx).
apply He.
Qed.

(** FLT is a nice format: it has a monotone exponent... *)
Global Instance FLT_exp_monotone : Monotone_exp FLT_exp.
Proof.
intros ex ey.
unfold FLT_exp.
zify ; lia.
Qed.

(** and it allows a rounding to nearest, ties to even. *)
Global Instance exists_NE_FLT :
  (Z.even beta = false \/ (1 < prec)%Z) ->
  Exists_NE beta FLT_exp.
Proof.
intros [H|H].
now left.
right.
intros e.
unfold FLT_exp.
destruct (Zmax_spec (e - prec) emin) as [(H1,H2)|(H1,H2)] ;
  rewrite H2 ; clear H2.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (e - prec + 1 - prec) emin).
lia.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (emin + 1 - prec) emin).
lia.
Qed.

(** Links between FLT and FLX *)
Theorem generic_format_FLT_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  generic_format beta (FLX_exp prec) x ->
  generic_format beta FLT_exp x.
Proof.
intros x Hx H.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0.
apply generic_format_0.
unfold generic_format, scaled_mantissa.
now rewrite cexp_FLT_FLX.
Qed.

Theorem generic_format_FLX_FLT :
  forall x : R,
  generic_format beta FLT_exp x -> generic_format beta (FLX_exp prec) x.
Proof.
clear prec_gt_0_.
intros x Hx.
unfold generic_format in Hx; rewrite Hx.
apply generic_format_F2R.
intros _.
rewrite <- Hx.
unfold cexp, FLX_exp, FLT_exp.
apply Z.le_max_l.
Qed.

Theorem round_FLT_FLX : forall rnd x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FLT_exp rnd x = round beta (FLX_exp prec) rnd x.
Proof.
intros rnd x Hx.
unfold round, scaled_mantissa.
rewrite cexp_FLT_FLX ; trivial.
Qed.

(** Links between FLT and FIX (underflow) *)
Theorem cexp_FLT_FIX :
  forall x, x <> 0%R ->
  (Rabs x < bpow (emin + prec))%R ->
  cexp beta FLT_exp x = cexp beta (FIX_exp emin) x.
Proof.
intros x Hx0 Hx.
unfold cexp.
apply Zmax_right.
unfold FIX_exp.
destruct (mag beta x) as (ex, Hex).
simpl.
cut (ex - 1 < emin + prec)%Z. lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := Hx).
now apply Hex.
Qed.

Theorem generic_format_FIX_FLT :
  forall x : R,
  generic_format beta FLT_exp x ->
  generic_format beta (FIX_exp emin) x.
Proof.
clear prec_gt_0_.
intros x Hx.
rewrite Hx.
apply generic_format_F2R.
intros _.
rewrite <- Hx.
apply Z.le_max_r.
Qed.

Theorem generic_format_FLT_FIX :
  forall x : R,
  (Rabs x <= bpow (emin + prec))%R ->
  generic_format beta (FIX_exp emin) x ->
  generic_format beta FLT_exp x.
Proof with auto with typeclass_instances.
apply generic_inclusion_le...
intros e He.
unfold FIX_exp.
apply Z.max_lub.
lia.
apply Z.le_refl.
Qed.

Lemma negligible_exp_FLT :
  exists n, negligible_exp FLT_exp = Some n /\ (n <= emin)%Z.
Proof.
case (negligible_exp_spec FLT_exp).
{ intro H; exfalso; specialize (H emin); revert H.
  apply Zle_not_lt, Z.le_max_r. }
intros n Hn; exists n; split; [now simpl|].
destruct (Z.max_spec (n - prec) emin) as [(Hm, Hm')|(Hm, Hm')].
{ now revert Hn; unfold FLT_exp; rewrite Hm'. }
revert Hn prec_gt_0_; unfold FLT_exp, Prec_gt_0; rewrite Hm'; lia.
Qed.

Theorem generic_format_FLT_1 :
  (emin <= 0)%Z ->
  generic_format beta FLT_exp 1.
Proof.
intros Hemin.
now apply (generic_format_FLT_bpow 0).
Qed.

Theorem ulp_FLT_0 :
  ulp beta FLT_exp 0 = bpow emin.
Proof.
unfold ulp.
rewrite Req_bool_true by easy.
case negligible_exp_spec.
- intros T.
  elim Zle_not_lt with (2 := T emin).
  apply Z.le_max_r.
- intros n Hn.
  apply f_equal.
  assert (H: FLT_exp emin = emin).
    apply Z.max_r.
    generalize (prec_gt_0 prec).
    clear ; lia.
  rewrite <- H.
  apply fexp_negligible_exp_eq.
  apply FLT_exp_valid.
  exact Hn.
  rewrite H.
  apply Z.le_refl.
Qed.

Theorem ulp_FLT_small :
  forall x, (Rabs x < bpow (emin + prec))%R ->
  ulp beta FLT_exp x = bpow emin.
Proof.
intros x Hx.
destruct (Req_dec x 0%R) as [Zx|Zx].
{ rewrite Zx.
  apply ulp_FLT_0. }
rewrite ulp_neq_0 by easy.
apply f_equal.
apply Z.max_r.
destruct (mag beta x) as [e He].
simpl.
cut (e - 1 < emin + prec)%Z. lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (2 := Hx).
now apply He.
Qed.

Theorem ulp_FLT_le :
  forall x, (bpow (emin + prec - 1) <= Rabs x)%R ->
  (ulp beta FLT_exp x <= Rabs x * bpow (1 - prec))%R.
Proof.
intros x Hx.
assert (Zx : (x <> 0)%R).
  intros Z; contradict Hx; apply Rgt_not_le, Rlt_gt.
  rewrite Z, Rabs_R0; apply bpow_gt_0.
rewrite ulp_neq_0 with (1 := Zx).
unfold cexp, FLT_exp.
destruct (mag beta x) as (e,He).
apply Rle_trans with (bpow (e-1)*bpow (1-prec))%R.
rewrite <- bpow_plus.
right; apply f_equal.
replace (e - 1 + (1 - prec))%Z with (e - prec)%Z by ring.
apply Z.max_l; simpl.
cut (emin+prec-1 < e)%Z. lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=Hx).
now apply He.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply He.
Qed.

Theorem ulp_FLT_gt :
  forall x, (Rabs x * bpow (-prec) < ulp beta FLT_exp x)%R.
Proof.
intros x; case (Req_dec x 0); intros Hx.
rewrite Hx, ulp_FLT_small, Rabs_R0, Rmult_0_l; try apply bpow_gt_0.
rewrite Rabs_R0; apply bpow_gt_0.
rewrite ulp_neq_0; try exact Hx.
unfold cexp, FLT_exp.
apply Rlt_le_trans with (bpow (mag beta x)*bpow (-prec))%R.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
now apply bpow_mag_gt.
rewrite <- bpow_plus.
apply bpow_le.
apply Z.le_max_l.
Qed.

Lemma ulp_FLT_exact_shift :
  forall x e,
  (x <> 0)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (ulp beta FLT_exp (x * bpow e) = ulp beta FLT_exp x * bpow e)%R.
Proof.
intros x e Nzx Hmx He.
unfold ulp; rewrite Req_bool_false;
  [|now intro H; apply Nzx, (Rmult_eq_reg_r (bpow e));
    [rewrite Rmult_0_l|apply Rgt_not_eq, Rlt_gt, bpow_gt_0]].
rewrite (Req_bool_false _ _ Nzx), <- bpow_plus; f_equal; unfold cexp, FLT_exp.
rewrite (mag_mult_bpow _ _ _ Nzx), !Z.max_l; lia.
Qed.

Lemma succ_FLT_exact_shift_pos :
  forall x e,
  (0 < x)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
Proof.
intros x e Px Hmx He.
rewrite succ_eq_pos; [|now apply Rlt_le, Rmult_lt_0_compat, bpow_gt_0].
rewrite (succ_eq_pos _ _ _ (Rlt_le _ _ Px)).
now rewrite Rmult_plus_distr_r; f_equal; apply ulp_FLT_exact_shift; [lra| |].
Qed.

Lemma succ_FLT_exact_shift :
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
  (succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
Proof.
intros x e Nzx Hmx He.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{ now apply succ_FLT_exact_shift_pos; [lra|lia|lia]. }
unfold succ.
rewrite Rle_bool_false; [|assert (H := bpow_gt_0 beta e); nra].
rewrite Rle_bool_false; [|now simpl].
rewrite Ropp_mult_distr_l_reverse, <-Ropp_mult_distr_l_reverse; f_equal.
unfold pred_pos.
rewrite mag_mult_bpow; [|lra].
replace (_ - 1)%Z with (mag beta (- x) - 1 + e)%Z; [|ring]; rewrite bpow_plus.
unfold Req_bool; rewrite Rcompare_mult_r; [|now apply bpow_gt_0].
fold (Req_bool (-x) (bpow (mag beta (-x) - 1))); case Req_bool.
{ rewrite mag_opp; unfold FLT_exp; do 2 (rewrite Z.max_l; [|lia]).
  replace (_ - _)%Z with (mag beta x - 1 - prec + e)%Z; [|ring].
  rewrite bpow_plus; ring. }
rewrite ulp_FLT_exact_shift; [ring|lra| |]; rewrite mag_opp; lia.
Qed.

Theorem ulp_FLT_pred_pos :
  forall x,
  generic_format beta FLT_exp x ->
  (0 <= x)%R ->
  ulp beta FLT_exp (pred beta FLT_exp x) = ulp beta FLT_exp x \/
  (x = bpow (mag beta x - 1) /\ ulp beta FLT_exp (pred beta FLT_exp x) = (ulp beta FLT_exp x / IZR beta)%R).
Proof.
intros x Fx [Hx|Hx] ; cycle 1.
{ rewrite <- Hx.
  rewrite pred_0.
  rewrite ulp_opp.
  left.
  apply ulp_ulp_0.
  apply FLT_exp_valid.
  typeclasses eauto. }
assert (Hp: (0 <= pred beta FLT_exp x)%R).
{ apply pred_ge_gt ; try easy.
  apply FLT_exp_valid.
  apply generic_format_0. }
destruct (Rle_or_lt (bpow (emin + prec)) x) as [Hs|Hs].
- unfold ulp.
  rewrite Req_bool_false ; cycle 1.
  { intros Zp.
    apply Rle_not_lt with (1 := Hs).
    generalize (f_equal (succ beta FLT_exp) Zp).
    rewrite succ_pred.
    rewrite succ_0, ulp_FLT_0.
    intros H.
    rewrite H.
    apply bpow_lt.
    generalize (prec_gt_0 prec).
    lia.
    apply FLT_exp_valid.
    exact Fx. }
  rewrite Req_bool_false by now apply Rgt_not_eq.
  unfold cexp.
  destruct (mag beta x) as [e He].
  simpl.
  specialize (He (Rgt_not_eq _ _ Hx)).
  rewrite Rabs_pos_eq in He by now apply Rlt_le.
  destruct (proj1 He) as [Hb|Hb].
  + left.
    apply (f_equal (fun v => bpow (FLT_exp v))).
    apply mag_unique.
    rewrite Rabs_pos_eq by easy.
    split.
    * apply pred_ge_gt ; try easy.
      apply FLT_exp_valid.
      apply generic_format_FLT_bpow.
      apply Z.lt_le_pred.
      apply lt_bpow with beta.
      apply Rle_lt_trans with (2 := proj2 He).
      apply Rle_trans with (2 := Hs).
      apply bpow_le.
      generalize (prec_gt_0 prec).
      lia.
    * apply pred_lt_le.
      now apply Rgt_not_eq.
      now apply Rlt_le.
  + right.
    split.
    easy.
    replace (FLT_exp _) with (FLT_exp e + -1)%Z.
    rewrite bpow_plus.
    now rewrite <- (Zmult_1_r beta).
    rewrite <- Hb.
    unfold FLT_exp at 1 2.
    replace (mag_val _ _ (mag _ _)) with (e - 1)%Z.
    rewrite <- Hb in Hs.
    apply le_bpow in Hs.
    zify ; lia.
    apply eq_sym, mag_unique.
    rewrite Hb.
    rewrite Rabs_pos_eq by easy.
    split ; cycle 1.
    { apply pred_lt_id.
      now apply Rgt_not_eq. }
    apply pred_ge_gt.
    apply FLT_exp_valid.
    apply generic_format_FLT_bpow.
    cut (emin + 1 < e)%Z. lia.
    apply lt_bpow with beta.
    apply Rle_lt_trans with (2 := proj2 He).
    apply Rle_trans with (2 := Hs).
    apply bpow_le.
    generalize (prec_gt_0 prec).
    lia.
    exact Fx.
    apply Rlt_le_trans with (2 := proj1 He).
    apply bpow_lt.
    apply Z.lt_pred_l.
- left.
  rewrite (ulp_FLT_small x).
  apply ulp_FLT_small.
  rewrite Rabs_pos_eq by easy.
  apply pred_lt_le.
  now apply Rgt_not_eq.
  now apply Rlt_le.
  rewrite Rabs_pos_eq by now apply Rlt_le.
  exact Hs.
Qed.

End RND_FLT.

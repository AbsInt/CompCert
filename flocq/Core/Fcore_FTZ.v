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

(** * Floating-point format with abrupt underflow *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_ulp.
Require Import Fcore_FLX.

Section RND_FTZ.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable emin prec : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

(* floating-point format with abrupt underflow *)
Definition FTZ_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (x <> R0 -> Zpower beta (prec - 1) <= Zabs (Fnum f) < Zpower beta prec)%Z /\
  (emin <= Fexp f)%Z.

Definition FTZ_exp e := if Zlt_bool (e - prec) emin then (emin + prec - 1)%Z else (e - prec)%Z.

(** Properties of the FTZ format *)
Global Instance FTZ_exp_valid : Valid_exp FTZ_exp.
Proof.
intros k.
unfold FTZ_exp.
generalize (Zlt_cases (k - prec) emin).
case (Zlt_bool (k - prec) emin) ; intros H1.
split ; intros H2.
omega.
split.
generalize (Zlt_cases (emin + prec + 1 - prec) emin).
case (Zlt_bool (emin + prec + 1 - prec) emin) ; intros H3.
omega.
generalize (Zlt_cases (emin + prec - 1 + 1 - prec) emin).
generalize (prec_gt_0 prec).
case (Zlt_bool (emin + prec - 1 + 1 - prec) emin) ; omega.
intros l H3.
generalize (Zlt_cases (l - prec) emin).
case (Zlt_bool (l - prec) emin) ; omega.
split ; intros H2.
generalize (Zlt_cases (k + 1 - prec) emin).
case (Zlt_bool (k + 1 - prec) emin) ; omega.
generalize (prec_gt_0 prec).
split ; intros ; omega.
Qed.

Theorem FLXN_format_FTZ :
  forall x, FTZ_format x -> FLXN_format beta prec x.
Proof.
intros x ((xm, xe), (Hx1, (Hx2, Hx3))).
eexists.
apply (conj Hx1 Hx2).
Qed.

Theorem generic_format_FTZ :
  forall x, FTZ_format x -> generic_format beta FTZ_exp x.
Proof.
intros x Hx.
cut (generic_format beta (FLX_exp prec) x).
apply generic_inclusion_ln_beta.
intros Zx.
destruct Hx as ((xm, xe), (Hx1, (Hx2, Hx3))).
simpl in Hx2, Hx3.
specialize (Hx2 Zx).
assert (Zxm: xm <> Z0).
contradict Zx.
rewrite Hx1, Zx.
apply F2R_0.
unfold FTZ_exp, FLX_exp.
rewrite Zlt_bool_false.
apply Zle_refl.
rewrite Hx1, ln_beta_F2R with (1 := Zxm).
cut (prec - 1 < ln_beta beta (Z2R xm))%Z.
clear -Hx3 ; omega.
apply ln_beta_gt_Zpower with (1 := Zxm).
apply Hx2.
apply generic_format_FLXN.
now apply FLXN_format_FTZ.
Qed.

Theorem FTZ_format_generic :
  forall x, generic_format beta FTZ_exp x -> FTZ_format x.
Proof.
intros x Hx.
destruct (Req_dec x 0) as [Hx3|Hx3].
exists (Float beta 0 emin).
split.
unfold F2R. simpl.
now rewrite Rmult_0_l.
split.
intros H.
now elim H.
apply Zle_refl.
unfold generic_format, scaled_mantissa, canonic_exp, FTZ_exp in Hx.
destruct (ln_beta beta x) as (ex, Hx4).
simpl in Hx.
specialize (Hx4 Hx3).
generalize (Zlt_cases (ex - prec) emin) Hx. clear Hx.
case (Zlt_bool (ex - prec) emin) ; intros Hx5 Hx2.
elim Rlt_not_ge with (1 := proj2 Hx4).
apply Rle_ge.
rewrite Hx2, <- F2R_Zabs.
rewrite <- (Rmult_1_l (bpow ex)).
unfold F2R. simpl.
apply Rmult_le_compat.
now apply (Z2R_le 0 1).
apply bpow_ge_0.
apply (Z2R_le 1).
apply (Zlt_le_succ 0).
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow (emin + prec - 1)).
apply bpow_gt_0.
rewrite Rmult_0_l.
change (0 < F2R (Float beta (Zabs (Ztrunc (x * bpow (- (emin + prec - 1))))) (emin + prec - 1)))%R.
rewrite F2R_Zabs, <- Hx2.
now apply Rabs_pos_lt.
apply bpow_le.
omega.
rewrite Hx2.
eexists ; repeat split ; simpl.
apply le_Z2R.
rewrite Z2R_Zpower.
apply Rmult_le_reg_r with (bpow (ex - prec)).
apply bpow_gt_0.
rewrite <- bpow_plus.
replace (prec - 1 + (ex - prec))%Z with (ex - 1)%Z by ring.
change (bpow (ex - 1) <= F2R (Float beta (Zabs (Ztrunc (x * bpow (- (ex - prec))))) (ex - prec)))%R.
rewrite F2R_Zabs, <- Hx2.
apply Hx4.
apply Zle_minus_le_0.
now apply (Zlt_le_succ 0).
apply lt_Z2R.
rewrite Z2R_Zpower.
apply Rmult_lt_reg_r with (bpow (ex - prec)).
apply bpow_gt_0.
rewrite <- bpow_plus.
replace (prec + (ex - prec))%Z with ex by ring.
change (F2R (Float beta (Zabs (Ztrunc (x * bpow (- (ex - prec))))) (ex - prec)) < bpow ex)%R.
rewrite F2R_Zabs, <- Hx2.
apply Hx4.
now apply Zlt_le_weak.
now apply Zge_le.
Qed.

Theorem FTZ_format_satisfies_any :
  satisfies_any FTZ_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FTZ_exp)).
intros x.
split.
apply FTZ_format_generic.
apply generic_format_FTZ.
Qed.

Theorem FTZ_format_FLXN :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  FLXN_format beta prec x -> FTZ_format x.
Proof.
intros x Hx Fx.
apply FTZ_format_generic.
apply generic_format_FLXN in Fx.
revert Hx Fx.
apply generic_inclusion_ge.
intros e He.
unfold FTZ_exp.
rewrite Zlt_bool_false.
apply Zle_refl.
omega.
Qed.

Theorem ulp_FTZ_0: ulp beta FTZ_exp 0 = bpow (emin+prec-1).
Proof with auto with typeclass_instances.
unfold ulp; rewrite Req_bool_true; trivial.
case (negligible_exp_spec FTZ_exp).
intros T; specialize (T (emin-1)%Z); contradict T.
apply Zle_not_lt; unfold FTZ_exp; unfold Prec_gt_0 in prec_gt_0_.
rewrite Zlt_bool_true; omega.
assert (V:(FTZ_exp (emin+prec-1) = emin+prec-1)%Z).
unfold FTZ_exp; rewrite Zlt_bool_true; omega.
intros n H2; rewrite <-V.
apply f_equal, fexp_negligible_exp_eq...
omega.
Qed.


Section FTZ_round.

(** Rounding with FTZ *)
Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Definition Zrnd_FTZ x :=
  if Rle_bool 1 (Rabs x) then rnd x else Z0.

Global Instance valid_rnd_FTZ : Valid_rnd Zrnd_FTZ.
Proof with auto with typeclass_instances.
split.
(* *)
intros x y Hxy.
unfold Zrnd_FTZ.
case Rle_bool_spec ; intros Hx ;
  case Rle_bool_spec ; intros Hy.
4: easy.
(* 1 <= |x| *)
now apply Zrnd_le.
rewrite <- (Zrnd_Z2R rnd 0).
apply Zrnd_le...
apply Rle_trans with (Z2R (-1)). 2: now apply Z2R_le.
destruct (Rabs_ge_inv _ _ Hx) as [Hx1|Hx1].
exact Hx1.
elim Rle_not_lt with (1 := Hx1).
apply Rle_lt_trans with (2 := Hy).
apply Rle_trans with (1 := Hxy).
apply RRle_abs.
(* |x| < 1 *)
rewrite <- (Zrnd_Z2R rnd 0).
apply Zrnd_le...
apply Rle_trans with (Z2R 1).
now apply Z2R_le.
destruct (Rabs_ge_inv _ _ Hy) as [Hy1|Hy1].
elim Rle_not_lt with (1 := Hy1).
apply Rlt_le_trans with (2 := Hxy).
apply (Rabs_def2 _ _ Hx).
exact Hy1.
(* *)
intros n.
unfold Zrnd_FTZ.
rewrite Zrnd_Z2R...
case Rle_bool_spec.
easy.
rewrite <- Z2R_abs.
intros H.
generalize (lt_Z2R _ 1 H).
clear.
now case n ; trivial ; simpl ; intros [p|p|].
Qed.

Theorem round_FTZ_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FTZ_exp Zrnd_FTZ x = round beta (FLX_exp prec) rnd x.
Proof.
intros x Hx.
unfold round, scaled_mantissa, canonic_exp.
destruct (ln_beta beta x) as (ex, He). simpl.
assert (Hx0: x <> 0%R).
intros Hx0.
apply Rle_not_lt with (1 := Hx).
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
specialize (He Hx0).
assert (He': (emin + prec <= ex)%Z).
apply (bpow_lt_bpow beta).
apply Rle_lt_trans with (1 := Hx).
apply He.
replace (FTZ_exp ex) with (FLX_exp prec ex).
unfold Zrnd_FTZ.
rewrite Rle_bool_true.
apply refl_equal.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow (- FLX_exp prec ex))).
change 1%R with (bpow 0).
rewrite <- (Zplus_opp_r (FLX_exp prec ex)).
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (2 := proj1 He).
apply bpow_le.
unfold FLX_exp.
generalize (prec_gt_0 prec).
clear -He' ; omega.
apply bpow_ge_0.
unfold FLX_exp, FTZ_exp.
rewrite Zlt_bool_false.
apply refl_equal.
clear -He' ; omega.
Qed.

Theorem round_FTZ_small :
  forall x : R,
  (Rabs x < bpow (emin + prec - 1))%R ->
  round beta FTZ_exp Zrnd_FTZ x = R0.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0.
apply round_0...
unfold round, scaled_mantissa, canonic_exp.
destruct (ln_beta beta x) as (ex, He). simpl.
specialize (He Hx0).
unfold Zrnd_FTZ.
rewrite Rle_bool_false.
apply F2R_0.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow (- FTZ_exp ex))).
change 1%R with (bpow 0).
rewrite <- (Zplus_opp_r (FTZ_exp ex)).
rewrite bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Rlt_le_trans with (1 := Hx).
apply bpow_le.
unfold FTZ_exp.
generalize (Zlt_cases (ex - prec) emin).
case Zlt_bool.
intros _.
apply Zle_refl.
intros He'.
elim Rlt_not_le with (1 := Hx).
apply Rle_trans with (2 := proj1 He).
apply bpow_le.
omega.
apply bpow_ge_0.
Qed.

End FTZ_round.

End RND_FTZ.

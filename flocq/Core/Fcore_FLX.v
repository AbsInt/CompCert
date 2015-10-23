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

(** * Floating-point format without underflow *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_FIX.
Require Import Fcore_ulp.
Require Import Fcore_rnd_ne.

Section RND_FLX.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable prec : Z.

Class Prec_gt_0 :=
  prec_gt_0 : (0 < prec)%Z.

Context { prec_gt_0_ : Prec_gt_0 }.

(* unbounded floating-point format *)
Definition FLX_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower beta prec)%Z.

Definition FLX_exp (e : Z) := (e - prec)%Z.

(** Properties of the FLX format *)

Global Instance FLX_exp_valid : Valid_exp FLX_exp.
Proof.
intros k.
unfold FLX_exp.
generalize prec_gt_0.
repeat split ; intros ; omega.
Qed.

Theorem FIX_format_FLX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FLX_format x ->
  FIX_format beta (e - prec) x.
Proof.
clear prec_gt_0_.
intros x e Hx ((xm, xe), (H1, H2)).
rewrite H1, (F2R_prec_normalize beta xm xe e prec).
now eexists.
exact H2.
now rewrite <- H1.
Qed.

Theorem FLX_format_generic :
  forall x, generic_format beta FLX_exp x -> FLX_format x.
Proof.
intros x H.
rewrite H.
unfold FLX_format.
eexists ; repeat split.
simpl.
apply lt_Z2R.
rewrite Z2R_abs.
rewrite <- scaled_mantissa_generic with (1 := H).
rewrite <- scaled_mantissa_abs.
apply Rmult_lt_reg_r with (bpow (canonic_exp beta FLX_exp (Rabs x))).
apply bpow_gt_0.
rewrite scaled_mantissa_mult_bpow.
rewrite Z2R_Zpower, <- bpow_plus.
2: now apply Zlt_le_weak.
unfold canonic_exp, FLX_exp.
ring_simplify (prec + (ln_beta beta (Rabs x) - prec))%Z.
rewrite ln_beta_abs.
destruct (Req_dec x 0) as [Hx|Hx].
rewrite Hx, Rabs_R0.
apply bpow_gt_0.
destruct (ln_beta beta x) as (ex, Ex).
now apply Ex.
Qed.

Theorem generic_format_FLX :
  forall x, FLX_format x -> generic_format beta FLX_exp x.
Proof.
clear prec_gt_0_.
intros x ((mx,ex),(H1,H2)).
simpl in H2.
rewrite H1.
apply generic_format_F2R.
intros Zmx.
unfold canonic_exp, FLX_exp.
rewrite ln_beta_F2R with (1 := Zmx).
apply Zplus_le_reg_r with (prec - ex)%Z.
ring_simplify.
now apply ln_beta_le_Zpower.
Qed.

Theorem FLX_format_satisfies_any :
  satisfies_any FLX_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp)).
intros x.
split.
apply FLX_format_generic.
apply generic_format_FLX.
Qed.

Theorem FLX_format_FIX :
  forall x e,
  (bpow (e - 1) <= Rabs x <= bpow e)%R ->
  FIX_format beta (e - prec) x ->
  FLX_format x.
Proof with auto with typeclass_instances.
intros x e Hx Fx.
apply FLX_format_generic.
apply generic_format_FIX in Fx.
revert Fx.
apply generic_inclusion with (e := e)...
apply Zle_refl.
Qed.

(** unbounded floating-point format with normal mantissas *)
Definition FLXN_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (x <> R0 ->
  Zpower beta (prec - 1) <= Zabs (Fnum f) < Zpower beta prec)%Z.

Theorem generic_format_FLXN :
  forall x, FLXN_format x -> generic_format beta FLX_exp x.
Proof.
intros x ((xm,ex),(H1,H2)).
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx.
apply generic_format_0.
specialize (H2 Zx).
apply generic_format_FLX.
rewrite H1.
eexists ; repeat split.
apply H2.
Qed.

Theorem FLXN_format_generic :
  forall x, generic_format beta FLX_exp x -> FLXN_format x.
Proof.
intros x Hx.
rewrite Hx.
simpl.
eexists ; split. split.
simpl.
rewrite <- Hx.
intros Zx.
split.
(* *)
apply le_Z2R.
rewrite Z2R_Zpower.
2: now apply Zlt_0_le_0_pred.
rewrite Z2R_abs, <- scaled_mantissa_generic with (1 := Hx).
apply Rmult_le_reg_r with (bpow (canonic_exp beta FLX_exp x)).
apply bpow_gt_0.
rewrite <- bpow_plus.
rewrite <- scaled_mantissa_abs.
rewrite <- canonic_exp_abs.
rewrite scaled_mantissa_mult_bpow.
unfold canonic_exp, FLX_exp.
rewrite ln_beta_abs.
ring_simplify (prec - 1 + (ln_beta beta x - prec))%Z.
destruct (ln_beta beta x) as (ex,Ex).
now apply Ex.
(* *)
apply lt_Z2R.
rewrite Z2R_Zpower.
2: now apply Zlt_le_weak.
rewrite Z2R_abs, <- scaled_mantissa_generic with (1 := Hx).
apply Rmult_lt_reg_r with (bpow (canonic_exp beta FLX_exp x)).
apply bpow_gt_0.
rewrite <- bpow_plus.
rewrite <- scaled_mantissa_abs.
rewrite <- canonic_exp_abs.
rewrite scaled_mantissa_mult_bpow.
unfold canonic_exp, FLX_exp.
rewrite ln_beta_abs.
ring_simplify (prec + (ln_beta beta x - prec))%Z.
destruct (ln_beta beta x) as (ex,Ex).
now apply Ex.
Qed.

Theorem FLXN_format_satisfies_any :
  satisfies_any FLXN_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp)).
split ; intros H.
now apply FLXN_format_generic.
now apply generic_format_FLXN.
Qed.

Theorem ulp_FLX_0: (ulp beta FLX_exp 0 = 0)%R.
Proof.
unfold ulp; rewrite Req_bool_true; trivial.
case (negligible_exp_spec FLX_exp).
intros _; reflexivity.
intros n H2; contradict H2.
unfold FLX_exp; unfold Prec_gt_0 in prec_gt_0_; omega.
Qed.

Theorem ulp_FLX_le: forall x, (ulp beta FLX_exp x <= Rabs x * bpow (1-prec))%R.
Proof.
intros x; case (Req_dec x 0); intros Hx.
rewrite Hx, ulp_FLX_0, Rabs_R0.
right; ring.
rewrite ulp_neq_0; try exact Hx.
unfold canonic_exp, FLX_exp.
replace (ln_beta beta x - prec)%Z with ((ln_beta beta x - 1) + (1-prec))%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply bpow_ln_beta_le.
Qed.


Theorem ulp_FLX_ge: forall x, (Rabs x * bpow (-prec) <= ulp beta FLX_exp x)%R.
Proof.
intros x; case (Req_dec x 0); intros Hx.
rewrite Hx, ulp_FLX_0, Rabs_R0.
right; ring.
rewrite ulp_neq_0; try exact Hx.
unfold canonic_exp, FLX_exp.
unfold Zminus; rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
left; now apply bpow_ln_beta_gt.
Qed.

(** FLX is a nice format: it has a monotone exponent... *)
Global Instance FLX_exp_monotone : Monotone_exp FLX_exp.
Proof.
intros ex ey Hxy.
now apply Zplus_le_compat_r.
Qed.

(** and it allows a rounding to nearest, ties to even. *)
Hypothesis NE_prop : Zeven beta = false \/ (1 < prec)%Z.

Global Instance exists_NE_FLX : Exists_NE beta FLX_exp.
Proof.
destruct NE_prop as [H|H].
now left.
right.
unfold FLX_exp.
split ; omega.
Qed.

End RND_FLX.

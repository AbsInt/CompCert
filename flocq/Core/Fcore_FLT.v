(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010-2011 Sylvie Boldo
#<br />#
Copyright (C) 2010-2011 Guillaume Melquiond

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
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_float_prop.
Require Import Fcore_FLX.
Require Import Fcore_FIX.
Require Import Fcore_rnd_ne.

Section RND_FLT.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable emin prec : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

(* floating-point format with gradual underflow *)
Definition FLT_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Zabs (Fnum f) < Zpower beta prec)%Z /\ (emin <= Fexp f)%Z.

Definition FLT_exp e := Zmax (e - prec) emin.

(** Properties of the FLT format *)
Global Instance FLT_exp_valid : Valid_exp FLT_exp.
Proof.
intros k.
unfold FLT_exp.
generalize (prec_gt_0 prec).
repeat split ;
  intros ; zify ; omega.
Qed.

Theorem generic_format_FLT :
  forall x, FLT_format x -> generic_format beta FLT_exp x.
Proof.
clear prec_gt_0_.
intros x ((mx, ex), (H1, (H2, H3))).
simpl in H2, H3.
rewrite H1.
apply generic_format_F2R.
intros Zmx.
unfold canonic_exp, FLT_exp.
rewrite ln_beta_F2R with (1 := Zmx).
apply Zmax_lub with (2 := H3).
apply Zplus_le_reg_r with (prec - ex)%Z.
ring_simplify.
now apply ln_beta_le_Zpower.
Qed.

Theorem FLT_format_generic :
  forall x, generic_format beta FLT_exp x -> FLT_format x.
Proof.
intros x.
unfold generic_format.
set (ex := canonic_exp beta FLT_exp x).
set (mx := Ztrunc (scaled_mantissa beta FLT_exp x)).
intros Hx.
rewrite Hx.
eexists ; repeat split ; simpl.
apply lt_Z2R.
rewrite Z2R_Zpower. 2: now apply Zlt_le_weak.
apply Rmult_lt_reg_r with (bpow ex).
apply bpow_gt_0.
rewrite <- bpow_plus.
change (F2R (Float beta (Zabs mx) ex) < bpow (prec + ex))%R.
rewrite F2R_Zabs.
rewrite <- Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
unfold canonic_exp in ex.
destruct (ln_beta beta x) as (ex', He).
simpl in ex.
specialize (He Hx0).
apply Rlt_le_trans with (1 := proj2 He).
apply bpow_le.
cut (ex' - prec <= ex)%Z. omega.
unfold ex, FLT_exp.
apply Zle_max_l.
apply Zle_max_r.
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

Theorem canonic_exp_FLT_FLX :
  forall x, x <> R0 ->
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  canonic_exp beta FLT_exp x = canonic_exp beta (FLX_exp prec) x.
Proof.
intros x Hx0 Hx.
unfold canonic_exp.
apply Zmax_left.
destruct (ln_beta beta x) as (ex, He).
unfold FLX_exp. simpl.
specialize (He Hx0).
cut (emin + prec - 1 < ex)%Z. omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := Hx).
apply He.
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
now rewrite canonic_exp_FLT_FLX.
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
unfold canonic_exp, FLX_exp, FLT_exp.
apply Zle_max_l.
Qed.

Theorem round_FLT_FLX : forall rnd x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FLT_exp rnd x = round beta (FLX_exp prec) rnd x.
intros rnd x Hx.
unfold round, scaled_mantissa.
rewrite canonic_exp_FLT_FLX ; trivial.
contradict Hx.
rewrite Hx, Rabs_R0.
apply Rlt_not_le.
apply bpow_gt_0.
Qed.

(** Links between FLT and FIX (underflow) *)
Theorem canonic_exp_FLT_FIX :
  forall x, x <> R0 ->
  (Rabs x < bpow (emin + prec))%R ->
  canonic_exp beta FLT_exp x = canonic_exp beta (FIX_exp emin) x.
Proof.
intros x Hx0 Hx.
unfold canonic_exp.
apply Zmax_right.
unfold FIX_exp.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
cut (ex - 1 < emin + prec)%Z. omega.
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
apply Zle_max_r.
Qed.

Theorem generic_format_FLT_FIX :
  forall x : R,
  (Rabs x <= bpow (emin + prec))%R ->
  generic_format beta (FIX_exp emin) x ->
  generic_format beta FLT_exp x.
Proof with auto with typeclass_instances.
clear prec_gt_0_.
apply generic_inclusion_le...
intros e He.
unfold FIX_exp.
apply Zmax_lub.
omega.
apply Zle_refl.
Qed.

(** FLT is a nice format: it has a monotone exponent... *)
Global Instance FLT_exp_monotone : Monotone_exp FLT_exp.
Proof.
intros ex ey.
unfold FLT_exp.
zify ; omega.
Qed.

(** and it allows a rounding to nearest, ties to even. *)
Hypothesis NE_prop : Zeven beta = false \/ (1 < prec)%Z.

Global Instance exists_NE_FLT : Exists_NE beta FLT_exp.
Proof.
destruct NE_prop as [H|H].
now left.
right.
intros e.
unfold FLT_exp.
destruct (Zmax_spec (e - prec) emin) as [(H1,H2)|(H1,H2)] ;
  rewrite H2 ; clear H2.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (e - prec + 1 - prec) emin).
omega.
generalize (Zmax_spec (e + 1 - prec) emin).
generalize (Zmax_spec (emin + 1 - prec) emin).
omega.
Qed.

End RND_FLT.

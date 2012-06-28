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

(** * Error of the rounded-to-nearest addition is representable. *)

Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.
Require Import Fcore_generic_fmt.
Require Import Fcalc_ops.

Section Fprop_plus_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Section round_repr_same_exp.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_repr_same_exp :
  forall m e,
  exists m',
  round beta fexp rnd (F2R (Float beta m e)) = F2R (Float beta m' e).
Proof with auto with typeclass_instances.
intros m e.
set (e' := canonic_exp beta fexp (F2R (Float beta m e))).
unfold round, scaled_mantissa. fold e'.
destruct (Zle_or_lt e' e) as [He|He].
exists m.
unfold F2R at 2. simpl.
rewrite Rmult_assoc, <- bpow_plus.
rewrite <- Z2R_Zpower. 2: omega.
rewrite <- Z2R_mult, Zrnd_Z2R...
unfold F2R. simpl.
rewrite Z2R_mult.
rewrite Rmult_assoc.
rewrite Z2R_Zpower. 2: omega.
rewrite <- bpow_plus.
apply (f_equal (fun v => Z2R m * bpow v)%R).
ring.
exists ((rnd (Z2R m * bpow (e - e'))) * Zpower beta (e' - e))%Z.
unfold F2R. simpl.
rewrite Z2R_mult.
rewrite Z2R_Zpower. 2: omega.
rewrite 2!Rmult_assoc.
rewrite <- 2!bpow_plus.
apply (f_equal (fun v => _ * bpow v)%R).
ring.
Qed.

End round_repr_same_exp.

Context { monotone_exp : Monotone_exp fexp }.
Notation format := (generic_format beta fexp).

Variable choice : Z -> bool.

Lemma plus_error_aux :
  forall x y,
  (canonic_exp beta fexp x <= canonic_exp beta fexp y)%Z ->
  format x -> format y ->
  format (round beta fexp (Znearest choice) (x + y) - (x + y))%R.
Proof.
intros x y.
set (ex := canonic_exp beta fexp x).
set (ey := canonic_exp beta fexp y).
intros He Hx Hy.
destruct (Req_dec (round beta fexp (Znearest choice) (x + y) - (x + y)) R0) as [H0|H0].
rewrite H0.
apply generic_format_0.
set (mx := Ztrunc (scaled_mantissa beta fexp x)).
set (my := Ztrunc (scaled_mantissa beta fexp y)).
(* *)
assert (Hxy: (x + y)%R = F2R (Float beta (mx + my * beta ^ (ey - ex)) ex)).
rewrite Hx, Hy.
fold mx my ex ey.
rewrite <- F2R_plus.
unfold Fplus. simpl.
now rewrite Zle_imp_le_bool with (1 := He).
(* *)
rewrite Hxy.
destruct (round_repr_same_exp (Znearest choice) (mx + my * beta ^ (ey - ex)) ex) as (mxy, Hxy').
rewrite Hxy'.
assert (H: (F2R (Float beta mxy ex) - F2R (Float beta (mx + my * beta ^ (ey - ex)) ex))%R =
  F2R (Float beta (mxy - (mx + my * beta ^ (ey - ex))) ex)).
now rewrite <- F2R_minus, Fminus_same_exp.
rewrite H.
apply generic_format_F2R.
intros _.
apply monotone_exp.
rewrite <- H, <- Hxy', <- Hxy.
apply ln_beta_le_abs.
exact H0.
pattern x at 3 ; replace x with (-(y - (x + y)))%R by ring.
rewrite Rabs_Ropp.
now apply (round_N_pt beta _ choice (x + y)).
Qed.

(** Error of the addition *)
Theorem plus_error :
  forall x y,
  format x -> format y ->
  format (round beta fexp (Znearest choice) (x + y) - (x + y))%R.
Proof.
intros x y Hx Hy.
destruct (Zle_or_lt (canonic_exp beta fexp x) (canonic_exp beta fexp y)).
now apply plus_error_aux.
rewrite Rplus_comm.
apply plus_error_aux ; try easy.
now apply Zlt_le_weak.
Qed.

End Fprop_plus_error.

Section Fprop_plus_zero.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { exp_not_FTZ : Exp_not_FTZ fexp }.
Notation format := (generic_format beta fexp).

Section round_plus_eq_zero_aux.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma round_plus_eq_zero_aux :
  forall x y,
  (canonic_exp beta fexp x <= canonic_exp beta fexp y)%Z ->
  format x -> format y ->
  (0 <= x + y)%R ->
  round beta fexp rnd (x + y) = R0 ->
  (x + y = 0)%R.
Proof with auto with typeclass_instances.
intros x y He Hx Hy Hp Hxy.
destruct (Req_dec (x + y) 0) as [H0|H0].
exact H0.
destruct (ln_beta beta (x + y)) as (exy, Hexy).
simpl.
specialize (Hexy H0).
destruct (Zle_or_lt exy (fexp exy)) as [He'|He'].
(* . *)
assert (H: (x + y)%R = F2R (Float beta (Ztrunc (x * bpow (- fexp exy)) +
  Ztrunc (y * bpow (- fexp exy))) (fexp exy))).
rewrite (subnormal_exponent beta fexp exy x He' Hx) at 1.
rewrite (subnormal_exponent beta fexp exy y He' Hy) at 1.
now rewrite <- F2R_plus, Fplus_same_exp.
rewrite H in Hxy.
rewrite round_generic in Hxy...
now rewrite <- H in Hxy.
apply generic_format_F2R.
intros _.
rewrite <- H.
unfold canonic_exp.
rewrite ln_beta_unique with (1 := Hexy).
apply Zle_refl.
(* . *)
elim Rle_not_lt with (1 := round_le beta _ rnd _ _ (proj1 Hexy)).
rewrite (Rabs_pos_eq _ Hp).
rewrite Hxy.
rewrite round_generic...
apply bpow_gt_0.
apply generic_format_bpow.
apply Zlt_succ_le.
now rewrite (Zsucc_pred exy) in He'.
Qed.

End round_plus_eq_zero_aux.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

(** rnd(x+y)=0 -> x+y = 0 provided this is not a FTZ format *)
Theorem round_plus_eq_zero :
  forall x y,
  format x -> format y ->
  round beta fexp rnd (x + y) = R0 ->
  (x + y = 0)%R.
Proof with auto with typeclass_instances.
intros x y Hx Hy.
destruct (Rle_or_lt R0 (x + y)) as [H1|H1].
(* . *)
revert H1.
destruct (Zle_or_lt (canonic_exp beta fexp x) (canonic_exp beta fexp y)) as [H2|H2].
now apply round_plus_eq_zero_aux.
rewrite Rplus_comm.
apply round_plus_eq_zero_aux ; try easy.
now apply Zlt_le_weak.
(* . *)
revert H1.
rewrite <- (Ropp_involutive (x + y)), Ropp_plus_distr, <- Ropp_0.
intros H1.
rewrite round_opp.
intros Hxy.
apply f_equal.
cut (round beta fexp (Zrnd_opp rnd) (- x + - y) = 0)%R.
cut (0 <= -x + -y)%R.
destruct (Zle_or_lt (canonic_exp beta fexp (-x)) (canonic_exp beta fexp (-y))) as [H2|H2].
apply round_plus_eq_zero_aux ; try apply generic_format_opp...
rewrite Rplus_comm.
apply round_plus_eq_zero_aux ; try apply generic_format_opp...
now apply Zlt_le_weak.
apply Rlt_le.
now apply Ropp_lt_cancel.
rewrite <- (Ropp_involutive (round _ _ _ _)).
rewrite Hxy.
apply Ropp_involutive.
Qed.

End Fprop_plus_zero.

(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: https://flocq.gitlabpages.inria.fr/

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

(** * Missing definitions/lemmas *)

From Coq Require Import Psatz Reals ZArith.

Require Import Zaux.

Section Rmissing.

(** About R *)
Theorem Rle_0_minus :
  forall x y, (x <= y)%R -> (0 <= y - x)%R.
Proof.
intros.
apply Rge_le.
apply Rge_minus.
now apply Rle_ge.
Qed.

Theorem Rabs_eq_Rabs :
  forall x y : R,
  Rabs x = Rabs y -> x = y \/ x = Ropp y.
Proof.
intros x y H.
unfold Rabs in H.
destruct (Rcase_abs x) as [_|_].
assert (H' := f_equal Ropp H).
rewrite Ropp_involutive in H'.
rewrite H'.
destruct (Rcase_abs y) as [_|_].
left.
apply Ropp_involutive.
now right.
rewrite H.
now destruct (Rcase_abs y) as [_|_] ; [right|left].
Qed.

Theorem Rabs_minus_le:
  forall x y : R,
  (0 <= y)%R -> (y <= 2*x)%R ->
  (Rabs (x-y) <= x)%R.
Proof.
intros x y Hx Hy.
apply Rabs_le.
lra.
Qed.

Theorem Rabs_eq_R0 x : (Rabs x = 0 -> x = 0)%R.
Proof. split_Rabs; lra. Qed.

Theorem Rmult_lt_compat :
  forall r1 r2 r3 r4,
  (0 <= r1)%R -> (0 <= r3)%R -> (r1 < r2)%R -> (r3 < r4)%R ->
  (r1 * r3 < r2 * r4)%R.
Proof.
intros r1 r2 r3 r4 Pr1 Pr3 H12 H34.
apply Rle_lt_trans with (r1 * r4)%R.
- apply Rmult_le_compat_l.
  + exact Pr1.
  + now apply Rlt_le.
- apply Rmult_lt_compat_r.
  + now apply Rle_lt_trans with r3.
  + exact H12.
Qed.

Lemma Rmult_neq_reg_r :
  forall r1 r2 r3 : R, (r2 * r1 <> r3 * r1)%R -> r2 <> r3.
Proof.
intros r1 r2 r3 H1 H2.
apply H1; rewrite H2; ring.
Qed.

Lemma Rmult_neq_compat_r :
  forall r1 r2 r3 : R,
  (r1 <> 0)%R -> (r2 <> r3)%R ->
  (r2 * r1 <> r3 * r1)%R.
Proof.
intros r1 r2 r3 H H1 H2.
now apply H1, Rmult_eq_reg_r with r1.
Qed.

Theorem Rmult_min_distr_r :
  forall r r1 r2 : R,
  (0 <= r)%R ->
  (Rmin r1 r2 * r)%R = Rmin (r1 * r) (r2 * r).
Proof.
intros r r1 r2 [Hr|Hr].
unfold Rmin.
destruct (Rle_dec r1 r2) as [H1|H1] ;
  destruct (Rle_dec (r1 * r) (r2 * r)) as [H2|H2] ;
  try easy.
apply (f_equal (fun x => Rmult x r)).
apply Rle_antisym.
exact H1.
apply Rmult_le_reg_r with (1 := Hr).
apply Rlt_le.
now apply Rnot_le_lt.
apply Rle_antisym.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rlt_le.
now apply Rnot_le_lt.
exact H2.
rewrite <- Hr.
rewrite 3!Rmult_0_r.
unfold Rmin.
destruct (Rle_dec 0 0) as [H0|H0].
easy.
elim H0.
apply Rle_refl.
Qed.

Theorem Rmult_min_distr_l :
  forall r r1 r2 : R,
  (0 <= r)%R ->
  (r * Rmin r1 r2)%R = Rmin (r * r1) (r * r2).
Proof.
intros r r1 r2 Hr.
rewrite 3!(Rmult_comm r).
now apply Rmult_min_distr_r.
Qed.

Lemma Rmin_opp: forall x y, (Rmin (-x) (-y) = - Rmax x y)%R.
Proof.
intros x y.
apply Rmax_case_strong; intros H.
rewrite Rmin_left; trivial.
now apply Ropp_le_contravar.
rewrite Rmin_right; trivial.
now apply Ropp_le_contravar.
Qed.

Lemma Rmax_opp: forall x y, (Rmax (-x) (-y) = - Rmin x y)%R.
Proof.
intros x y.
apply Rmin_case_strong; intros H.
rewrite Rmax_left; trivial.
now apply Ropp_le_contravar.
rewrite Rmax_right; trivial.
now apply Ropp_le_contravar.
Qed.

Theorem exp_le :
  forall x y : R,
  (x <= y)%R -> (exp x <= exp y)%R.
Proof.
intros x y [H|H].
apply Rlt_le.
now apply exp_increasing.
rewrite H.
apply Rle_refl.
Qed.

Theorem Rinv_lt :
  forall x y,
  (0 < x)%R -> (x < y)%R -> (/y < /x)%R.
Proof.
intros x y Hx Hxy.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
exact Hx.
now apply Rlt_trans with x.
exact Hxy.
Qed.

Theorem Rinv_le :
  forall x y,
  (0 < x)%R -> (x <= y)%R -> (/y <= /x)%R.
Proof.
intros x y Hx Hxy.
apply Rle_Rinv.
exact Hx.
now apply Rlt_le_trans with x.
exact Hxy.
Qed.

Theorem sqrt_ge_0 :
  forall x : R,
  (0 <= sqrt x)%R.
Proof.
intros x.
unfold sqrt.
destruct (Rcase_abs x) as [_|H].
apply Rle_refl.
apply Rsqrt_positivity.
Qed.

Lemma sqrt_neg : forall x, (x <= 0)%R -> (sqrt x = 0)%R.
Proof.
intros x Npx.
destruct (Req_dec x 0) as [Zx|Nzx].
- (* x = 0 *)
  rewrite Zx.
  exact sqrt_0.
- (* x < 0 *)
  unfold sqrt.
  destruct Rcase_abs.
  + reflexivity.
  + exfalso.
    now apply Nzx, Rle_antisym; [|apply Rge_le].
Qed.

Lemma Rsqr_le_abs_0_alt :
  forall x y,
  (x² <= y² -> x <= Rabs y)%R.
Proof.
intros x y H.
apply (Rle_trans _ (Rabs x)); [apply Rle_abs|apply (Rsqr_le_abs_0 _ _ H)].
Qed.

Theorem Rabs_le_inv :
  forall x y,
  (Rabs x <= y)%R -> (-y <= x <= y)%R.
Proof.
intros x y Hxy.
split.
apply Rle_trans with (- Rabs x)%R.
now apply Ropp_le_contravar.
apply Ropp_le_cancel.
rewrite Ropp_involutive, <- Rabs_Ropp.
apply RRle_abs.
apply Rle_trans with (2 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_ge :
  forall x y,
  (y <= -x \/ x <= y)%R -> (x <= Rabs y)%R.
Proof.
intros x y [Hyx|Hxy].
apply Rle_trans with (-y)%R.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
rewrite <- Rabs_Ropp.
apply RRle_abs.
apply Rle_trans with (1 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_ge_inv :
  forall x y,
  (x <= Rabs y)%R -> (y <= -x \/ x <= y)%R.
Proof.
intros x y.
unfold Rabs.
case Rcase_abs ; intros Hy Hxy.
left.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
now right.
Qed.

Theorem Rabs_lt :
  forall x y,
  (-y < x < y)%R -> (Rabs x < y)%R.
Proof.
intros x y (Hyx,Hxy).
now apply Rabs_def1.
Qed.

Theorem Rabs_lt_inv :
  forall x y,
  (Rabs x < y)%R -> (-y < x < y)%R.
Proof.
intros x y H.
now split ; eapply Rabs_def2.
Qed.

Theorem Rabs_gt :
  forall x y,
  (y < -x \/ x < y)%R -> (x < Rabs y)%R.
Proof.
intros x y [Hyx|Hxy].
rewrite <- Rabs_Ropp.
apply Rlt_le_trans with (Ropp y).
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
apply RRle_abs.
apply Rlt_le_trans with (1 := Hxy).
apply RRle_abs.
Qed.

Theorem Rabs_gt_inv :
  forall x y,
  (x < Rabs y)%R -> (y < -x \/ x < y)%R.
Proof.
intros x y.
unfold Rabs.
case Rcase_abs ; intros Hy Hxy.
left.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
now right.
Qed.

End Rmissing.

Section IZR.

Theorem IZR_le_lt :
  forall m n p, (m <= n < p)%Z -> (IZR m <= IZR n < IZR p)%R.
Proof.
intros m n p (H1, H2).
split.
now apply IZR_le.
now apply IZR_lt.
Qed.

Theorem le_lt_IZR :
  forall m n p, (IZR m <= IZR n < IZR p)%R -> (m <= n < p)%Z.
Proof.
intros m n p (H1, H2).
split.
now apply le_IZR.
now apply lt_IZR.
Qed.

Theorem neq_IZR :
  forall m n, (IZR m <> IZR n)%R -> (m <> n)%Z.
Proof.
intros m n H H'.
apply H.
now apply f_equal.
Qed.

End IZR.

(** Decidable comparison on reals *)
Section Rcompare.

Definition Rcompare x y :=
  match total_order_T x y with
  | inleft (left _) => Lt
  | inleft (right _) => Eq
  | inright _ => Gt
  end.

Inductive Rcompare_prop (x y : R) : comparison -> Prop :=
  | Rcompare_Lt_ : (x < y)%R -> Rcompare_prop x y Lt
  | Rcompare_Eq_ : x = y -> Rcompare_prop x y Eq
  | Rcompare_Gt_ : (y < x)%R -> Rcompare_prop x y Gt.

Theorem Rcompare_spec :
  forall x y, Rcompare_prop x y (Rcompare x y).
Proof.
intros x y.
unfold Rcompare.
now destruct (total_order_T x y) as [[H|H]|H] ; constructor.
Qed.

Global Opaque Rcompare.

Theorem Rcompare_Lt :
  forall x y,
  (x < y)%R -> Rcompare x y = Lt.
Proof.
intros x y H.
case Rcompare_spec ; intro H'.
easy.
rewrite H' in H.
elim (Rlt_irrefl _ H).
elim (Rlt_irrefl x).
now apply Rlt_trans with y.
Qed.

Theorem Rcompare_Lt_inv :
  forall x y,
  Rcompare x y = Lt -> (x < y)%R.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_not_Lt :
  forall x y,
  (y <= x)%R -> Rcompare x y <> Lt.
Proof.
intros x y H1 H2.
apply Rle_not_lt with (1 := H1).
now apply Rcompare_Lt_inv.
Qed.

Theorem Rcompare_not_Lt_inv :
  forall x y,
  Rcompare x y <> Lt -> (y <= x)%R.
Proof.
intros x y H.
apply Rnot_lt_le.
contradict H.
now apply Rcompare_Lt.
Qed.

Theorem Rcompare_Eq :
  forall x y,
  x = y -> Rcompare x y = Eq.
Proof.
intros x y H.
rewrite H.
now case Rcompare_spec ; intro H' ; try elim (Rlt_irrefl _ H').
Qed.

Theorem Rcompare_Eq_inv :
  forall x y,
  Rcompare x y = Eq -> x = y.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_Gt :
  forall x y,
  (y < x)%R -> Rcompare x y = Gt.
Proof.
intros x y H.
case Rcompare_spec ; intro H'.
elim (Rlt_irrefl x).
now apply Rlt_trans with y.
rewrite H' in H.
elim (Rlt_irrefl _ H).
easy.
Qed.

Theorem Rcompare_Gt_inv :
  forall x y,
  Rcompare x y = Gt -> (y < x)%R.
Proof.
intros x y.
now case Rcompare_spec.
Qed.

Theorem Rcompare_not_Gt :
  forall x y,
  (x <= y)%R -> Rcompare x y <> Gt.
Proof.
intros x y H1 H2.
apply Rle_not_lt with (1 := H1).
now apply Rcompare_Gt_inv.
Qed.

Theorem Rcompare_not_Gt_inv :
  forall x y,
  Rcompare x y <> Gt -> (x <= y)%R.
Proof.
intros x y H.
apply Rnot_lt_le.
contradict H.
now apply Rcompare_Gt.
Qed.

Theorem Rcompare_IZR :
  forall x y, Rcompare (IZR x) (IZR y) = Z.compare x y.
Proof.
intros x y.
case Rcompare_spec ; intros H ; apply sym_eq.
apply Zcompare_Lt.
now apply lt_IZR.
apply Zcompare_Eq.
now apply eq_IZR.
apply Zcompare_Gt.
now apply lt_IZR.
Qed.

Theorem Rcompare_sym :
  forall x y,
  Rcompare x y = CompOpp (Rcompare y x).
Proof.
intros x y.
destruct (Rcompare_spec y x) as [H|H|H].
now apply Rcompare_Gt.
now apply Rcompare_Eq.
now apply Rcompare_Lt.
Qed.

Lemma Rcompare_opp :
  forall x y,
  Rcompare (- x) (- y) = Rcompare y x.
Proof.
intros x y.
destruct (Rcompare_spec y x);
  destruct (Rcompare_spec (- x) (- y));
  try reflexivity; exfalso; lra.
Qed.

Theorem Rcompare_plus_r :
  forall z x y,
  Rcompare (x + z) (y + z) = Rcompare x y.
Proof.
intros z x y.
destruct (Rcompare_spec x y) as [H|H|H].
apply Rcompare_Lt.
now apply Rplus_lt_compat_r.
apply Rcompare_Eq.
now rewrite H.
apply Rcompare_Gt.
now apply Rplus_lt_compat_r.
Qed.

Theorem Rcompare_plus_l :
  forall z x y,
  Rcompare (z + x) (z + y) = Rcompare x y.
Proof.
intros z x y.
rewrite 2!(Rplus_comm z).
apply Rcompare_plus_r.
Qed.

Theorem Rcompare_mult_r :
  forall z x y,
  (0 < z)%R ->
  Rcompare (x * z) (y * z) = Rcompare x y.
Proof.
intros z x y Hz.
destruct (Rcompare_spec x y) as [H|H|H].
apply Rcompare_Lt.
now apply Rmult_lt_compat_r.
apply Rcompare_Eq.
now rewrite H.
apply Rcompare_Gt.
now apply Rmult_lt_compat_r.
Qed.

Theorem Rcompare_mult_l :
  forall z x y,
  (0 < z)%R ->
  Rcompare (z * x) (z * y) = Rcompare x y.
Proof.
intros z x y.
rewrite 2!(Rmult_comm z).
apply Rcompare_mult_r.
Qed.

Theorem Rcompare_middle :
  forall x d u,
  Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2).
Proof.
intros x d u.
rewrite <- (Rcompare_plus_r (- x / 2 - d / 2) x).
rewrite <- (Rcompare_mult_r (/2) (x - d)).
field_simplify (x + (- x / 2 - d / 2))%R.
now field_simplify ((d + u) / 2 + (- x / 2 - d / 2))%R.
apply Rinv_0_lt_compat.
now apply IZR_lt.
Qed.

Theorem Rcompare_half_l :
  forall x y, Rcompare (x / 2) y = Rcompare x (2 * y).
Proof.
intros x y.
rewrite <- (Rcompare_mult_r 2%R).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now rewrite Rmult_comm.
now apply IZR_neq.
now apply IZR_lt.
Qed.

Theorem Rcompare_half_r :
  forall x y, Rcompare x (y / 2) = Rcompare (2 * x) y.
Proof.
intros x y.
rewrite <- (Rcompare_mult_r 2%R).
unfold Rdiv.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now rewrite Rmult_comm.
now apply IZR_neq.
now apply IZR_lt.
Qed.

Theorem Rcompare_sqr :
  forall x y,
  Rcompare (x * x) (y * y) = Rcompare (Rabs x) (Rabs y).
Proof.
intros x y.
destruct (Rcompare_spec (Rabs x) (Rabs y)) as [H|H|H].
apply Rcompare_Lt.
now apply Rsqr_lt_abs_1.
change (Rcompare (Rsqr x) (Rsqr y) = Eq).
rewrite Rsqr_abs, H, (Rsqr_abs y).
now apply Rcompare_Eq.
apply Rcompare_Gt.
now apply Rsqr_lt_abs_1.
Qed.

Theorem Rmin_compare :
  forall x y,
  Rmin x y = match Rcompare x y with Lt => x | Eq => x | Gt => y end.
Proof.
intros x y.
unfold Rmin.
destruct (Rle_dec x y) as [[Hx|Hx]|Hx].
now rewrite Rcompare_Lt.
now rewrite Rcompare_Eq.
rewrite Rcompare_Gt.
easy.
now apply Rnot_le_lt.
Qed.

End Rcompare.

Section Rle_bool.

Definition Rle_bool x y :=
  match Rcompare x y with
  | Gt => false
  | _ => true
  end.

Inductive Rle_bool_prop (x y : R) : bool -> Prop :=
  | Rle_bool_true_ : (x <= y)%R -> Rle_bool_prop x y true
  | Rle_bool_false_ : (y < x)%R -> Rle_bool_prop x y false.

Theorem Rle_bool_spec :
  forall x y, Rle_bool_prop x y (Rle_bool x y).
Proof.
intros x y.
unfold Rle_bool.
case Rcompare_spec ; constructor.
now apply Rlt_le.
rewrite H.
apply Rle_refl.
exact H.
Qed.

Theorem Rle_bool_true :
  forall x y,
  (x <= y)%R -> Rle_bool x y = true.
Proof.
intros x y Hxy.
case Rle_bool_spec ; intros H.
apply refl_equal.
elim (Rlt_irrefl x).
now apply Rle_lt_trans with y.
Qed.

Theorem Rle_bool_false :
  forall x y,
  (y < x)%R -> Rle_bool x y = false.
Proof.
intros x y Hxy.
case Rle_bool_spec ; intros H.
elim (Rlt_irrefl x).
now apply Rle_lt_trans with y.
apply refl_equal.
Qed.

End Rle_bool.

Section Rlt_bool.

Definition Rlt_bool x y :=
  match Rcompare x y with
  | Lt => true
  | _ => false
  end.

Inductive Rlt_bool_prop (x y : R) : bool -> Prop :=
  | Rlt_bool_true_ : (x < y)%R -> Rlt_bool_prop x y true
  | Rlt_bool_false_ : (y <= x)%R -> Rlt_bool_prop x y false.

Theorem Rlt_bool_spec :
  forall x y, Rlt_bool_prop x y (Rlt_bool x y).
Proof.
intros x y.
unfold Rlt_bool.
case Rcompare_spec ; constructor.
exact H.
rewrite H.
apply Rle_refl.
now apply Rlt_le.
Qed.

Theorem negb_Rlt_bool :
  forall x y,
  negb (Rle_bool x y) = Rlt_bool y x.
Proof.
intros x y.
unfold Rlt_bool, Rle_bool.
rewrite Rcompare_sym.
now case Rcompare.
Qed.

Theorem negb_Rle_bool :
  forall x y,
  negb (Rlt_bool x y) = Rle_bool y x.
Proof.
intros x y.
unfold Rlt_bool, Rle_bool.
rewrite Rcompare_sym.
now case Rcompare.
Qed.

Theorem Rlt_bool_true :
  forall x y,
  (x < y)%R -> Rlt_bool x y = true.
Proof.
intros x y Hxy.
rewrite <- negb_Rlt_bool.
now rewrite Rle_bool_false.
Qed.

Theorem Rlt_bool_false :
  forall x y,
  (y <= x)%R -> Rlt_bool x y = false.
Proof.
intros x y Hxy.
rewrite <- negb_Rlt_bool.
now rewrite Rle_bool_true.
Qed.

Lemma Rlt_bool_opp :
  forall x y,
  Rlt_bool (- x) (- y) = Rlt_bool y x.
Proof.
intros x y.
now unfold Rlt_bool; rewrite Rcompare_opp.
Qed.

End Rlt_bool.

Section Req_bool.

Definition Req_bool x y :=
  match Rcompare x y with
  | Eq => true
  | _ => false
  end.

Inductive Req_bool_prop (x y : R) : bool -> Prop :=
  | Req_bool_true_ : (x = y)%R -> Req_bool_prop x y true
  | Req_bool_false_ : (x <> y)%R -> Req_bool_prop x y false.

Theorem Req_bool_spec :
  forall x y, Req_bool_prop x y (Req_bool x y).
Proof.
intros x y.
unfold Req_bool.
case Rcompare_spec ; constructor.
now apply Rlt_not_eq.
easy.
now apply Rgt_not_eq.
Qed.

Theorem Req_bool_true :
  forall x y,
  (x = y)%R -> Req_bool x y = true.
Proof.
intros x y Hxy.
case Req_bool_spec ; intros H.
apply refl_equal.
contradict H.
exact Hxy.
Qed.

Theorem Req_bool_false :
  forall x y,
  (x <> y)%R -> Req_bool x y = false.
Proof.
intros x y Hxy.
case Req_bool_spec ; intros H.
contradict Hxy.
exact H.
apply refl_equal.
Qed.

End Req_bool.

Section Floor_Ceil.

(** Zfloor and Zceil *)
Definition Zfloor (x : R) := (up x - 1)%Z.

Theorem Zfloor_lb :
  forall x : R,
  (IZR (Zfloor x) <= x)%R.
Proof.
intros x.
unfold Zfloor.
rewrite minus_IZR.
simpl.
apply Rplus_le_reg_r with (1 - x)%R.
ring_simplify.
exact (proj2 (archimed x)).
Qed.

Theorem Zfloor_ub :
  forall x : R,
  (x < IZR (Zfloor x) + 1)%R.
Proof.
intros x.
unfold Zfloor.
rewrite minus_IZR.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
exact (proj1 (archimed x)).
Qed.

Theorem Zfloor_lub :
  forall n x,
  (IZR n <= x)%R ->
  (n <= Zfloor x)%Z.
Proof.
intros n x Hnx.
apply Zlt_succ_le.
apply lt_IZR.
apply Rle_lt_trans with (1 := Hnx).
unfold Z.succ.
rewrite plus_IZR.
apply Zfloor_ub.
Qed.

Theorem Zfloor_imp :
  forall n x,
  (IZR n <= x < IZR (n + 1))%R ->
  Zfloor x = n.
Proof.
intros n x Hnx.
apply Zle_antisym.
apply Zlt_succ_le.
apply lt_IZR.
apply Rle_lt_trans with (2 := proj2 Hnx).
apply Zfloor_lb.
now apply Zfloor_lub.
Qed.

Theorem Zfloor_IZR :
  forall n,
  Zfloor (IZR n) = n.
Proof.
intros n.
apply Zfloor_imp.
split.
apply Rle_refl.
apply IZR_lt.
apply Zlt_succ.
Qed.

Theorem Zfloor_le :
  forall x y, (x <= y)%R ->
  (Zfloor x <= Zfloor y)%Z.
Proof.
intros x y Hxy.
apply Zfloor_lub.
apply Rle_trans with (2 := Hxy).
apply Zfloor_lb.
Qed.

Definition Zceil (x : R) := (- Zfloor (- x))%Z.

Theorem Zceil_ub :
  forall x : R,
  (x <= IZR (Zceil x))%R.
Proof.
intros x.
unfold Zceil.
rewrite opp_IZR.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Zfloor_lb.
Qed.

Theorem Zceil_lb :
  forall x : R,
  (IZR (Zceil x) < x + 1)%R.
Proof.
intros x.
unfold Zceil.
rewrite opp_IZR.
rewrite <-(Ropp_involutive (x + 1)), Ropp_plus_distr.
apply Ropp_lt_contravar, (Rplus_lt_reg_r 1); ring_simplify.
apply Zfloor_ub.
Qed.

Theorem Zceil_glb :
  forall n x,
  (x <= IZR n)%R ->
  (Zceil x <= n)%Z.
Proof.
intros n x Hnx.
unfold Zceil.
apply Zopp_le_cancel.
rewrite Z.opp_involutive.
apply Zfloor_lub.
rewrite opp_IZR.
now apply Ropp_le_contravar.
Qed.

Theorem Zceil_imp :
  forall n x,
  (IZR (n - 1) < x <= IZR n)%R ->
  Zceil x = n.
Proof.
intros n x Hnx.
unfold Zceil.
rewrite <- (Z.opp_involutive n).
apply f_equal.
apply Zfloor_imp.
split.
rewrite opp_IZR.
now apply Ropp_le_contravar.
rewrite <- (Z.opp_involutive 1).
rewrite <- Zopp_plus_distr.
rewrite opp_IZR.
now apply Ropp_lt_contravar.
Qed.

Theorem Zceil_IZR :
  forall n,
  Zceil (IZR n) = n.
Proof.
intros n.
unfold Zceil.
rewrite <- opp_IZR, Zfloor_IZR.
apply Z.opp_involutive.
Qed.

Theorem Zceil_le :
  forall x y, (x <= y)%R ->
  (Zceil x <= Zceil y)%Z.
Proof.
intros x y Hxy.
apply Zceil_glb.
apply Rle_trans with (1 := Hxy).
apply Zceil_ub.
Qed.

Theorem Zceil_floor_neq :
  forall x : R,
  (IZR (Zfloor x) <> x)%R ->
  (Zceil x = Zfloor x + 1)%Z.
Proof.
intros x Hx.
apply Zceil_imp.
split.
ring_simplify (Zfloor x + 1 - 1)%Z.
apply Rnot_le_lt.
intros H.
apply Hx.
apply Rle_antisym.
apply Zfloor_lb.
exact H.
apply Rlt_le.
rewrite plus_IZR.
apply Zfloor_ub.
Qed.

Definition Ztrunc x := if Rlt_bool x 0 then Zceil x else Zfloor x.

Theorem Ztrunc_IZR :
  forall n,
  Ztrunc (IZR n) = n.
Proof.
intros n.
unfold Ztrunc.
case Rlt_bool_spec ; intro H.
apply Zceil_IZR.
apply Zfloor_IZR.
Qed.

Theorem Ztrunc_floor :
  forall x,
  (0 <= x)%R ->
  Ztrunc x = Zfloor x.
Proof.
intros x Hx.
unfold Ztrunc.
case Rlt_bool_spec ; intro H.
elim Rlt_irrefl with x.
now apply Rlt_le_trans with R0.
apply refl_equal.
Qed.

Theorem Ztrunc_ceil :
  forall x,
  (x <= 0)%R ->
  Ztrunc x = Zceil x.
Proof.
intros x Hx.
unfold Ztrunc.
case Rlt_bool_spec ; intro H.
apply refl_equal.
rewrite (Rle_antisym _ _ Hx H).
rewrite Zceil_IZR.
apply Zfloor_IZR.
Qed.

Theorem Ztrunc_le :
  forall x y, (x <= y)%R ->
  (Ztrunc x <= Ztrunc y)%Z.
Proof.
intros x y Hxy.
unfold Ztrunc at 1.
case Rlt_bool_spec ; intro Hx.
unfold Ztrunc.
case Rlt_bool_spec ; intro Hy.
now apply Zceil_le.
apply Z.le_trans with 0%Z.
apply Zceil_glb.
now apply Rlt_le.
now apply Zfloor_lub.
rewrite Ztrunc_floor.
now apply Zfloor_le.
now apply Rle_trans with x.
Qed.

Theorem Ztrunc_opp :
  forall x,
  Ztrunc (- x) = Z.opp (Ztrunc x).
Proof.
intros x.
unfold Ztrunc at 2.
case Rlt_bool_spec ; intros Hx.
rewrite Ztrunc_floor.
apply sym_eq.
apply Z.opp_involutive.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite Ztrunc_ceil.
unfold Zceil.
now rewrite Ropp_involutive.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
Qed.

Theorem Ztrunc_abs :
  forall x,
  Ztrunc (Rabs x) = Z.abs (Ztrunc x).
Proof.
intros x.
rewrite Ztrunc_floor. 2: apply Rabs_pos.
unfold Ztrunc.
case Rlt_bool_spec ; intro H.
rewrite Rabs_left with (1 := H).
rewrite Zabs_non_eq.
apply sym_eq.
apply Z.opp_involutive.
apply Zceil_glb.
now apply Rlt_le.
rewrite Rabs_pos_eq with (1 := H).
apply sym_eq.
apply Z.abs_eq.
now apply Zfloor_lub.
Qed.

Theorem Ztrunc_lub :
  forall n x,
  (IZR n <= Rabs x)%R ->
  (n <= Z.abs (Ztrunc x))%Z.
Proof.
intros n x H.
rewrite <- Ztrunc_abs.
rewrite Ztrunc_floor. 2: apply Rabs_pos.
now apply Zfloor_lub.
Qed.

Definition Zaway x := if Rlt_bool x 0 then Zfloor x else Zceil x.

Theorem Zaway_IZR :
  forall n,
  Zaway (IZR n) = n.
Proof.
intros n.
unfold Zaway.
case Rlt_bool_spec ; intro H.
apply Zfloor_IZR.
apply Zceil_IZR.
Qed.

Theorem Zaway_ceil :
  forall x,
  (0 <= x)%R ->
  Zaway x = Zceil x.
Proof.
intros x Hx.
unfold Zaway.
case Rlt_bool_spec ; intro H.
elim Rlt_irrefl with x.
now apply Rlt_le_trans with R0.
apply refl_equal.
Qed.

Theorem Zaway_floor :
  forall x,
  (x <= 0)%R ->
  Zaway x = Zfloor x.
Proof.
intros x Hx.
unfold Zaway.
case Rlt_bool_spec ; intro H.
apply refl_equal.
rewrite (Rle_antisym _ _ Hx H).
rewrite Zfloor_IZR.
apply Zceil_IZR.
Qed.

Theorem Zaway_le :
  forall x y, (x <= y)%R ->
  (Zaway x <= Zaway y)%Z.
Proof.
intros x y Hxy.
unfold Zaway at 1.
case Rlt_bool_spec ; intro Hx.
unfold Zaway.
case Rlt_bool_spec ; intro Hy.
now apply Zfloor_le.
apply le_IZR.
apply Rle_trans with 0%R.
apply Rlt_le.
apply Rle_lt_trans with (2 := Hx).
apply Zfloor_lb.
apply Rle_trans with (1 := Hy).
apply Zceil_ub.
rewrite Zaway_ceil.
now apply Zceil_le.
now apply Rle_trans with x.
Qed.

Theorem Zaway_opp :
  forall x,
  Zaway (- x) = Z.opp (Zaway x).
Proof.
intros x.
unfold Zaway at 2.
case Rlt_bool_spec ; intro H.
rewrite Zaway_ceil.
unfold Zceil.
now rewrite Ropp_involutive.
apply Rlt_le.
now apply Ropp_0_gt_lt_contravar.
rewrite Zaway_floor.
apply sym_eq.
apply Z.opp_involutive.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
Qed.

Theorem Zaway_abs :
  forall x,
  Zaway (Rabs x) = Z.abs (Zaway x).
Proof.
intros x.
rewrite Zaway_ceil. 2: apply Rabs_pos.
unfold Zaway.
case Rlt_bool_spec ; intro H.
rewrite Rabs_left with (1 := H).
rewrite Zabs_non_eq.
apply (f_equal (fun v => - Zfloor v)%Z).
apply Ropp_involutive.
apply le_IZR.
apply Rlt_le.
apply Rle_lt_trans with (2 := H).
apply Zfloor_lb.
rewrite Rabs_pos_eq with (1 := H).
apply sym_eq.
apply Z.abs_eq.
apply le_IZR.
apply Rle_trans with (1 := H).
apply Zceil_ub.
Qed.

End Floor_Ceil.

Theorem Rcompare_floor_ceil_middle :
  forall x,
  IZR (Zfloor x) <> x ->
  Rcompare (x - IZR (Zfloor x)) (/ 2) = Rcompare (x - IZR (Zfloor x)) (IZR (Zceil x) - x).
Proof.
intros x Hx.
rewrite Zceil_floor_neq with (1 := Hx).
rewrite plus_IZR.
destruct (Rcompare_spec (x - IZR (Zfloor x)) (/ 2)) as [H1|H1|H1] ; apply sym_eq.
(* . *)
apply Rcompare_Lt.
apply Rplus_lt_reg_l with (x - IZR (Zfloor x))%R.
replace (x - IZR (Zfloor x) + (x - IZR (Zfloor x)))%R with ((x - IZR (Zfloor x)) * 2)%R by ring.
replace (x - IZR (Zfloor x) + (IZR (Zfloor x) + 1 - x))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply IZR_lt.
(* . *)
apply Rcompare_Eq.
replace (IZR (Zfloor x) + 1 - x)%R with (1 - (x - IZR (Zfloor x)))%R by ring.
rewrite H1.
field.
(* . *)
apply Rcompare_Gt.
apply Rplus_lt_reg_l with (x - IZR (Zfloor x))%R.
replace (x - IZR (Zfloor x) + (x - IZR (Zfloor x)))%R with ((x - IZR (Zfloor x)) * 2)%R by ring.
replace (x - IZR (Zfloor x) + (IZR (Zfloor x) + 1 - x))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply IZR_lt.
Qed.

Theorem Rcompare_ceil_floor_middle :
  forall x,
  IZR (Zfloor x) <> x ->
  Rcompare (IZR (Zceil x) - x) (/ 2) = Rcompare (IZR (Zceil x) - x) (x - IZR (Zfloor x)).
Proof.
intros x Hx.
rewrite Zceil_floor_neq with (1 := Hx).
rewrite plus_IZR.
destruct (Rcompare_spec (IZR (Zfloor x) + 1 - x) (/ 2)) as [H1|H1|H1] ; apply sym_eq.
(* . *)
apply Rcompare_Lt.
apply Rplus_lt_reg_l with (IZR (Zfloor x) + 1 - x)%R.
replace (IZR (Zfloor x) + 1 - x + (IZR (Zfloor x) + 1 - x))%R with ((IZR (Zfloor x) + 1 - x) * 2)%R by ring.
replace (IZR (Zfloor x) + 1 - x + (x - IZR (Zfloor x)))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply IZR_lt.
(* . *)
apply Rcompare_Eq.
replace (x - IZR (Zfloor x))%R with (1 - (IZR (Zfloor x) + 1 - x))%R by ring.
rewrite H1.
field.
(* . *)
apply Rcompare_Gt.
apply Rplus_lt_reg_l with (IZR (Zfloor x) + 1 - x)%R.
replace (IZR (Zfloor x) + 1 - x + (IZR (Zfloor x) + 1 - x))%R with ((IZR (Zfloor x) + 1 - x) * 2)%R by ring.
replace (IZR (Zfloor x) + 1 - x + (x - IZR (Zfloor x)))%R with (/2 * 2)%R by field.
apply Rmult_lt_compat_r with (2 := H1).
now apply IZR_lt.
Qed.

Theorem Zfloor_div :
  forall x y,
  y <> Z0 ->
  Zfloor (IZR x / IZR y) = (x / y)%Z.
Proof.
intros x y Zy.
generalize (Z.div_mod x y Zy).
intros Hx.
rewrite Hx at 1.
assert (Zy': IZR y <> 0%R).
contradict Zy.
now apply eq_IZR.
unfold Rdiv.
rewrite plus_IZR, Rmult_plus_distr_r, mult_IZR.
replace (IZR y * IZR (x / y) * / IZR y)%R with (IZR (x / y)) by now field.
apply Zfloor_imp.
rewrite plus_IZR.
assert (0 <= IZR (x mod y) * / IZR y < 1)%R.
(* *)
assert (forall x' y', (0 < y')%Z -> 0 <= IZR (x' mod y') * / IZR y' < 1)%R.
(* . *)
clear.
intros x y Hy.
split.
apply Rmult_le_pos.
apply IZR_le.
refine (proj1 (Z_mod_lt _ _ _)).
now apply Z.lt_gt.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply Rmult_lt_reg_r with (IZR y).
now apply IZR_lt.
rewrite Rmult_1_l, Rmult_assoc, Rinv_l, Rmult_1_r.
apply IZR_lt.
eapply Z_mod_lt.
now apply Z.lt_gt.
apply Rgt_not_eq.
now apply IZR_lt.
(* . *)
destruct (Z_lt_le_dec y 0) as [Hy|Hy].
rewrite <- Rmult_opp_opp.
rewrite Ropp_inv_permute with (1 := Zy').
rewrite <- 2!opp_IZR.
rewrite <- Zmod_opp_opp.
apply H.
clear -Hy ; lia.
apply H.
clear -Zy Hy ; lia.
(* *)
split.
pattern (IZR (x / y)) at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
apply H.
apply Rplus_lt_compat_l.
apply H.
Qed.

Theorem Ztrunc_div :
  forall x y, y <> 0%Z ->
  Ztrunc (IZR x / IZR y) = Z.quot x y.
Proof.
  destruct y; [easy | |]; destruct x; intros _.
  - rewrite Z.quot_0_l; [| easy]. unfold Rdiv. rewrite Rmult_0_l.
    rewrite Ztrunc_floor; [| apply Rle_refl]. now rewrite Zfloor_IZR.
  - rewrite Z.quot_div_nonneg; [| easy | easy]. rewrite <-Zfloor_div; [| easy].
    unfold Ztrunc. rewrite Rlt_bool_false; [reflexivity |].
    apply Rle_mult_inv_pos; [now apply IZR_le | now apply IZR_lt].
  - rewrite <-Pos2Z.opp_pos. rewrite Z.quot_opp_l; [| easy].
    rewrite Z.quot_div_nonneg; [| easy | easy]. rewrite <-Zfloor_div; [| easy].
    rewrite Ropp_Ropp_IZR. rewrite Ropp_div. unfold Ztrunc. rewrite Rlt_bool_true.
    + unfold Zceil. now rewrite Ropp_involutive.
    + apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; now apply IZR_lt.
  - rewrite Z.quot_0_l; [| easy]. unfold Rdiv. rewrite Rmult_0_l.
    rewrite Ztrunc_floor; [| apply Rle_refl]. now rewrite Zfloor_IZR.
  - rewrite <-Pos2Z.opp_pos. rewrite Z.quot_opp_r; [| easy].
    rewrite Z.quot_div_nonneg; [| easy | easy]. rewrite <-Zfloor_div; [| easy].
    rewrite Ropp_Ropp_IZR. rewrite Ropp_div_den; [| easy]. unfold Ztrunc.
    rewrite Rlt_bool_true.
    + unfold Zceil. now rewrite Ropp_involutive.
    + apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; now apply IZR_lt.
  - rewrite <-2Pos2Z.opp_pos. rewrite Z.quot_opp_l; [| easy]. rewrite Z.quot_opp_r; [| easy].
    rewrite Z.quot_div_nonneg; [| easy | easy]. rewrite <-Zfloor_div; [| easy].
    rewrite 2Ropp_Ropp_IZR. rewrite Ropp_div. rewrite Ropp_div_den; [| easy].
    rewrite Z.opp_involutive. rewrite Ropp_involutive.
    unfold Ztrunc. rewrite Rlt_bool_false; [reflexivity |].
    apply Rle_mult_inv_pos; [now apply IZR_le | now apply IZR_lt].
Qed.

Section pow.

Variable r : radix.

Theorem radix_pos : (0 < IZR r)%R.
Proof.
destruct r as (v, Hr). simpl.
apply IZR_lt.
apply Z.lt_le_trans with 2%Z.
easy.
now apply Zle_bool_imp_le.
Qed.

(** Well-used function called bpow for computing the power function #&beta;#^e *)
Definition bpow e :=
  match e with
  | Zpos p => IZR (Zpower_pos r p)
  | Zneg p => Rinv (IZR (Zpower_pos r p))
  | Z0 => 1%R
  end.

Theorem IZR_Zpower_pos :
  forall n m,
  IZR (Zpower_pos n m) = powerRZ (IZR n) (Zpos m).
Proof.
intros.
rewrite Zpower_pos_nat.
simpl.
induction (nat_of_P m).
apply refl_equal.
unfold Zpower_nat.
simpl.
rewrite mult_IZR.
apply Rmult_eq_compat_l.
exact IHn0.
Qed.

Theorem bpow_powerRZ :
  forall e,
  bpow e = powerRZ (IZR r) e.
Proof.
destruct e ; unfold bpow.
reflexivity.
now rewrite IZR_Zpower_pos.
now rewrite IZR_Zpower_pos.
Qed.

Theorem  bpow_ge_0 :
  forall e : Z, (0 <= bpow e)%R.
Proof.
intros.
rewrite bpow_powerRZ.
apply powerRZ_le.
apply radix_pos.
Qed.

Theorem bpow_gt_0 :
  forall e : Z, (0 < bpow e)%R.
Proof.
intros.
rewrite bpow_powerRZ.
apply powerRZ_lt.
apply radix_pos.
Qed.

Theorem bpow_plus :
  forall e1 e2 : Z, (bpow (e1 + e2) = bpow e1 * bpow e2)%R.
Proof.
intros.
repeat rewrite bpow_powerRZ.
apply powerRZ_add.
apply Rgt_not_eq.
apply radix_pos.
Qed.

Theorem bpow_1 :
  bpow 1 = IZR r.
Proof.
unfold bpow, Zpower_pos. simpl.
now rewrite Zmult_1_r.
Qed.

Theorem bpow_plus_1 :
  forall e : Z, (bpow (e + 1) = IZR r * bpow e)%R.
Proof.
intros.
rewrite <- bpow_1.
rewrite <- bpow_plus.
now rewrite Zplus_comm.
Qed.

Theorem bpow_opp :
  forall e : Z, (bpow (-e) = /bpow e)%R.
Proof.
intros [|p|p].
apply eq_sym, Rinv_1.
now change (-Zpos p)%Z with (Zneg p).
change (-Zneg p)%Z with (Zpos p).
simpl; rewrite Rinv_involutive; trivial.
apply Rgt_not_eq.
apply (bpow_gt_0 (Zpos p)).
Qed.

Theorem IZR_Zpower_nat :
  forall e : nat,
  IZR (Zpower_nat r e) = bpow (Z_of_nat e).
Proof.
intros [|e].
split.
rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ.
rewrite <- Zpower_pos_nat.
now rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Theorem IZR_Zpower :
  forall e : Z,
  (0 <= e)%Z ->
  IZR (Zpower r e) = bpow e.
Proof.
intros [|e|e] H.
split.
split.
now elim H.
Qed.

Theorem bpow_lt :
  forall e1 e2 : Z,
  (e1 < e2)%Z -> (bpow e1 < bpow e2)%R.
Proof.
intros e1 e2 H.
replace e2 with (e1 + (e2 - e1))%Z by ring.
rewrite <- (Rmult_1_r (bpow e1)).
rewrite bpow_plus.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
assert (0 < e2 - e1)%Z by lia.
destruct (e2 - e1)%Z ; try discriminate H0.
clear.
rewrite <- IZR_Zpower by easy.
apply IZR_lt.
now apply Zpower_gt_1.
Qed.

Theorem lt_bpow :
  forall e1 e2 : Z,
  (bpow e1 < bpow e2)%R -> (e1 < e2)%Z.
Proof.
intros e1 e2 H.
apply Z.gt_lt.
apply Znot_le_gt.
intros H'.
apply Rlt_not_le with (1 := H).
destruct (Zle_lt_or_eq _ _ H').
apply Rlt_le.
now apply bpow_lt.
rewrite H0.
apply Rle_refl.
Qed.

Theorem bpow_le :
  forall e1 e2 : Z,
  (e1 <= e2)%Z -> (bpow e1 <= bpow e2)%R.
Proof.
intros e1 e2 H.
apply Rnot_lt_le.
intros H'.
apply Zle_not_gt with (1 := H).
apply Z.lt_gt.
now apply lt_bpow.
Qed.

Theorem le_bpow :
  forall e1 e2 : Z,
  (bpow e1 <= bpow e2)%R -> (e1 <= e2)%Z.
Proof.
intros e1 e2 H.
apply Znot_gt_le.
intros H'.
apply Rle_not_lt with (1 := H).
apply bpow_lt.
now apply Z.gt_lt.
Qed.

Theorem bpow_inj :
  forall e1 e2 : Z,
  bpow e1 = bpow e2 -> e1 = e2.
Proof.
intros.
apply Zle_antisym.
apply le_bpow.
now apply Req_le.
apply le_bpow.
now apply Req_le.
Qed.

Theorem bpow_exp :
  forall e : Z,
  bpow e = exp (IZR e * ln (IZR r)).
Proof.
(* positive case *)
assert (forall e, bpow (Zpos e) = exp (IZR (Zpos e) * ln (IZR r))).
intros e.
unfold bpow.
rewrite Zpower_pos_nat.
rewrite <- positive_nat_Z.
rewrite <- INR_IZR_INZ.
induction (nat_of_P e).
rewrite Rmult_0_l.
now rewrite exp_0.
rewrite Zpower_nat_S.
rewrite S_INR.
rewrite Rmult_plus_distr_r.
rewrite exp_plus.
rewrite Rmult_1_l.
rewrite exp_ln.
rewrite <- IHn.
rewrite <- mult_IZR.
now rewrite Zmult_comm.
apply radix_pos.
(* general case *)
intros [|e|e].
rewrite Rmult_0_l.
now rewrite exp_0.
apply H.
unfold bpow.
change (IZR (Zpower_pos r e)) with (bpow (Zpos e)).
rewrite H.
rewrite <- exp_Ropp.
rewrite <- Ropp_mult_distr_l_reverse.
now rewrite <- opp_IZR.
Qed.

Lemma sqrt_bpow :
  forall e,
  sqrt (bpow (2 * e)) = bpow e.
Proof.
intro e.
change 2%Z with (1 + 1)%Z; rewrite Z.mul_add_distr_r, Z.mul_1_l, bpow_plus.
apply sqrt_square, bpow_ge_0.
Qed.

Lemma sqrt_bpow_ge :
  forall e,
  (bpow (e / 2) <= sqrt (bpow e))%R.
Proof.
intro e.
rewrite <- (sqrt_square (bpow _)); [|now apply bpow_ge_0].
apply sqrt_le_1_alt; rewrite <- bpow_plus; apply bpow_le.
now replace (_ + _)%Z with (2 * (e / 2))%Z by ring; apply Z_mult_div_ge.
Qed.

(** Another well-used function for having the magnitude of a real number x to the base #&beta;# *)
Record mag_prop x := {
  mag_val :> Z ;
  _ : (x <> 0)%R -> (bpow (mag_val - 1)%Z <= Rabs x < bpow mag_val)%R
}.

Definition mag :
  forall x : R, mag_prop x.
Proof.
intros x.
set (fact := ln (IZR r)).
(* . *)
assert (0 < fact)%R.
apply exp_lt_inv.
rewrite exp_0.
unfold fact.
rewrite exp_ln.
apply IZR_lt.
apply radix_gt_1.
apply radix_pos.
(* . *)
exists (Zfloor (ln (Rabs x) / fact) + 1)%Z.
intros Hx'.
generalize (Rabs_pos_lt _ Hx'). clear Hx'.
generalize (Rabs x). clear x.
intros x Hx.
rewrite 2!bpow_exp.
fold fact.
pattern x at 2 3 ; replace x with (exp (ln x * / fact * fact)).
split.
rewrite minus_IZR.
apply exp_le.
apply Rmult_le_compat_r.
now apply Rlt_le.
unfold Rminus.
rewrite plus_IZR.
rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
apply Zfloor_lb.
apply exp_increasing.
apply Rmult_lt_compat_r.
exact H.
rewrite plus_IZR.
apply Zfloor_ub.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
now apply exp_ln.
now apply Rgt_not_eq.
Qed.

Theorem bpow_lt_bpow :
  forall e1 e2,
  (bpow (e1 - 1) < bpow e2)%R ->
  (e1 <= e2)%Z.
Proof.
intros e1 e2 He.
rewrite (Zsucc_pred e1).
apply Zlt_le_succ.
now apply lt_bpow.
Qed.

Theorem bpow_unique :
  forall x e1 e2,
  (bpow (e1 - 1) <= x < bpow e1)%R ->
  (bpow (e2 - 1) <= x < bpow e2)%R ->
  e1 = e2.
Proof.
intros x e1 e2 (H1a,H1b) (H2a,H2b).
apply Zle_antisym ;
  apply bpow_lt_bpow ;
  apply Rle_lt_trans with x ;
  assumption.
Qed.

Theorem mag_unique :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= Rabs x < bpow e)%R ->
  mag x = e :> Z.
Proof.
intros x e1 He.
destruct (Req_dec x 0) as [Hx|Hx].
elim Rle_not_lt with (1 := proj1 He).
rewrite Hx, Rabs_R0.
apply bpow_gt_0.
destruct (mag x) as (e2, Hx2).
simpl.
apply bpow_unique with (2 := He).
now apply Hx2.
Qed.

Theorem mag_opp :
  forall x,
  mag (-x) = mag x :> Z.
Proof.
intros x.
destruct (Req_dec x 0) as [Hx|Hx].
now rewrite Hx, Ropp_0.
destruct (mag x) as (e, He).
simpl.
specialize (He Hx).
apply mag_unique.
now rewrite Rabs_Ropp.
Qed.

Theorem mag_abs :
  forall x,
  mag (Rabs x) = mag x :> Z.
Proof.
intros x.
unfold Rabs.
case Rcase_abs ; intros _.
apply mag_opp.
apply refl_equal.
Qed.

Theorem mag_unique_pos :
  forall (x : R) (e : Z),
  (bpow (e - 1) <= x < bpow e)%R ->
  mag x = e :> Z.
Proof.
intros x e1 He1.
rewrite <- mag_abs.
apply mag_unique.
rewrite 2!Rabs_pos_eq.
exact He1.
apply Rle_trans with (2 := proj1 He1).
apply bpow_ge_0.
apply Rabs_pos.
Qed.

Theorem mag_le_abs :
  forall x y,
  (x <> 0)%R -> (Rabs x <= Rabs y)%R ->
  (mag x <= mag y)%Z.
Proof.
intros x y H0x Hxy.
destruct (mag x) as (ex, Hx).
destruct (mag y) as (ey, Hy).
simpl.
apply bpow_lt_bpow.
specialize (Hx H0x).
apply Rle_lt_trans with (1 := proj1 Hx).
apply Rle_lt_trans with (1 := Hxy).
apply Hy.
intros Hy'.
apply Rlt_not_le with (1 := Rabs_pos_lt _ H0x).
apply Rle_trans with (1 := Hxy).
rewrite Hy', Rabs_R0.
apply Rle_refl.
Qed.

Theorem mag_le :
  forall x y,
  (0 < x)%R -> (x <= y)%R ->
  (mag x <= mag y)%Z.
Proof.
intros x y H0x Hxy.
apply mag_le_abs.
now apply Rgt_not_eq.
rewrite 2!Rabs_pos_eq.
exact Hxy.
apply Rle_trans with (2 := Hxy).
now apply Rlt_le.
now apply Rlt_le.
Qed.

Lemma lt_mag :
  forall x y,
  (0 < y)%R ->
  (mag x < mag y)%Z -> (x < y)%R.
Proof.
intros x y Py.
case (Rle_or_lt x 0); intros Px.
intros H.
now apply Rle_lt_trans with 0%R.
destruct (mag x) as (ex, Hex).
destruct (mag y) as (ey, Hey).
simpl.
intro H.
destruct Hex as (_,Hex); [now apply Rgt_not_eq|].
destruct Hey as (Hey,_); [now apply Rgt_not_eq|].
rewrite Rabs_right in Hex; [|now apply Rle_ge; apply Rlt_le].
rewrite Rabs_right in Hey; [|now apply Rle_ge; apply Rlt_le].
apply (Rlt_le_trans _ _ _ Hex).
apply Rle_trans with (bpow (ey - 1)); [|exact Hey].
now apply bpow_le; lia.
Qed.

Theorem mag_bpow :
  forall e, (mag (bpow e) = e + 1 :> Z)%Z.
Proof.
intros e.
apply mag_unique.
rewrite Rabs_right.
replace (e + 1 - 1)%Z with e by ring.
split.
apply Rle_refl.
apply bpow_lt.
apply Zlt_succ.
apply Rle_ge.
apply bpow_ge_0.
Qed.

Theorem mag_mult_bpow :
  forall x e, x <> 0%R ->
  (mag (x * bpow e) = mag x + e :>Z)%Z.
Proof.
intros x e Zx.
destruct (mag x) as (ex, Ex) ; simpl.
specialize (Ex Zx).
apply mag_unique.
rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow e)) by apply bpow_ge_0.
split.
replace (ex + e - 1)%Z with (ex - 1 + e)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Ex.
rewrite bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Ex.
Qed.

Theorem mag_le_bpow :
  forall x e,
  x <> 0%R ->
  (Rabs x < bpow e)%R ->
  (mag x <= e)%Z.
Proof.
intros x e Zx Hx.
destruct (mag x) as (ex, Ex) ; simpl.
specialize (Ex Zx).
apply bpow_lt_bpow.
now apply Rle_lt_trans with (Rabs x).
Qed.

Theorem mag_gt_bpow :
  forall x e,
  (bpow e <= Rabs x)%R ->
  (e < mag x)%Z.
Proof.
intros x e Hx.
destruct (mag x) as (ex, Ex) ; simpl.
apply lt_bpow.
apply Rle_lt_trans with (1 := Hx).
apply Ex.
intros Zx.
apply Rle_not_lt with (1 := Hx).
rewrite Zx, Rabs_R0.
apply bpow_gt_0.
Qed.

Theorem mag_ge_bpow :
  forall x e,
  (bpow (e - 1) <= Rabs x)%R ->
  (e <= mag x)%Z.
Proof.
intros x e H.
destruct (Rlt_or_le (Rabs x) (bpow e)) as [Hxe|Hxe].
- (* Rabs x w bpow e *)
  assert (mag x = e :> Z) as Hln.
  now apply mag_unique; split.
  rewrite Hln.
  now apply Z.le_refl.
- (* bpow e <= Rabs x *)
  apply Zlt_le_weak.
  now apply mag_gt_bpow.
Qed.

Theorem bpow_mag_gt :
  forall x,
  (Rabs x < bpow (mag x))%R.
Proof.
intros x.
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx, Rabs_R0.
apply bpow_gt_0.
destruct (mag x) as (ex, Ex) ; simpl.
now apply Ex.
Qed.

Theorem bpow_mag_le :
  forall x, (x <> 0)%R ->
    (bpow (mag x-1) <= Rabs x)%R.
Proof.
intros x Hx.
destruct (mag x) as (ex, Ex) ; simpl.
now apply Ex.
Qed.


Theorem mag_le_Zpower :
  forall m e,
  m <> Z0 ->
  (Z.abs m < Zpower r e)%Z->
  (mag (IZR m) <= e)%Z.
Proof.
intros m e Zm Hm.
apply mag_le_bpow.
now apply IZR_neq.
destruct (Zle_or_lt 0 e).
rewrite <- abs_IZR, <- IZR_Zpower with (1 := H).
now apply IZR_lt.
elim Zm.
cut (Z.abs m < 0)%Z.
now case m.
clear -Hm H.
now destruct e.
Qed.

Theorem mag_gt_Zpower :
  forall m e,
  m <> Z0 ->
  (Zpower r e <= Z.abs m)%Z ->
  (e < mag (IZR m))%Z.
Proof.
intros m e Zm Hm.
apply mag_gt_bpow.
rewrite <- abs_IZR.
destruct (Zle_or_lt 0 e).
rewrite <- IZR_Zpower with (1 := H).
now apply IZR_le.
apply Rle_trans with (bpow 0).
apply bpow_le.
now apply Zlt_le_weak.
apply IZR_le.
clear -Zm.
lia.
Qed.

Lemma mag_mult :
  forall x y,
  (x <> 0)%R -> (y <> 0)%R ->
  (mag x + mag y - 1 <= mag (x * y) <= mag x + mag y)%Z.
Proof.
intros x y Hx Hy.
destruct (mag x) as (ex, Hx2).
destruct (mag y) as (ey, Hy2).
simpl.
destruct (Hx2 Hx) as (Hx21,Hx22); clear Hx2.
destruct (Hy2 Hy) as (Hy21,Hy22); clear Hy2.
assert (Hxy : (bpow (ex + ey - 1 - 1) <= Rabs (x * y))%R).
{ replace (ex + ey -1 -1)%Z with (ex - 1 + (ey - 1))%Z; [|ring].
  rewrite bpow_plus.
  rewrite Rabs_mult.
  now apply Rmult_le_compat; try apply bpow_ge_0. }
assert (Hxy2 : (Rabs (x * y) < bpow (ex + ey))%R).
{ rewrite Rabs_mult.
  rewrite bpow_plus.
  apply Rmult_le_0_lt_compat; try assumption.
  now apply Rle_trans with (bpow (ex - 1)); try apply bpow_ge_0.
  now apply Rle_trans with (bpow (ey - 1)); try apply bpow_ge_0. }
split.
- now apply mag_ge_bpow.
- apply mag_le_bpow.
  + now apply Rmult_integral_contrapositive_currified.
  + assumption.
Qed.

Lemma mag_plus :
  forall x y,
  (0 < y)%R -> (y <= x)%R ->
  (mag x <= mag (x + y) <= mag x + 1)%Z.
Proof.
assert (Hr : (2 <= r)%Z).
{ destruct r as (beta_val,beta_prop).
  now apply Zle_bool_imp_le. }
intros x y Hy Hxy.
assert (Hx : (0 < x)%R) by apply (Rlt_le_trans _ _ _ Hy Hxy).
destruct (mag x) as (ex,Hex); simpl.
destruct Hex as (Hex0,Hex1); [now apply Rgt_not_eq|].
assert (Haxy : (Rabs (x + y) < bpow (ex + 1))%R).
{ rewrite bpow_plus_1.
  apply Rlt_le_trans with (2 * bpow ex)%R.
  - rewrite Rabs_pos_eq.
    apply Rle_lt_trans with (2 * Rabs x)%R.
    + rewrite Rabs_pos_eq.
      replace (2 * x)%R with (x + x)%R by ring.
      now apply Rplus_le_compat_l.
      now apply Rlt_le.
    + apply Rmult_lt_compat_l with (2 := Hex1).
      exact Rlt_0_2.
    + rewrite <- (Rplus_0_l 0).
      now apply Rlt_le, Rplus_lt_compat.
  - apply Rmult_le_compat_r.
    now apply bpow_ge_0.
    now apply IZR_le. }
assert (Haxy2 : (bpow (ex - 1) <= Rabs (x + y))%R).
{ apply (Rle_trans _ _ _ Hex0).
  rewrite Rabs_right; [|now apply Rgt_ge].
  apply Rabs_ge; right.
  rewrite <- (Rplus_0_r x) at 1.
  apply Rplus_le_compat_l.
  now apply Rlt_le. }
split.
- now apply mag_ge_bpow.
- apply mag_le_bpow.
  + now apply tech_Rplus; [apply Rlt_le|].
  + exact Haxy.
Qed.

Lemma mag_minus :
  forall x y,
  (0 < y)%R -> (y < x)%R ->
  (mag (x - y) <= mag x)%Z.
Proof.
intros x y Py Hxy.
assert (Px : (0 < x)%R) by apply (Rlt_trans _ _ _ Py Hxy).
apply mag_le.
- now apply Rlt_Rminus.
- rewrite <- (Rplus_0_r x) at 2.
  apply Rplus_le_compat_l.
  rewrite <- Ropp_0.
  now apply Ropp_le_contravar; apply Rlt_le.
Qed.

Lemma mag_minus_lb :
  forall x y,
  (0 < x)%R -> (0 < y)%R ->
  (mag y <= mag x - 2)%Z ->
  (mag x - 1 <= mag (x - y))%Z.
Proof.
assert (Hbeta : (2 <= r)%Z).
{ destruct r as (beta_val,beta_prop).
  now apply Zle_bool_imp_le. }
intros x y Px Py Hln.
assert (Oxy : (y < x)%R); [apply lt_mag;[assumption|lia]|].
destruct (mag x) as (ex,Hex).
destruct (mag y) as (ey,Hey).
simpl in Hln |- *.
destruct Hex as (Hex,_); [now apply Rgt_not_eq|].
destruct Hey as (_,Hey); [now apply Rgt_not_eq|].
assert (Hbx : (bpow (ex - 2) + bpow (ex - 2) <= x)%R).
{ ring_simplify.
  apply Rle_trans with (bpow (ex - 1)).
  - replace (ex - 1)%Z with (ex - 2 + 1)%Z by ring.
    rewrite bpow_plus_1.
    apply Rmult_le_compat_r; [now apply bpow_ge_0|].
    now apply IZR_le.
  - now rewrite Rabs_right in Hex; [|apply Rle_ge; apply Rlt_le]. }
assert (Hby : (y < bpow (ex - 2))%R).
{ apply Rlt_le_trans with (bpow ey).
  now rewrite Rabs_right in Hey; [|apply Rle_ge; apply Rlt_le].
  now apply bpow_le. }
assert (Hbxy : (bpow (ex - 2) <= x - y)%R).
{ apply Ropp_lt_contravar in Hby.
  apply Rlt_le in Hby.
  replace (bpow (ex - 2))%R with (bpow (ex - 2) + bpow (ex - 2)
                                                  - bpow (ex - 2))%R by ring.
  now apply Rplus_le_compat. }
apply mag_ge_bpow.
replace (ex - 1 - 1)%Z with (ex - 2)%Z by ring.
now apply Rabs_ge; right.
Qed.

Theorem mag_plus_ge :
  forall x y,
  (x <> 0)%R ->
  (mag y <= mag x - 2)%Z ->
  (mag x - 1 <= mag (x + y))%Z.
Proof.
intros x y Zx.
destruct (Req_dec y 0) as [Zy|Zy].
{ intros _.
  rewrite Zy, Rplus_0_r.
  lia. }
rewrite <- (mag_abs x), <- (mag_abs y).
intros Hm.
assert (H: Rabs x <> Rabs y).
{ intros H.
  apply Zlt_not_le with (2 := Hm).
  rewrite H.
  lia. }
apply mag_minus_lb in Hm ; try now apply Rabs_pos_lt.
apply Z.le_trans with (1 := Hm).
apply mag_le_abs.
now apply Rminus_eq_contra.
rewrite <- (Ropp_involutive y).
rewrite Rabs_Ropp.
apply Rabs_triang_inv2.
Qed.

Lemma mag_div :
  forall x y : R,
  x <> 0%R -> y <> 0%R ->
  (mag x - mag y <= mag (x / y) <= mag x - mag y + 1)%Z.
Proof.
intros x y Px Py.
destruct (mag x) as (ex,Hex).
destruct (mag y) as (ey,Hey).
simpl.
unfold Rdiv.
assert (Heiy : (bpow (- ey) < Rabs (/ y) <= bpow (- ey + 1))%R).
{ rewrite Rabs_Rinv by easy.
  split.
  - rewrite bpow_opp.
    apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat.
      now apply Rabs_pos_lt.
      now apply bpow_gt_0.
    + now apply Hey.
  - replace (_ + _)%Z with (- (ey - 1))%Z by ring.
    rewrite bpow_opp.
    apply Rinv_le; [now apply bpow_gt_0|].
    now apply Hey. }
split.
- apply mag_ge_bpow.
  replace (_ - _)%Z with (ex - 1 - ey)%Z by ring.
  unfold Zminus at 1; rewrite bpow_plus.
  rewrite Rabs_mult.
  apply Rmult_le_compat.
  + now apply bpow_ge_0.
  + now apply bpow_ge_0.
  + now apply Hex.
  + now apply Rlt_le; apply Heiy.
- apply mag_le_bpow.
  + apply Rmult_integral_contrapositive_currified.
    exact Px.
    now apply Rinv_neq_0_compat.
  + replace (_ + 1)%Z with (ex + (- ey + 1))%Z by ring.
    rewrite bpow_plus.
    apply Rlt_le_trans with (bpow ex * Rabs (/ y))%R.
    * rewrite Rabs_mult.
      apply Rmult_lt_compat_r.
      apply Rabs_pos_lt.
      now apply Rinv_neq_0_compat.
      now apply Hex.
    * apply Rmult_le_compat_l; [now apply bpow_ge_0|].
      apply Heiy.
Qed.

Lemma mag_sqrt :
  forall x,
  (0 < x)%R ->
  mag (sqrt x) = Z.div2 (mag x + 1) :> Z.
Proof.
intros x Px.
apply mag_unique.
destruct mag as [e He].
simpl.
specialize (He (Rgt_not_eq _ _ Px)).
rewrite Rabs_pos_eq in He by now apply Rlt_le.
split.
- rewrite <- (Rabs_pos_eq (bpow _)) by apply bpow_ge_0.
  apply Rsqr_le_abs_0.
  rewrite Rsqr_sqrt by now apply Rlt_le.
  apply Rle_trans with (2 := proj1 He).
  unfold Rsqr ; rewrite <- bpow_plus.
  apply bpow_le.
  generalize (Zdiv2_odd_eqn (e + 1)).
  destruct Z.odd ; intros ; lia.
- rewrite <- (Rabs_pos_eq (bpow _)) by apply bpow_ge_0.
  apply Rsqr_lt_abs_0.
  rewrite Rsqr_sqrt by now apply Rlt_le.
  apply Rlt_le_trans with (1 := proj2 He).
  unfold Rsqr ; rewrite <- bpow_plus.
  apply bpow_le.
  generalize (Zdiv2_odd_eqn (e + 1)).
  destruct Z.odd ; intros ; lia.
Qed.

Lemma mag_1 : mag 1 = 1%Z :> Z.
Proof.
apply mag_unique_pos; rewrite bpow_1; simpl; split; [now right|apply IZR_lt].
assert (H := Zle_bool_imp_le _ _ (radix_prop r)); revert H.
now apply Z.lt_le_trans.
Qed.

End pow.

Section Bool.

Theorem eqb_sym :
  forall x y, Bool.eqb x y = Bool.eqb y x.
Proof.
now intros [|] [|].
Qed.

Theorem eqb_false :
  forall x y, x = negb y -> Bool.eqb x y = false.
Proof.
now intros [|] [|].
Qed.

Theorem eqb_true :
  forall x y, x = y -> Bool.eqb x y = true.
Proof.
now intros [|] [|].
Qed.

End Bool.

Section cond_Ropp.

Definition cond_Ropp (b : bool) m := if b then Ropp m else m.

Theorem IZR_cond_Zopp :
  forall b m,
  IZR (cond_Zopp b m) = cond_Ropp b (IZR m).
Proof.
intros [|] m.
apply opp_IZR.
apply refl_equal.
Qed.

Theorem abs_cond_Ropp :
  forall b m,
  Rabs (cond_Ropp b m) = Rabs m.
Proof.
intros [|] m.
apply Rabs_Ropp.
apply refl_equal.
Qed.

Theorem cond_Ropp_Rlt_bool :
  forall m,
  cond_Ropp (Rlt_bool m 0) m = Rabs m.
Proof.
intros m.
apply sym_eq.
case Rlt_bool_spec ; intros Hm.
now apply Rabs_left.
now apply Rabs_pos_eq.
Qed.

Theorem Rlt_bool_cond_Ropp :
  forall x sx, (0 < x)%R ->
  Rlt_bool (cond_Ropp sx x) 0 = sx.
Proof.
  intros x sx Hx. destruct sx; simpl.
  - apply Rlt_bool_true. now apply Ropp_lt_gt_0_contravar.
  - apply Rlt_bool_false. now left.
Qed.

Theorem cond_Ropp_involutive :
  forall b x,
  cond_Ropp b (cond_Ropp b x) = x.
Proof.
intros [|] x.
apply Ropp_involutive.
apply refl_equal.
Qed.

Theorem cond_Ropp_inj :
  forall b x y,
  cond_Ropp b x = cond_Ropp b y -> x = y.
Proof.
intros b x y H.
rewrite <- (cond_Ropp_involutive b x), H.
apply cond_Ropp_involutive.
Qed.

Theorem cond_Ropp_mult_l :
  forall b x y,
  cond_Ropp b (x * y) = (cond_Ropp b x * y)%R.
Proof.
intros [|] x y.
apply sym_eq.
apply Ropp_mult_distr_l_reverse.
apply refl_equal.
Qed.

Theorem cond_Ropp_mult_r :
  forall b x y,
  cond_Ropp b (x * y) = (x * cond_Ropp b y)%R.
Proof.
intros [|] x y.
apply sym_eq.
apply Ropp_mult_distr_r_reverse.
apply refl_equal.
Qed.

Theorem cond_Ropp_plus :
  forall b x y,
  cond_Ropp b (x + y) = (cond_Ropp b x + cond_Ropp b y)%R.
Proof.
intros [|] x y.
apply Ropp_plus_distr.
apply refl_equal.
Qed.

End cond_Ropp.


(** LPO taken from Coquelicot *)

Theorem LPO_min :
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
  {n : nat | P n /\ forall i, (i < n)%nat -> ~ P i} + {forall n, ~ P n}.
Proof.
assert (Hi: forall n, (0 < INR n + 1)%R).
  intros N.
  rewrite <- S_INR.
  apply lt_0_INR.
  apply Nat.lt_0_succ.
intros P HP.
set (E y := exists n, (P n /\ y = / (INR n + 1))%R \/ (~ P n /\ y = 0)%R).
assert (HE: forall n, P n -> E (/ (INR n + 1))%R).
  intros n Pn.
  exists n.
  left.
  now split.
assert (BE: is_upper_bound E 1).
  intros x [y [[_ ->]|[_ ->]]].
  rewrite <- Rinv_1 at 2.
  apply Rinv_le.
  exact Rlt_0_1.
  rewrite <- S_INR.
  apply (le_INR 1), le_n_S, le_0_n.
  exact Rle_0_1.
destruct (completeness E) as [l [ub lub]].
  now exists 1%R.
  destruct (HP O) as [H0|H0].
  exists 1%R.
  exists O.
  left.
  apply (conj H0).
  rewrite Rplus_0_l.
  apply sym_eq, Rinv_1.
  exists 0%R.
  exists O.
  right.
  now split.
destruct (Rle_lt_dec l 0) as [Hl|Hl].
  right.
  intros n Pn.
  apply Rle_not_lt with (1 := Hl).
  apply Rlt_le_trans with (/ (INR n + 1))%R.
  now apply Rinv_0_lt_compat.
  apply ub.
  now apply HE.
left.
set (N := Z.abs_nat (up (/l) - 2)).
exists N.
assert (HN: (INR N + 1 = IZR (up (/ l)) - 1)%R).
  unfold N.
  rewrite INR_IZR_INZ.
  rewrite inj_Zabs_nat.
  replace (IZR (up (/ l)) - 1)%R with (IZR (up (/ l) - 2) + 1)%R.
  apply (f_equal (fun v => IZR v + 1)%R).
  apply Z.abs_eq.
  apply Zle_minus_le_0.
  apply (Zlt_le_succ 1).
  apply lt_IZR.
  apply Rle_lt_trans with (/l)%R.
  apply Rmult_le_reg_r with (1 := Hl).
  rewrite Rmult_1_l, Rinv_l by now apply Rgt_not_eq.
  apply lub.
  exact BE.
  apply archimed.
  rewrite minus_IZR.
  simpl.
  ring.
assert (H: forall i, (i < N)%nat -> ~ P i).
  intros i HiN Pi.
  unfold is_upper_bound in ub.
  refine (Rle_not_lt _ _ (ub (/ (INR i + 1))%R _) _).
  now apply HE.
  rewrite <- (Rinv_involutive l) by now apply Rgt_not_eq.
  apply Rinv_1_lt_contravar.
  rewrite <- S_INR.
  apply (le_INR 1).
  apply le_n_S.
  apply le_0_n.
  apply Rlt_le_trans with (INR N + 1)%R.
  apply Rplus_lt_compat_r.
  now apply lt_INR.
  rewrite HN.
  apply Rplus_le_reg_r with (-/l + 1)%R.
  ring_simplify.
  apply archimed.
destruct (HP N) as [PN|PN].
  now split.
exfalso.
refine (Rle_not_lt _ _ (lub (/ (INR (S N) + 1))%R _) _).
  intros x [y [[Py ->]|[_ ->]]].
  destruct (eq_nat_dec y N) as [HyN|HyN].
  elim PN.
  now rewrite <- HyN.
  apply Rinv_le.
  apply Hi.
  apply Rplus_le_compat_r.
  apply Rnot_lt_le.
  intros Hy.
  refine (H _ _ Py).
  apply INR_lt in Hy.
  clear -Hy HyN ; lia.
  now apply Rlt_le, Rinv_0_lt_compat.
rewrite S_INR, HN.
ring_simplify (IZR (up (/ l)) - 1 + 1)%R.
rewrite <- (Rinv_involutive l) at 2 by now apply Rgt_not_eq.
apply Rinv_1_lt_contravar.
rewrite <- Rinv_1.
apply Rinv_le.
exact Hl.
now apply lub.
apply archimed.
Qed.

Theorem LPO :
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
  {n : nat | P n} + {forall n, ~ P n}.
Proof.
intros P HP.
destruct (LPO_min P HP) as [[n [Pn _]]|Pn].
left.
now exists n.
now right.
Qed.


Lemma LPO_Z : forall P : Z -> Prop, (forall n, P n \/ ~P n) ->
  {n : Z| P n} + {forall n, ~ P n}.
Proof.
intros P H.
destruct (LPO (fun n => P (Z.of_nat n))) as [J|J].
intros n; apply H.
destruct J as (n, Hn).
left; now exists (Z.of_nat n).
destruct (LPO (fun n => P (-Z.of_nat n)%Z)) as [K|K].
intros n; apply H.
destruct K as (n, Hn).
left; now exists (-Z.of_nat n)%Z.
right; intros n; case (Zle_or_lt 0 n); intros M.
rewrite <- (Z.abs_eq n); trivial.
rewrite <- Zabs2Nat.id_abs.
apply J.
rewrite <- (Z.opp_involutive n).
rewrite <- (Z.abs_neq n).
rewrite <- Zabs2Nat.id_abs.
apply K.
lia.
Qed.



(** A little tactic to simplify terms of the form [bpow a * bpow b]. *)
Ltac bpow_simplify :=
  (* bpow ex * bpow ey ~~> bpow (ex + ey) *)
  repeat
    match goal with
      | |- context [(bpow _ _ * bpow _ _)] =>
        rewrite <- bpow_plus
      | |- context [(?X1 * bpow _ _ * bpow _ _)] =>
        rewrite (Rmult_assoc X1); rewrite <- bpow_plus
      | |- context [(?X1 * (?X2 * bpow _ _) * bpow _ _)] =>
        rewrite <- (Rmult_assoc X1 X2); rewrite (Rmult_assoc (X1 * X2));
        rewrite <- bpow_plus
    end;
  (* ring_simplify arguments of bpow *)
  repeat
    match goal with
      | |- context [(bpow _ ?X)] =>
        progress ring_simplify X
    end;
  (* bpow 0 ~~> 1 *)
  change (bpow _ 0) with 1;
  repeat
    match goal with
      | |- context [(_ * 1)] =>
        rewrite Rmult_1_r
    end.

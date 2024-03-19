(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: https://flocq.gitlabpages.inria.fr/

Copyright (C) 2010-2018 Sylvie Boldo
#<br />#
Copyright (C) 2010-2018 Guillaume Melquiond

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

From Coq Require Import ZArith Reals Psatz.

Require Import Core Operations Relative.

Section Fprop_plus_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Section round_repr_same_exp.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma round_repr_same_exp :
  forall m e,
  exists m',
  round beta fexp rnd (F2R (Float beta m e)) = F2R (Float beta m' e).
Proof with auto with typeclass_instances.
intros m e.
set (e' := cexp beta fexp (F2R (Float beta m e))).
unfold round, scaled_mantissa. fold e'.
destruct (Zle_or_lt e' e) as [He|He].
exists m.
unfold F2R at 2. simpl.
rewrite Rmult_assoc, <- bpow_plus.
rewrite <- IZR_Zpower by lia.
rewrite <- mult_IZR, Zrnd_IZR...
unfold F2R. simpl.
rewrite mult_IZR.
rewrite Rmult_assoc.
rewrite IZR_Zpower by lia.
rewrite <- bpow_plus.
apply (f_equal (fun v => IZR m * bpow v)%R).
ring.
exists ((rnd (IZR m * bpow (e - e'))) * Zpower beta (e' - e))%Z.
unfold F2R. simpl.
rewrite mult_IZR.
rewrite IZR_Zpower by lia.
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
  (cexp beta fexp x <= cexp beta fexp y)%Z ->
  format x -> format y ->
  format (round beta fexp (Znearest choice) (x + y) - (x + y))%R.
Proof.
intros x y.
set (ex := cexp beta fexp x).
set (ey := cexp beta fexp y).
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
apply mag_le_abs.
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
destruct (Zle_or_lt (cexp beta fexp x) (cexp beta fexp y)).
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

Lemma round_plus_neq_0_aux :
  forall x y,
  (cexp beta fexp x <= cexp beta fexp y)%Z ->
  format x -> format y ->
  (0 < x + y)%R ->
  round beta fexp rnd (x + y) <> 0%R.
Proof with auto with typeclass_instances.
intros x y He Hx Hy Hxy.
destruct (mag beta (x + y)) as (exy, Hexy).
simpl.
specialize (Hexy (Rgt_not_eq _ _ Hxy)).
destruct (Zle_or_lt exy (fexp exy)) as [He'|He'].
(* . *)
assert (H: (x + y)%R = F2R (Float beta (Ztrunc (x * bpow (- fexp exy)) +
  Ztrunc (y * bpow (- fexp exy))) (fexp exy))).
rewrite (subnormal_exponent beta fexp exy x He' Hx) at 1.
rewrite (subnormal_exponent beta fexp exy y He' Hy) at 1.
now rewrite <- F2R_plus, Fplus_same_exp.
rewrite H.
rewrite round_generic...
rewrite <- H.
now apply Rgt_not_eq.
apply generic_format_F2R.
intros _.
rewrite <- H.
unfold cexp.
rewrite mag_unique with (1 := Hexy).
apply Z.le_refl.
(* . *)
intros H.
elim Rle_not_lt with (1 := round_le beta _ rnd _ _ (proj1 Hexy)).
rewrite (Rabs_pos_eq _ (Rlt_le _ _ Hxy)).
rewrite H.
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
Theorem round_plus_neq_0 :
  forall x y,
  format x -> format y ->
  (x + y <> 0)%R ->
  round beta fexp rnd (x + y) <> 0%R.
Proof with auto with typeclass_instances.
intros x y Hx Hy Hxy.
destruct (Rle_or_lt 0 (x + y)) as [H1|H1].
(* . *)
destruct (Zle_or_lt (cexp beta fexp x) (cexp beta fexp y)) as [H2|H2].
apply round_plus_neq_0_aux...
lra.
rewrite Rplus_comm.
apply round_plus_neq_0_aux ; try easy.
now apply Zlt_le_weak.
lra.
(* . *)
rewrite <- (Ropp_involutive (x + y)), Ropp_plus_distr.
rewrite round_opp.
apply Ropp_neq_0_compat.
destruct (Zle_or_lt (cexp beta fexp (-x)) (cexp beta fexp (-y))) as [H2|H2].
apply round_plus_neq_0_aux; try apply generic_format_opp...
lra.
rewrite Rplus_comm.
apply round_plus_neq_0_aux; try apply generic_format_opp...
now apply Zlt_le_weak.
lra.
Qed.

Theorem round_plus_eq_0 :
  forall x y,
  format x -> format y ->
  round beta fexp rnd (x + y) = 0%R ->
  (x + y = 0)%R.
Proof with auto with typeclass_instances.
intros x y Fx Fy H.
destruct (Req_dec (x + y) 0) as [H'|H'].
exact H'.
contradict H.
now apply round_plus_neq_0.
Qed.

End Fprop_plus_zero.

Section Fprop_plus_FLT.
Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Theorem FLT_format_plus_small: forall x y,
  generic_format beta (FLT_exp emin prec) x ->
  generic_format beta (FLT_exp emin prec) y ->
   (Rabs (x+y) <= bpow (prec+emin))%R ->
    generic_format beta (FLT_exp emin prec) (x+y).
Proof with auto with typeclass_instances.
intros x y Fx Fy H.
apply generic_format_FLT_FIX...
rewrite Zplus_comm; assumption.
apply generic_format_FIX_FLT, FIX_format_generic in Fx.
apply generic_format_FIX_FLT, FIX_format_generic in Fy.
destruct Fx as [nx H1x H2x].
destruct Fy as [ny H1y H2y].
apply generic_format_FIX.
exists (Float beta (Fnum nx+Fnum ny)%Z emin).
rewrite H1x,H1y; unfold F2R; simpl.
rewrite H2x, H2y.
rewrite plus_IZR; ring.
easy.
Qed.

Variable choice : Z -> bool.

Lemma FLT_plus_error_N_ex : forall x y,
  generic_format beta (FLT_exp emin prec) x ->
  generic_format beta (FLT_exp emin prec) y ->
  exists eps,
  (Rabs eps <= u_ro beta prec / (1 + u_ro beta prec))%R /\
  round beta (FLT_exp emin prec) (Znearest choice) (x + y)
  = ((x + y) * (1 + eps))%R.
Proof.
intros x y Fx Fy.
assert (Pb := u_rod1pu_ro_pos beta prec).
destruct (Rle_or_lt (bpow (emin + prec - 1)) (Rabs (x + y))) as [M|M].
{ destruct (relative_error_N_FLX'_ex beta prec prec_gt_0_ choice (x + y))
    as (d, (Bd, Hd)).
  now exists d; split; [exact Bd|]; rewrite <- Hd; apply round_FLT_FLX. }
exists 0%R; rewrite Rabs_R0; split; [exact Pb|]; rewrite Rplus_0_r, Rmult_1_r.
apply round_generic; [apply valid_rnd_N|].
apply FLT_format_plus_small; [exact Fx|exact Fy|].
apply Rlt_le, (Rlt_le_trans _ _ _ M), bpow_le; lia.
Qed.

Lemma FLT_plus_error_N_round_ex : forall x y,
  generic_format beta (FLT_exp emin prec) x ->
  generic_format beta (FLT_exp emin prec) y ->
  exists eps,
  (Rabs eps <= u_ro beta prec)%R /\
  (x + y
   = round beta (FLT_exp emin prec) (Znearest choice) (x + y) * (1 + eps))%R.
Proof.
intros x y Fx Fy.
now apply relative_error_N_round_ex_derive, FLT_plus_error_N_ex.
Qed.

End Fprop_plus_FLT.

Section Fprop_plus_mult_ulp.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.
Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Notation format := (generic_format beta fexp).
Notation cexp := (cexp beta fexp).

Lemma ex_shift :
  forall x e, format x -> (e <= cexp x)%Z ->
  exists m, (x = IZR m * bpow e)%R.
Proof with auto with typeclass_instances.
intros x e Fx He.
exists (Ztrunc (scaled_mantissa beta fexp x)*Zpower beta (cexp x -e))%Z.
rewrite Fx at 1; unfold F2R; simpl.
rewrite mult_IZR, Rmult_assoc.
f_equal.
rewrite IZR_Zpower by lia.
rewrite <- bpow_plus; f_equal; ring.
Qed.

Lemma mag_minus1 :
  forall z, z <> 0%R ->
  (mag beta z - 1)%Z = mag beta (z / IZR beta).
Proof.
intros z Hz.
unfold Zminus.
rewrite <- mag_mult_bpow by easy.
now rewrite bpow_opp, bpow_1.
Qed.

Theorem round_plus_F2R :
  forall x y, format x -> format y -> (x <> 0)%R ->
  exists m,
  round beta fexp rnd (x+y) = F2R (Float beta m (cexp (x / IZR beta))).
Proof with auto with typeclass_instances.
intros x y Fx Fy Zx.
case (Zle_or_lt (mag beta (x/IZR beta)) (mag beta y)); intros H1.
pose (e:=cexp (x / IZR beta)).
destruct (ex_shift x e) as (nx, Hnx); try exact Fx.
apply monotone_exp.
rewrite <- (mag_minus1 x Zx); lia.
destruct (ex_shift y e) as (ny, Hny); try assumption.
apply monotone_exp...
destruct (round_repr_same_exp beta fexp rnd (nx+ny) e) as (n,Hn).
exists n.
fold e.
rewrite <- Hn; f_equal.
rewrite Hnx, Hny; unfold F2R; simpl; rewrite plus_IZR; ring.
unfold F2R; simpl.
(* *)
destruct (ex_shift (round beta fexp rnd (x + y)) (cexp (x/IZR beta))) as (n,Hn).
apply generic_format_round...
apply Z.le_trans with (cexp (x+y)).
apply monotone_exp.
rewrite <- mag_minus1 by easy.
rewrite <- (mag_abs beta (x+y)).
(* . *)
assert (U: (Rabs (x+y) = Rabs x + Rabs y)%R \/ (y <> 0 /\ Rabs (x+y) = Rabs x - Rabs y)%R).
assert (V: forall x y, (Rabs y <= Rabs x)%R ->
   (Rabs (x+y) = Rabs x + Rabs y)%R \/ (y <> 0 /\ Rabs (x+y) = Rabs x - Rabs y)%R).
clear; intros x y.
case (Rle_or_lt 0 y); intros Hy.
case Hy; intros Hy'.
case (Rle_or_lt 0 x); intros Hx.
intros _; rewrite (Rabs_pos_eq y) by easy.
rewrite (Rabs_pos_eq x) by easy.
left; apply Rabs_pos_eq.
now apply Rplus_le_le_0_compat.
rewrite (Rabs_pos_eq y) by easy.
rewrite (Rabs_left x) by easy.
intros H; right; split.
now apply Rgt_not_eq.
rewrite Rabs_left1.
ring.
apply Rplus_le_reg_l with (-x)%R; ring_simplify; assumption.
intros _; left.
now rewrite <- Hy', Rabs_R0, 2!Rplus_0_r.
case (Rle_or_lt 0 x); intros Hx.
rewrite (Rabs_left y) by easy.
rewrite (Rabs_pos_eq x) by easy.
intros H; right; split.
now apply Rlt_not_eq.
rewrite Rabs_pos_eq.
ring.
apply Rplus_le_reg_l with (-y)%R; ring_simplify; assumption.
intros _; left.
rewrite (Rabs_left y) by easy.
rewrite (Rabs_left x) by easy.
rewrite Rabs_left1.
ring.
lra.
apply V; left.
apply lt_mag with beta.
now apply Rabs_pos_lt.
rewrite <- mag_minus1 in H1; try assumption.
rewrite 2!mag_abs; lia.
(* . *)
destruct U as [U|U].
rewrite U; apply Z.le_trans with (mag beta x).
lia.
rewrite <- mag_abs.
apply mag_le.
now apply Rabs_pos_lt.
apply Rplus_le_reg_l with (-Rabs x)%R; ring_simplify.
apply Rabs_pos.
destruct U as (U',U); rewrite U.
rewrite <- mag_abs.
apply mag_minus_lb.
now apply Rabs_pos_lt.
now apply Rabs_pos_lt.
rewrite 2!mag_abs.
assert (mag beta y < mag beta x - 1)%Z.
now rewrite (mag_minus1 x Zx).
lia.
apply cexp_round_ge...
apply round_plus_neq_0...
contradict H1; apply Zle_not_lt.
rewrite <- (mag_minus1 x Zx).
replace y with (-x)%R.
rewrite mag_opp; lia.
lra.
now exists n.
Qed.

Context {exp_not_FTZ : Exp_not_FTZ fexp}.

Theorem round_plus_ge_ulp :
  forall x y, format x -> format y ->
  round beta fexp rnd (x+y) <> 0%R ->
  (ulp beta fexp (x/IZR beta) <= Rabs (round beta fexp rnd (x+y)))%R.
Proof with auto with typeclass_instances.
intros x y Fx Fy KK.
case (Req_dec x 0); intros Zx.
(* *)
rewrite Zx, Rplus_0_l.
rewrite round_generic...
unfold Rdiv; rewrite Rmult_0_l.
rewrite Fy.
unfold F2R; simpl; rewrite Rabs_mult.
rewrite (Rabs_pos_eq (bpow _)) by apply bpow_ge_0.
case (Z.eq_dec (Ztrunc (scaled_mantissa beta fexp y)) 0); intros Hm.
contradict KK.
rewrite Zx, Fy, Hm; unfold F2R; simpl.
rewrite Rplus_0_l, Rmult_0_l.
apply round_0...
apply Rle_trans with (1*bpow (cexp y))%R.
rewrite Rmult_1_l.
rewrite <- ulp_neq_0.
apply ulp_ge_ulp_0...
intros K; apply Hm.
rewrite K, scaled_mantissa_0.
apply Ztrunc_IZR.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- abs_IZR.
apply IZR_le.
apply (Zlt_le_succ 0).
now apply Z.abs_pos.
(* *)
destruct (round_plus_F2R x y Fx Fy Zx) as (m,Hm).
case (Z.eq_dec m 0); intros Zm.
contradict KK.
rewrite Hm, Zm.
apply F2R_0.
rewrite Hm, <- F2R_Zabs.
rewrite ulp_neq_0.
rewrite <- (Rmult_1_l (bpow _)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le.
apply (Zlt_le_succ 0).
now apply Z.abs_pos.
apply Rmult_integral_contrapositive_currified with (1 := Zx).
apply Rinv_neq_0_compat.
apply Rgt_not_eq, radix_pos.
Qed.

End Fprop_plus_mult_ulp.

Section Fprop_plus_ge_ulp.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.
Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Theorem round_FLT_plus_ge :
  forall x y e,
  generic_format beta (FLT_exp emin prec) x -> generic_format beta (FLT_exp emin prec) y ->
  (bpow (e + prec) <= Rabs x)%R ->
  round beta (FLT_exp emin prec) rnd (x + y) <> 0%R ->
  (bpow e <= Rabs (round beta (FLT_exp emin prec) rnd (x + y)))%R.
Proof with auto with typeclass_instances.
intros x y e Fx Fy He KK.
assert (Zx: x <> 0%R).
  contradict He.
  apply Rlt_not_le; rewrite He, Rabs_R0.
  apply bpow_gt_0.
apply Rle_trans with (ulp beta (FLT_exp emin prec) (x/IZR beta)).
2: apply round_plus_ge_ulp...
rewrite ulp_neq_0.
unfold cexp.
rewrite <- mag_minus1; try assumption.
unfold FLT_exp; apply bpow_le.
apply Z.le_trans with (2:=Z.le_max_l _ _).
destruct (mag beta x) as (n,Hn); simpl.
cut (e + prec < n)%Z. lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=He).
now apply Hn.
apply Rmult_integral_contrapositive_currified; try assumption.
apply Rinv_neq_0_compat.
apply Rgt_not_eq.
apply radix_pos.
Qed.

Lemma round_FLT_plus_ge' :
  forall x y e,
  generic_format beta (FLT_exp emin prec) x -> generic_format beta (FLT_exp emin prec) y ->
  (x <> 0%R -> (bpow (e+prec) <= Rabs x)%R) ->
  (x = 0%R -> y <> 0%R -> (bpow e <= Rabs y)%R) ->
  round beta (FLT_exp emin prec) rnd (x+y) <> 0%R ->
  (bpow e <= Rabs (round beta (FLT_exp emin prec) rnd (x+y)))%R.
Proof with auto with typeclass_instances.
intros x y e Fx Fy H1 H2 H3.
case (Req_dec x 0); intros H4.
case (Req_dec y 0); intros H5.
contradict H3.
rewrite H4, H5, Rplus_0_l; apply round_0...
rewrite H4, Rplus_0_l.
rewrite round_generic...
apply round_FLT_plus_ge; try easy.
now apply H1.
Qed.

Theorem round_FLX_plus_ge :
  forall x y e,
  generic_format beta (FLX_exp prec) x -> generic_format beta (FLX_exp prec) y ->
  (bpow (e+prec) <= Rabs x)%R ->
  (round beta (FLX_exp prec) rnd (x+y) <> 0)%R ->
  (bpow e <= Rabs (round beta (FLX_exp prec) rnd (x+y)))%R.
Proof with auto with typeclass_instances.
intros x y e Fx Fy He KK.
assert (Zx: x <> 0%R).
  contradict He.
  apply Rlt_not_le; rewrite He, Rabs_R0.
  apply bpow_gt_0.
apply Rle_trans with (ulp beta (FLX_exp prec) (x/IZR beta)).
2: apply round_plus_ge_ulp...
rewrite ulp_neq_0.
unfold cexp.
rewrite <- mag_minus1 by easy.
unfold FLX_exp; apply bpow_le.
destruct (mag beta x) as (n,Hn); simpl.
cut (e + prec < n)%Z. lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=He).
now apply Hn.
apply Rmult_integral_contrapositive_currified; try assumption.
apply Rinv_neq_0_compat.
apply Rgt_not_eq.
apply radix_pos.
Qed.

End Fprop_plus_ge_ulp.

Section Fprop_plus_le_ops.

Variable beta : radix.
Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Variable choice : Z -> bool.

Lemma plus_error_le_l :
  forall x y,
  generic_format beta fexp x -> generic_format beta fexp y ->
  (Rabs (round beta fexp (Znearest choice) (x + y) - (x + y)) <= Rabs x)%R.
Proof.
intros x y Fx Fy.
apply (Rle_trans _ (Rabs (y - (x + y)))); [now apply round_N_pt|].
rewrite Rabs_minus_sym; right; f_equal; ring.
Qed.

Lemma plus_error_le_r :
  forall x y,
  generic_format beta fexp x -> generic_format beta fexp y ->
  (Rabs (round beta fexp (Znearest choice) (x + y) - (x + y)) <= Rabs y)%R.
Proof. now intros x y Fx Fy; rewrite Rplus_comm; apply plus_error_le_l. Qed.

End Fprop_plus_le_ops.

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

(** * Relative error of the roundings *)
Require Import Fcore.

Section Fprop_relative.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Section Fprop_relative_generic.

Variable fexp : Z -> Z.
Context { prop_exp : Valid_exp fexp }.

Section relative_error_conversion.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Lemma relative_error_lt_conversion :
  forall x b, (0 < b)%R ->
  (x <> 0 -> Rabs (round beta fexp rnd x - x) < b * Rabs x)%R ->
  exists eps,
  (Rabs eps < b)%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros x b Hb0 Hxb.
destruct (Req_dec x 0) as [Hx0|Hx0].
(* *)
exists 0%R.
split.
now rewrite Rabs_R0.
rewrite Hx0, Rmult_0_l.
apply round_0...
(* *)
specialize (Hxb Hx0).
exists ((round beta fexp rnd x - x) / x)%R.
split. 2: now field.
unfold Rdiv.
rewrite Rabs_mult.
apply Rmult_lt_reg_r with (Rabs x).
now apply Rabs_pos_lt.
rewrite Rmult_assoc, <- Rabs_mult.
rewrite Rinv_l with (1 := Hx0).
now rewrite Rabs_R1, Rmult_1_r.
Qed.

Lemma relative_error_le_conversion :
  forall x b, (0 <= b)%R ->
  (Rabs (round beta fexp rnd x - x) <= b * Rabs x)%R ->
  exists eps,
  (Rabs eps <= b)%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros x b Hb0 Hxb.
destruct (Req_dec x 0) as [Hx0|Hx0].
(* *)
exists 0%R.
split.
now rewrite Rabs_R0.
rewrite Hx0, Rmult_0_l.
apply round_0...
(* *)
exists ((round beta fexp rnd x - x) / x)%R.
split. 2: now field.
unfold Rdiv.
rewrite Rabs_mult.
apply Rmult_le_reg_r with (Rabs x).
now apply Rabs_pos_lt.
rewrite Rmult_assoc, <- Rabs_mult.
rewrite Rinv_l with (1 := Hx0).
now rewrite Rabs_R1, Rmult_1_r.
Qed.

End relative_error_conversion.

Variable emin p : Z.
Hypothesis Hmin : forall k, (emin < k)%Z -> (p <= k - fexp k)%Z.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem relative_error :
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs x)%R.
Proof with auto with typeclass_instances.
intros x Hx.
assert (Hx': (x <> 0)%R).
intros T; contradict Hx; rewrite T, Rabs_R0.
apply Rlt_not_le, bpow_gt_0.
apply Rlt_le_trans with (ulp beta fexp x)%R.
now apply error_lt_ulp...
rewrite ulp_neq_0; trivial.
unfold canonic_exp.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_plus.
apply bpow_le.
assert (emin < ex)%Z.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

(** 1+#&epsilon;# property in any rounding *)
Theorem relative_error_ex :
  forall x,
  (bpow emin <= Rabs x)%R ->
  exists eps,
  (Rabs eps < bpow (-p + 1))%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_lt_conversion...
apply bpow_gt_0.
intros _.
now apply relative_error.
Qed.

Theorem relative_error_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs x)%R.
Proof.
intros m x Hx.
apply relative_error.
unfold x.
rewrite <- F2R_Zabs.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, F2R_Zabs.
now apply Rabs_pos_lt.
Qed.

Theorem relative_error_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps < bpow (-p + 1))%R /\ round beta fexp rnd x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros m x.
apply relative_error_lt_conversion...
apply bpow_gt_0.
now apply relative_error_F2R_emin.
Qed.

Theorem relative_error_round :
  (0 < p)%Z ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs (round beta fexp rnd x))%R.
Proof with auto with typeclass_instances.
intros Hp x Hx.
assert (Hx': (x <> 0)%R).
intros T; contradict Hx; rewrite T, Rabs_R0.
apply Rlt_not_le, bpow_gt_0.
apply Rlt_le_trans with (ulp beta fexp x)%R.
now apply error_lt_ulp.
rewrite ulp_neq_0; trivial.
unfold canonic_exp.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
assert (He': (emin < ex)%Z).
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_plus.
apply bpow_le.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
generalize He.
apply round_abs_abs...
clear rnd valid_rnd x Hx Hx' He.
intros rnd valid_rnd x _ Hx.
rewrite <- (round_generic beta fexp rnd (bpow (ex - 1))).
now apply round_le.
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
generalize (Hmin ex).
omega.
Qed.

Theorem relative_error_round_F2R_emin :
  (0 < p)%Z ->
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < bpow (-p + 1) * Rabs (round beta fexp rnd x))%R.
Proof.
intros Hp m x Hx.
apply relative_error_round.
exact Hp.
unfold x.
rewrite <- F2R_Zabs.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, F2R_Zabs.
now apply Rabs_pos_lt.
Qed.

Variable choice : Z -> bool.

Theorem relative_error_N :
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs x)%R.
Proof.
intros x Hx.
apply Rle_trans with (/2 * ulp beta fexp x)%R.
now apply error_le_half_ulp.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
assert (Hx': (x <> 0)%R).
intros H.
apply Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
rewrite ulp_neq_0; trivial.
unfold canonic_exp.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_plus.
apply bpow_le.
assert (emin < ex)%Z.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply He.
Qed.

(** 1+#&epsilon;# property in rounding to nearest *)
Theorem relative_error_N_ex :
  forall x,
  (bpow emin <= Rabs x)%R ->
  exists eps,
  (Rabs eps <= /2 * bpow (-p + 1))%R /\ round beta fexp (Znearest choice) x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_le_conversion...
apply Rlt_le.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply bpow_gt_0.
now apply relative_error_N.
Qed.

Theorem relative_error_N_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs x)%R.
Proof with auto with typeclass_instances.
intros m x.
destruct (Req_dec x 0) as [Hx|Hx].
(* . *)
rewrite Hx, round_0...
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.
(* . *)
apply relative_error_N.
unfold x.
rewrite <- F2R_Zabs.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, F2R_Zabs.
now apply Rabs_pos_lt.
Qed.

Theorem relative_error_N_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps <= /2 * bpow (-p + 1))%R /\ round beta fexp (Znearest choice) x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros m x.
apply relative_error_le_conversion...
apply Rlt_le.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply bpow_gt_0.
now apply relative_error_N_F2R_emin.
Qed.

Theorem relative_error_N_round :
  (0 < p)%Z ->
  forall x,
  (bpow emin <= Rabs x)%R ->
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs (round beta fexp (Znearest choice) x))%R.
Proof with auto with typeclass_instances.
intros Hp x Hx.
apply Rle_trans with (/2 * ulp beta fexp x)%R.
now apply error_le_half_ulp.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
assert (Hx': (x <> 0)%R).
intros H.
apply Rlt_not_le with (2 := Hx).
rewrite H, Rabs_R0.
apply bpow_gt_0.
rewrite ulp_neq_0; trivial.
unfold canonic_exp.
destruct (ln_beta beta x) as (ex, He).
simpl.
specialize (He Hx').
assert (He': (emin < ex)%Z).
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
exact Hx.
apply Rle_trans with (bpow (-p + 1) * bpow (ex - 1))%R.
rewrite <- bpow_plus.
apply bpow_le.
generalize (Hmin ex).
omega.
apply Rmult_le_compat_l.
apply bpow_ge_0.
generalize He.
apply round_abs_abs...
clear rnd valid_rnd x Hx Hx' He.
intros rnd valid_rnd x _ Hx.
rewrite <- (round_generic beta fexp rnd (bpow (ex - 1))).
now apply round_le.
apply generic_format_bpow.
ring_simplify (ex - 1 + 1)%Z.
generalize (Hmin ex).
omega.
Qed.

Theorem relative_error_N_round_F2R_emin :
  (0 < p)%Z ->
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * bpow (-p + 1) * Rabs (round beta fexp (Znearest choice) x))%R.
Proof with auto with typeclass_instances.
intros Hp m x.
destruct (Req_dec x 0) as [Hx|Hx].
(* . *)
rewrite Hx, round_0...
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.
(* . *)
apply relative_error_N_round with (1 := Hp).
unfold x.
rewrite <- F2R_Zabs.
apply bpow_le_F2R.
apply F2R_lt_reg with beta emin.
rewrite F2R_0, F2R_Zabs.
now apply Rabs_pos_lt.
Qed.

End Fprop_relative_generic.

Section Fprop_relative_FLT.

Variable emin prec : Z.
Variable Hp : Zlt 0 prec.

Lemma relative_error_FLT_aux :
  forall k, (emin + prec - 1 < k)%Z -> (prec <= k - FLT_exp emin prec k)%Z.
Proof.
intros k Hk.
unfold FLT_exp.
generalize (Zmax_spec (k - prec) emin).
omega.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem relative_error_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error with (emin + prec - 1)%Z...
apply relative_error_FLT_aux.
Qed.

Theorem relative_error_FLT_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (x <> 0)%R ->
  (Rabs (round beta (FLT_exp emin prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof with auto with typeclass_instances.
intros m x Zx.
destruct (Rlt_or_le (Rabs x) (bpow (emin + prec - 1))) as [Hx|Hx].
rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_lt_0_compat.
apply bpow_gt_0.
now apply Rabs_pos_lt.
apply generic_format_FLT_FIX...
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx).
apply bpow_le.
apply Zle_pred.
apply generic_format_FIX.
now exists (Float beta m emin).
now apply relative_error_FLT.
Qed.

Theorem relative_error_FLT_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) rnd x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros m x.
apply relative_error_lt_conversion...
apply bpow_gt_0.
now apply relative_error_FLT_F2R_emin.
Qed.

(** 1+#&epsilon;# property in any rounding in FLT *)
Theorem relative_error_FLT_ex :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) rnd x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_lt_conversion...
apply bpow_gt_0.
intros _; now apply relative_error_FLT.
Qed.

Variable choice : Z -> bool.

Theorem relative_error_N_FLT :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_N with (emin + prec - 1)%Z...
apply relative_error_FLT_aux.
Qed.

(** 1+#&epsilon;# property in rounding to nearest in FLT *)
Theorem relative_error_N_FLT_ex :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_le_conversion...
apply Rlt_le.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply bpow_gt_0.
now apply relative_error_N_FLT.
Qed.

Theorem relative_error_N_FLT_round :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (round beta (FLT_exp emin prec) (Znearest choice) x))%R.
Proof with auto with typeclass_instances.
intros x Hx.
apply relative_error_N_round with (emin + prec - 1)%Z...
apply relative_error_FLT_aux.
Qed.

Theorem relative_error_N_FLT_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof with auto with typeclass_instances.
intros m x.
destruct (Rlt_or_le (Rabs x) (bpow (emin + prec - 1))) as [Hx|Hx].
rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
apply Rmult_le_pos.
apply Rlt_le.
apply (RinvN_pos 1).
apply bpow_ge_0.
apply Rabs_pos.
apply generic_format_FLT_FIX...
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx).
apply bpow_le.
apply Zle_pred.
apply generic_format_FIX.
now exists (Float beta m emin).
now apply relative_error_N_FLT.
Qed.

Theorem relative_error_N_FLT_F2R_emin_ex :
  forall m, let x := F2R (Float beta m emin) in
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros m x.
apply relative_error_le_conversion...
apply Rmult_le_pos.
apply Rlt_le.
apply (RinvN_pos 1).
apply bpow_ge_0.
now apply relative_error_N_FLT_F2R_emin.
Qed.


Theorem relative_error_N_FLT_round_F2R_emin :
  forall m, let x := F2R (Float beta m emin) in
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (round beta (FLT_exp emin prec) (Znearest choice) x))%R.
Proof with auto with typeclass_instances.
intros m x.
destruct (Rlt_or_le (Rabs x) (bpow (emin + prec - 1))) as [Hx|Hx].
rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
apply Rmult_le_pos.
apply Rlt_le.
apply (RinvN_pos 1).
apply bpow_ge_0.
apply Rabs_pos.
apply generic_format_FLT_FIX...
apply Rlt_le.
apply Rlt_le_trans with (1 := Hx).
apply bpow_le.
apply Zle_pred.
apply generic_format_FIX.
now exists (Float beta m emin).
apply relative_error_N_round with (emin := (emin + prec - 1)%Z)...
apply relative_error_FLT_aux.
Qed.

Lemma error_N_FLT_aux :
  forall x,
  (0 < x)%R ->
  exists eps, exists  eta,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\
  (Rabs eta <= /2 * bpow (emin))%R      /\
  (eps*eta=0)%R /\
  round beta (FLT_exp emin prec) (Znearest choice) x = (x * (1 + eps) + eta)%R.
Proof.
intros x Hx2.
case (Rle_or_lt (bpow (emin+prec)) x); intros Hx.
(* *)
destruct relative_error_N_ex with (FLT_exp emin prec) (emin+prec)%Z prec choice x
  as (eps,(Heps1,Heps2)).
now apply FLT_exp_valid.
intros; unfold FLT_exp.
rewrite Zmax_left; omega.
rewrite Rabs_right;[assumption|apply Rle_ge; now left].
exists eps; exists 0%R.
split;[assumption|split].
rewrite Rabs_R0; apply Rmult_le_pos.
apply Rlt_le, pos_half_prf.
apply bpow_ge_0.
split;[apply Rmult_0_r|idtac].
now rewrite Rplus_0_r.
(* *)
exists 0%R; exists (round beta (FLT_exp emin prec) (Znearest choice) x - x)%R.
split.
rewrite Rabs_R0; apply Rmult_le_pos.
apply Rlt_le, pos_half_prf.
apply bpow_ge_0.
split.
apply Rle_trans with (/2*ulp beta (FLT_exp emin prec) x)%R.
apply error_le_half_ulp.
now apply FLT_exp_valid.
apply Rmult_le_compat_l.
apply Rlt_le, pos_half_prf.
rewrite ulp_neq_0.
2: now apply Rgt_not_eq.
apply bpow_le.
unfold FLT_exp, canonic_exp.
rewrite Zmax_right.
omega.
destruct (ln_beta beta x) as (e,He); simpl.
assert (e-1 < emin+prec)%Z.
apply (lt_bpow beta).
apply Rle_lt_trans with (2:=Hx).
rewrite <- (Rabs_right x).
apply He; auto with real.
apply Rle_ge; now left.
omega.
split;ring.
Qed.

End Fprop_relative_FLT.

Lemma error_N_FLT :
  forall (emin prec : Z), (0 < prec)%Z ->
  forall (choice : Z -> bool),
  forall (x : R),
  exists eps eta : R,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\
  (Rabs eta <= /2 * bpow emin)%R /\
  (eps * eta = 0)%R /\
  (round beta (FLT_exp emin prec) (Znearest choice) x
   = x * (1 + eps) + eta)%R.
Proof.
intros emin prec Pprec choice x.
destruct (Rtotal_order x 0) as [Nx|[Zx|Px]].
{ assert (Pmx : (0 < - x)%R).
  { now rewrite <- Ropp_0; apply Ropp_lt_contravar. }
  destruct (error_N_FLT_aux emin prec Pprec
                            (fun t : Z => negb (choice (- (t + 1))%Z))
                            (- x)%R Pmx)
    as (d,(e,(Hd,(He,(Hde,Hr))))).
  exists d; exists (- e)%R; split; [exact Hd|split; [|split]].
  { now rewrite Rabs_Ropp. }
  { now rewrite Ropp_mult_distr_r_reverse, <- Ropp_0; apply f_equal. }
  rewrite <- (Ropp_involutive x), round_N_opp.
  now rewrite Ropp_mult_distr_l_reverse, <- Ropp_plus_distr; apply f_equal. }
{ assert (Ph2 : (0 <= / 2)%R).
  { apply (Rmult_le_reg_l 2 _ _ Rlt_0_2).
    rewrite Rmult_0_r, Rinv_r; [exact Rle_0_1|].
    apply Rgt_not_eq, Rlt_gt, Rlt_0_2. }
  exists 0%R; exists 0%R; rewrite Zx; split; [|split; [|split]].
  { now rewrite Rabs_R0; apply Rmult_le_pos; [|apply bpow_ge_0]. }
  { now rewrite Rabs_R0; apply Rmult_le_pos; [|apply bpow_ge_0]. }
  { now rewrite Rmult_0_l. }
  now rewrite Rmult_0_l, Rplus_0_l, round_0; [|apply valid_rnd_N]. }
now apply error_N_FLT_aux.
Qed.

Section Fprop_relative_FLX.

Variable prec : Z.
Variable Hp : Zlt 0 prec.

Lemma relative_error_FLX_aux :
  forall k, (prec <= k - FLX_exp prec k)%Z.
Proof.
intros k.
unfold FLX_exp.
omega.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem relative_error_FLX :
  forall x,
  (x <> 0)%R ->
  (Rabs (round beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs x)%R.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (ln_beta beta x) as (ex, He).
specialize (He Hx).
apply relative_error with (ex - 1)%Z...
intros k _.
apply relative_error_FLX_aux.
apply He.
Qed.

(** 1+#&epsilon;# property in any rounding in FLX *)
Theorem relative_error_FLX_ex :
  forall x,
  exists eps,
  (Rabs eps < bpow (-prec + 1))%R /\ round beta (FLX_exp prec) rnd x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros x.
apply relative_error_lt_conversion...
apply bpow_gt_0.
now apply relative_error_FLX.
Qed.

Theorem relative_error_FLX_round :
  forall x,
  (x <> 0)%R ->
  (Rabs (round beta (FLX_exp prec) rnd x - x) < bpow (-prec + 1) * Rabs (round beta (FLX_exp prec) rnd x))%R.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (ln_beta beta x) as (ex, He).
specialize (He Hx).
apply relative_error_round with (ex - 1)%Z...
intros k _.
apply relative_error_FLX_aux.
apply He.
Qed.

Variable choice : Z -> bool.

Theorem relative_error_N_FLX :
  forall x,
  (Rabs (round beta (FLX_exp prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs x)%R.
Proof with auto with typeclass_instances.
intros x.
destruct (Req_dec x 0) as [Hx|Hx].
(* . *)
rewrite Hx, round_0...
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.
(* . *)
destruct (ln_beta beta x) as (ex, He).
specialize (He Hx).
apply relative_error_N with (ex - 1)%Z...
intros k _.
apply relative_error_FLX_aux.
apply He.
Qed.

(** 1+#&epsilon;# property in rounding to nearest in FLX *)
Theorem relative_error_N_FLX_ex :
  forall x,
  exists eps,
  (Rabs eps <= /2 * bpow (-prec + 1))%R /\ round beta (FLX_exp prec) (Znearest choice) x = (x * (1 + eps))%R.
Proof with auto with typeclass_instances.
intros x.
apply relative_error_le_conversion...
apply Rlt_le.
apply Rmult_lt_0_compat.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
apply bpow_gt_0.
now apply relative_error_N_FLX.
Qed.

Theorem relative_error_N_FLX_round :
  forall x,
  (Rabs (round beta (FLX_exp prec) (Znearest choice) x - x) <= /2 * bpow (-prec + 1) * Rabs (round beta (FLX_exp prec) (Znearest choice) x))%R.
Proof with auto with typeclass_instances.
intros x.
destruct (Req_dec x 0) as [Hx|Hx].
(* . *)
rewrite Hx, round_0...
unfold Rminus.
rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0.
rewrite Rmult_0_r.
apply Rle_refl.
(* . *)
destruct (ln_beta beta x) as (ex, He).
specialize (He Hx).
apply relative_error_N_round with (ex - 1)%Z.
now apply FLX_exp_valid.
intros k _.
apply relative_error_FLX_aux.
exact Hp.
apply He.
Qed.

End Fprop_relative_FLX.

End Fprop_relative.
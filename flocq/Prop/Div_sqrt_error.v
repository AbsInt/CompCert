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

(** * Remainder of the division and square root are in the FLX format *)

From Coq Require Import ZArith Reals Psatz.

Require Import Core Operations Relative Sterbenz Mult_error.

Section Fprop_divsqrt_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.

Lemma generic_format_plus_prec :
  forall fexp, (forall e, (fexp e <= e - prec)%Z) ->
  forall x y (fx fy: float beta),
  (x = F2R fx)%R -> (y = F2R fy)%R -> (Rabs (x+y) < bpow (prec+Fexp fx))%R ->
  (Rabs (x+y) < bpow (prec+Fexp fy))%R ->
  generic_format beta fexp (x+y)%R.
Proof.
intros fexp Hfexp x y fx fy Hx Hy H1 H2.
case (Req_dec (x+y) 0); intros H.
rewrite H; apply generic_format_0.
rewrite Hx, Hy, <- F2R_plus.
apply generic_format_F2R.
intros _.
change (F2R _) with (F2R (Fplus fx fy)).
apply Z.le_trans with (Z.min (Fexp fx) (Fexp fy)).
rewrite F2R_plus, <- Hx, <- Hy.
unfold cexp.
apply Z.le_trans with (1:=Hfexp _).
apply Zplus_le_reg_l with prec; ring_simplify.
apply mag_le_bpow with (1 := H).
now apply Z.min_case.
rewrite <- Fexp_Fplus.
apply Z.le_refl.
Qed.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (cexp beta (FLX_exp prec)).

Variable choice : Z -> bool.


(** Remainder of the division in FLX *)
Theorem div_error_FLX :
  forall rnd { Zrnd : Valid_rnd rnd } x y,
  format x -> format y ->
  format (x - round beta (FLX_exp prec) rnd (x/y) * y)%R.
Proof with auto with typeclass_instances.
intros rnd Zrnd x y Hx Hy.
destruct (Req_dec y 0) as [Zy|Zy].
now rewrite Zy, Rmult_0_r, Rminus_0_r.
destruct (Req_dec (round beta (FLX_exp prec) rnd (x/y)) 0) as [Hr|Hr].
rewrite Hr; ring_simplify (x-0*y)%R; assumption.
assert (Zx: x <> R0).
contradict Hr.
rewrite Hr.
unfold Rdiv.
now rewrite Rmult_0_l, round_0.
destruct (canonical_generic_format _ _ x Hx) as (fx,(Hx1,Hx2)).
destruct (canonical_generic_format _ _ y Hy) as (fy,(Hy1,Hy2)).
destruct (canonical_generic_format beta (FLX_exp prec) (round beta (FLX_exp prec) rnd (x / y))) as (fr,(Hr1,Hr2)).
apply generic_format_round...
unfold Rminus; apply generic_format_plus_prec with fx (Fopp (Fmult fr fy)); trivial.
intros e; apply Z.le_refl.
now rewrite F2R_opp, F2R_mult, <- Hr1, <- Hy1.
(* *)
destruct (relative_error_FLX_ex beta prec (prec_gt_0 prec) rnd (x / y)%R) as (eps,(Heps1,Heps2)).
rewrite Heps2.
rewrite <- Rabs_Ropp.
replace (-(x + - (x / y * (1 + eps) * y)))%R with (x * eps)%R by now field.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs x * 1)%R.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
apply Rlt_le_trans with (1 := Heps1).
change 1%R with (bpow 0).
apply bpow_le.
generalize (prec_gt_0 prec).
clear ; lia.
rewrite Rmult_1_r.
rewrite Hx2, <- Hx1.
unfold cexp.
destruct (mag beta x) as (ex, Hex).
simpl.
specialize (Hex Zx).
apply Rlt_le.
apply Rlt_le_trans with (1 := proj2 Hex).
apply bpow_le.
unfold FLX_exp.
ring_simplify.
apply Z.le_refl.
(* *)
replace (Fexp (Fopp (Fmult fr fy))) with (Fexp fr + Fexp fy)%Z.
2: unfold Fopp, Fmult; destruct fr; destruct fy; now simpl.
replace (x + - (round beta (FLX_exp prec) rnd (x / y) * y))%R with
  (y * (-(round beta (FLX_exp prec) rnd (x / y) - x/y)))%R.
2: field; assumption.
rewrite Rabs_mult.
apply Rlt_le_trans with (Rabs y * bpow (Fexp fr))%R.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
rewrite Rabs_Ropp.
replace (bpow (Fexp fr)) with (ulp beta (FLX_exp prec) (F2R fr)).
rewrite <- Hr1.
apply error_lt_ulp_round...
apply Rmult_integral_contrapositive_currified; try apply Rinv_neq_0_compat; assumption.
rewrite ulp_neq_0.
2: now rewrite <- Hr1.
apply f_equal.
now rewrite Hr2, <- Hr1.
replace (prec+(Fexp fr+Fexp fy))%Z with ((prec+Fexp fy)+Fexp fr)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite Hy2, <- Hy1 ; unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta y - prec))%Z.
destruct (mag beta y); simpl.
left; now apply a.
Qed.

(** Remainder of the square in FLX (with p>1) and rounding to nearest *)
Variable Hp1 : Z.lt 1 prec.

Theorem sqrt_error_FLX_N :
  forall x, format x ->
  format (x - Rsqr (round beta (FLX_exp prec) (Znearest choice) (sqrt x)))%R.
Proof with auto with typeclass_instances.
intros x Hx.
destruct (total_order_T x 0) as [[Hxz|Hxz]|Hxz].
unfold sqrt.
destruct (Rcase_abs x).
rewrite round_0...
unfold Rsqr.
now rewrite Rmult_0_l, Rminus_0_r.
elim (Rlt_irrefl 0).
now apply Rgt_ge_trans with x.
rewrite Hxz, sqrt_0, round_0...
unfold Rsqr.
rewrite Rmult_0_l, Rminus_0_r.
apply generic_format_0.
case (Req_dec (round beta (FLX_exp prec) (Znearest choice) (sqrt x)) 0); intros Hr.
rewrite Hr; unfold Rsqr; ring_simplify (x-0*0)%R; assumption.
destruct (canonical_generic_format _ _ x Hx) as (fx,(Hx1,Hx2)).
destruct (canonical_generic_format beta (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) (sqrt x))) as (fr,(Hr1,Hr2)).
apply generic_format_round...
unfold Rminus; apply generic_format_plus_prec with fx (Fopp (Fmult fr fr)); trivial.
intros e; apply Z.le_refl.
unfold Rsqr; now rewrite F2R_opp,F2R_mult, <- Hr1.
(* *)
apply Rle_lt_trans with x.
apply Rabs_minus_le.
apply Rle_0_sqr.
destruct (relative_error_N_FLX_ex beta prec (prec_gt_0 prec) choice (sqrt x)) as (eps,(Heps1,Heps2)).
rewrite Heps2.
rewrite Rsqr_mult, Rsqr_sqrt, Rmult_comm. 2: now apply Rlt_le.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rle_trans with (5²/4²)%R.
rewrite <- Rsqr_div.
apply Rsqr_le_abs_1.
apply Rle_trans with (1 := Rabs_triang _ _).
rewrite Rabs_R1.
apply Rplus_le_reg_l with (-1)%R.
replace (-1 + (1 + Rabs eps))%R with (Rabs eps) by ring.
apply Rle_trans with (1 := Heps1).
rewrite Rabs_pos_eq.
apply Rmult_le_reg_l with 2%R.
now apply IZR_lt.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
apply Rle_trans with (bpow (-1)).
apply bpow_le.
lia.
replace (2 * (-1 + 5 / 4))%R with (/2)%R by field.
apply Rinv_le.
now apply IZR_lt.
apply IZR_le.
unfold Zpower_pos. simpl.
rewrite Zmult_1_r.
apply Zle_bool_imp_le.
apply beta.
now apply IZR_neq.
unfold Rdiv.
apply Rmult_le_pos.
now apply IZR_le.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
now apply IZR_neq.
unfold Rsqr.
replace (5 * 5 / (4 * 4))%R with (25 * /16)%R by field.
apply Rmult_le_reg_r with 16%R.
now apply IZR_lt.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now apply (IZR_le _ 32).
now apply IZR_neq.
rewrite Hx2, <- Hx1; unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta x - prec))%Z.
destruct (mag beta x); simpl.
rewrite <- (Rabs_right x).
apply a.
now apply Rgt_not_eq.
now apply Rgt_ge.
(* *)
replace (Fexp (Fopp (Fmult fr fr))) with (Fexp fr + Fexp fr)%Z.
2: unfold Fopp, Fmult; destruct fr; now simpl.
rewrite Hr1.
replace (x + - Rsqr (F2R fr))%R with (-((F2R fr - sqrt x)*(F2R fr + sqrt x)))%R.
2: rewrite <- (sqrt_sqrt x) at 3; auto.
2: unfold Rsqr; ring.
rewrite Rabs_Ropp, Rabs_mult.
apply Rle_lt_trans with ((/2*bpow (Fexp fr))* Rabs (F2R fr + sqrt x))%R.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rle_trans with (/2*ulp beta  (FLX_exp prec) (F2R fr))%R.
rewrite <- Hr1.
apply error_le_half_ulp_round...
right; rewrite ulp_neq_0.
2: now rewrite <- Hr1.
apply f_equal.
rewrite Hr2, <- Hr1; trivial.
rewrite Rmult_assoc, Rmult_comm.
replace (prec+(Fexp fr+Fexp fr))%Z with (Fexp fr + (prec+Fexp fr))%Z by ring.
rewrite bpow_plus, Rmult_assoc.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
apply Rmult_lt_reg_l with (1 := Rlt_0_2).
apply Rle_lt_trans with (Rabs (F2R fr + sqrt x)).
right; field.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
(* . *)
assert (Rabs (F2R fr) < bpow (prec + Fexp fr))%R.
rewrite Hr2.
unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta (F2R fr) - prec))%Z.
destruct (mag beta (F2R fr)); simpl.
apply a.
rewrite <- Hr1; auto.
(* . *)
apply Rlt_le_trans with (bpow (prec + Fexp fr)+ Rabs (sqrt x))%R.
now apply Rplus_lt_compat_r.
(* . *)
replace (2 * bpow (prec + Fexp fr))%R with (bpow (prec + Fexp fr) + bpow (prec + Fexp fr))%R by ring.
apply Rplus_le_compat_l.
assert (sqrt x <> 0)%R.
apply Rgt_not_eq.
now apply sqrt_lt_R0.
destruct (mag beta (sqrt x)) as (es,Es).
specialize (Es H0).
apply Rle_trans with (bpow es).
now apply Rlt_le.
apply bpow_le.
case (Zle_or_lt es (prec + Fexp fr)) ; trivial.
intros H1.
absurd (Rabs (F2R fr) < bpow (es - 1))%R.
apply Rle_not_lt.
rewrite <- Hr1.
apply abs_round_ge_generic...
apply generic_format_bpow.
unfold FLX_exp; lia.
apply Es.
apply Rlt_le_trans with (1:=H).
apply bpow_le.
lia.
now apply Rlt_le.
Qed.

Lemma sqrt_error_N_FLX_aux1 x (Fx : format x) (Px : (0 < x)%R) :
  exists (mu : R) (e : Z), (format mu /\ x = mu * bpow (2 * e) :> R
                            /\ 1 <= mu < bpow 2)%R.
Proof.
set (e := ((mag beta x - 1) / 2)%Z).
set (mu := (x * bpow (-2 * e)%Z)%R).
assert (Hbe : (bpow (-2 * e) * bpow (2 * e) = 1)%R).
{ now rewrite <- bpow_plus; case e; simpl; [reflexivity| |]; intro p;
    rewrite Z.pos_sub_diag. }
assert (Fmu : format mu); [now apply mult_bpow_exact_FLX|].
exists mu, e; split; [exact Fmu|split; [|split]].
{ set (e2 := (2 * e)%Z); simpl; unfold mu; rewrite Rmult_assoc.
  now unfold e2; rewrite Hbe, Rmult_1_r. }
{ apply (Rmult_le_reg_r (bpow (2 * e))).
  { apply bpow_gt_0. }
  rewrite Rmult_1_l; set (e2 := (2 * e)%Z); simpl; unfold mu.
  unfold e2; rewrite Rmult_assoc, Hbe, Rmult_1_r.
  apply (Rle_trans _ (bpow (mag beta x - 1))).
  { now apply bpow_le; unfold e; apply Z_mult_div_ge. }
  set (l := mag _ _); rewrite <- (Rabs_pos_eq _ (Rlt_le _ _ Px)).
  unfold l; apply bpow_mag_le.
  intro Hx; revert Px; rewrite Hx; apply Rlt_irrefl. }
simpl; unfold mu; change (IZR _) with (bpow 2).
apply (Rmult_lt_reg_r (bpow (2 * e))); [now apply bpow_gt_0|].
rewrite Rmult_assoc, Hbe, Rmult_1_r.
apply (Rlt_le_trans _ (bpow (mag beta x))).
{ rewrite <- (Rabs_pos_eq _ (Rlt_le _ _ Px)) at 1; apply bpow_mag_gt. }
rewrite <- bpow_plus; apply bpow_le; unfold e; set (mxm1 := (_ - 1)%Z).
replace (_ * _)%Z with (2 * (mxm1 / 2) + mxm1 mod 2 - mxm1 mod 2)%Z by ring.
rewrite <- Z.div_mod; [|now simpl].
apply (Zplus_le_reg_r _ _ (mxm1 mod 2 - mag beta x)%Z).
unfold mxm1; destruct (Z.mod_bound_or (mag beta x - 1) 2); lia.
Qed.

Notation u_ro := (u_ro beta prec).

Lemma sqrt_error_N_FLX_aux2 x (Fx : format x) :
  (1 <= x)%R ->
  (x = 1 :> R \/ x = 1 + 2 * u_ro :> R \/ 1 + 4 * u_ro <= x)%R.
Proof.
intro HxGe1.
assert (Pu_ro : (0 <= u_ro)%R); [apply Rmult_le_pos; [lra|apply bpow_ge_0]|].
destruct (Rle_or_lt x 1) as [HxLe1|HxGt1]; [now left; apply Rle_antisym|right].
assert (F1 : format 1); [now apply generic_format_FLX_1|].
assert (H2eps : (2 * u_ro = bpow (-prec + 1))%R).
{ unfold u_ro; rewrite bpow_plus; field. }
assert (HmuGe1p2eps : (1 + 2 * u_ro <= x)%R).
{ rewrite H2eps, <- succ_FLX_1.
  now apply succ_le_lt; [now apply FLX_exp_valid| | |]. }
destruct (Rle_or_lt x (1 + 2 * u_ro)) as [HxLe1p2eps|HxGt1p2eps];
  [now left; apply Rle_antisym|right].
assert (Hulp1p2eps : (ulp beta (FLX_exp prec) (1 + 2 * u_ro) = 2 * u_ro)%R).
{ destruct (ulp_succ_pos _ _ _ F1 Rlt_0_1) as [Hsucc|Hsucc].
  { now rewrite H2eps, <- succ_FLX_1, <- ulp_FLX_1. }
  exfalso; revert Hsucc; apply Rlt_not_eq.
  rewrite succ_FLX_1, mag_1, bpow_1, <- H2eps; simpl.
  apply (Rlt_le_trans _ 2); [apply Rplus_lt_compat_l|].
  { unfold u_ro; rewrite <-Rmult_assoc, Rinv_r, Rmult_1_l; [|lra].
    change R1 with (bpow 0); apply bpow_lt; lia. }
  apply IZR_le, Zle_bool_imp_le, radix_prop. }
assert (Hsucc1p2eps :
          (succ beta (FLX_exp prec) (1 + 2 * u_ro) = 1 + 4 * u_ro)%R).
{ unfold succ; rewrite Rle_bool_true; [rewrite Hulp1p2eps; ring|].
  apply Rplus_le_le_0_compat; lra. }
rewrite <- Hsucc1p2eps.
apply succ_le_lt; [now apply FLX_exp_valid| |exact Fx|now simpl].
rewrite H2eps, <- succ_FLX_1.
now apply generic_format_succ; [apply FLX_exp_valid|].
Qed.

Lemma sqrt_error_N_FLX_aux3 :
  (u_ro / sqrt (1 + 4 * u_ro) <= 1 - 1 / sqrt (1 + 2 * u_ro))%R.
Proof.
assert (Pu_ro : (0 <= u_ro)%R); [apply Rmult_le_pos; [lra|apply bpow_ge_0]|].
unfold Rdiv; apply (Rplus_le_reg_r (/ sqrt (1 + 2 * u_ro))); ring_simplify.
apply (Rmult_le_reg_r (sqrt (1 + 4 * u_ro) * sqrt (1 + 2 * u_ro))).
{ apply Rmult_lt_0_compat; apply sqrt_lt_R0; lra. }
field_simplify; [|split; apply Rgt_not_eq, Rlt_gt, sqrt_lt_R0; lra].
try unfold Rdiv; rewrite ?Rinv_1, ?Rmult_1_r.
apply Rsqr_incr_0_var; [|now apply Rmult_le_pos; apply sqrt_pos].
rewrite <-sqrt_mult; [|lra|lra].
rewrite Rsqr_sqrt; [|apply Rmult_le_pos; lra].
unfold Rsqr; ring_simplify; unfold pow; rewrite !Rmult_1_r.
rewrite !sqrt_def; [|lra|lra].
apply (Rplus_le_reg_r (-u_ro * u_ro - 1 -4 * u_ro - 2 * u_ro ^ 3)).
ring_simplify; apply Rsqr_incr_0_var.
{ unfold Rsqr; ring_simplify.
  unfold pow; rewrite !Rmult_1_r, !sqrt_def; [|lra|lra].
  apply (Rplus_le_reg_r (-32 * u_ro ^ 4 - 24 * u_ro ^ 3 - 4 * u_ro ^ 2)).
  ring_simplify.
  replace (_ + _)%R
    with (((4 * u_ro ^ 2 - 28 * u_ro + 9) * u_ro + 4) * u_ro ^ 3)%R by ring.
  apply Rmult_le_pos; [|now apply pow_le].
  assert (Heps_le_half : (u_ro <= 1 / 2)%R).
  { unfold u_ro, Rdiv; rewrite Rmult_comm; apply Rmult_le_compat_r; [lra|].
    change 1%R with (bpow 0); apply bpow_le; lia. }
  apply (Rle_trans _ (-8 * u_ro + 4)); [lra|].
  apply Rplus_le_compat_r, Rmult_le_compat_r; [apply Pu_ro|].
  now assert (H : (0 <= u_ro ^ 2)%R); [apply pow2_ge_0|lra]. }
assert (H : (u_ro ^ 3 <= u_ro ^ 2)%R).
{ unfold pow; rewrite <-!Rmult_assoc, Rmult_1_r.
  apply Rmult_le_compat_l; [now apply Rmult_le_pos; apply Pu_ro|].
  now apply Rlt_le, u_ro_lt_1. }
now assert (H' : (0 <= u_ro ^ 2)%R); [apply pow2_ge_0|lra].
Qed.

Lemma om1ds1p2u_ro_pos : (0 <= 1 - 1 / sqrt (1 + 2 * u_ro))%R.
Proof.
unfold Rdiv; rewrite Rmult_1_l, <-Rinv_1 at 1.
apply Rle_0_minus, Rinv_le; [lra|].
rewrite <- sqrt_1 at 1; apply sqrt_le_1_alt.
assert (H := u_ro_pos beta prec); lra.
Qed.

Lemma om1ds1p2u_ro_le_u_rod1pu_ro :
  (1 - 1 / sqrt (1 + 2 * u_ro) <= u_ro / (1 + u_ro))%R.
Proof.
assert (Pu_ro := u_ro_pos beta prec).
apply (Rmult_le_reg_r (sqrt (1 + 2 * u_ro) * (1 + u_ro))).
{ apply Rmult_lt_0_compat; [apply sqrt_lt_R0|]; lra. }
field_simplify; [|lra|intro H; apply sqrt_eq_0 in H; lra].
try unfold Rdiv; unfold Rminus; rewrite ?Rinv_1, ?Rmult_1_r, !Rplus_assoc.
rewrite <-(Rplus_0_r (sqrt _ * _)) at 2; apply Rplus_le_compat_l.
apply (Rplus_le_reg_r (1 + u_ro)); ring_simplify.
rewrite <-(sqrt_square (_ + 1)); [|lra]; apply sqrt_le_1_alt.
assert (H : (0 <= u_ro * u_ro)%R); [apply Rmult_le_pos|]; lra.
Qed.

Lemma s1p2u_rom1_pos : (0 <= sqrt (1 + 2 * u_ro) - 1)%R.
apply (Rplus_le_reg_r 1); ring_simplify.
rewrite <-sqrt_1 at 1; apply sqrt_le_1_alt.
assert (H := u_ro_pos beta prec); lra.
Qed.

Theorem sqrt_error_N_FLX x (Fx : format x) :
  (Rabs (round beta (FLX_exp prec) (Znearest choice) (sqrt x) - sqrt x)
   <= (1 - 1 / sqrt (1 + 2 * u_ro)) * Rabs (sqrt x))%R.
Proof.
assert (Peps := u_ro_pos beta prec).
assert (Peps' : (0 < u_ro)%R).
{ unfold u_ro; apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
assert (Pb := om1ds1p2u_ro_pos).
assert (Pb' := s1p2u_rom1_pos).
destruct (Rle_or_lt x 0) as [Nx|Px].
{ rewrite (sqrt_neg _ Nx), round_0, Rabs_R0, Rmult_0_r; [|apply valid_rnd_N].
  now unfold Rminus; rewrite Rplus_0_l, Rabs_Ropp, Rabs_R0; right. }
destruct (sqrt_error_N_FLX_aux1 _ Fx Px)
  as (mu, (e, (Fmu, (Hmu, (HmuGe1, HmuLtsqradix))))).
pose (t := sqrt x).
set (rt := round _ _ _ _).
assert (Ht : (t = sqrt mu * bpow e)%R).
{ unfold t; rewrite Hmu, sqrt_mult_alt; [|now apply (Rle_trans _ _ _ Rle_0_1)].
  now rewrite sqrt_bpow. }
destruct (sqrt_error_N_FLX_aux2 _ Fmu HmuGe1) as [Hmu'|[Hmu'|Hmu']].
{ unfold rt; fold t; rewrite Ht, Hmu', sqrt_1, Rmult_1_l.
  rewrite round_generic; [|now apply valid_rnd_N|].
  { rewrite Rminus_diag_eq, Rabs_R0; [|now simpl].
    now apply Rmult_le_pos; [|apply Rabs_pos]. }
  apply generic_format_bpow'; [now apply FLX_exp_valid|].
  unfold FLX_exp; lia. }
{ assert (Hsqrtmu : (1 <= sqrt mu < 1 + u_ro)%R); [rewrite Hmu'; split|].
  { rewrite <- sqrt_1 at 1; apply sqrt_le_1_alt; lra. }
  { rewrite <- sqrt_square; [|lra]; apply sqrt_lt_1_alt; split; [lra|].
    ring_simplify; assert (0 < u_ro ^ 2)%R; [apply pow_lt|]; lra. }
  assert (Fbpowe : generic_format beta (FLX_exp prec) (bpow e)).
  { apply generic_format_bpow; unfold FLX_exp; lia. }
  assert (Hrt : rt = bpow e :> R).
  { unfold rt; fold t; rewrite Ht; simpl; apply Rle_antisym.
    { apply round_N_le_midp; [now apply FLX_exp_valid|exact Fbpowe|].
      apply (Rlt_le_trans _ ((1 + u_ro) * bpow e)).
      { now apply Rmult_lt_compat_r; [apply bpow_gt_0|]. }
      unfold succ; rewrite Rle_bool_true; [|now apply bpow_ge_0].
      rewrite ulp_bpow; unfold FLX_exp.
      unfold Z.sub, u_ro; rewrite !bpow_plus; right; field. }
    apply round_ge_generic;
      [now apply FLX_exp_valid|now apply valid_rnd_N|exact Fbpowe|].
    rewrite <- (Rmult_1_l (bpow _)) at 1.
    now apply Rmult_le_compat_r; [apply bpow_ge_0|]. }
  fold t; rewrite Hrt, Ht, Hmu', <-(Rabs_pos_eq _ Pb), <-Rabs_mult.
  rewrite Rabs_minus_sym; right; f_equal; field; lra. }
assert (Hsqrtmu : (1 + u_ro < sqrt mu)%R).
{ apply (Rlt_le_trans _ (sqrt (1 + 4 * u_ro))); [|now apply sqrt_le_1_alt].
  assert (P1peps : (0 <= 1 + u_ro)%R)
    by now apply Rplus_le_le_0_compat; [lra|apply Peps].
  rewrite <- (sqrt_square (1 + u_ro)); [|lra].
  apply sqrt_lt_1_alt; split; [now apply Rmult_le_pos|].
  apply (Rplus_lt_reg_r (-1 - 2 * u_ro)); ring_simplify; simpl.
  rewrite Rmult_1_r; apply Rmult_lt_compat_r; [apply Peps'|].
  now apply (Rlt_le_trans _ 1); [apply u_ro_lt_1|lra]. }
assert (Hulpt : (ulp beta (FLX_exp prec) t = 2 * u_ro * bpow e)%R).
{ unfold ulp; rewrite Req_bool_false; [|apply Rgt_not_eq, Rlt_gt].
  { unfold u_ro; rewrite <-Rmult_assoc, Rinv_r, Rmult_1_l, <-bpow_plus; [|lra].
    f_equal; unfold cexp, FLX_exp.
    assert (Hmagt : (mag beta t = 1 + e :> Z)%Z).
    { apply mag_unique.
      unfold t; rewrite (Rabs_pos_eq _ (Rlt_le _ _ (sqrt_lt_R0 _ Px))).
      fold t; split.
      { rewrite Ht; replace (_ - _)%Z with e by ring.
        rewrite <- (Rmult_1_l (bpow _)) at 1; apply Rmult_le_compat_r.
        { apply bpow_ge_0. }
        now rewrite <- sqrt_1; apply sqrt_le_1_alt. }
      rewrite bpow_plus, bpow_1, Ht; simpl.
      apply Rmult_lt_compat_r; [now apply bpow_gt_0|].
      rewrite <- sqrt_square.
      { apply sqrt_lt_1_alt; split; [lra|].
        apply (Rlt_le_trans _ _ _ HmuLtsqradix); right.
        now unfold bpow, Z.pow_pos; simpl; rewrite Zmult_1_r, mult_IZR. }
      apply IZR_le, (Z.le_trans _ 2), Zle_bool_imp_le, radix_prop; lia. }
    rewrite Hmagt; ring. }
  rewrite Ht; apply Rmult_lt_0_compat; [|now apply bpow_gt_0].
  now apply (Rlt_le_trans _ 1); [lra|rewrite <- sqrt_1; apply sqrt_le_1_alt]. }
assert (Pt : (0 < t)%R).
{ rewrite Ht; apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
assert (H : (Rabs ((rt - sqrt x) / sqrt x)
             <= 1 - 1 / sqrt (1 + 2 * u_ro))%R).
{ unfold Rdiv; rewrite Rabs_mult, (Rabs_pos_eq (/ _));
    [|now left; apply Rinv_0_lt_compat].
  apply (Rle_trans _ ((u_ro * bpow e) / t)).
  { unfold Rdiv; apply Rmult_le_compat_r; [now left; apply Rinv_0_lt_compat|].
    apply (Rle_trans _ _ _ (error_le_half_ulp _ _ _ _)).
    fold t; rewrite Hulpt; right; field. }
  apply (Rle_trans _ (u_ro / sqrt (1 + 4 * u_ro))).
  { apply (Rle_trans _ (u_ro * bpow e / (sqrt (1 + 4 * u_ro) * bpow e))).
    { unfold Rdiv; apply Rmult_le_compat_l;
        [now apply Rmult_le_pos; [apply Peps|apply bpow_ge_0]|].
      apply Rinv_le.
      { apply Rmult_lt_0_compat; [apply sqrt_lt_R0; lra|apply bpow_gt_0]. }
      now rewrite Ht; apply Rmult_le_compat_r;
        [apply bpow_ge_0|apply sqrt_le_1_alt]. }
    right; field; split; apply Rgt_not_eq, Rlt_gt;
      [apply sqrt_lt_R0; lra|apply bpow_gt_0]. }
  apply sqrt_error_N_FLX_aux3. }
revert H; unfold Rdiv; rewrite Rabs_mult, Rabs_Rinv; [|fold t; lra]; intro H.
apply (Rmult_le_reg_r (/ Rabs (sqrt x)));
  [apply Rinv_0_lt_compat, Rabs_pos_lt; fold t; lra|].
apply (Rle_trans _ _ _ H); right; field; split; [apply Rabs_no_R0;fold t|]; lra.
Qed.

Theorem sqrt_error_N_FLX_ex x (Fx : format x) :
  exists eps,
  (Rabs eps <= 1 - 1 / sqrt (1 + 2 * u_ro))%R /\
  round beta (FLX_exp prec) (Znearest choice) (sqrt x)
  = (sqrt x * (1 + eps))%R.
Proof.
now apply relative_error_le_conversion;
  [apply valid_rnd_N|apply om1ds1p2u_ro_pos|apply sqrt_error_N_FLX].
Qed.

Lemma sqrt_error_N_round_ex_derive :
  forall x rx,
  (exists eps,
   (Rabs eps <= 1 - 1 / sqrt (1 + 2 * u_ro))%R /\ rx = (x * (1 + eps))%R) ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\ x = (rx * (1 + eps))%R.
Proof.
intros x rx (d, (Bd, Hd)).
assert (H := Rabs_le_inv _ _ Bd).
assert (H' := om1ds1p2u_ro_le_u_rod1pu_ro).
assert (H'' := u_rod1pu_ro_le_u_ro beta prec).
assert (H''' := u_ro_lt_1 beta prec prec_gt_0_).
assert (Hpos := s1p2u_rom1_pos).
destruct (Req_dec rx 0) as [Zfx|Nzfx].
{ exists 0%R; split; [now rewrite Rabs_R0|].
  rewrite Rplus_0_r, Rmult_1_r, Zfx; rewrite Zfx in Hd.
  destruct (Rmult_integral _ _ (sym_eq Hd)); lra. }
destruct (Req_dec x 0) as [Zx|Nzx].
{ now exfalso; revert Hd; rewrite Zx; rewrite Rmult_0_l. }
set (d' := ((x - rx) / rx)%R).
assert (Hd' : (Rabs d' <= sqrt (1 + 2 * u_ro) - 1)%R).
{ unfold d'; rewrite Hd.
  replace (_ / _)%R with (- d / (1 + d))%R; [|now field; split; lra].
  unfold Rdiv; rewrite Rabs_mult, Rabs_Ropp.
  rewrite (Rabs_pos_eq (/ _)); [|apply Rlt_le, Rinv_0_lt_compat; lra].
  apply (Rmult_le_reg_r (1 + d)); [lra|].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [|lra].
  apply (Rle_trans _ _ _ Bd).
  apply (Rle_trans _ ((sqrt (1 + 2 * u_ro) - 1) * (1/sqrt (1 + 2 * u_ro))));
    [right; field|apply Rmult_le_compat_l]; lra. }
now exists d'; split; [exact Hd'|]; unfold d'; field.
Qed.

(** sqrt(1 + 2 u_ro) - 1 <= u_ro *)
Theorem sqrt_error_N_FLX_round_ex :
  forall x,
  format x ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\
  sqrt x = (round beta (FLX_exp prec) (Znearest choice) (sqrt x) * (1 + eps))%R.
Proof.
now intros x Fx; apply sqrt_error_N_round_ex_derive, sqrt_error_N_FLX_ex.
Qed.

Variable emin : Z.
Hypothesis Hemin : (emin <= 2 * (1 - prec))%Z.

Theorem sqrt_error_N_FLT_ex :
  forall x,
  generic_format beta (FLT_exp emin prec) x ->
  exists eps,
  (Rabs eps <= 1 - 1 / sqrt (1 + 2 * u_ro))%R /\
  round beta (FLT_exp emin prec) (Znearest choice) (sqrt x)
  = (sqrt x * (1 + eps))%R.
Proof.
intros x Fx.
assert (Heps := u_ro_pos).
assert (Pb := om1ds1p2u_ro_pos).
destruct (Rle_or_lt x 0) as [Nx|Px].
{ exists 0%R; split; [now rewrite Rabs_R0|].
  now rewrite (sqrt_neg x Nx), round_0, Rmult_0_l; [|apply valid_rnd_N]. }
assert (Fx' := generic_format_FLX_FLT _ _ _ _ Fx).
destruct (sqrt_error_N_FLX_ex _ Fx') as (d, (Bd, Hd)).
exists d; split; [exact Bd|]; rewrite <-Hd; apply round_FLT_FLX.
apply (Rle_trans _ (bpow (emin / 2)%Z)).
{ apply bpow_le, Z.div_le_lower_bound; lia. }
apply (Rle_trans _ _ _ (sqrt_bpow_ge _ _)).
rewrite Rabs_pos_eq; [|now apply sqrt_pos]; apply sqrt_le_1_alt.
revert Fx; apply generic_format_ge_bpow; [|exact Px].
intro e; unfold FLT_exp; apply Z.le_max_r.
Qed.

(** sqrt(1 + 2 u_ro) - 1 <= u_ro *)
Theorem sqrt_error_N_FLT_round_ex :
  forall x,
  generic_format beta (FLT_exp emin prec) x ->
  exists eps,
  (Rabs eps <= sqrt (1 + 2 * u_ro) - 1)%R /\
  sqrt x
  = (round beta (FLT_exp emin prec) (Znearest choice) (sqrt x) * (1 + eps))%R.
Proof.
now intros x Fx; apply sqrt_error_N_round_ex_derive, sqrt_error_N_FLT_ex.
Qed.

End Fprop_divsqrt_error.

Section format_REM_aux.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Notation format := (generic_format beta fexp).

Lemma format_REM_aux:
  forall x y : R,
  format x -> format y -> (0 <= x)%R -> (0 < y)%R ->
  ((0 < x/y < /2)%R -> rnd (x/y) = 0%Z) ->
  format (x - IZR (rnd (x/y))*y).
Proof with auto with typeclass_instances.
intros x y Fx Fy Hx Hy rnd_small.
pose (n:=rnd (x / y)).
assert (Hn:(IZR n = round beta (FIX_exp 0) rnd (x/y))%R).
unfold round, FIX_exp, cexp, scaled_mantissa, F2R; simpl.
now rewrite 2!Rmult_1_r.
assert (H:(0 <= n)%Z).
apply le_IZR; rewrite Hn; simpl.
apply Rle_trans with (round beta (FIX_exp 0) rnd 0).
right; apply sym_eq, round_0...
apply round_le...
apply Fourier_util.Rle_mult_inv_pos; assumption.
case (Zle_lt_or_eq 0 n); try exact H.
clear H; intros H.
case (Zle_lt_or_eq 1 n).
lia.
clear H; intros H.
set (ex := cexp beta fexp x).
set (ey := cexp beta fexp y).
set (mx := Ztrunc (scaled_mantissa beta fexp x)).
set (my := Ztrunc (scaled_mantissa beta fexp y)).
case (Zle_or_lt ey ex); intros Hexy.
(* ey <= ex *)
assert (H0:(x-IZR n *y = F2R (Float beta (mx*beta^(ex-ey) - n*my) ey))%R).
unfold Rminus; rewrite Rplus_comm.
replace (IZR n) with (F2R (Float beta n 0)).
rewrite Fx, Fy.
fold mx my ex ey.
rewrite <- F2R_mult.
rewrite <- F2R_opp.
rewrite <- F2R_plus.
unfold Fplus. simpl.
rewrite Zle_imp_le_bool with (1 := Hexy).
f_equal; f_equal; ring.
unfold F2R; simpl; ring.
fold n; rewrite H0.
apply generic_format_F2R.
rewrite <- H0; intros H3.
apply monotone_exp.
apply mag_le_abs.
rewrite H0; apply F2R_neq_0; easy.
apply Rmult_le_reg_l with (/Rabs y)%R.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt.
now apply Rgt_not_eq.
rewrite Rinv_l.
2: apply Rgt_not_eq, Rabs_pos_lt.
2: now apply Rgt_not_eq.
rewrite <- Rabs_Rinv.
2: now apply Rgt_not_eq.
rewrite <- Rabs_mult.
replace (/y * (x - IZR n *y))%R with (-(IZR n - x/y))%R.
rewrite Rabs_Ropp.
rewrite Hn.
apply Rle_trans with (1:= error_le_ulp beta (FIX_exp 0) _ _).
rewrite ulp_FIX.
simpl; apply Rle_refl.
field.
now apply Rgt_not_eq.
(* ex < ey: impossible as 1 < n *)
absurd (1 < n)%Z; try easy.
apply Zle_not_lt.
apply le_IZR; simpl; rewrite Hn.
apply round_le_generic...
apply generic_format_FIX.
exists (Float beta 1 0); try easy.
unfold F2R; simpl; ring.
apply Rmult_le_reg_r with y; try easy.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l, Rmult_1_r, Rmult_1_l.
2: now apply Rgt_not_eq.
assert (mag beta x < mag beta y)%Z.
case (Zle_or_lt (mag beta y) (mag beta x)); try easy.
intros J; apply monotone_exp in J; clear -J Hexy.
unfold ex, ey, cexp in Hexy; lia.
left; apply lt_mag with beta; easy.
(* n = 1 -> Sterbenz + rnd_small *)
intros Hn'; fold n; rewrite <- Hn'.
rewrite Rmult_1_l.
case Hx; intros Hx'.
assert (J:(0 < x/y)%R).
apply Fourier_util.Rlt_mult_inv_pos; assumption.
apply sterbenz...
assert (H0:(Rabs (1  - x/y) < 1)%R).
rewrite Hn', Hn.
apply Rlt_le_trans with (ulp beta (FIX_exp 0) (round beta (FIX_exp 0) rnd (x / y)))%R.
apply error_lt_ulp_round...
now apply Rgt_not_eq.
rewrite ulp_FIX.
rewrite <- Hn, <- Hn'.
apply Rle_refl.
apply Rabs_lt_inv in H0.
split; apply Rmult_le_reg_l with (/y)%R; try now apply Rinv_0_lt_compat.
unfold Rdiv; rewrite <- Rmult_assoc.
rewrite Rinv_l.
2: now apply Rgt_not_eq.
rewrite Rmult_1_l, Rmult_comm; fold (x/y)%R.
case (Rle_or_lt (/2) (x/y)); try easy.
intros K.
elim Zlt_not_le with (1 := H).
apply Zeq_le.
apply rnd_small.
now split.
apply Ropp_le_cancel; apply Rplus_le_reg_l with 1%R.
apply Rle_trans with (1-x/y)%R.
2: right; unfold Rdiv; ring.
left; apply Rle_lt_trans with (2:=proj1 H0).
right; field.
now apply Rgt_not_eq.
rewrite <- Hx', Rminus_0_l.
now apply generic_format_opp.
(* n = 0 *)
clear H; intros H; fold n; rewrite <- H.
now rewrite Rmult_0_l, Rminus_0_r.
Qed.

End format_REM_aux.

Section format_REM.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Context { monotone_exp : Monotone_exp fexp }.

Notation format := (generic_format beta fexp).

Theorem format_REM :
  forall rnd : R -> Z, Valid_rnd rnd ->
  forall x y : R,
  ((Rabs (x/y) < /2)%R -> rnd (x/y)%R = 0%Z) ->
  format x -> format y ->
  format (x - IZR (rnd (x/y)%R) * y).
Proof with auto with typeclass_instances.
(* assume 0 < y *)
assert (H: forall rnd : R -> Z, Valid_rnd rnd ->
  forall x y : R,
  ((Rabs (x/y) < /2)%R -> rnd (x/y)%R = 0%Z) ->
  format x -> format y -> (0 < y)%R ->
  format (x - IZR (rnd (x/y)%R) * y)).
intros rnd valid_rnd x y Hrnd Fx Fy Hy.
case (Rle_or_lt 0 x); intros Hx.
apply format_REM_aux; try easy.
intros K.
apply Hrnd.
rewrite Rabs_pos_eq.
apply K.
apply Rlt_le, K.
replace (x - IZR (rnd (x/y)) * y)%R with
   (- (-x - IZR (Zrnd_opp rnd (-x/y)) * y))%R.
apply generic_format_opp.
apply format_REM_aux; try easy...
now apply generic_format_opp.
apply Ropp_le_cancel; rewrite Ropp_0, Ropp_involutive; now left.
replace (- x / y)%R with (- (x/y))%R by (unfold Rdiv; ring).
intros K.
unfold Zrnd_opp.
rewrite Ropp_involutive, Hrnd.
easy.
rewrite Rabs_left.
apply K.
apply Ropp_lt_cancel.
now rewrite Ropp_0.
unfold Zrnd_opp.
replace (- (- x / y))%R with (x / y)%R by (unfold Rdiv; ring).
rewrite opp_IZR.
ring.
(* *)
intros rnd valid_rnd x y Hrnd Fx Fy.
case (Rle_or_lt 0 y); intros Hy.
destruct Hy as [Hy|Hy].
now apply H.
now rewrite <- Hy, Rmult_0_r, Rminus_0_r.
replace (IZR (rnd (x/y)) * y)%R with
  (IZR ((Zrnd_opp rnd) ((x / -y))) * -y)%R.
apply H; try easy...
replace (x / - y)%R with (- (x/y))%R.
intros K.
unfold Zrnd_opp.
rewrite Ropp_involutive, Hrnd.
easy.
now rewrite <- Rabs_Ropp.
field; now apply Rlt_not_eq.
now apply generic_format_opp.
apply Ropp_lt_cancel; now rewrite Ropp_0, Ropp_involutive.
unfold Zrnd_opp.
replace (- (x / - y))%R with (x/y)%R.
rewrite opp_IZR.
ring.
field; now apply Rlt_not_eq.
Qed.

Theorem format_REM_ZR:
  forall x y : R,
  format x -> format y ->
  format (x - IZR (Ztrunc (x/y)) * y).
Proof with auto with typeclass_instances.
intros x y Fx Fy.
apply format_REM; try easy...
intros K.
apply Z.abs_0_iff.
rewrite <- Ztrunc_abs.
rewrite Ztrunc_floor by apply Rabs_pos.
apply Zle_antisym.
replace 0%Z with (Zfloor (/2)).
apply Zfloor_le.
now apply Rlt_le.
apply Zfloor_imp.
simpl ; lra.
apply Zfloor_lub.
apply Rabs_pos.
Qed.

Theorem format_REM_N :
  forall choice,
  forall x y : R,
  format x -> format y ->
  format (x - IZR (Znearest choice (x/y)) * y).
Proof with auto with typeclass_instances.
intros choice x y Fx Fy.
apply format_REM; try easy...
intros K.
apply Znearest_imp.
now rewrite Rminus_0_r.
Qed.

End format_REM.

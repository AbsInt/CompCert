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

(** * Remainder of the division and square root are in the FLX format *)
Require Import Fcore.
Require Import Fcalc_ops.
Require Import Fprop_relative.

Section Fprop_divsqrt_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.

Theorem generic_format_plus_prec:
  forall fexp, (forall e, (fexp e  <= e - prec)%Z) ->
  forall x y (fx fy: float beta),
  (x = F2R fx)%R -> (y = F2R fy)%R -> (Rabs (x+y) < bpow (prec+Fexp fx))%R -> (Rabs (x+y) < bpow (prec+Fexp fy))%R
  -> generic_format beta fexp (x+y)%R.
intros fexp Hfexp x y fx fy Hx Hy H1 H2.
case (Req_dec (x+y) 0); intros H.
rewrite H; apply generic_format_0.
rewrite Hx, Hy, <- F2R_plus.
apply generic_format_F2R.
intros _.
case_eq (Fplus beta fx fy).
intros mz ez Hz.
rewrite <- Hz.
apply Zle_trans with (Zmin (Fexp fx) (Fexp fy)).
rewrite F2R_plus, <- Hx, <- Hy.
unfold canonic_exp.
apply Zle_trans with (1:=Hfexp _).
apply Zplus_le_reg_l with prec; ring_simplify.
apply ln_beta_le_bpow with (1 := H).
now apply Zmin_case.
rewrite <- Fexp_Fplus, Hz.
apply Zle_refl.
Qed.

Theorem ex_Fexp_canonic: forall fexp, forall x, generic_format beta fexp x
  -> exists fx:float beta, (x=F2R fx)%R /\ Fexp fx = canonic_exp beta fexp x.
intros fexp x; unfold generic_format.
exists (Float beta (Ztrunc (scaled_mantissa beta fexp x)) (canonic_exp beta fexp x)).
split; auto.
Qed.


Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exp beta (FLX_exp prec)).

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
destruct (ex_Fexp_canonic _ x Hx) as (fx,(Hx1,Hx2)).
destruct (ex_Fexp_canonic _ y Hy) as (fy,(Hy1,Hy2)).
destruct (ex_Fexp_canonic (FLX_exp prec) (round beta (FLX_exp prec) rnd (x / y))) as (fr,(Hr1,Hr2)).
apply generic_format_round...
unfold Rminus; apply generic_format_plus_prec with fx (Fopp beta (Fmult beta fr fy)); trivial.
intros e; apply Zle_refl.
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
clear ; omega.
rewrite Rmult_1_r.
rewrite Hx2.
unfold canonic_exp.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
specialize (Hex Zx).
apply Rlt_le.
apply Rlt_le_trans with (1 := proj2 Hex).
apply bpow_le.
unfold FLX_exp.
ring_simplify.
apply Zle_refl.
(* *)
replace (Fexp (Fopp beta (Fmult beta fr fy))) with (Fexp fr + Fexp fy)%Z.
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
rewrite Hy2; unfold canonic_exp, FLX_exp.
ring_simplify (prec + (ln_beta beta y - prec))%Z.
destruct (ln_beta beta y); simpl.
left; now apply a.
Qed.

(** Remainder of the square in FLX (with p>1) and rounding to nearest *)
Variable Hp1 : Zlt 1 prec.

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
destruct (ex_Fexp_canonic _ x Hx) as (fx,(Hx1,Hx2)).
destruct (ex_Fexp_canonic (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) (sqrt x))) as (fr,(Hr1,Hr2)).
apply generic_format_round...
unfold Rminus; apply generic_format_plus_prec with fx (Fopp beta (Fmult beta fr fr)); trivial.
intros e; apply Zle_refl.
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
now apply (Z2R_lt 0 2).
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
apply Rle_trans with (bpow (-1)).
apply bpow_le.
omega.
replace (2 * (-1 + 5 / 4))%R with (/2)%R by field.
apply Rinv_le.
now apply (Z2R_lt 0 2).
apply (Z2R_le 2).
unfold Zpower_pos. simpl.
rewrite Zmult_1_r.
apply Zle_bool_imp_le.
apply beta.
apply Rgt_not_eq.
now apply (Z2R_lt 0 2).
unfold Rdiv.
apply Rmult_le_pos.
now apply (Z2R_le 0 5).
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 4).
apply Rgt_not_eq.
now apply (Z2R_lt 0 4).
unfold Rsqr.
replace (5 * 5 / (4 * 4))%R with (25 * /16)%R by field.
apply Rmult_le_reg_r with 16%R.
now apply (Z2R_lt 0 16).
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now apply (Z2R_le 25 32).
apply Rgt_not_eq.
now apply (Z2R_lt 0 16).
rewrite Hx2; unfold canonic_exp, FLX_exp.
ring_simplify (prec + (ln_beta beta x - prec))%Z.
destruct (ln_beta beta x); simpl.
rewrite <- (Rabs_right x).
apply a.
now apply Rgt_not_eq.
now apply Rgt_ge.
(* *)
replace (Fexp (Fopp beta (Fmult beta fr fr))) with (Fexp fr + Fexp fr)%Z.
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
rewrite Hr2; unfold canonic_exp; rewrite Hr1.
unfold FLX_exp.
ring_simplify (prec + (ln_beta beta (F2R fr) - prec))%Z.
destruct (ln_beta beta (F2R fr)); simpl.
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
destruct (ln_beta beta (sqrt x)) as (es,Es).
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
unfold FLX_exp; omega.
apply Es.
apply Rlt_le_trans with (1:=H).
apply bpow_le.
omega.
now apply Rlt_le.
Qed.

End Fprop_divsqrt_error.

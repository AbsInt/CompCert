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

(** * Error of the multiplication is in the FLX/FLT format *)
Require Import Fcore.
Require Import Fcalc_ops.

Section Fprop_mult_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (canonic_exp beta (FLX_exp prec)).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

(** Auxiliary result that provides the exponent *)
Lemma mult_error_FLX_aux:
  forall x y,
  format x -> format y ->
  (round beta (FLX_exp prec) rnd (x * y) - (x * y) <> 0)%R ->
  exists f:float beta,
      (F2R f = round beta (FLX_exp prec) rnd (x * y) - (x * y))%R
      /\  (canonic_exp beta (FLX_exp prec) (F2R f) <= Fexp f)%Z
      /\ (Fexp f = cexp x + cexp y)%Z.
Proof with auto with typeclass_instances.
intros x y Hx Hy Hz.
set (f := (round beta (FLX_exp prec) rnd (x * y))).
destruct (Req_dec (x * y) 0) as [Hxy0|Hxy0].
contradict Hz.
rewrite Hxy0.
rewrite round_0...
ring.
destruct (ln_beta beta (x * y)) as (exy, Hexy).
specialize (Hexy Hxy0).
destruct (ln_beta beta (f - x * y)) as (er, Her).
specialize (Her Hz).
destruct (ln_beta beta x) as (ex, Hex).
assert (Hx0: (x <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_l.
specialize (Hex Hx0).
destruct (ln_beta beta y) as (ey, Hey).
assert (Hy0: (y <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_r.
specialize (Hey Hy0).
(* *)
assert (Hc1: (cexp (x * y)%R - prec <= cexp x + cexp y)%Z).
unfold canonic_exp, FLX_exp.
rewrite ln_beta_unique with (1 := Hex).
rewrite ln_beta_unique with (1 := Hey).
rewrite ln_beta_unique with (1 := Hexy).
cut (exy - 1 < ex + ey)%Z. omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (1 := proj1 Hexy).
rewrite Rabs_mult.
rewrite bpow_plus.
apply Rmult_le_0_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Hex.
apply Hey.
(* *)
assert (Hc2: (cexp x + cexp y <= cexp (x * y)%R)%Z).
unfold canonic_exp, FLX_exp.
rewrite ln_beta_unique with (1 := Hex).
rewrite ln_beta_unique with (1 := Hey).
rewrite ln_beta_unique with (1 := Hexy).
cut ((ex - 1) + (ey - 1) < exy)%Z.
generalize (prec_gt_0 prec).
clear ; omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 Hexy).
rewrite Rabs_mult.
rewrite bpow_plus.
apply Rmult_le_compat.
apply bpow_ge_0.
apply bpow_ge_0.
apply Hex.
apply Hey.
(* *)
assert (Hr: ((F2R (Float beta (- (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) *
  Ztrunc (scaled_mantissa beta (FLX_exp prec) y)) + rnd (scaled_mantissa beta (FLX_exp prec) (x * y)) *
  beta ^ (cexp (x * y)%R - (cexp x + cexp y))) (cexp x + cexp y))) = f - x * y)%R).
rewrite Hx at 6.
rewrite Hy at 6.
rewrite <- F2R_mult.
simpl.
unfold f, round, Rminus.
rewrite <- F2R_opp, Rplus_comm, <- F2R_plus.
unfold Fplus. simpl.
now rewrite Zle_imp_le_bool with (1 := Hc2).
(* *)
exists (Float beta (- (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) *
  Ztrunc (scaled_mantissa beta (FLX_exp prec) y)) + rnd (scaled_mantissa beta (FLX_exp prec) (x * y)) *
  beta ^ (cexp (x * y)%R - (cexp x + cexp y))) (cexp x + cexp y)).
split;[assumption|split].
rewrite Hr.
simpl.
clear Hr.
apply Zle_trans with (cexp (x * y)%R - prec)%Z.
unfold canonic_exp, FLX_exp.
apply Zplus_le_compat_r.
rewrite ln_beta_unique with (1 := Hexy).
apply ln_beta_le_bpow with (1 := Hz).
replace (bpow (exy - prec)) with (ulp beta (FLX_exp prec) (x * y)).
apply error_lt_ulp...
rewrite ulp_neq_0; trivial.
unfold canonic_exp.
now rewrite ln_beta_unique with (1 := Hexy).
apply Hc1.
reflexivity.
Qed.

(** Error of the multiplication in FLX *)
Theorem mult_error_FLX :
  forall x y,
  format x -> format y ->
  format (round beta (FLX_exp prec) rnd (x * y) - (x * y))%R.
Proof.
intros x y Hx Hy.
destruct (Req_dec (round beta (FLX_exp prec) rnd (x * y) - x * y) 0) as [Hr0|Hr0].
rewrite Hr0.
apply generic_format_0.
destruct (mult_error_FLX_aux x y Hx Hy Hr0) as ((m,e),(H1,(H2,H3))).
rewrite <- H1.
now apply generic_format_F2R.
Qed.

End Fprop_mult_error.

Section Fprop_mult_error_FLT.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation cexp := (canonic_exp beta (FLT_exp emin prec)).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

(** Error of the multiplication in FLT with underflow requirements *)
Theorem mult_error_FLT :
  forall x y,
  format x -> format y ->
  (x*y = 0)%R \/ (bpow (emin + 2*prec - 1) <= Rabs (x * y))%R ->
  format (round beta (FLT_exp emin prec) rnd (x * y) - (x * y))%R.
Proof with auto with typeclass_instances.
intros x y Hx Hy Hxy.
set (f := (round beta (FLT_exp emin prec) rnd (x * y))).
destruct (Req_dec (f - x * y) 0) as [Hr0|Hr0].
rewrite Hr0.
apply generic_format_0.
destruct Hxy as [Hxy|Hxy].
unfold f.
rewrite Hxy.
rewrite round_0...
ring_simplify (0 - 0)%R.
apply generic_format_0.
destruct (mult_error_FLX_aux beta prec rnd x y) as ((m,e),(H1,(H2,H3))).
now apply generic_format_FLX_FLT with emin.
now apply generic_format_FLX_FLT with emin.
rewrite <- (round_FLT_FLX beta emin).
assumption.
apply Rle_trans with (2:=Hxy).
apply bpow_le.
generalize (prec_gt_0 prec).
clear ; omega.
rewrite <- (round_FLT_FLX beta emin) in H1.
2:apply Rle_trans with (2:=Hxy).
2:apply bpow_le ; generalize (prec_gt_0 prec) ; clear ; omega.
unfold f; rewrite <- H1.
apply generic_format_F2R.
intros _.
simpl in H2, H3.
unfold canonic_exp, FLT_exp.
case (Zmax_spec (ln_beta beta (F2R (Float beta m e)) - prec) emin);
  intros (M1,M2); rewrite M2.
apply Zle_trans with (2:=H2).
unfold canonic_exp, FLX_exp.
apply Zle_refl.
rewrite H3.
unfold canonic_exp, FLX_exp.
assert (Hxy0:(x*y <> 0)%R).
contradict Hr0.
unfold f.
rewrite Hr0.
rewrite round_0...
ring.
assert (Hx0: (x <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_l.
assert (Hy0: (y <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_r.
destruct (ln_beta beta x) as (ex,Ex) ; simpl.
specialize (Ex Hx0).
destruct (ln_beta beta y) as (ey,Ey) ; simpl.
specialize (Ey Hy0).
assert (emin + 2 * prec -1 < ex + ey)%Z.
2: omega.
apply (lt_bpow beta).
apply Rle_lt_trans with (1:=Hxy).
rewrite Rabs_mult, bpow_plus.
apply Rmult_le_0_lt_compat; try apply Rabs_pos.
apply Ex.
apply Ey.
Qed.

End Fprop_mult_error_FLT.

(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

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

(** * Error of the multiplication is in the FLX/FLT format *)

From Coq Require Import ZArith Reals Lia.

Require Import Core Operations Plus_error.

Section Fprop_mult_error.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLX_exp prec)).
Notation cexp := (cexp beta (FLX_exp prec)).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

(** Auxiliary result that provides the exponent *)
Lemma mult_error_FLX_aux:
  forall x y,
  format x -> format y ->
  (round beta (FLX_exp prec) rnd (x * y) - (x * y) <> 0)%R ->
  exists f:float beta,
    (F2R f = round beta (FLX_exp prec) rnd (x * y) - (x * y))%R
    /\ (cexp (F2R f) <= Fexp f)%Z
    /\ (Fexp f = cexp x + cexp y)%Z.
Proof with auto with typeclass_instances.
intros x y Hx Hy Hz.
set (f := (round beta (FLX_exp prec) rnd (x * y))).
destruct (Req_dec (x * y) 0) as [Hxy0|Hxy0].
contradict Hz.
rewrite Hxy0.
rewrite round_0...
ring.
destruct (mag beta (x * y)) as (exy, Hexy).
specialize (Hexy Hxy0).
destruct (mag beta (f - x * y)) as (er, Her).
specialize (Her Hz).
destruct (mag beta x) as (ex, Hex).
assert (Hx0: (x <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_l.
specialize (Hex Hx0).
destruct (mag beta y) as (ey, Hey).
assert (Hy0: (y <> 0)%R).
contradict Hxy0.
now rewrite Hxy0, Rmult_0_r.
specialize (Hey Hy0).
(* *)
assert (Hc1: (cexp (x * y)%R - prec <= cexp x + cexp y)%Z).
unfold cexp, FLX_exp.
rewrite mag_unique with (1 := Hex).
rewrite mag_unique with (1 := Hey).
rewrite mag_unique with (1 := Hexy).
cut (exy - 1 < ex + ey)%Z. lia.
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
unfold cexp, FLX_exp.
rewrite mag_unique with (1 := Hex).
rewrite mag_unique with (1 := Hey).
rewrite mag_unique with (1 := Hexy).
cut ((ex - 1) + (ey - 1) < exy)%Z.
generalize (prec_gt_0 prec).
clear ; lia.
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
apply Z.le_trans with (cexp (x * y)%R - prec)%Z.
unfold cexp, FLX_exp.
apply Zplus_le_compat_r.
rewrite mag_unique with (1 := Hexy).
apply mag_le_bpow with (1 := Hz).
replace (bpow (exy - prec)) with (ulp beta (FLX_exp prec) (x * y)).
apply error_lt_ulp...
rewrite ulp_neq_0; trivial.
unfold cexp.
now rewrite mag_unique with (1 := Hexy).
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

Lemma mult_bpow_exact_FLX :
  forall x e,
  format x ->
  format (x * bpow e)%R.
Proof.
intros x e Fx.
destruct (Req_dec x 0) as [Zx|Nzx].
{ rewrite Zx, Rmult_0_l; apply generic_format_0. }
rewrite Fx.
set (mx := Ztrunc _); set (ex := cexp _).
pose (f := {| Fnum := mx; Fexp := ex + e |} : float beta).
apply (generic_format_F2R' _ _ _ f).
{ now unfold F2R; simpl; rewrite bpow_plus, Rmult_assoc. }
intro Nzmx; unfold mx, ex; rewrite <- Fx.
unfold f, ex; simpl; unfold cexp; rewrite (mag_mult_bpow _ _ _ Nzx).
unfold FLX_exp; lia.
Qed.

End Fprop_mult_error.

Section Fprop_mult_error_FLT.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation cexp := (cexp beta (FLT_exp emin prec)).

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

(** Error of the multiplication in FLT with underflow requirements *)
Theorem mult_error_FLT :
  forall x y,
  format x -> format y ->
  (x * y <> 0 -> bpow (emin + 2*prec - 1) <= Rabs (x * y))%R ->
  format (round beta (FLT_exp emin prec) rnd (x * y) - (x * y))%R.
Proof with auto with typeclass_instances.
intros x y Hx Hy Hxy.
set (f := (round beta (FLT_exp emin prec) rnd (x * y))).
destruct (Req_dec (f - x * y) 0) as [Hr0|Hr0].
rewrite Hr0.
apply generic_format_0.
destruct (Req_dec (x * y) 0) as [Hxy'|Hxy'].
unfold f.
rewrite Hxy'.
rewrite round_0...
ring_simplify (0 - 0)%R.
apply generic_format_0.
specialize (Hxy Hxy').
destruct (mult_error_FLX_aux beta prec rnd x y) as ((m,e),(H1,(H2,H3))).
now apply generic_format_FLX_FLT with emin.
now apply generic_format_FLX_FLT with emin.
rewrite <- (round_FLT_FLX beta emin).
assumption.
apply Rle_trans with (2:=Hxy).
apply bpow_le.
generalize (prec_gt_0 prec).
clear ; lia.
rewrite <- (round_FLT_FLX beta emin) in H1.
2:apply Rle_trans with (2:=Hxy).
2:apply bpow_le ; generalize (prec_gt_0 prec) ; clear ; lia.
unfold f; rewrite <- H1.
apply generic_format_F2R.
intros _.
simpl in H2, H3.
unfold cexp, FLT_exp.
case (Zmax_spec (mag beta (F2R (Float beta m e)) - prec) emin);
  intros (M1,M2); rewrite M2.
apply Z.le_trans with (2:=H2).
unfold cexp, FLX_exp.
apply Z.le_refl.
rewrite H3.
unfold cexp, FLX_exp.
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
destruct (mag beta x) as (ex,Ex) ; simpl.
specialize (Ex Hx0).
destruct (mag beta y) as (ey,Ey) ; simpl.
specialize (Ey Hy0).
cut (emin + 2 * prec -1 < ex + ey)%Z. lia.
apply (lt_bpow beta).
apply Rle_lt_trans with (1:=Hxy).
rewrite Rabs_mult, bpow_plus.
apply Rmult_le_0_lt_compat; try apply Rabs_pos.
apply Ex.
apply Ey.
Qed.

Lemma F2R_ge: forall (y:float beta),
   (F2R y <> 0)%R -> (bpow (Fexp y) <= Rabs (F2R y))%R.
Proof.
intros (ny,ey).
rewrite <- F2R_Zabs; unfold F2R; simpl.
case (Zle_lt_or_eq 0 (Z.abs ny)).
apply Z.abs_nonneg.
intros Hy _.
rewrite <- (Rmult_1_l (bpow _)) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le; lia.
intros H1 H2; contradict H2.
replace ny with 0%Z.
simpl; ring.
now apply sym_eq, Z.abs_0_iff, sym_eq.
Qed.

Theorem mult_error_FLT_ge_bpow :
  forall x y e,
  format x -> format y ->
  (bpow (e+2*prec-1) <= Rabs (x * y))%R ->
  (round beta (FLT_exp emin prec) rnd (x * y) - (x * y) <> 0)%R ->
  (bpow e <= Rabs (round beta (FLT_exp emin prec) rnd (x * y) - (x * y)))%R.
Proof with auto with typeclass_instances.
intros x y e.
set (f := (round beta (FLT_exp emin prec) rnd (x * y))).
intros Fx Fy H1.
unfold f; rewrite Fx, Fy, <- F2R_mult.
simpl Fmult.
destruct (round_repr_same_exp beta (FLT_exp emin prec)
 rnd (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x) *
             Ztrunc (scaled_mantissa beta (FLT_exp emin prec) y))
      (cexp x + cexp y)) as (n,Hn).
rewrite Hn; clear Hn.
rewrite <- F2R_minus, Fminus_same_exp.
intros K.
eapply Rle_trans with (2:=F2R_ge _ K).
simpl (Fexp _).
apply bpow_le.
unfold cexp, FLT_exp.
destruct (mag beta x) as (ex,Hx).
destruct (mag beta y) as (ey,Hy).
simpl; apply Z.le_trans with ((ex-prec)+(ey-prec))%Z.
2: apply Zplus_le_compat; apply Z.le_max_l.
cut (e + 2*prec -1< ex+ey)%Z. lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=H1).
rewrite Rabs_mult, bpow_plus.
apply Rmult_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Hx.
intros K'; contradict H1; apply Rlt_not_le.
rewrite K', Rmult_0_l, Rabs_R0; apply bpow_gt_0.
apply Hy.
intros K'; contradict H1; apply Rlt_not_le.
rewrite K', Rmult_0_r, Rabs_R0; apply bpow_gt_0.
Qed.

Lemma mult_bpow_exact_FLT :
  forall x e,
  format x ->
  (emin + prec - mag beta x <= e)%Z ->
  format (x * bpow e)%R.
Proof.
intros x e Fx He.
destruct (Req_dec x 0) as [Zx|Nzx].
{ rewrite Zx, Rmult_0_l; apply generic_format_0. }
rewrite Fx.
set (mx := Ztrunc _); set (ex := cexp _).
pose (f := {| Fnum := mx; Fexp := ex + e |} : float beta).
apply (generic_format_F2R' _ _ _ f).
{ now unfold F2R; simpl; rewrite bpow_plus, Rmult_assoc. }
intro Nzmx; unfold mx, ex; rewrite <- Fx.
unfold f, ex; simpl; unfold cexp; rewrite (mag_mult_bpow _ _ _ Nzx).
unfold FLT_exp; rewrite Z.max_l by lia; rewrite <- Z.add_max_distr_r.
set (n := (_ - _ + _)%Z); apply (Z.le_trans _ n); [unfold n; lia|].
apply Z.le_max_l.
Qed.

Lemma mult_bpow_pos_exact_FLT :
  forall x e,
  format x ->
  (0 <= e)%Z ->
  format (x * bpow e)%R.
Proof.
intros x e Fx He.
destruct (Req_dec x 0) as [Zx|Nzx].
{ rewrite Zx, Rmult_0_l; apply generic_format_0. }
rewrite Fx.
set (mx := Ztrunc _); set (ex := cexp _).
pose (f := {| Fnum := mx; Fexp := ex + e |} : float beta).
apply (generic_format_F2R' _ _ _ f).
{ now unfold F2R; simpl; rewrite bpow_plus, Rmult_assoc. }
intro Nzmx; unfold mx, ex; rewrite <- Fx.
unfold f, ex; simpl; unfold cexp; rewrite (mag_mult_bpow _ _ _ Nzx).
unfold FLT_exp; rewrite <-Z.add_max_distr_r.
replace (_ - _ + e)%Z with (mag beta x + e - prec)%Z; [ |ring].
apply Z.max_le_compat_l; lia.
Qed.

End Fprop_mult_error_FLT.

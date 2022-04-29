(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2013-2018 Sylvie Boldo
#<br />#
Copyright (C) 2013-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Rounding to odd and its properties, including the equivalence
      between rnd_NE and double rounding with rnd_odd and then rnd_NE *)

From Coq Require Import ZArith Reals Psatz.

Require Import Core Operations.

Definition Zrnd_odd x :=  match Req_EM_T x (IZR (Zfloor x))  with
  | left _   => Zfloor x
  | right _  => match (Z.even (Zfloor x)) with
      | true => Zceil x
      | false => Zfloor x
     end
  end.



Global Instance valid_rnd_odd : Valid_rnd Zrnd_odd.
Proof.
split.
(* . *)
intros x y Hxy.
assert (Zfloor x <= Zrnd_odd y)%Z.
(* .. *)
apply Z.le_trans with (Zfloor y).
now apply Zfloor_le.
unfold Zrnd_odd; destruct (Req_EM_T  y (IZR (Zfloor y))).
now apply Z.le_refl.
case (Z.even (Zfloor y)).
apply le_IZR.
apply Rle_trans with y.
apply Zfloor_lb.
apply Zceil_ub.
now apply Z.le_refl.
unfold Zrnd_odd at 1.
(* . *)
destruct (Req_EM_T  x (IZR (Zfloor x))) as [Hx|Hx].
(* .. *)
apply H.
(* .. *)
case_eq (Z.even (Zfloor x)); intros Hx2.
2: apply H.
unfold Zrnd_odd; destruct (Req_EM_T  y (IZR (Zfloor y))) as [Hy|Hy].
apply Zceil_glb.
now rewrite <- Hy.
case_eq (Z.even (Zfloor y)); intros Hy2.
now apply Zceil_le.
apply Zceil_glb.
assert (H0:(Zfloor x <= Zfloor y)%Z) by now apply Zfloor_le.
case (Zle_lt_or_eq _ _  H0); intros H1.
apply Rle_trans with (1:=Zceil_ub _).
rewrite Zceil_floor_neq.
apply IZR_le; lia.
now apply sym_not_eq.
contradict Hy2.
rewrite <- H1, Hx2; discriminate.
(* . *)
intros n; unfold Zrnd_odd.
rewrite Zfloor_IZR, Zceil_IZR.
destruct (Req_EM_T  (IZR n) (IZR n)); trivial.
case (Z.even n); trivial.
Qed.



Lemma Zrnd_odd_Zodd: forall x, x <> (IZR (Zfloor x)) ->
  (Z.even (Zrnd_odd x)) = false.
Proof.
intros x Hx; unfold Zrnd_odd.
destruct (Req_EM_T  x (IZR (Zfloor x))) as [H|H].
now contradict H.
case_eq (Z.even (Zfloor x)).
(* difficult case *)
intros H'.
rewrite Zceil_floor_neq.
rewrite Z.even_add, H'.
reflexivity.
now apply sym_not_eq.
trivial.
Qed.


Lemma Zfloor_plus: forall (n:Z) y,
  (Zfloor (IZR n+y) = n + Zfloor y)%Z.
Proof.
intros n y; unfold Zfloor.
unfold Zminus; rewrite Zplus_assoc; f_equal.
apply sym_eq, tech_up.
rewrite plus_IZR.
apply Rplus_lt_compat_l.
apply archimed.
rewrite plus_IZR, Rplus_assoc.
apply Rplus_le_compat_l.
apply Rplus_le_reg_r with (-y)%R.
ring_simplify (y+1+-y)%R.
apply archimed.
Qed.

Lemma Zceil_plus: forall (n:Z) y,
  (Zceil (IZR n+y) = n + Zceil y)%Z.
Proof.
intros n y; unfold Zceil.
rewrite Ropp_plus_distr, <- Ropp_Ropp_IZR.
rewrite Zfloor_plus.
ring.
Qed.


Lemma Zeven_abs: forall z, Z.even (Z.abs z) = Z.even z.
Proof.
intros z; case (Zle_or_lt z 0); intros H1.
rewrite Z.abs_neq; try assumption.
apply Z.even_opp.
rewrite Z.abs_eq; auto with zarith.
Qed.




Lemma Zrnd_odd_plus: forall x y, (x = IZR (Zfloor x)) ->
    Z.even (Zfloor x) = true ->
   (IZR (Zrnd_odd (x+y)) = x+IZR (Zrnd_odd y))%R.
Proof.
intros x y Hx H.
unfold Zrnd_odd; rewrite Hx, Zfloor_plus.
case (Req_EM_T y (IZR (Zfloor y))); intros Hy.
rewrite Hy; repeat rewrite <- plus_IZR.
repeat rewrite Zfloor_IZR.
case (Req_EM_T _ _); intros K; easy.
case (Req_EM_T _ _); intros K.
contradict Hy.
apply Rplus_eq_reg_l with (IZR (Zfloor x)).
now rewrite K, plus_IZR.
rewrite Z.even_add, H; simpl.
case (Z.even (Zfloor y)).
now rewrite Zceil_plus, plus_IZR.
now rewrite plus_IZR.
Qed.


Section Fcore_rnd_odd.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }.

Notation format := (generic_format beta fexp).
Notation canonical := (canonical beta fexp).
Notation cexp := (cexp beta fexp).


Definition Rnd_odd_pt (x f : R) :=
  format f /\ ((f = x)%R \/
    ((Rnd_DN_pt format x f \/ Rnd_UP_pt format x f) /\
    exists g : float beta, f = F2R g /\ canonical g /\ Z.even (Fnum g) = false)).

Definition Rnd_odd (rnd : R -> R) :=
  forall x : R, Rnd_odd_pt x (rnd x).

Theorem Rnd_odd_pt_opp_inv :   forall x f : R,
  Rnd_odd_pt (-x) (-f) -> Rnd_odd_pt x f.
Proof with auto with typeclass_instances.
intros x f (H1,H2).
split.
replace f with (-(-f))%R by ring.
now apply generic_format_opp.
destruct H2.
left.
replace f with (-(-f))%R by ring.
rewrite H; ring.
right.
destruct H as (H2,(g,(Hg1,(Hg2,Hg3)))).
split.
destruct H2.
right.
replace f with (-(-f))%R by ring.
replace x with (-(-x))%R by ring.
apply Rnd_UP_pt_opp...
apply generic_format_opp.
left.
replace f with (-(-f))%R by ring.
replace x with (-(-x))%R by ring.
apply Rnd_DN_pt_opp...
apply generic_format_opp.
exists (Float beta (-Fnum g) (Fexp g)).
split.
rewrite F2R_Zopp.
replace f with (-(-f))%R by ring.
rewrite Hg1; reflexivity.
split.
now apply canonical_opp.
simpl.
now rewrite Z.even_opp.
Qed.


Theorem round_odd_opp :
  forall x,
  round beta fexp Zrnd_odd (-x) = (- round beta fexp Zrnd_odd x)%R.
Proof.
intros x; unfold round.
rewrite <- F2R_Zopp.
unfold F2R; simpl.
apply f_equal2; apply f_equal.
rewrite scaled_mantissa_opp.
generalize (scaled_mantissa beta fexp x); intros r.
unfold Zrnd_odd.
case (Req_EM_T (- r) (IZR (Zfloor (- r)))).
case (Req_EM_T r (IZR (Zfloor r))).
intros Y1 Y2.
apply eq_IZR.
now rewrite opp_IZR, <- Y1, <-Y2.
intros Y1 Y2.
absurd (r=IZR (Zfloor r)); trivial.
pattern r at 2; replace r with (-(-r))%R by ring.
rewrite Y2, <- opp_IZR.
rewrite Zfloor_IZR.
rewrite opp_IZR, <- Y2.
ring.
case (Req_EM_T r (IZR (Zfloor r))).
intros Y1 Y2.
absurd (-r=IZR (Zfloor (-r)))%R; trivial.
pattern r at 2; rewrite Y1.
rewrite <- opp_IZR, Zfloor_IZR.
now rewrite opp_IZR, <- Y1.
intros Y1 Y2.
unfold Zceil; rewrite Ropp_involutive.
replace  (Z.even (Zfloor (- r))) with (negb (Z.even (Zfloor r))).
case (Z.even (Zfloor r));  simpl; ring.
apply trans_eq with (Z.even (Zceil r)).
rewrite Zceil_floor_neq.
rewrite Z.even_add.
destruct (Z.even (Zfloor r)); reflexivity.
now apply sym_not_eq.
rewrite <- (Z.even_opp (Zfloor (- r))).
reflexivity.
apply cexp_opp.
Qed.



Theorem round_odd_pt :
  forall x,
  Rnd_odd_pt x (round beta fexp Zrnd_odd x).
Proof with auto with typeclass_instances.
cut (forall x : R, (0 < x)%R -> Rnd_odd_pt x (round beta fexp Zrnd_odd x)).
intros H x; case (Rle_or_lt 0 x).
intros H1; destruct H1.
now apply H.
rewrite <- H0.
rewrite round_0...
split.
apply generic_format_0.
now left.
intros Hx; apply Rnd_odd_pt_opp_inv.
rewrite <- round_odd_opp.
apply H.
auto with real.
(* *)
intros x Hxp.
generalize (generic_format_round beta fexp Zrnd_odd x).
set (o:=round beta fexp Zrnd_odd x).
intros Ho.
split.
assumption.
(* *)
case (Req_dec o x); intros Hx.
now left.
right.
assert (o=round beta fexp Zfloor x \/ o=round beta fexp Zceil x).
unfold o, round, F2R;simpl.
case (Zrnd_DN_or_UP Zrnd_odd  (scaled_mantissa beta fexp x))...
intros H; rewrite H; now left.
intros H; rewrite H; now right.
split.
destruct H; rewrite H.
left; apply round_DN_pt...
right; apply round_UP_pt...
(* *)
unfold o, Zrnd_odd, round.
case (Req_EM_T (scaled_mantissa beta fexp x)
     (IZR (Zfloor (scaled_mantissa beta fexp x)))).
intros T.
absurd (o=x); trivial.
apply round_generic...
unfold generic_format, F2R; simpl.
rewrite <- (scaled_mantissa_mult_bpow beta fexp) at 1.
apply f_equal2; trivial; rewrite T at 1.
apply f_equal, sym_eq, Ztrunc_floor.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
intros L.
case_eq (Z.even (Zfloor (scaled_mantissa beta fexp x))).
(* . *)
generalize (generic_format_round beta fexp Zceil x).
unfold generic_format.
set (f:=round beta fexp Zceil x).
set (ef := cexp f).
set (mf := Ztrunc (scaled_mantissa beta fexp f)).
exists (Float beta mf ef).
unfold canonical.
rewrite <- H0.
repeat split; try assumption.
apply trans_eq with (negb (Z.even (Zfloor (scaled_mantissa beta fexp x)))).
2: rewrite H1; reflexivity.
apply trans_eq with (negb (Z.even (Fnum
  (Float beta  (Zfloor (scaled_mantissa beta fexp x)) (cexp x))))).
2: reflexivity.
case (Rle_lt_or_eq_dec 0 (round beta fexp Zfloor x)).
rewrite <- round_0 with beta fexp Zfloor...
apply round_le...
now left.
intros Y.
generalize (DN_UP_parity_generic beta fexp)...
unfold DN_UP_parity_prop.
intros T; apply T with x; clear T.
unfold generic_format.
rewrite <- (scaled_mantissa_mult_bpow beta fexp x) at 1.
unfold F2R; simpl.
apply Rmult_neq_compat_r.
apply Rgt_not_eq, bpow_gt_0.
rewrite Ztrunc_floor.
assumption.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
unfold canonical.
simpl.
apply sym_eq, cexp_DN...
unfold canonical.
rewrite <- H0; reflexivity.
reflexivity.
apply trans_eq with (round beta fexp Ztrunc (round beta fexp Zceil x)).
reflexivity.
apply round_generic...
intros Y.
replace  (Fnum {| Fnum := Zfloor (scaled_mantissa beta fexp x); Fexp := cexp x |})
   with (Fnum (Float beta 0 (fexp (mag beta 0)))).
generalize (DN_UP_parity_generic beta fexp)...
unfold DN_UP_parity_prop.
intros T; apply T with x; clear T.
unfold generic_format.
rewrite <- (scaled_mantissa_mult_bpow beta fexp x) at 1.
unfold F2R; simpl.
apply Rmult_neq_compat_r.
apply Rgt_not_eq, bpow_gt_0.
rewrite Ztrunc_floor.
assumption.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
apply canonical_0.
unfold canonical.
rewrite <- H0; reflexivity.
rewrite <- Y; unfold F2R; simpl; ring.
apply trans_eq with (round beta fexp Ztrunc (round beta fexp Zceil x)).
reflexivity.
apply round_generic...
simpl.
apply eq_IZR, Rmult_eq_reg_r with (bpow (cexp x)).
unfold round, F2R in Y; simpl in Y; rewrite <- Y.
simpl; ring.
apply Rgt_not_eq, bpow_gt_0.
(* . *)
intros Y.
case (Rle_lt_or_eq_dec 0 (round beta fexp Zfloor x)).
rewrite <- round_0 with beta fexp Zfloor...
apply round_le...
now left.
intros Hrx.
set (ef := cexp x).
set (mf := Zfloor (scaled_mantissa beta fexp x)).
exists (Float beta mf ef).
unfold canonical.
repeat split; try assumption.
simpl.
apply trans_eq with (cexp (round beta fexp Zfloor x )).
apply sym_eq, cexp_DN...
reflexivity.
intros Hrx; contradict Y.
replace (Zfloor (scaled_mantissa beta fexp x)) with 0%Z.
simpl; discriminate.
apply eq_IZR, Rmult_eq_reg_r with (bpow (cexp x)).
unfold round, F2R in Hrx; simpl in Hrx; rewrite <- Hrx.
simpl; ring.
apply Rgt_not_eq, bpow_gt_0.
Qed.

Theorem Rnd_odd_pt_unique :
  forall x f1 f2 : R,
  Rnd_odd_pt x f1 -> Rnd_odd_pt x f2 ->
  f1 = f2.
Proof.
intros x f1 f2 (Ff1,H1) (Ff2,H2).
(* *)
case (generic_format_EM beta fexp x); intros L.
apply trans_eq with x.
case H1; try easy.
intros (J,_); case J; intros J'.
apply Rnd_DN_pt_idempotent with format; assumption.
apply Rnd_UP_pt_idempotent with format; assumption.
case H2; try easy.
intros (J,_); case J; intros J'; apply sym_eq.
apply Rnd_DN_pt_idempotent with format; assumption.
apply Rnd_UP_pt_idempotent with format; assumption.
(* *)
destruct H1 as [H1|(H1,H1')].
contradict L; now rewrite <- H1.
destruct H2 as [H2|(H2,H2')].
contradict L; now rewrite <- H2.
destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
apply Rnd_DN_pt_unique with format x; assumption.
destruct H1' as (ff,(K1,(K2,K3))).
destruct H2' as (gg,(L1,(L2,L3))).
absurd (true = false); try discriminate.
rewrite <- L3.
apply trans_eq with (negb (Z.even (Fnum ff))).
rewrite K3; easy.
apply sym_eq.
generalize (DN_UP_parity_generic beta fexp).
unfold DN_UP_parity_prop; intros T; apply (T x); clear T; try assumption...
rewrite <- K1; apply Rnd_DN_pt_unique with (generic_format beta fexp) x; try easy...
now apply round_DN_pt...
rewrite <- L1; apply Rnd_UP_pt_unique with (generic_format beta fexp) x; try easy...
now apply round_UP_pt...
(* *)
destruct H1' as (ff,(K1,(K2,K3))).
destruct H2' as (gg,(L1,(L2,L3))).
absurd (true = false); try discriminate.
rewrite <- K3.
apply trans_eq with (negb (Z.even (Fnum gg))).
rewrite L3; easy.
apply sym_eq.
generalize (DN_UP_parity_generic beta fexp).
unfold DN_UP_parity_prop; intros T; apply (T x); clear T; try assumption...
rewrite <- L1; apply Rnd_DN_pt_unique with (generic_format beta fexp) x; try easy...
now apply round_DN_pt...
rewrite <- K1; apply Rnd_UP_pt_unique with (generic_format beta fexp) x; try easy...
now apply round_UP_pt...
apply Rnd_UP_pt_unique with format x; assumption.
Qed.

Theorem Rnd_odd_pt_monotone :
  round_pred_monotone (Rnd_odd_pt).
Proof with auto with typeclass_instances.
intros x y f g H1 H2 Hxy.
apply Rle_trans with (round beta fexp Zrnd_odd x).
right; apply Rnd_odd_pt_unique with x; try assumption.
apply round_odd_pt.
apply Rle_trans with (round beta fexp Zrnd_odd y).
apply round_le...
right; apply Rnd_odd_pt_unique with y; try assumption.
apply round_odd_pt.
Qed.

End Fcore_rnd_odd.

Section Odd_prop_aux.

Variable beta : radix.
Hypothesis Even_beta: Z.even (radix_val beta)=true.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.
Variable fexpe : Z -> Z.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }. (* for underflow reason *)
Context { valid_expe : Valid_exp fexpe }.
Context { exists_NE_e : Exists_NE beta fexpe }. (* for defining rounding to odd *)

Hypothesis fexpe_fexp: forall e, (fexpe e <= fexp e -2)%Z.


Lemma generic_format_fexpe_fexp: forall x,
 generic_format beta fexp x ->  generic_format beta fexpe x.
Proof.
intros x Hx.
apply generic_inclusion_mag with fexp; trivial; intros Hx2.
generalize (fexpe_fexp (mag beta x)).
lia.
Qed.



Lemma exists_even_fexp_lt: forall (c:Z->Z), forall (x:R),
      (exists f:float beta, F2R f = x /\ (c (mag beta x) < Fexp f)%Z) ->
      exists f:float beta, F2R f =x /\ canonical beta c f /\ Z.even (Fnum f) = true.
Proof with auto with typeclass_instances.
intros c x (g,(Hg1,Hg2)).
exists (Float beta
     (Fnum g*Z.pow (radix_val beta) (Fexp g - c (mag beta x)))
     (c (mag beta x))).
assert (F2R (Float beta
     (Fnum g*Z.pow (radix_val beta) (Fexp g - c (mag beta x)))
     (c (mag beta x))) = x).
unfold F2R; simpl.
rewrite mult_IZR, IZR_Zpower.
rewrite Rmult_assoc, <- bpow_plus.
rewrite <- Hg1; unfold F2R.
apply f_equal, f_equal.
ring.
lia.
split; trivial.
split.
unfold canonical, cexp.
now rewrite H.
simpl.
rewrite Z.even_mul.
rewrite Z.even_pow.
rewrite Even_beta.
apply Bool.orb_true_intro.
now right.
lia.
Qed.


Variable choice:Z->bool.
Variable x:R.


Variable d u: float beta.
Hypothesis Hd: Rnd_DN_pt (generic_format beta fexp) x (F2R d).
Hypothesis Cd: canonical beta fexp d.
Hypothesis Hu: Rnd_UP_pt (generic_format beta fexp) x (F2R u).
Hypothesis Cu: canonical beta fexp u.

Hypothesis xPos: (0 < x)%R.


Let m:= ((F2R d+F2R u)/2)%R.


Lemma d_eq: F2R d= round beta fexp Zfloor x.
Proof with auto with typeclass_instances.
apply Rnd_DN_pt_unique with (generic_format beta fexp) x...
apply round_DN_pt...
Qed.


Lemma u_eq: F2R u= round beta fexp Zceil x.
Proof with auto with typeclass_instances.
apply Rnd_UP_pt_unique with (generic_format beta fexp) x...
apply round_UP_pt...
Qed.


Lemma d_ge_0: (0 <= F2R d)%R.
Proof with auto with typeclass_instances.
rewrite d_eq; apply round_ge_generic...
apply generic_format_0.
now left.
Qed.



Lemma mag_d:  (0< F2R d)%R ->
    (mag beta (F2R d) = mag beta x :>Z).
Proof with auto with typeclass_instances.
intros Y.
rewrite d_eq; apply mag_DN...
now rewrite <- d_eq.
Qed.


Lemma Fexp_d: (0 < F2R d)%R -> Fexp d =fexp (mag beta x).
Proof with auto with typeclass_instances.
intros Y.
now rewrite Cd, <- mag_d.
Qed.



Lemma format_bpow_x: (0 < F2R d)%R
    -> generic_format beta fexp  (bpow (mag beta x)).
Proof with auto with typeclass_instances.
intros Y.
apply generic_format_bpow.
apply valid_exp.
rewrite <- Fexp_d; trivial.
apply Z.lt_le_trans with  (mag beta (F2R d))%Z.
rewrite Cd; apply mag_generic_gt...
now apply Rgt_not_eq.
apply Hd.
apply mag_le; trivial.
apply Hd.
Qed.


Lemma format_bpow_d: (0 < F2R d)%R ->
  generic_format beta fexp (bpow (mag beta (F2R d))).
Proof with auto with typeclass_instances.
intros Y; apply generic_format_bpow.
apply valid_exp.
apply mag_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonical.
Qed.


Lemma d_le_m: (F2R d <= m)%R.
Proof.
assert (F2R d <= F2R u)%R.
  apply Rle_trans with x.
  apply Hd.
  apply Hu.
unfold m.
lra.
Qed.

Lemma m_le_u: (m <= F2R u)%R.
Proof.
assert (F2R d <= F2R u)%R.
  apply Rle_trans with x.
  apply Hd.
  apply Hu.
unfold m.
lra.
Qed.

Lemma mag_m: (0 < F2R d)%R -> (mag beta m =mag beta (F2R d) :>Z).
Proof with auto with typeclass_instances.
intros dPos; apply mag_unique_pos.
split.
apply Rle_trans with (F2R d).
destruct (mag beta (F2R d)) as (e,He).
simpl.
rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
apply d_le_m.
case m_le_u; intros H.
apply Rlt_le_trans with (1:=H).
rewrite u_eq.
apply round_le_generic...
apply generic_format_bpow.
apply valid_exp.
apply mag_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonical.
case (Rle_or_lt x (bpow (mag beta (F2R d)))); trivial; intros Z.
absurd ((bpow (mag beta (F2R d)) <= (F2R d)))%R.
apply Rlt_not_le.
destruct  (mag beta (F2R d)) as (e,He).
simpl in *; rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
apply Rle_trans with (round beta fexp Zfloor x).
2: right; apply sym_eq, d_eq.
apply round_ge_generic...
apply generic_format_bpow.
apply valid_exp.
apply mag_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonical.
now left.
replace m with (F2R d).
destruct (mag beta (F2R d)) as (e,He).
simpl in *; rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
unfold m in H |- *.
lra.
Qed.


Lemma mag_m_0: (0 = F2R d)%R
    -> (mag beta m =mag beta (F2R u)-1:>Z)%Z.
Proof with auto with typeclass_instances.
intros Y.
apply mag_unique_pos.
unfold m; rewrite <- Y, Rplus_0_l.
rewrite u_eq.
destruct (mag beta x) as (e,He).
rewrite Rabs_pos_eq in He by now apply Rlt_le.
rewrite round_UP_small_pos with (ex:=e).
rewrite mag_bpow.
ring_simplify (fexp e + 1 - 1)%Z.
split.
unfold Zminus; rewrite bpow_plus.
unfold Rdiv; apply Rmult_le_compat_l.
apply bpow_ge_0.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r; apply Rinv_le.
exact Rlt_0_2.
apply IZR_le.
specialize (radix_gt_1 beta).
lia.
apply Rlt_le_trans with (bpow (fexp e)*1)%R.
2: right; ring.
unfold Rdiv; apply Rmult_lt_compat_l.
apply bpow_gt_0.
lra.
now apply He, Rgt_not_eq.
apply exp_small_round_0_pos with beta (Zfloor) x...
now apply He, Rgt_not_eq.
now rewrite <- d_eq, Y.
Qed.





Lemma u'_eq:  (0 < F2R d)%R -> exists f:float beta, F2R f = F2R u /\ (Fexp f = Fexp d)%Z.
Proof with auto with typeclass_instances.
intros Y.
rewrite u_eq; unfold round.
eexists; repeat split.
simpl; now rewrite Fexp_d.
Qed.


Lemma m_eq :
  (0 < F2R d)%R ->
  exists f:float beta,
  F2R f = m /\ (Fexp f = fexp (mag beta x) - 1)%Z.
Proof with auto with typeclass_instances.
intros Y.
specialize (Zeven_ex (radix_val beta)); rewrite Even_beta.
intros (b, Hb); rewrite Zplus_0_r in Hb.
destruct u'_eq as (u', (Hu'1,Hu'2)); trivial.
exists (Fmult (Float beta b (-1)) (Fplus d u'))%R.
split.
rewrite F2R_mult, F2R_plus, Hu'1.
unfold m; rewrite Rmult_comm.
unfold Rdiv; apply f_equal.
unfold F2R; simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Hb, mult_IZR.
simpl; field.
apply Rgt_not_eq, Rmult_lt_reg_l with (1 := Rlt_0_2).
rewrite Rmult_0_r, <- (mult_IZR 2), <-Hb.
apply radix_pos.
apply trans_eq with (-1+Fexp (Fplus d u'))%Z.
unfold Fmult.
destruct  (Fplus d u'); reflexivity.
rewrite Zplus_comm; unfold Zminus; apply f_equal2.
2: reflexivity.
rewrite Fexp_Fplus.
rewrite Z.min_l.
now rewrite Fexp_d.
rewrite Hu'2; lia.
Qed.

Lemma m_eq_0: (0 = F2R d)%R ->  exists f:float beta,
   F2R f = m /\ (Fexp f = fexp (mag beta (F2R u)) -1)%Z.
Proof with auto with typeclass_instances.
intros Y.
specialize (Zeven_ex (radix_val beta)); rewrite Even_beta.
intros (b, Hb); rewrite Zplus_0_r in Hb.
exists (Fmult (Float beta b (-1)) u)%R.
split.
rewrite F2R_mult; unfold m; rewrite <- Y, Rplus_0_l.
rewrite Rmult_comm.
unfold Rdiv; apply f_equal.
unfold F2R; simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Hb, mult_IZR.
simpl; field.
apply Rgt_not_eq, Rmult_lt_reg_l with (1 := Rlt_0_2).
rewrite Rmult_0_r, <- (mult_IZR 2), <-Hb.
apply radix_pos.
apply trans_eq with (-1+Fexp u)%Z.
unfold Fmult.
destruct u; reflexivity.
rewrite Zplus_comm, Cu; unfold Zminus; now apply f_equal2.
Qed.

Lemma fexp_m_eq_0:  (0 = F2R d)%R ->
  (fexp (mag beta (F2R u)-1) < fexp (mag beta (F2R u))+1)%Z.
Proof with auto with typeclass_instances.
intros Y.
assert ((fexp (mag beta (F2R u) - 1) <= fexp (mag beta (F2R u))))%Z.
2: lia.
destruct (mag beta x) as (e,He).
rewrite Rabs_right in He.
2: now left.
assert (e <= fexp e)%Z.
apply exp_small_round_0_pos with beta (Zfloor) x...
now apply He, Rgt_not_eq.
now rewrite <- d_eq, Y.
rewrite u_eq, round_UP_small_pos with (ex:=e); trivial.
2: now apply He, Rgt_not_eq.
rewrite mag_bpow.
ring_simplify (fexp e + 1 - 1)%Z.
replace (fexp (fexp e)) with (fexp e).
case exists_NE_; intros V.
contradict V; rewrite Even_beta; discriminate.
rewrite (proj2 (V e)); lia.
apply sym_eq, valid_exp; lia.
Qed.

Lemma Fm:  generic_format beta fexpe m.
Proof.
case (d_ge_0); intros Y.
(* *)
destruct m_eq as (g,(Hg1,Hg2)); trivial.
apply generic_format_F2R' with g.
now apply sym_eq.
intros H; unfold cexp; rewrite Hg2.
rewrite mag_m; trivial.
rewrite <- Fexp_d; trivial.
rewrite Cd.
unfold cexp.
generalize (fexpe_fexp (mag beta (F2R d))).
lia.
(* *)
destruct m_eq_0 as (g,(Hg1,Hg2)); trivial.
apply generic_format_F2R' with g.
assumption.
intros H; unfold cexp; rewrite Hg2.
rewrite mag_m_0; try assumption.
apply Z.le_trans with (1:=fexpe_fexp _).
generalize (fexp_m_eq_0 Y).
lia.
Qed.



Lemma Zm:
   exists g : float beta, F2R g = m /\ canonical beta fexpe g /\ Z.even (Fnum g) = true.
Proof with auto with typeclass_instances.
case (d_ge_0); intros Y.
(* *)
destruct m_eq as (g,(Hg1,Hg2)); trivial.
apply exists_even_fexp_lt.
exists g; split; trivial.
rewrite Hg2.
rewrite mag_m; trivial.
rewrite <- Fexp_d; trivial.
rewrite Cd.
unfold cexp.
generalize (fexpe_fexp  (mag beta (F2R d))).
lia.
(* *)
destruct m_eq_0 as (g,(Hg1,Hg2)); trivial.
apply exists_even_fexp_lt.
exists g; split; trivial.
rewrite Hg2.
rewrite mag_m_0; trivial.
apply Z.le_lt_trans with (1:=fexpe_fexp _).
generalize (fexp_m_eq_0 Y).
lia.
Qed.


Lemma DN_odd_d_aux :
  forall z, (F2R d <= z < F2R u)%R ->
  Rnd_DN_pt (generic_format beta fexp) z (F2R d).
Proof with auto with typeclass_instances.
intros z Hz1.
replace (F2R d) with (round beta fexp Zfloor z).
apply round_DN_pt...
case (Rnd_DN_UP_pt_split _ _ _ _ Hd Hu (round beta fexp Zfloor z)).
apply generic_format_round...
intros Y; apply Rle_antisym; trivial.
apply round_DN_pt...
apply Hd.
apply Hz1.
intros Y ; elim (Rlt_irrefl z).
apply Rlt_le_trans with (1:=proj2 Hz1), Rle_trans with (1:=Y).
apply round_DN_pt...
Qed.

Lemma UP_odd_d_aux :
  forall z, (F2R d < z <= F2R u)%R ->
  Rnd_UP_pt (generic_format beta fexp) z (F2R u).
Proof with auto with typeclass_instances.
intros z Hz1.
replace (F2R u) with (round beta fexp Zceil z).
apply round_UP_pt...
case (Rnd_DN_UP_pt_split _ _ _ _ Hd Hu (round beta fexp Zceil z)).
apply generic_format_round...
intros Y ; elim (Rlt_irrefl z).
apply Rle_lt_trans with (2:=proj1 Hz1), Rle_trans with (2:=Y).
apply round_UP_pt...
intros Y; apply Rle_antisym; trivial.
apply round_UP_pt...
apply Hu.
apply Hz1.
Qed.


Lemma round_N_odd_pos :
  round beta fexp (Znearest choice) (round beta fexpe Zrnd_odd x) =
               round beta fexp (Znearest choice) x.
Proof with auto with typeclass_instances.
set (o:=round beta fexpe Zrnd_odd x).
case (generic_format_EM beta fexp x); intros Hx.
replace o with x; trivial.
unfold o; apply sym_eq, round_generic...
now apply generic_format_fexpe_fexp.
assert (K1:(F2R d <= o)%R).
apply round_ge_generic...
apply generic_format_fexpe_fexp, Hd.
apply Hd.
assert (K2:(o <= F2R u)%R).
apply round_le_generic...
apply generic_format_fexpe_fexp, Hu.
apply Hu.
assert (P:(x <> m -> o=m -> (forall P:Prop, P))).
intros Y1 Y2.
assert (H:(Rnd_odd_pt beta fexpe x o)).
apply round_odd_pt...
destruct H as (_,H); destruct H.
absurd (x=m)%R; try trivial.
now rewrite <- Y2, H.
destruct H as (_,(k,(Hk1,(Hk2,Hk3)))).
destruct Zm as (k',(Hk'1,(Hk'2,Hk'3))).
absurd (true=false).
discriminate.
rewrite <- Hk3, <- Hk'3.
apply f_equal, f_equal.
apply canonical_unique with fexpe...
now rewrite Hk'1, <- Y2.
assert (generic_format beta fexp o -> (forall P:Prop, P)).
intros Y.
assert (H:(Rnd_odd_pt beta fexpe x o)).
apply round_odd_pt...
destruct H as (_,H); destruct H.
absurd (generic_format beta fexp x); trivial.
now rewrite <- H.
destruct H as (_,(k,(Hk1,(Hk2,Hk3)))).
destruct (exists_even_fexp_lt fexpe o) as (k',(Hk'1,(Hk'2,Hk'3))).
eexists; split.
apply sym_eq, Y.
simpl; unfold cexp.
apply Z.le_lt_trans with (1:=fexpe_fexp _).
lia.
absurd (true=false).
discriminate.
rewrite <- Hk3, <- Hk'3.
apply f_equal, f_equal.
apply canonical_unique with fexpe...
now rewrite Hk'1, <- Hk1.
case K1; clear K1; intros K1.
2: apply H; rewrite <- K1; apply Hd.
case K2; clear K2; intros K2.
2: apply H; rewrite K2; apply Hu.
case (Rle_or_lt  x m); intros Y;[destruct Y|idtac].
(* . *)
apply trans_eq with (F2R d).
apply round_N_eq_DN_pt with (F2R u)...
apply DN_odd_d_aux; split; try left; assumption.
apply UP_odd_d_aux; split; try left; assumption.
assert (o <= (F2R d + F2R u) / 2)%R.
apply round_le_generic...
apply Fm.
now left.
destruct H1; trivial.
apply P.
now apply Rlt_not_eq.
trivial.
apply sym_eq, round_N_eq_DN_pt with (F2R u)...
(* . *)
replace o with x.
reflexivity.
apply sym_eq, round_generic...
rewrite H0; apply Fm.
(* . *)
apply trans_eq with (F2R u).
apply round_N_eq_UP_pt with (F2R d)...
apply DN_odd_d_aux; split; try left; assumption.
apply UP_odd_d_aux; split; try left; assumption.
assert ((F2R d + F2R u) / 2 <= o)%R.
apply round_ge_generic...
apply Fm.
now left.
destruct H0; trivial.
apply P.
now apply Rgt_not_eq.
rewrite <- H0; trivial.
apply sym_eq, round_N_eq_UP_pt with (F2R d)...
Qed.


End Odd_prop_aux.

Section Odd_prop.

Variable beta : radix.
Hypothesis Even_beta: Z.even (radix_val beta)=true.

Variable fexp : Z -> Z.
Variable fexpe : Z -> Z.
Variable choice:Z->bool.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }. (* for underflow reason *)
Context { valid_expe : Valid_exp fexpe }.
Context { exists_NE_e : Exists_NE beta fexpe }. (* for defining rounding to odd *)

Hypothesis fexpe_fexp: forall e, (fexpe e <= fexp e -2)%Z.

Theorem round_N_odd :
  forall x,
  round beta fexp (Znearest choice) (round beta fexpe Zrnd_odd x) =
               round beta fexp (Znearest choice) x.
Proof with auto with typeclass_instances.
intros x.
case (total_order_T x 0); intros H; [case H; clear H; intros H | idtac].
rewrite <- (Ropp_involutive x).
rewrite round_odd_opp.
rewrite 2!round_N_opp.
apply f_equal.
destruct (canonical_generic_format beta fexp (round beta fexp Zfloor (-x))) as (d,(Hd1,Hd2)).
apply generic_format_round...
destruct (canonical_generic_format beta fexp (round beta fexp Zceil (-x))) as (u,(Hu1,Hu2)).
apply generic_format_round...
apply round_N_odd_pos with d u...
rewrite <- Hd1; apply round_DN_pt...
rewrite <- Hu1; apply round_UP_pt...
auto with real.
(* . *)
rewrite H; repeat rewrite round_0...
(* . *)
destruct (canonical_generic_format beta fexp (round beta fexp Zfloor x)) as (d,(Hd1,Hd2)).
apply generic_format_round...
destruct (canonical_generic_format beta fexp (round beta fexp Zceil x)) as (u,(Hu1,Hu2)).
apply generic_format_round...
apply round_N_odd_pos with d u...
rewrite <- Hd1; apply round_DN_pt...
rewrite <- Hu1; apply round_UP_pt...
Qed.

End Odd_prop.


Section Odd_propbis.

Variable beta : radix.
Hypothesis Even_beta: Z.even (radix_val beta)=true.

Variable emin prec:Z.
Variable choice:Z->bool.

Hypothesis prec_gt_1: (1 < prec)%Z.


Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation cexp_flt := (cexp beta (FLT_exp emin prec)).
Notation fexpe k := (FLT_exp (emin-k) (prec+k)).



Lemma Zrnd_odd_plus': forall x y,
  (exists n:Z, exists e:Z, (x = IZR n*bpow beta e)%R /\ (1 <= e)%Z) ->
   (IZR (Zrnd_odd (x+y)) = x+IZR (Zrnd_odd y))%R.
Proof.
intros x y (n,(e,(H1,H2))).
apply Zrnd_odd_plus.
rewrite H1.
rewrite <- IZR_Zpower.
2: auto with zarith.
now rewrite <- mult_IZR, Zfloor_IZR.
rewrite H1, <- IZR_Zpower.
2: auto with zarith.
rewrite <- mult_IZR, Zfloor_IZR.
rewrite Z.even_mul.
rewrite Z.even_pow.
2: auto with zarith.
rewrite Even_beta.
apply Bool.orb_true_iff; now right.
Qed.



Theorem mag_round_odd: forall (x:R),
 (emin < mag beta x)%Z ->
  (mag_val beta _ (mag beta (round beta (FLT_exp emin prec) Zrnd_odd x))
      = mag_val beta x (mag beta x))%Z.
Proof with auto with typeclass_instances.
intros x.
assert (T:Prec_gt_0 prec).
unfold Prec_gt_0; auto with zarith.
case (Req_dec x 0); intros Zx.
intros _; rewrite Zx, round_0...
destruct (mag beta x) as (e,He); simpl; intros H.
apply mag_unique; split.
apply abs_round_ge_generic...
apply generic_format_FLT_bpow...
now apply Z.lt_le_pred.
now apply He.
assert (V:
  (Rabs (round beta (FLT_exp emin prec) Zrnd_odd x) <= bpow beta e)%R).
apply abs_round_le_generic...
apply generic_format_FLT_bpow...
now apply Zlt_le_weak.
left; now apply He.
case V; try easy; intros K.
assert (H0:Rnd_odd_pt beta (FLT_exp emin prec) x (round beta (FLT_exp emin prec) Zrnd_odd x)).
apply round_odd_pt...
destruct H0 as (_,HH); destruct HH as [H0|(H0,(g,(Hg1,(Hg2,Hg3))))].
absurd (Rabs x < bpow beta e)%R.
apply Rle_not_lt; right.
now rewrite <- H0,K.
now apply He.
pose (gg:=Float beta (Zpower beta (e-FLT_exp emin prec (e+1))) (FLT_exp emin prec (e+1))).
assert (Y1: F2R gg = bpow beta e).
unfold F2R; simpl.
rewrite IZR_Zpower.
rewrite <- bpow_plus.
f_equal; ring.
assert (FLT_exp emin prec (e+1) <= e)%Z; [idtac|auto with zarith].
unfold FLT_exp.
apply Z.max_case_strong; auto with zarith.
assert (Y2: canonical beta (FLT_exp emin prec) gg).
unfold canonical; rewrite Y1; unfold gg; simpl.
unfold cexp; now rewrite mag_bpow.
assert (Y3: Fnum gg = Z.abs (Fnum g)).
apply trans_eq with (Fnum (Fabs g)).
2: destruct g; unfold Fabs; now simpl.
f_equal.
apply canonical_unique with (FLT_exp emin prec); try assumption.
destruct g; unfold Fabs; apply canonical_abs; easy.
now rewrite Y1, F2R_abs, <- Hg1,K.
assert (Y4: Z.even (Fnum gg) = true).
unfold gg; simpl.
rewrite Z.even_pow; try assumption.
assert (FLT_exp emin prec (e+1) < e)%Z; [idtac|auto with zarith].
unfold FLT_exp.
apply Z.max_case_strong; auto with zarith.
absurd (true = false).
discriminate.
rewrite <- Hg3.
rewrite <- Zeven_abs.
now rewrite <- Y3.
Qed.

Theorem fexp_round_odd: forall (x:R),
  (cexp_flt (round beta (FLT_exp emin prec) Zrnd_odd x)
      = cexp_flt x)%Z.
Proof with auto with typeclass_instances.
intros x.
assert (G0:Valid_exp (FLT_exp emin prec)).
apply FLT_exp_valid; unfold Prec_gt_0; auto with zarith.
case (Req_dec x 0); intros Zx.
rewrite Zx, round_0...
case (Zle_or_lt (mag beta x) emin).
unfold cexp; destruct (mag beta x) as (e,He); simpl.
intros H; unfold FLT_exp at 4.
rewrite Z.max_r.
2: auto with zarith.
apply Z.max_r.
assert (G: Rabs (round beta (FLT_exp emin prec) Zrnd_odd x) = bpow beta emin).
assert (G1: (Rabs (round beta (FLT_exp emin prec) Zrnd_odd x) <= bpow beta emin)%R).
apply abs_round_le_generic...
apply generic_format_bpow'...
unfold FLT_exp; rewrite Z.max_r; auto with zarith.
left; apply Rlt_le_trans with (bpow beta e).
now apply He.
now apply bpow_le.
assert (G2: (0 <= Rabs (round beta (FLT_exp emin prec) Zrnd_odd x))%R).
apply Rabs_pos.
assert (G3: (Rabs (round beta (FLT_exp emin prec) Zrnd_odd x) <> 0)%R).
assert (H0:Rnd_odd_pt beta (FLT_exp emin prec) x
    (round beta (FLT_exp emin prec) Zrnd_odd x)).
apply round_odd_pt...
destruct H0 as (_,H0); destruct H0 as [H0|(_,(g,(Hg1,(Hg2,Hg3))))].
apply Rgt_not_eq; rewrite H0.
apply Rlt_le_trans with (bpow beta (e-1)).
apply bpow_gt_0.
now apply He.
rewrite Hg1; intros K.
contradict Hg3.
replace (Fnum g) with 0%Z.
easy.
case (Z.eq_dec (Fnum g) Z0); intros W; try easy.
contradict K.
apply Rabs_no_R0.
now apply F2R_neq_0.
apply Rle_antisym; try assumption.
apply Rle_trans with (succ beta (FLT_exp emin prec) 0).
right; rewrite succ_0.
rewrite ulp_FLT_small; try easy.
unfold Prec_gt_0; auto with zarith.
rewrite Rabs_R0; apply bpow_gt_0.
apply succ_le_lt...
apply generic_format_0.
apply generic_format_abs; apply generic_format_round...
case G2; [easy|intros; now contradict G3].
rewrite <- mag_abs.
rewrite G, mag_bpow; auto with zarith.
intros H; unfold cexp.
now rewrite mag_round_odd.
Qed.




End Odd_propbis.



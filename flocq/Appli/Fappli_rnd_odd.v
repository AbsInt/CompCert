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

(** * Rounding to odd and its properties, including the equivalence
      between rnd_NE and double rounding with rnd_odd and then rnd_NE *)

Require Import Reals Psatz.
Require Import Fcore.
Require Import Fcalc_ops.

Definition Zrnd_odd x :=  match Req_EM_T x (Z2R (Zfloor x))  with
  | left _   => Zfloor x
  | right _  => match (Zeven (Zfloor x)) with
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
apply Zle_trans with (Zfloor y).
now apply Zfloor_le.
unfold Zrnd_odd; destruct (Req_EM_T  y (Z2R (Zfloor y))).
now apply Zle_refl.
case (Zeven (Zfloor y)).
apply le_Z2R.
apply Rle_trans with y.
apply Zfloor_lb.
apply Zceil_ub.
now apply Zle_refl.
unfold Zrnd_odd at 1.
(* . *)
destruct (Req_EM_T  x (Z2R (Zfloor x))) as [Hx|Hx].
(* .. *)
apply H.
(* .. *)
case_eq (Zeven (Zfloor x)); intros Hx2.
2: apply H.
unfold Zrnd_odd; destruct (Req_EM_T  y (Z2R (Zfloor y))) as [Hy|Hy].
apply Zceil_glb.
now rewrite <- Hy.
case_eq (Zeven (Zfloor y)); intros Hy2.
now apply Zceil_le.
apply Zceil_glb.
assert (H0:(Zfloor x <= Zfloor y)%Z) by now apply Zfloor_le.
case (Zle_lt_or_eq _ _  H0); intros H1.
apply Rle_trans with (1:=Zceil_ub _).
rewrite Zceil_floor_neq.
apply Z2R_le; omega.
now apply sym_not_eq.
contradict Hy2.
rewrite <- H1, Hx2; discriminate.
(* . *)
intros n; unfold Zrnd_odd.
rewrite Zfloor_Z2R, Zceil_Z2R.
destruct (Req_EM_T  (Z2R n) (Z2R n)); trivial.
case (Zeven n); trivial.
Qed.



Lemma Zrnd_odd_Zodd: forall x, x <> (Z2R (Zfloor x)) ->
  (Zeven (Zrnd_odd x)) = false.
Proof.
intros x Hx; unfold Zrnd_odd.
destruct (Req_EM_T  x (Z2R (Zfloor x))) as [H|H].
now contradict H.
case_eq (Zeven (Zfloor x)).
(* difficult case *)
intros H'.
rewrite Zceil_floor_neq.
rewrite Zeven_plus, H'.
reflexivity.
now apply sym_not_eq.
trivial.
Qed.




Section Fcore_rnd_odd.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }.

Notation format := (generic_format beta fexp).
Notation canonic := (canonic beta fexp).
Notation cexp := (canonic_exp beta fexp).


Definition Rnd_odd_pt (x f : R) :=
  format f /\ ((f = x)%R \/
    ((Rnd_DN_pt format x f \/ Rnd_UP_pt format x f) /\
    exists g : float beta, f = F2R g /\ canonic g /\ Zeven (Fnum g) = false)).

Definition Rnd_odd (rnd : R -> R) :=
  forall x : R, Rnd_odd_pt x (rnd x).


Theorem Rnd_odd_pt_sym :   forall x f : R,
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
apply Rnd_DN_UP_pt_sym...
apply generic_format_opp.
left.
replace f with (-(-f))%R by ring.
replace x with (-(-x))%R by ring.
apply Rnd_UP_DN_pt_sym...
apply generic_format_opp.
exists (Float beta (-Fnum g) (Fexp g)).
split.
rewrite F2R_Zopp.
replace f with (-(-f))%R by ring.
rewrite Hg1; reflexivity.
split.
now apply canonic_opp.
simpl.
now rewrite Zeven_opp.
Qed.


Theorem round_odd_opp :
  forall x,
  (round beta fexp Zrnd_odd  (-x) = (- round beta fexp Zrnd_odd x))%R.
Proof.
intros x; unfold round.
rewrite <- F2R_Zopp.
unfold F2R; simpl.
apply f_equal2; apply f_equal.
rewrite scaled_mantissa_opp.
generalize (scaled_mantissa beta fexp x); intros r.
unfold Zrnd_odd.
case (Req_EM_T (- r) (Z2R (Zfloor (- r)))).
case (Req_EM_T r (Z2R (Zfloor r))).
intros Y1 Y2.
apply eq_Z2R.
now rewrite Z2R_opp, <- Y1, <-Y2.
intros Y1 Y2.
absurd (r=Z2R (Zfloor r)); trivial.
pattern r at 2; replace r with (-(-r))%R by ring.
rewrite Y2, <- Z2R_opp.
rewrite Zfloor_Z2R.
rewrite Z2R_opp, <- Y2.
ring.
case (Req_EM_T r (Z2R (Zfloor r))).
intros Y1 Y2.
absurd (-r=Z2R (Zfloor (-r)))%R; trivial.
pattern r at 2; rewrite Y1.
rewrite <- Z2R_opp, Zfloor_Z2R.
now rewrite Z2R_opp, <- Y1.
intros Y1 Y2.
unfold Zceil; rewrite Ropp_involutive.
replace  (Zeven (Zfloor (- r))) with (negb (Zeven (Zfloor r))).
case (Zeven (Zfloor r));  simpl; ring.
apply trans_eq with (Zeven (Zceil r)).
rewrite Zceil_floor_neq.
rewrite Zeven_plus.
destruct (Zeven (Zfloor r)); reflexivity.
now apply sym_not_eq.
rewrite <- (Zeven_opp (Zfloor (- r))).
reflexivity.
apply canonic_exp_opp.
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
intros Hx; apply Rnd_odd_pt_sym.
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
     (Z2R (Zfloor (scaled_mantissa beta fexp x)))).
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
case_eq (Zeven (Zfloor (scaled_mantissa beta fexp x))).
(* . *)
generalize (generic_format_round beta fexp Zceil x).
unfold generic_format.
set (f:=round beta fexp Zceil x).
set (ef := canonic_exp beta fexp f).
set (mf := Ztrunc (scaled_mantissa beta fexp f)).
exists (Float beta mf ef).
unfold Fcore_generic_fmt.canonic.
rewrite <- H0.
repeat split; try assumption.
apply trans_eq with (negb (Zeven (Zfloor (scaled_mantissa beta fexp x)))).
2: rewrite H1; reflexivity.
apply trans_eq with (negb (Zeven (Fnum
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
unfold Fcore_generic_fmt.canonic.
simpl.
apply sym_eq, canonic_exp_DN...
unfold Fcore_generic_fmt.canonic.
rewrite <- H0; reflexivity.
reflexivity.
apply trans_eq with (round beta fexp Ztrunc (round beta fexp Zceil x)).
reflexivity.
apply round_generic...
intros Y.
replace  (Fnum {| Fnum := Zfloor (scaled_mantissa beta fexp x); Fexp := cexp x |})
   with (Fnum (Float beta 0 (fexp (ln_beta beta 0)))).
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
apply canonic_0.
unfold Fcore_generic_fmt.canonic.
rewrite <- H0; reflexivity.
rewrite <- Y; unfold F2R; simpl; ring.
apply trans_eq with (round beta fexp Ztrunc (round beta fexp Zceil x)).
reflexivity.
apply round_generic...
simpl.
apply eq_Z2R, Rmult_eq_reg_r with (bpow (cexp x)).
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
set (ef := canonic_exp beta fexp x).
set (mf := Zfloor (scaled_mantissa beta fexp x)).
exists (Float beta mf ef).
unfold Fcore_generic_fmt.canonic.
repeat split; try assumption.
simpl.
apply trans_eq with (cexp (round beta fexp Zfloor x )).
apply sym_eq, canonic_exp_DN...
reflexivity.
intros Hrx; contradict Y.
replace (Zfloor (scaled_mantissa beta fexp x)) with 0%Z.
simpl; discriminate.
apply eq_Z2R, Rmult_eq_reg_r with (bpow (cexp x)).
unfold round, F2R in Hrx; simpl in Hrx; rewrite <- Hrx.
simpl; ring.
apply Rgt_not_eq, bpow_gt_0.
Qed.



Theorem Rnd_odd_pt_unicity :
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
apply Rnd_DN_pt_unicity with format x; assumption.
destruct H1' as (ff,(K1,(K2,K3))).
destruct H2' as (gg,(L1,(L2,L3))).
absurd (true = false); try discriminate.
rewrite <- L3.
apply trans_eq with (negb (Zeven (Fnum ff))).
rewrite K3; easy.
apply sym_eq.
generalize (DN_UP_parity_generic beta fexp).
unfold DN_UP_parity_prop; intros T; apply (T x); clear T; try assumption...
rewrite <- K1; apply Rnd_DN_pt_unicity with (generic_format beta fexp) x; try easy...
now apply round_DN_pt...
rewrite <- L1; apply Rnd_UP_pt_unicity with (generic_format beta fexp) x; try easy...
now apply round_UP_pt...
(* *)
destruct H1' as (ff,(K1,(K2,K3))).
destruct H2' as (gg,(L1,(L2,L3))).
absurd (true = false); try discriminate.
rewrite <- K3.
apply trans_eq with (negb (Zeven (Fnum gg))).
rewrite L3; easy.
apply sym_eq.
generalize (DN_UP_parity_generic beta fexp).
unfold DN_UP_parity_prop; intros T; apply (T x); clear T; try assumption...
rewrite <- L1; apply Rnd_DN_pt_unicity with (generic_format beta fexp) x; try easy...
now apply round_DN_pt...
rewrite <- K1; apply Rnd_UP_pt_unicity with (generic_format beta fexp) x; try easy...
now apply round_UP_pt...
apply Rnd_UP_pt_unicity with format x; assumption.
Qed.



Theorem Rnd_odd_pt_monotone :
  round_pred_monotone (Rnd_odd_pt).
Proof with auto with typeclass_instances.
intros x y f g H1 H2 Hxy.
apply Rle_trans with (round beta fexp Zrnd_odd x).
right; apply Rnd_odd_pt_unicity with x; try assumption.
apply round_odd_pt.
apply Rle_trans with (round beta fexp Zrnd_odd y).
apply round_le...
right; apply Rnd_odd_pt_unicity with y; try assumption.
apply round_odd_pt.
Qed.




End Fcore_rnd_odd.

Section Odd_prop_aux.

Variable beta : radix.
Hypothesis Even_beta: Zeven (radix_val beta)=true.

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
apply generic_inclusion_ln_beta with fexp; trivial; intros Hx2.
generalize (fexpe_fexp (ln_beta beta x)).
omega.
Qed.



Lemma exists_even_fexp_lt: forall (c:Z->Z), forall (x:R),
      (exists f:float beta, F2R f = x /\ (c (ln_beta beta x) < Fexp f)%Z) ->
      exists f:float beta, F2R f =x /\ canonic beta c f /\ Zeven (Fnum f) = true.
Proof with auto with typeclass_instances.
intros c x (g,(Hg1,Hg2)).
exists (Float beta
     (Fnum g*Z.pow (radix_val beta) (Fexp g - c (ln_beta beta x)))
     (c (ln_beta beta x))).
assert (F2R (Float beta
     (Fnum g*Z.pow (radix_val beta) (Fexp g - c (ln_beta beta x)))
     (c (ln_beta beta x))) = x).
unfold F2R; simpl.
rewrite Z2R_mult, Z2R_Zpower.
rewrite Rmult_assoc, <- bpow_plus.
rewrite <- Hg1; unfold F2R.
apply f_equal, f_equal.
ring.
omega.
split; trivial.
split.
unfold canonic, canonic_exp.
now rewrite H.
simpl.
rewrite Zeven_mult.
rewrite Zeven_Zpower.
rewrite Even_beta.
apply Bool.orb_true_intro.
now right.
omega.
Qed.


Variable choice:Z->bool.
Variable x:R.


Variable d u: float beta.
Hypothesis Hd: Rnd_DN_pt (generic_format beta fexp) x (F2R d).
Hypothesis Cd: canonic beta fexp d.
Hypothesis Hu: Rnd_UP_pt (generic_format beta fexp) x (F2R u).
Hypothesis Cu: canonic beta fexp u.

Hypothesis xPos: (0 < x)%R.


Let m:= ((F2R d+F2R u)/2)%R.


Lemma d_eq: F2R d= round beta fexp Zfloor x.
Proof with auto with typeclass_instances.
apply Rnd_DN_pt_unicity with (generic_format beta fexp) x...
apply round_DN_pt...
Qed.


Lemma u_eq: F2R u= round beta fexp Zceil x.
Proof with auto with typeclass_instances.
apply Rnd_UP_pt_unicity with (generic_format beta fexp) x...
apply round_UP_pt...
Qed.


Lemma d_ge_0: (0 <= F2R d)%R.
Proof with auto with typeclass_instances.
rewrite d_eq; apply round_ge_generic...
apply generic_format_0.
now left.
Qed.



Lemma ln_beta_d:  (0< F2R d)%R ->
    (ln_beta beta (F2R d) = ln_beta beta x :>Z).
Proof with auto with typeclass_instances.
intros Y.
rewrite d_eq; apply ln_beta_DN...
now rewrite <- d_eq.
Qed.


Lemma Fexp_d: (0 < F2R d)%R -> Fexp d =fexp (ln_beta beta x).
Proof with auto with typeclass_instances.
intros Y.
now rewrite Cd, <- ln_beta_d.
Qed.



Lemma format_bpow_x: (0 < F2R d)%R
    -> generic_format beta fexp  (bpow (ln_beta beta x)).
Proof with auto with typeclass_instances.
intros Y.
apply generic_format_bpow.
apply valid_exp.
rewrite <- Fexp_d; trivial.
apply Zlt_le_trans with  (ln_beta beta (F2R d))%Z.
rewrite Cd; apply ln_beta_generic_gt...
now apply Rgt_not_eq.
apply Hd.
apply ln_beta_le; trivial.
apply Hd.
Qed.


Lemma format_bpow_d: (0 < F2R d)%R ->
  generic_format beta fexp (bpow (ln_beta beta (F2R d))).
Proof with auto with typeclass_instances.
intros Y; apply generic_format_bpow.
apply valid_exp.
apply ln_beta_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonic.
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

Lemma ln_beta_m: (0 < F2R d)%R -> (ln_beta beta m =ln_beta beta (F2R d) :>Z).
Proof with auto with typeclass_instances.
intros dPos; apply ln_beta_unique_pos.
split.
apply Rle_trans with (F2R d).
destruct (ln_beta beta (F2R d)) as (e,He).
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
apply ln_beta_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonic.
case (Rle_or_lt x (bpow (ln_beta beta (F2R d)))); trivial; intros Z.
absurd ((bpow (ln_beta beta (F2R d)) <= (F2R d)))%R.
apply Rlt_not_le.
destruct  (ln_beta beta (F2R d)) as (e,He).
simpl in *; rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
apply Rle_trans with (round beta fexp Zfloor x).
2: right; apply sym_eq, d_eq.
apply round_ge_generic...
apply generic_format_bpow.
apply valid_exp.
apply ln_beta_generic_gt...
now apply Rgt_not_eq.
now apply generic_format_canonic.
now left.
replace m with (F2R d).
destruct (ln_beta beta (F2R d)) as (e,He).
simpl in *; rewrite Rabs_right in He.
apply He.
now apply Rgt_not_eq.
apply Rle_ge; now left.
unfold m in H |- *.
lra.
Qed.


Lemma ln_beta_m_0: (0 = F2R d)%R
    -> (ln_beta beta m =ln_beta beta (F2R u)-1:>Z)%Z.
Proof with auto with typeclass_instances.
intros Y.
apply ln_beta_unique_pos.
unfold m; rewrite <- Y, Rplus_0_l.
rewrite u_eq.
destruct (ln_beta beta x) as (e,He).
rewrite Rabs_pos_eq in He by now apply Rlt_le.
rewrite round_UP_small_pos with (ex:=e).
rewrite ln_beta_bpow.
ring_simplify (fexp e + 1 - 1)%Z.
split.
unfold Zminus; rewrite bpow_plus.
unfold Rdiv; apply Rmult_le_compat_l.
apply bpow_ge_0.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r; apply Rinv_le.
exact Rlt_0_2.
apply (Z2R_le 2).
specialize (radix_gt_1 beta).
omega.
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




Lemma m_eq: (0 < F2R d)%R ->  exists f:float beta,
   F2R f = m /\ (Fexp f = fexp (ln_beta beta x) -1)%Z.
Proof with auto with typeclass_instances.
intros Y.
specialize (Zeven_ex (radix_val beta)); rewrite Even_beta.
intros (b, Hb); rewrite Zplus_0_r in Hb.
destruct u'_eq as (u', (Hu'1,Hu'2)); trivial.
exists (Fmult beta (Float beta b (-1)) (Fplus beta d u'))%R.
split.
rewrite F2R_mult, F2R_plus, Hu'1.
unfold m; rewrite Rmult_comm.
unfold Rdiv; apply f_equal.
unfold F2R; simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Hb, Z2R_mult.
simpl; field.
apply Rgt_not_eq, Rmult_lt_reg_l with (1 := Rlt_0_2).
rewrite Rmult_0_r, <- (Z2R_mult 2), <-Hb.
apply radix_pos.
apply trans_eq with (-1+Fexp (Fplus beta d u'))%Z.
unfold Fmult.
destruct  (Fplus beta d u'); reflexivity.
rewrite Zplus_comm; unfold Zminus; apply f_equal2.
2: reflexivity.
rewrite Fexp_Fplus.
rewrite Z.min_l.
now rewrite Fexp_d.
rewrite Hu'2; omega.
Qed.

Lemma m_eq_0: (0 = F2R d)%R ->  exists f:float beta,
   F2R f = m /\ (Fexp f = fexp (ln_beta beta (F2R u)) -1)%Z.
Proof with auto with typeclass_instances.
intros Y.
specialize (Zeven_ex (radix_val beta)); rewrite Even_beta.
intros (b, Hb); rewrite Zplus_0_r in Hb.
exists (Fmult beta (Float beta b (-1)) u)%R.
split.
rewrite F2R_mult; unfold m; rewrite <- Y, Rplus_0_l.
rewrite Rmult_comm.
unfold Rdiv; apply f_equal.
unfold F2R; simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Hb, Z2R_mult.
simpl; field.
apply Rgt_not_eq, Rmult_lt_reg_l with (1 := Rlt_0_2).
rewrite Rmult_0_r, <- (Z2R_mult 2), <-Hb.
apply radix_pos.
apply trans_eq with (-1+Fexp u)%Z.
unfold Fmult.
destruct u; reflexivity.
rewrite Zplus_comm, Cu; unfold Zminus; now apply f_equal2.
Qed.

Lemma fexp_m_eq_0:  (0 = F2R d)%R ->
  (fexp (ln_beta beta (F2R u)-1) < fexp (ln_beta beta (F2R u))+1)%Z.
Proof with auto with typeclass_instances.
intros Y.
assert ((fexp (ln_beta beta (F2R u) - 1) <= fexp (ln_beta beta (F2R u))))%Z.
2: omega.
destruct (ln_beta beta x) as (e,He).
rewrite Rabs_right in He.
2: now left.
assert (e <= fexp e)%Z.
apply exp_small_round_0_pos with beta (Zfloor) x...
now apply He, Rgt_not_eq.
now rewrite <- d_eq, Y.
rewrite u_eq, round_UP_small_pos with (ex:=e); trivial.
2: now apply He, Rgt_not_eq.
rewrite ln_beta_bpow.
ring_simplify (fexp e + 1 - 1)%Z.
replace (fexp (fexp e)) with (fexp e).
case exists_NE_; intros V.
contradict V; rewrite Even_beta; discriminate.
rewrite (proj2 (V e)); omega.
apply sym_eq, valid_exp; omega.
Qed.

Lemma Fm:  generic_format beta fexpe m.
case (d_ge_0); intros Y.
(* *)
destruct m_eq as (g,(Hg1,Hg2)); trivial.
apply generic_format_F2R' with g.
now apply sym_eq.
intros H; unfold canonic_exp; rewrite Hg2.
rewrite ln_beta_m; trivial.
rewrite <- Fexp_d; trivial.
rewrite Cd.
unfold canonic_exp.
generalize (fexpe_fexp (ln_beta beta (F2R d))).
omega.
(* *)
destruct m_eq_0 as (g,(Hg1,Hg2)); trivial.
apply generic_format_F2R' with g.
assumption.
intros H; unfold canonic_exp; rewrite Hg2.
rewrite ln_beta_m_0; try assumption.
apply Zle_trans with (1:=fexpe_fexp _).
assert (fexp (ln_beta beta (F2R u)-1) < fexp (ln_beta beta (F2R u))+1)%Z;[idtac|omega].
now apply fexp_m_eq_0.
Qed.



Lemma Zm:
   exists g : float beta, F2R g = m /\ canonic beta fexpe g /\ Zeven (Fnum g) = true.
Proof with auto with typeclass_instances.
case (d_ge_0); intros Y.
(* *)
destruct m_eq as (g,(Hg1,Hg2)); trivial.
apply exists_even_fexp_lt.
exists g; split; trivial.
rewrite Hg2.
rewrite ln_beta_m; trivial.
rewrite <- Fexp_d; trivial.
rewrite Cd.
unfold canonic_exp.
generalize (fexpe_fexp  (ln_beta beta (F2R d))).
omega.
(* *)
destruct m_eq_0 as (g,(Hg1,Hg2)); trivial.
apply exists_even_fexp_lt.
exists g; split; trivial.
rewrite Hg2.
rewrite ln_beta_m_0; trivial.
apply Zle_lt_trans with (1:=fexpe_fexp _).
assert (fexp (ln_beta beta (F2R u)-1) < fexp (ln_beta beta (F2R u))+1)%Z;[idtac|omega].
now apply fexp_m_eq_0.
Qed.


Lemma DN_odd_d_aux: forall z, (F2R d<= z< F2R u)%R ->
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
intros Y; absurd (z < z)%R.
auto with real.
apply Rlt_le_trans with (1:=proj2 Hz1), Rle_trans with (1:=Y).
apply round_DN_pt...
Qed.

Lemma UP_odd_d_aux: forall z, (F2R d< z <= F2R u)%R ->
    Rnd_UP_pt (generic_format beta fexp) z (F2R u).
Proof with auto with typeclass_instances.
intros z Hz1.
replace (F2R u) with (round beta fexp Zceil z).
apply round_UP_pt...
case (Rnd_DN_UP_pt_split _ _ _ _ Hd Hu (round beta fexp Zceil z)).
apply generic_format_round...
intros Y; absurd (z < z)%R.
auto with real.
apply Rle_lt_trans with (2:=proj1 Hz1), Rle_trans with (2:=Y).
apply round_UP_pt...
intros Y; apply Rle_antisym; trivial.
apply round_UP_pt...
apply Hu.
apply Hz1.
Qed.


Theorem round_odd_prop_pos:
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
apply canonic_unicity with fexpe...
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
simpl; unfold canonic_exp.
apply Zle_lt_trans with (1:=fexpe_fexp _).
omega.
absurd (true=false).
discriminate.
rewrite <- Hk3, <- Hk'3.
apply f_equal, f_equal.
apply canonic_unicity with fexpe...
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
Hypothesis Even_beta: Zeven (radix_val beta)=true.

Variable fexp : Z -> Z.
Variable fexpe : Z -> Z.
Variable choice:Z->bool.

Context { valid_exp : Valid_exp fexp }.
Context { exists_NE_ : Exists_NE beta fexp }. (* for underflow reason *)
Context { valid_expe : Valid_exp fexpe }.
Context { exists_NE_e : Exists_NE beta fexpe }. (* for defining rounding to odd *)

Hypothesis fexpe_fexp: forall e, (fexpe e <= fexp e -2)%Z.


Theorem canonizer: forall f, generic_format beta fexp f
   -> exists g : float beta, f = F2R g /\ canonic beta fexp g.
Proof with auto with typeclass_instances.
intros f Hf.
exists (Float beta (Ztrunc (scaled_mantissa beta fexp f)) (canonic_exp beta fexp f)).
assert (L:(f = F2R (Float beta (Ztrunc (scaled_mantissa beta fexp f)) (canonic_exp beta fexp f)))).
apply trans_eq with (round beta fexp Ztrunc f).
apply sym_eq, round_generic...
reflexivity.
split; trivial.
unfold canonic; rewrite <- L.
reflexivity.
Qed.




Theorem round_odd_prop: forall x,
  round beta fexp (Znearest choice) (round beta fexpe Zrnd_odd x) =
               round beta fexp (Znearest choice) x.
Proof with auto with typeclass_instances.
intros x.
case (total_order_T x 0); intros H; [case H; clear H; intros H | idtac].
rewrite <- (Ropp_involutive x).
rewrite round_odd_opp.
rewrite 2!round_N_opp.
apply f_equal.
destruct (canonizer (round beta fexp Zfloor (-x))) as (d,(Hd1,Hd2)).
apply generic_format_round...
destruct (canonizer (round beta fexp Zceil (-x))) as (u,(Hu1,Hu2)).
apply generic_format_round...
apply round_odd_prop_pos with d u...
rewrite <- Hd1; apply round_DN_pt...
rewrite <- Hu1; apply round_UP_pt...
auto with real.
(* . *)
rewrite H; repeat rewrite round_0...
(* . *)
destruct (canonizer (round beta fexp Zfloor x)) as (d,(Hd1,Hd2)).
apply generic_format_round...
destruct (canonizer (round beta fexp Zceil x)) as (u,(Hu1,Hu2)).
apply generic_format_round...
apply round_odd_prop_pos with d u...
rewrite <- Hd1; apply round_DN_pt...
rewrite <- Hu1; apply round_UP_pt...
Qed.


End Odd_prop.

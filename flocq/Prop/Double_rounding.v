(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2014-2018 Sylvie Boldo
#<br />#
Copyright (C) 2014-2018 Guillaume Melquiond
#<br />#
Copyright (C) 2014-2018 Pierre Roux

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Conditions for innocuous double rounding. *)

From Coq Require Import ZArith Reals Psatz.

Require Import Core FTZ.

Open Scope R_scope.

Section Double_round.

Variable beta : radix.
Notation bpow e := (bpow beta e).
Notation mag x := (mag beta x).

Definition round_round_eq fexp1 fexp2 choice1 choice2 x :=
  round beta fexp1 (Znearest choice1) (round beta fexp2 (Znearest choice2) x)
  = round beta fexp1 (Znearest choice1) x.

(** A little tactic to simplify terms of the form [bpow a * bpow b]. *)
Ltac bpow_simplify :=
  (* bpow ex * bpow ey ~~> bpow (ex + ey) *)
  repeat
    match goal with
      | |- context [(Raux.bpow _ _ * Raux.bpow _ _)] =>
        rewrite <- bpow_plus
      | |- context [(?X1 * Raux.bpow _ _ * Raux.bpow _ _)] =>
        rewrite (Rmult_assoc X1); rewrite <- bpow_plus
      | |- context [(?X1 * (?X2 * Raux.bpow _ _) * Raux.bpow _ _)] =>
        rewrite <- (Rmult_assoc X1 X2); rewrite (Rmult_assoc (X1 * X2));
        rewrite <- bpow_plus
    end;
  (* ring_simplify arguments of bpow *)
  repeat
    match goal with
      | |- context [(Raux.bpow _ ?X)] =>
        progress ring_simplify X
    end;
  (* bpow 0 ~~> 1 *)
  change (Raux.bpow _ 0) with 1;
  repeat
    match goal with
      | |- context [(_ * 1)] =>
        rewrite Rmult_1_r
    end.

Definition midp (fexp : Z -> Z) (x : R) :=
  round beta fexp Zfloor x + / 2 * ulp beta fexp x.

Definition midp' (fexp : Z -> Z) (x : R) :=
  round beta fexp Zceil x - / 2 * ulp beta fexp x.

Lemma round_round_lt_mid_further_place' :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  x < bpow (mag x) - / 2 * ulp beta fexp2 x ->
  x < midp fexp1 x - / 2 * ulp beta fexp2 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hx1.
unfold round_round_eq.
set (x' := round beta fexp1 Zfloor x).
intro Hx2'.
assert (Hx2 : x - round beta fexp1 Zfloor x
              < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
{ now apply (Rplus_lt_reg_r (round beta fexp1 Zfloor x)); ring_simplify. }
set (x'' := round beta fexp2 (Znearest choice2) x).
assert (Hr1 : Rabs (x'' - x) <= / 2 * bpow (fexp2 (mag x))).
apply Rle_trans with (/ 2 * ulp beta fexp2 x).
now unfold x''; apply error_le_half_ulp...
rewrite ulp_neq_0;[now right|now apply Rgt_not_eq].
assert (Pxx' : 0 <= x - x').
{ apply Rle_0_minus.
  apply round_DN_pt.
  exact Vfexp1. }
rewrite 2!ulp_neq_0 in Hx2; try (apply Rgt_not_eq; assumption).
assert (Hr2 : Rabs (x'' - x') < / 2 * bpow (fexp1 (mag x))).
{ replace (x'' - x') with (x'' - x + (x - x')) by ring.
  apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
  replace (/ 2 * _) with (/ 2 * bpow (fexp2 (mag x))
                          + (/ 2 * (bpow (fexp1 (mag x))
                                    - bpow (fexp2 (mag x))))) by ring.
  apply Rplus_le_lt_compat.
  - exact Hr1.
  - now rewrite Rabs_right; [|now apply Rle_ge]; apply Hx2. }
destruct (Req_dec x'' 0) as [Zx''|Nzx''].
- (* x'' = 0 *)
  rewrite Zx'' in Hr1 |- *.
  rewrite round_0; [|now apply valid_rnd_N].
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  rewrite (Znearest_imp _ _ 0); [now simpl; rewrite Rmult_0_l|].
  apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult; rewrite Rmult_minus_distr_r.
  rewrite Rmult_0_l.
  bpow_simplify.
  rewrite Rabs_minus_sym.
  apply (Rle_lt_trans _ _ _ Hr1).
  apply Rmult_lt_compat_l; [lra|].
  apply bpow_lt.
  lia.
- (* x'' <> 0 *)
  assert (Lx'' : mag x'' = mag x :> Z).
  { apply Zle_antisym.
    - apply mag_le_bpow; [exact Nzx''|].
      replace x'' with (x'' - x + x) by ring.
      apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
      replace (bpow _) with (/ 2 * bpow (fexp2 (mag x))
                             + (bpow (mag x)
                                - / 2 * bpow (fexp2 (mag x)))) by ring.
      apply Rplus_le_lt_compat; [exact Hr1|].
      rewrite ulp_neq_0 in Hx1;[idtac| now apply Rgt_not_eq].
      now rewrite Rabs_right; [|apply Rle_ge; apply Rlt_le].
    - unfold x'' in Nzx'' |- *.
      now apply mag_round_ge; [|apply valid_rnd_N|]. }
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  rewrite Lx''.
  rewrite (Znearest_imp _ _ (Zfloor (scaled_mantissa beta fexp1 x))).
  + rewrite (Znearest_imp _ _ (Zfloor (scaled_mantissa beta fexp1 x)));
    [reflexivity|].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    fold x'.
    bpow_simplify.
    rewrite Rabs_right; [|now apply Rle_ge].
    apply (Rlt_le_trans _ _ _ Hx2).
    apply Rmult_le_compat_l; [lra|].
    generalize (bpow_ge_0 beta (fexp2 (mag x))).
    unfold ulp, cexp; lra.
  + apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    fold x'.
    now bpow_simplify.
Qed.

Lemma round_round_lt_mid_further_place :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  x < midp fexp1 x - / 2 * ulp beta fexp2 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1.
intro Hx2'.
assert (Hx2 : x - round beta fexp1 Zfloor x
              < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
{ now apply (Rplus_lt_reg_r (round beta fexp1 Zfloor x)); ring_simplify. }
revert Hx2.
unfold round_round_eq.
set (x' := round beta fexp1 Zfloor x).
intro Hx2.
assert (Pxx' : 0 <= x - x').
{ apply Rle_0_minus.
  apply round_DN_pt.
  exact Vfexp1. }
assert (x < bpow (mag x) - / 2 * bpow (fexp2 (mag x)));
  [|apply round_round_lt_mid_further_place'; try assumption]...
2: rewrite ulp_neq_0;[assumption|now apply Rgt_not_eq].
destruct (Req_dec x' 0) as [Zx'|Nzx'].
- (* x' = 0 *)
  rewrite Zx' in Hx2; rewrite Rminus_0_r in Hx2.
  apply (Rlt_le_trans _ _ _ Hx2).
  rewrite Rmult_minus_distr_l.
  rewrite 2!ulp_neq_0;[idtac|now apply Rgt_not_eq|now apply Rgt_not_eq].
  apply Rplus_le_compat_r.
  apply (Rmult_le_reg_r (bpow (- mag x))); [now apply bpow_gt_0|].
  unfold ulp, cexp; bpow_simplify.
  apply Rmult_le_reg_l with (1 := Rlt_0_2).
  replace (2 * (/ 2 * _)) with (bpow (fexp1 (mag x) - mag x)) by field.
  apply Rle_trans with 1; [|lra].
  change 1 with (bpow 0); apply bpow_le.
  lia.
- (* x' <> 0 *)
  assert (Px' : 0 < x').
  { assert (0 <= x'); [|lra].
    unfold x'.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_0_l.
    unfold round, F2R, cexp; simpl; bpow_simplify.
    apply IZR_le.
    apply Zfloor_lub.
    rewrite <- (Rabs_right x); [|now apply Rle_ge; apply Rlt_le].
    rewrite scaled_mantissa_abs.
    apply Rabs_pos. }
  assert (Hx' : x' <= bpow (mag x) - ulp beta fexp1 x).
  { apply (Rplus_le_reg_r (ulp beta fexp1 x)); ring_simplify.
    rewrite <- ulp_DN.
    - change (round _ _ _ _) with x'.
      apply id_p_ulp_le_bpow.
      + exact Px'.
      + change x' with (round beta fexp1 Zfloor x).
        now apply generic_format_round; [|apply valid_rnd_DN].
      + apply Rle_lt_trans with x.
        * now apply round_DN_pt.
        * rewrite <- (Rabs_right x) at 1; [|now apply Rle_ge; apply Rlt_le].
          apply bpow_mag_gt.
    - exact Vfexp1.
    - now apply Rlt_le. }
  fold (cexp beta fexp2 x); fold (ulp beta fexp2 x).
  assert (/ 2 * ulp beta fexp1 x <= ulp beta fexp1 x).
  rewrite <- (Rmult_1_l (ulp _ _ _)) at 2.
  apply Rmult_le_compat_r; [|lra].
  apply ulp_ge_0.
  rewrite 2!ulp_neq_0 in Hx2;[|now apply Rgt_not_eq|now apply Rgt_not_eq].
  rewrite ulp_neq_0 in Hx';[|now apply Rgt_not_eq].
  rewrite ulp_neq_0 in H;[|now apply Rgt_not_eq].
  lra.
Qed.

Lemma round_round_lt_mid_same_place :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) = fexp1 (mag x))%Z ->
  x < midp fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 choice1 choice2 x Px Hf2f1.
intro Hx'.
assert (Hx : x - round beta fexp1 Zfloor x < / 2 * ulp beta fexp1 x).
{ now apply (Rplus_lt_reg_r (round beta fexp1 Zfloor x)); ring_simplify. }
revert Hx.
unfold round_round_eq.
set (x' := round beta fexp1 Zfloor x).
intro Hx.
assert (Pxx' : 0 <= x - x').
{ apply Rle_0_minus.
  apply round_DN_pt.
  exact Vfexp1. }
assert (H : Rabs (x * bpow (- fexp1 (mag x)) -
                  IZR (Zfloor (x * bpow (- fexp1 (mag x))))) < / 2).
{ apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  unfold scaled_mantissa, cexp in Hx.
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  apply Rabs_lt.
  change (IZR _ * _) with x'.
  split.
  - apply Rlt_le_trans with 0; [|exact Pxx'].
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    rewrite <- (Rmult_0_r (/ 2)).
    apply Rmult_lt_compat_l; [lra|].
    apply bpow_gt_0.
  - rewrite ulp_neq_0 in Hx;try apply Rgt_not_eq; assumption. }
unfold round at 2.
unfold F2R, scaled_mantissa, cexp; simpl.
rewrite Hf2f1.
rewrite (Znearest_imp _ _ (Zfloor (scaled_mantissa beta fexp1 x)) H).
rewrite round_generic.
  + unfold round, F2R, scaled_mantissa, cexp; simpl.
    now rewrite (Znearest_imp _ _ (Zfloor (x * bpow (- fexp1 (mag x))))).
  + now apply valid_rnd_N.
  + fold (cexp beta fexp1 x).
    change (IZR _ * bpow _) with (round beta fexp1 Zfloor x).
    apply generic_format_round.
    exact Vfexp1.
    now apply valid_rnd_DN.
Qed.

Lemma round_round_lt_mid :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x))%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  x < midp fexp1 x ->
  ((fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
   x < midp fexp1 x - / 2 * ulp beta fexp2 x) ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1 Hx Hx'.
destruct (Zle_or_lt (fexp1 (mag x)) (fexp2 (mag x))) as [Hf2'|Hf2'].
- (* fexp1 (mag x) <= fexp2 (mag x) *)
  assert (Hf2'' : (fexp2 (mag x) = fexp1 (mag x) :> Z)%Z) by lia.
  now apply round_round_lt_mid_same_place.
- (* fexp2 (mag x) < fexp1 (mag x) *)
  assert (Hf2'' : (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z) by lia.
  generalize (Hx' Hf2''); intro Hx''.
  now apply round_round_lt_mid_further_place.
Qed.

Lemma round_round_gt_mid_further_place' :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  round beta fexp2 (Znearest choice2) x < bpow (mag x) ->
  midp' fexp1 x + / 2 * ulp beta fexp2 x < x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1.
intros Hx1 Hx2'.
assert (Hx2 : round beta fexp1 Zceil x - x
              < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
{ apply (Rplus_lt_reg_r (- / 2 * ulp beta fexp1 x + x
                         + / 2 * ulp beta fexp2 x)); ring_simplify.
  now unfold midp' in Hx2'. }
revert Hx1 Hx2.
unfold round_round_eq.
set (x' := round beta fexp1 Zceil x).
set (x'' := round beta fexp2 (Znearest choice2) x).
intros Hx1 Hx2.
assert (Hr1 : Rabs (x'' - x) <= / 2 * bpow (fexp2 (mag x))).
  apply Rle_trans with (/2* ulp beta fexp2 x).
  now unfold x''; apply error_le_half_ulp...
  rewrite ulp_neq_0;[now right|now apply Rgt_not_eq].
assert (Px'x : 0 <= x' - x).
{ apply Rle_0_minus.
  apply round_UP_pt.
  exact Vfexp1. }
assert (Hr2 : Rabs (x'' - x') < / 2 * bpow (fexp1 (mag x))).
{ replace (x'' - x') with (x'' - x + (x - x')) by ring.
  apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
  replace (/ 2 * _) with (/ 2 * bpow (fexp2 (mag x))
                          + (/ 2 * (bpow (fexp1 (mag x))
                                    - bpow (fexp2 (mag x))))) by ring.
  apply Rplus_le_lt_compat.
  - exact Hr1.
  - rewrite Rabs_minus_sym.
   rewrite 2!ulp_neq_0 in Hx2; try (apply Rgt_not_eq; assumption).
    now rewrite Rabs_right; [|now apply Rle_ge]; apply Hx2. }
destruct (Req_dec x'' 0) as [Zx''|Nzx''].
- (* x'' = 0 *)
  rewrite Zx'' in Hr1 |- *.
  rewrite round_0; [|now apply valid_rnd_N].
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  rewrite (Znearest_imp _ _ 0); [now simpl; rewrite Rmult_0_l|].
  apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult; rewrite Rmult_minus_distr_r.
  rewrite Rmult_0_l.
  bpow_simplify.
  rewrite Rabs_minus_sym.
  apply (Rle_lt_trans _ _ _ Hr1).
  apply Rmult_lt_compat_l; [lra|].
  apply bpow_lt.
  lia.
- (* x'' <> 0 *)
  assert (Lx'' : mag x'' = mag x :> Z).
  { apply Zle_antisym.
    - apply mag_le_bpow; [exact Nzx''|].
      rewrite Rabs_right; [exact Hx1|apply Rle_ge].
      apply round_ge_generic.
      + exact Vfexp2.
      + now apply valid_rnd_N.
      + apply generic_format_0.
      + now apply Rlt_le.
    - unfold x'' in Nzx'' |- *.
      now apply mag_round_ge; [|apply valid_rnd_N|]. }
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  rewrite Lx''.
  rewrite (Znearest_imp _ _ (Zceil (scaled_mantissa beta fexp1 x))).
  + rewrite (Znearest_imp _ _ (Zceil (scaled_mantissa beta fexp1 x)));
    [reflexivity|].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    fold x'.
    bpow_simplify.
    rewrite Rabs_minus_sym.
    rewrite Rabs_right; [|now apply Rle_ge].
    apply (Rlt_le_trans _ _ _ Hx2).
    apply Rmult_le_compat_l; [lra|].
    generalize (bpow_ge_0 beta (fexp2 (mag x))).
    rewrite 2!ulp_neq_0; try (apply Rgt_not_eq; assumption).
    unfold cexp; lra.
  + apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    fold x'.
    now bpow_simplify.
Qed.

Lemma round_round_gt_mid_further_place :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  midp' fexp1 x + / 2 * ulp beta fexp2 x < x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1 Hx2'.
assert (Hx2 : round beta fexp1 Zceil x - x
              < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
{ apply (Rplus_lt_reg_r (- / 2 * ulp beta fexp1 x + x
                         + / 2 * ulp beta fexp2 x)); ring_simplify.
  now unfold midp' in Hx2'. }
revert Hx2.
unfold round_round_eq.
set (x' := round beta fexp1 Zfloor x).
intro Hx2.
set (x'' := round beta fexp2 (Znearest choice2) x).
destruct (Rlt_or_le x'' (bpow (mag x))) as [Hx''|Hx''];
  [now apply round_round_gt_mid_further_place'|].
(* bpow (mag x) <= x'' *)
assert (Hx''pow : x'' = bpow (mag x)).
{ assert (H'x'' : x'' < bpow (mag x) + / 2 * ulp beta fexp2 x).
  { apply Rle_lt_trans with (x + / 2 * ulp beta fexp2 x).
    - apply (Rplus_le_reg_r (- x)); ring_simplify.
      apply Rabs_le_inv.
      apply error_le_half_ulp.
      exact Vfexp2.
    - apply Rplus_lt_compat_r.
      rewrite <- Rabs_right at 1; [|now apply Rle_ge; apply Rlt_le].
      apply bpow_mag_gt. }
  apply Rle_antisym; [|exact Hx''].
  unfold x'', round, F2R, scaled_mantissa, cexp; simpl.
  apply (Rmult_le_reg_r (bpow (- fexp2 (mag x)))); [now apply bpow_gt_0|].
  bpow_simplify.
  rewrite <- (IZR_Zpower _ (_ - _)) by lia.
  apply IZR_le.
  apply Zlt_succ_le; unfold Z.succ.
  apply lt_IZR.
  rewrite plus_IZR; rewrite IZR_Zpower by lia.
  apply (Rmult_lt_reg_r (bpow (fexp2 (mag x)))); [now apply bpow_gt_0|].
  rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
  bpow_simplify.
  apply (Rlt_le_trans _ _ _ H'x'').
  apply Rplus_le_compat_l.
  rewrite <- (Rmult_1_l (Raux.bpow _ _)).
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
  apply Rmult_le_compat_r; [now apply bpow_ge_0|].
  lra. }
assert (Hr : Rabs (x - x'') < / 2 * ulp beta fexp1 x).
{ apply Rle_lt_trans with (/ 2 * ulp beta fexp2 x).
  - rewrite Rabs_minus_sym.
    apply error_le_half_ulp.
    exact Vfexp2.
  - apply Rmult_lt_compat_l; [lra|].
    rewrite 2!ulp_neq_0; try now apply Rgt_not_eq.
    unfold cexp; apply bpow_lt.
    lia. }
unfold round, F2R, scaled_mantissa, cexp; simpl.
assert (Hf : (0 <= mag x - fexp1 (mag x''))%Z).
{ rewrite Hx''pow.
  rewrite mag_bpow.
  cut (fexp1 (mag x + 1) <= mag x)%Z. lia.
  destruct (Zle_or_lt (mag x) (fexp1 (mag x))) as [Hle|Hlt];
    [|now apply Vfexp1].
  assert (H : (mag x = fexp1 (mag x) :> Z)%Z);
    [now apply Zle_antisym|].
  rewrite H.
  now apply Vfexp1. }
rewrite (Znearest_imp _ _ (beta ^ (mag x - fexp1 (mag x'')))%Z).
- rewrite (Znearest_imp _ _ (beta ^ (mag x - fexp1 (mag x)))%Z).
  + rewrite IZR_Zpower by exact Hf.
    rewrite IZR_Zpower by lia.
    now bpow_simplify.
  + rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
      [|now apply Rle_ge; apply bpow_ge_0].
    rewrite <- Rabs_mult.
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
   rewrite ulp_neq_0 in Hr;[idtac|now apply Rgt_not_eq].
    rewrite <- Hx''pow; exact Hr.
- rewrite IZR_Zpower; [|exact Hf].
  apply (Rmult_lt_reg_r (bpow (fexp1 (mag x'')))); [now apply bpow_gt_0|].
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  rewrite Rminus_diag_eq; [|exact Hx''pow].
  rewrite Rabs_R0.
  rewrite <- (Rmult_0_r (/ 2)).
  apply Rmult_lt_compat_l; [lra|apply bpow_gt_0].
Qed.

Lemma round_round_gt_mid_same_place :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) = fexp1 (mag x))%Z ->
  midp' fexp1 x < x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 choice1 choice2 x Px Hf2f1 Hx'.
assert (Hx : round beta fexp1 Zceil x - x < / 2 * ulp beta fexp1 x).
{ apply (Rplus_lt_reg_r (- / 2 * ulp beta fexp1 x + x)); ring_simplify.
  now unfold midp' in Hx'. }
assert (H : Rabs (IZR (Zceil (x * bpow (- fexp1 (mag x))))
                  - x * bpow (- fexp1 (mag x))) < / 2).
{ apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  unfold scaled_mantissa, cexp in Hx.
  rewrite <- (Rabs_right (bpow (fexp1 _))) at 1;
    [|now apply Rle_ge; apply bpow_ge_0].
  rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  apply Rabs_lt.
  split.
  - apply Rlt_le_trans with 0.
    + rewrite <- Ropp_0; apply Ropp_lt_contravar.
      rewrite <- (Rmult_0_r (/ 2)).
      apply Rmult_lt_compat_l; [lra|].
      apply bpow_gt_0.
    + apply Rle_0_minus.
      apply round_UP_pt.
      exact Vfexp1.
  -  rewrite ulp_neq_0 in Hx;[exact Hx|now apply Rgt_not_eq]. }
unfold round_round_eq, round at 2.
unfold F2R, scaled_mantissa, cexp; simpl.
rewrite Hf2f1.
rewrite (Znearest_imp _ _ (Zceil (scaled_mantissa beta fexp1 x))).
- rewrite round_generic.
  + unfold round, F2R, scaled_mantissa, cexp; simpl.
    now rewrite (Znearest_imp _ _ (Zceil (x * bpow (- fexp1 (mag x)))));
      [|rewrite Rabs_minus_sym].
  + now apply valid_rnd_N.
  + fold (cexp beta fexp1 x).
    change (IZR _ * bpow _) with (round beta fexp1 Zceil x).
    apply generic_format_round.
    exact Vfexp1.
    now apply valid_rnd_UP.
- now rewrite Rabs_minus_sym.
Qed.

Lemma round_round_gt_mid :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x))%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  midp' fexp1 x < x ->
  ((fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
   midp' fexp1 x + / 2 * ulp beta fexp2 x < x) ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1 Hx Hx'.
destruct (Zle_or_lt (fexp1 (mag x)) (fexp2 (mag x))) as [Hf2'|Hf2'].
- (* fexp1 (mag x) <= fexp2 (mag x) *)
  assert (Hf2'' : (fexp2 (mag x) = fexp1 (mag x) :> Z)%Z) by lia.
  now apply round_round_gt_mid_same_place.
- (* fexp2 (mag x) < fexp1 (mag x) *)
  assert (Hf2'' : (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z) by lia.
  generalize (Hx' Hf2''); intro Hx''.
  now apply round_round_gt_mid_further_place.
Qed.

Section Double_round_mult.

Lemma mag_mult_disj :
  forall x y,
  x <> 0 -> y <> 0 ->
  ((mag (x * y) = (mag x + mag y - 1)%Z :> Z)
   \/ (mag (x * y) = (mag x + mag y)%Z :> Z)).
Proof.
intros x y Zx Zy.
destruct (mag_mult beta x y Zx Zy).
lia.
Qed.

Definition round_round_mult_hyp fexp1 fexp2 :=
  (forall ex ey, (fexp2 (ex + ey) <= fexp1 ex + fexp1 ey)%Z)
  /\ (forall ex ey, (fexp2 (ex + ey - 1) <= fexp1 ex + fexp1 ey)%Z).

Lemma round_round_mult_aux :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_mult_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x * y).
Proof.
intros fexp1 fexp2 Hfexp x y Fx Fy.
destruct (Req_dec x 0) as [Zx|Zx].
- (* x = 0 *)
  rewrite Zx.
  rewrite Rmult_0_l.
  now apply generic_format_0.
- (* x <> 0 *)
  destruct (Req_dec y 0) as [Zy|Zy].
  + (* y = 0 *)
    rewrite Zy.
    rewrite Rmult_0_r.
    now apply generic_format_0.
  + (* y <> 0 *)
    revert Fx Fy.
    unfold generic_format.
    unfold cexp.
    set (mx := Ztrunc (scaled_mantissa beta fexp1 x)).
    set (my := Ztrunc (scaled_mantissa beta fexp1 y)).
    unfold F2R; simpl.
    intros Fx Fy.
    set (fxy := Float beta (mx * my) (fexp1 (mag x) + fexp1 (mag y))).
    assert (Hxy : x * y = F2R fxy).
    { unfold fxy, F2R; simpl.
      rewrite bpow_plus.
      rewrite mult_IZR.
      rewrite Fx, Fy at 1.
      ring. }
    apply generic_format_F2R' with (f := fxy); [now rewrite Hxy|].
    intros _.
    unfold cexp, fxy; simpl.
    destruct Hfexp as (Hfexp1, Hfexp2).
    now destruct (mag_mult_disj x y Zx Zy) as [Lxy|Lxy]; rewrite Lxy.
Qed.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Theorem round_round_mult :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_mult_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  round beta fexp1 rnd (round beta fexp2 rnd (x * y))
  = round beta fexp1 rnd (x * y).
Proof.
intros fexp1 fexp2 Hfexp x y Fx Fy.
assert (Hxy : round beta fexp2 rnd (x * y) = x * y).
{ apply round_generic; [assumption|].
  now apply (round_round_mult_aux fexp1 fexp2). }
now rewrite Hxy at 1.
Qed.

Section Double_round_mult_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem round_round_mult_FLX :
  (2 * prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round beta (FLX_exp prec) rnd (round beta (FLX_exp prec') rnd (x * y))
  = round beta (FLX_exp prec) rnd (x * y).
Proof.
intros Hprec x y Fx Fy.
apply round_round_mult;
  [|now apply generic_format_FLX|now apply generic_format_FLX].
unfold round_round_mult_hyp; split; intros ex ey; unfold FLX_exp;
lia.
Qed.

End Double_round_mult_FLX.

Section Double_round_mult_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem round_round_mult_FLT :
  (emin' <= 2 * emin)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round beta (FLT_exp emin prec) rnd
        (round beta (FLT_exp emin' prec') rnd (x * y))
  = round beta (FLT_exp emin prec) rnd (x * y).
Proof.
intros Hemin Hprec x y Fx Fy.
apply round_round_mult;
  [|now apply generic_format_FLT|now apply generic_format_FLT].
unfold round_round_mult_hyp; split; intros ex ey;
unfold FLT_exp;
generalize (Zmax_spec (ex + ey - prec') emin');
generalize (Zmax_spec (ex + ey - 1 - prec') emin');
generalize (Zmax_spec (ex - prec) emin);
generalize (Zmax_spec (ey - prec) emin);
lia.
Qed.

End Double_round_mult_FLT.

Section Double_round_mult_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem round_round_mult_FTZ :
  (emin' + prec' <= 2 * emin + prec)%Z ->
  (2 * prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round beta (FTZ_exp emin prec) rnd
        (round beta (FTZ_exp emin' prec') rnd (x * y))
  = round beta (FTZ_exp emin prec) rnd (x * y).
Proof.
intros Hemin Hprec x y Fx Fy.
apply round_round_mult;
  [|now apply generic_format_FTZ|now apply generic_format_FTZ].
unfold round_round_mult_hyp; split; intros ex ey;
unfold FTZ_exp;
unfold Prec_gt_0 in *;
destruct (Z.ltb_spec (ex + ey - prec') emin');
destruct (Z.ltb_spec (ex - prec) emin);
destruct (Z.ltb_spec (ey - prec) emin);
destruct (Z.ltb_spec (ex + ey - 1 - prec') emin');
lia.
Qed.

End Double_round_mult_FTZ.

End Double_round_mult.

Section Double_round_plus.

Lemma mag_plus_disj :
  forall x y,
  0 < y -> y <= x ->
  ((mag (x + y) = mag x :> Z)
   \/ (mag (x + y) = (mag x + 1)%Z :> Z)).
Proof.
intros x y Py Hxy.
destruct (mag_plus beta x y Py Hxy).
lia.
Qed.

Lemma mag_plus_separated :
  forall fexp : Z -> Z,
  forall x y,
  0 < x -> 0 <= y ->
  generic_format beta fexp x ->
  (mag y <= fexp (mag x))%Z ->
  (mag (x + y) = mag x :> Z).
Proof.
intros fexp x y Px Nny Fx Hsep.
apply mag_plus_eps with (1 := Px) (2 := Fx).
apply (conj Nny).
rewrite <- Rabs_pos_eq with (1 := Nny).
apply Rlt_le_trans with (1 := bpow_mag_gt beta _).
rewrite ulp_neq_0 by now apply Rgt_not_eq.
now apply bpow_le.
Qed.

Lemma mag_minus_disj :
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= mag x - 2)%Z ->
  ((mag (x - y) = mag x :> Z)
   \/ (mag (x - y) = (mag x - 1)%Z :> Z)).
Proof.
intros x y Px Py Hln.
assert (Hxy : y < x); [now apply (lt_mag beta); [ |lia]|].
generalize (mag_minus beta x y Py Hxy); intro Hln2.
generalize (mag_minus_lb beta x y Px Py Hln); intro Hln3.
lia.
Qed.

Lemma mag_minus_separated :
  forall fexp : Z -> Z, Valid_exp fexp ->
  forall x y,
  0 < x -> 0 < y -> y < x ->
  bpow (mag x - 1) < x ->
  generic_format beta fexp x -> (mag y <= fexp (mag x))%Z ->
  (mag (x - y) = mag x :> Z).
Proof.
intros fexp Vfexp x y Px Py Yltx Xgtpow Fx Ly.
apply mag_unique.
split.
- apply Rabs_ge; right.
  assert (Hy : y < ulp beta fexp (bpow (mag x - 1))).
  { rewrite ulp_bpow.
    replace (_ + _)%Z with (mag x : Z) by ring.
    rewrite <- (Rabs_right y); [|now apply Rle_ge; apply Rlt_le].
    apply Rlt_le_trans with (bpow (mag y)).
    - apply bpow_mag_gt.
    - now apply bpow_le. }
  apply (Rplus_le_reg_r y); ring_simplify.
  apply Rle_trans with (bpow (mag x - 1)
                        + ulp beta fexp (bpow (mag x - 1))).
  + now apply Rplus_le_compat_l; apply Rlt_le.
  + rewrite <- succ_eq_pos;[idtac|apply bpow_ge_0].
    apply succ_le_lt; [apply Vfexp|idtac|exact Fx|assumption].
    apply (generic_format_bpow beta fexp (mag x - 1)).
    replace (_ + _)%Z with (mag x : Z) by ring.
    cut (fexp (mag x) < mag x)%Z. lia.
    now apply mag_generic_gt; [|now apply Rgt_not_eq|].
- rewrite Rabs_right.
  + apply Rlt_trans with x.
    * rewrite <- (Rplus_0_r x) at 2.
      apply Rplus_lt_compat_l.
      rewrite <- Ropp_0.
      now apply Ropp_lt_contravar.
    * apply Rabs_lt_inv.
      apply bpow_mag_gt.
  + lra.
Qed.

Definition round_round_plus_hyp fexp1 fexp2 :=
  (forall ex ey, (fexp1 (ex + 1) - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (fexp1 (ex - 1) + 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (fexp1 ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z).

Lemma round_round_plus_aux0_aux_aux :
  forall (fexp1 fexp2 : Z -> Z),
  forall x y,
  (fexp1 (mag x) <= fexp1 (mag y))%Z ->
  (fexp2 (mag (x + y))%Z <= fexp1 (mag x))%Z ->
  (fexp2 (mag (x + y))%Z <= fexp1 (mag y))%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof.
intros fexp1 fexp2 x y Oxy Hlnx Hlny Fx Fy.
destruct (Req_dec x 0) as [Zx|Nzx].
- (* x = 0 *)
  rewrite Zx, Rplus_0_l in Hlny |- *.
  now apply (generic_inclusion_mag beta fexp1).
- (* x <> 0 *)
  destruct (Req_dec y 0) as [Zy|Nzy].
  + (* y = 0 *)
    rewrite Zy, Rplus_0_r in Hlnx |- *.
    now apply (generic_inclusion_mag beta fexp1).
  + (* y <> 0 *)
    revert Fx Fy.
    unfold generic_format at -3, cexp, F2R; simpl.
    set (mx := Ztrunc (scaled_mantissa beta fexp1 x)).
    set (my := Ztrunc (scaled_mantissa beta fexp1 y)).
    intros Fx Fy.
    set (fxy := Float beta (mx + my * (beta ^ (fexp1 (mag y)
                                               - fexp1 (mag x))))
                      (fexp1 (mag x))).
    assert (Hxy : x + y = F2R fxy).
    { unfold fxy, F2R; simpl.
      rewrite plus_IZR.
      rewrite Rmult_plus_distr_r.
      rewrite <- Fx.
      rewrite mult_IZR.
      rewrite IZR_Zpower by lia.
      bpow_simplify.
      now rewrite <- Fy. }
    apply generic_format_F2R' with (f := fxy); [now rewrite Hxy|].
    intros _.
    now unfold cexp, fxy; simpl.
Qed.

Lemma round_round_plus_aux0_aux :
  forall (fexp1 fexp2 : Z -> Z),
  forall x y,
  (fexp2 (mag (x + y))%Z <= fexp1 (mag x))%Z ->
  (fexp2 (mag (x + y))%Z <= fexp1 (mag y))%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof.
intros fexp1 fexp2 x y Hlnx Hlny Fx Fy.
destruct (Z.le_gt_cases (fexp1 (mag x)) (fexp1 (mag y))) as [Hle|Hgt].
- now apply (round_round_plus_aux0_aux_aux fexp1).
- rewrite Rplus_comm in Hlnx, Hlny |- *.
  now apply (round_round_plus_aux0_aux_aux fexp1); [lia| | | |].
Qed.

(* fexp1 (mag x) - 1 <= mag y :
 * addition is exact in the largest precision (fexp2). *)
Lemma round_round_plus_aux0 :
  forall (fexp1 fexp2 : Z -> Z), Valid_exp fexp1 ->
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  (0 < x)%R -> (0 < y)%R -> (y <= x)%R ->
  (fexp1 (mag x) - 1 <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof.
intros fexp1 fexp2 Vfexp1 Hexp x y Px Py Hyx Hln Fx Fy.
assert (Nny : (0 <= y)%R); [now apply Rlt_le|].
destruct Hexp as (_,(Hexp2,(Hexp3,Hexp4))).
destruct (Z.le_gt_cases (mag y) (fexp1 (mag x))) as [Hle|Hgt].
- (* mag y <= fexp1 (mag x) *)
  assert (Lxy : mag (x + y) = mag x :> Z);
  [now apply (mag_plus_separated fexp1)|].
  apply (round_round_plus_aux0_aux fexp1);
    [| |assumption|assumption]; rewrite Lxy.
  + now apply Hexp4; lia.
  + now apply Hexp3; lia.
- (* fexp1 (mag x) < mag y *)
  apply (round_round_plus_aux0_aux fexp1); [| |assumption|assumption].
  destruct (mag_plus_disj x y Py Hyx) as [Lxy|Lxy]; rewrite Lxy.
  + now apply Hexp4; lia.
  + apply Hexp2; apply (mag_le beta y x Py) in Hyx.
    replace (_ - _)%Z with (mag x : Z) by ring.
    lia.
  + destruct (mag_plus_disj x y Py Hyx) as [Lxy|Lxy]; rewrite Lxy.
    * now apply Hexp3; lia.
    * apply Hexp2.
      replace (_ - _)%Z with (mag x : Z) by ring.
      lia.
Qed.

Lemma round_round_plus_aux1_aux :
  forall k, (0 < k)%Z ->
  forall (fexp : Z -> Z),
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= fexp (mag x) - k)%Z ->
  (mag (x + y) = mag x :> Z) ->
  generic_format beta fexp x ->
  0 < (x + y) - round beta fexp Zfloor (x + y) < bpow (fexp (mag x) - k).
Proof.
assert (Hbeta : (2 <= beta)%Z).
{ destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le. }
intros k Hk fexp x y Px Py Hln Hlxy Fx.
revert Fx.
unfold round, generic_format, F2R, scaled_mantissa, cexp; simpl.
rewrite Hlxy.
set (mx := Ztrunc (x * bpow (- fexp (mag x)))).
intros Fx.
assert (R : (x + y) * bpow (- fexp (mag x))
            = IZR mx + y * bpow (- fexp (mag x))).
{ rewrite Fx at 1.
  rewrite Rmult_plus_distr_r.
  now bpow_simplify. }
rewrite R.
assert (LB : 0 < y * bpow (- fexp (mag x))).
{ rewrite <- (Rmult_0_r y).
  now apply Rmult_lt_compat_l; [|apply bpow_gt_0]. }
assert (UB : y * bpow (- fexp (mag x)) < / IZR (beta ^ k)).
{ apply Rlt_le_trans with (bpow (mag y) * bpow (- fexp (mag x))).
  - apply Rmult_lt_compat_r; [now apply bpow_gt_0|].
    rewrite <- (Rabs_right y) at 1; [|now apply Rle_ge; apply Rlt_le].
    apply bpow_mag_gt.
  - apply Rle_trans with (bpow (fexp (mag x) - k)
                          * bpow (- fexp (mag x)))%R.
    + apply Rmult_le_compat_r; [now apply bpow_ge_0|].
      now apply bpow_le.
    + bpow_simplify.
      rewrite bpow_opp.
      destruct k.
      * lia.
      * simpl; unfold Raux.bpow, Z.pow_pos.
        now apply Rle_refl.
      * casetype False; apply (Z.lt_irrefl 0).
        apply (Z.lt_trans _ _ _ Hk).
        apply Zlt_neg_0. }
rewrite (Zfloor_imp mx).
{ split; ring_simplify.
  - apply (Rmult_lt_reg_r (bpow (- fexp (mag x)))); [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r, Rmult_0_l.
    bpow_simplify.
    rewrite R; ring_simplify.
    now apply Rmult_lt_0_compat; [|apply bpow_gt_0].
  - apply (Rmult_lt_reg_r (bpow (- fexp (mag x)))); [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    rewrite R; ring_simplify.
    apply (Rlt_le_trans _ _ _ UB).
    rewrite bpow_opp.
    apply Rinv_le; [now apply bpow_gt_0|].
    now rewrite IZR_Zpower; [right|lia]. }
split.
- rewrite <- Rplus_0_r at 1; apply Rplus_le_compat_l.
  now apply Rlt_le.
- rewrite plus_IZR; apply Rplus_lt_compat_l.
  apply (Rmult_lt_reg_r (bpow (fexp (mag x)))); [now apply bpow_gt_0|].
  rewrite Rmult_1_l.
  bpow_simplify.
  apply Rlt_trans with (bpow (mag y)).
  + rewrite <- Rabs_right at 1; [|now apply Rle_ge; apply Rlt_le].
    apply bpow_mag_gt.
  + apply bpow_lt; lia.
Qed.

(* mag y <= fexp1 (mag x) - 2 : round_round_lt_mid applies. *)
Lemma round_round_plus_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= fexp1 (mag x) - 2)%Z ->
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof.
assert (Hbeta : (2 <= beta)%Z).
{ destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le. }
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Hly Fx.
assert (Lxy : mag (x + y) = mag x :> Z);
  [now apply (mag_plus_separated fexp1); [|apply Rlt_le| |lia]|].
destruct Hexp as (_,(_,(_,Hexp4))).
assert (Hf2 : (fexp2 (mag x) <= fexp1 (mag x))%Z);
  [now apply Hexp4; lia|].
assert (Bpow2 : bpow (- 2) <= / 2 * / 2).
{ replace (/2 * /2) with (/4) by field.
  rewrite (bpow_opp _ 2).
  apply Rinv_le; [lra|].
  apply (IZR_le (2 * 2) (beta * (beta * 1))).
  rewrite Zmult_1_r.
  now apply Zmult_le_compat; lia. }
assert (P2 : (0 < 2)%Z) by lia.
unfold round_round_eq.
apply round_round_lt_mid.
- exact Vfexp1.
- exact Vfexp2.
- lra.
- now rewrite Lxy.
- rewrite Lxy.
  cut (fexp1 (mag x) < mag x)%Z. lia.
  now apply mag_generic_gt; [|apply Rgt_not_eq|].
- unfold midp.
  apply (Rplus_lt_reg_r (- round beta fexp1 Zfloor (x + y))).
  apply (Rlt_le_trans _ _ _ (proj2 (round_round_plus_aux1_aux 2 P2 fexp1 x y Px
                                                               Py Hly Lxy Fx))).
  ring_simplify.
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold cexp; rewrite Lxy.
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag x)))); [now apply bpow_gt_0|].
  bpow_simplify.
  apply (Rle_trans _ _ _ Bpow2).
  rewrite <- (Rmult_1_r (/ 2)) at 3.
  apply Rmult_le_compat_l; lra.
- rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold round, F2R, scaled_mantissa, cexp; simpl; rewrite Lxy.
  intro Hf2'.
  apply (Rmult_lt_reg_r (bpow (- fexp1 (mag x))));
    [now apply bpow_gt_0|].
  apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
  bpow_simplify.
  apply (Rplus_lt_reg_r (- round beta fexp1 Zfloor (x + y))).
  unfold midp; ring_simplify.
  apply (Rlt_le_trans _ _ _ (proj2 (round_round_plus_aux1_aux 2 P2 fexp1 x y Px
                                                               Py Hly Lxy Fx))).
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag x)))); [now apply bpow_gt_0|].
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold cexp; rewrite Lxy, Rmult_minus_distr_r; bpow_simplify.
  apply (Rle_trans _ _ _ Bpow2).
  rewrite <- (Rmult_1_r (/ 2)) at 3; rewrite <- Rmult_minus_distr_l.
  apply Rmult_le_compat_l; [lra|].
  apply (Rplus_le_reg_r (- 1)); ring_simplify.
  replace (_ - _) with (- (/ 2)) by lra.
  apply Ropp_le_contravar.
  { apply Rle_trans with (bpow (- 1)).
    - apply bpow_le; lia.
    - unfold Raux.bpow, Z.pow_pos; simpl.
      apply Rinv_le; [lra|].
      apply IZR_le; lia. }
Qed.

(* round_round_plus_aux{0,1} together *)
Lemma round_round_plus_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y -> y <= x ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Hyx Fx Fy.
unfold round_round_eq.
destruct (Zle_or_lt (mag y) (fexp1 (mag x) - 2)) as [Hly|Hly].
- (* mag y <= fexp1 (mag x) - 2 *)
  now apply round_round_plus_aux1.
- (* fexp1 (mag x) - 2 < mag y *)
  rewrite (round_generic beta fexp2).
  + reflexivity.
  + now apply valid_rnd_N.
  + assert (Hf1 : (fexp1 (mag x) - 1 <= mag y)%Z) by lia.
    now apply (round_round_plus_aux0 fexp1).
Qed.

Lemma round_round_plus_aux :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Nnx Nny Fx Fy.
unfold round_round_eq.
destruct (Req_dec x 0) as [Zx|Nzx].
- (* x = 0 *)
  destruct Hexp as (_,(_,(_,Hexp4))).
  rewrite Zx; rewrite Rplus_0_l.
  rewrite (round_generic beta fexp2).
  + reflexivity.
  + now apply valid_rnd_N.
  + apply (generic_inclusion_mag beta fexp1).
    now intros _; apply Hexp4; lia.
    exact Fy.
- (* x <> 0 *)
  destruct (Req_dec y 0) as [Zy|Nzy].
  + (* y = 0 *)
    destruct Hexp as (_,(_,(_,Hexp4))).
    rewrite Zy; rewrite Rplus_0_r.
    rewrite (round_generic beta fexp2).
    * reflexivity.
    * now apply valid_rnd_N.
    * apply (generic_inclusion_mag beta fexp1).
      now intros _; apply Hexp4; lia.
      exact Fx.
  + (* y <> 0 *)
    assert (Px : 0 < x); [lra|].
    assert (Py : 0 < y); [lra|].
    destruct (Rlt_or_le x y) as [H|H].
    * (* x < y *)
      apply Rlt_le in H.
      rewrite Rplus_comm.
      now apply round_round_plus_aux2.
    * now apply round_round_plus_aux2.
Qed.

Lemma round_round_minus_aux0_aux :
  forall (fexp1 fexp2 : Z -> Z),
  forall x y,
  (fexp2 (mag (x - y))%Z <= fexp1 (mag x))%Z ->
  (fexp2 (mag (x - y))%Z <= fexp1 (mag y))%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof.
intros fexp1 fexp2 x y.
replace (x - y)%R with (x + (- y))%R; [|ring].
intros Hlnx Hlny Fx Fy.
rewrite <- (mag_opp beta y) in Hlny.
apply generic_format_opp in Fy.
now apply (round_round_plus_aux0_aux fexp1).
Qed.

(* fexp1 (mag x) - 1 <= mag y :
 * substraction is exact in the largest precision (fexp2). *)
Lemma round_round_minus_aux0 :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (fexp1 (mag x) - 1 <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof.
intros fexp1 fexp2 Hexp x y Py Hyx Hln Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hyx).
destruct Hexp as (Hexp1,(_,(Hexp3,Hexp4))).
assert (Lyx : (mag y <= mag x)%Z);
  [now apply mag_le; [|apply Rlt_le]|].
destruct (Z.lt_ge_cases (mag x - 2) (mag y)) as [Hlt|Hge].
- (* mag x - 2 < mag y *)
  assert (Hor : (mag y = mag x :> Z) \/ (mag y = mag x - 1 :> Z)%Z) by lia.
  destruct Hor as [Heq|Heqm1].
  + (* mag y = mag x *)
    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    * apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
    * rewrite Heq.
      apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
  + (* mag y = mag x - 1 *)
    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    * apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
    * rewrite Heqm1.
      apply Hexp4.
      apply Zplus_le_compat_r.
      now apply mag_minus.
- (* mag y <= mag x - 2 *)
  destruct (mag_minus_disj x y Px Py Hge) as [Lxmy|Lxmy].
  + (* mag (x - y) = mag x *)
    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    * apply Hexp4.
      lia.
    * now rewrite Lxmy; apply Hexp3.
  + (* mag (x - y) = mag x - 1 *)
    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy];
    rewrite Lxmy.
    * apply Hexp1.
      replace (_ + _)%Z with (mag x : Z); [|ring].
      now apply Z.le_trans with (mag y).
    * apply Hexp1.
      now replace (_ + _)%Z with (mag x : Z); [|ring].
Qed.

(* mag y <= fexp1 (mag x) - 2,
 * fexp1 (mag (x - y)) - 1 <= mag y :
 * substraction is exact in the largest precision (fexp2). *)
Lemma round_round_minus_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp1 (mag x) - 2)%Z ->
  (fexp1 (mag (x - y)) - 1 <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2  Hexp x y Py Hyx Hln Hln' Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hyx).
destruct Hexp as (Hexp1,(Hexp2,(Hexp3,Hexp4))).
assert (Lyx : (mag y <= mag x)%Z);
  [now apply mag_le; [|apply Rlt_le]|].
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
- apply Z.le_trans with (fexp1 (mag (x - y))).
  + apply Hexp4; lia.
  + lia.
- now apply Hexp3.
Qed.

Lemma round_round_minus_aux2_aux :
  forall (fexp : Z -> Z),
  Valid_exp fexp ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp (mag x) - 1)%Z ->
  generic_format beta fexp x ->
  generic_format beta fexp y ->
  round beta fexp Zceil (x - y) - (x - y) <= y.
Proof.
intros fexp Vfexp x y Py Hxy Hly Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hxy).
revert Fx.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp (mag x)))).
intro Fx.
assert (Hfx : (fexp (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
destruct (Rlt_or_le (bpow (mag x - 1)) x) as [Hx|Hx].
- (* bpow (mag x - 1) < x *)
  assert (Lxy : mag (x - y) = mag x :> Z);
    [now apply (mag_minus_separated fexp); [| | | | | |lia]|].
  assert (Rxy : round beta fexp Zceil (x - y) = x).
  { unfold round, F2R, scaled_mantissa, cexp; simpl.
    rewrite Lxy.
    apply eq_sym; rewrite Fx at 1; apply eq_sym.
    apply Rmult_eq_compat_r.
    apply f_equal.
    rewrite Fx at 1.
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    apply Zceil_imp.
    split.
    - unfold Zminus; rewrite plus_IZR.
      apply Rplus_lt_compat_l.
      apply Ropp_lt_contravar; simpl.
      apply (Rmult_lt_reg_r (bpow (fexp (mag x))));
        [now apply bpow_gt_0|].
      rewrite Rmult_1_l; bpow_simplify.
      apply Rlt_le_trans with (bpow (mag y)).
      + rewrite <- Rabs_right at 1; [|now apply Rle_ge; apply Rlt_le].
        apply bpow_mag_gt.
      + apply bpow_le.
        lia.
    - rewrite <- (Rplus_0_r (IZR _)) at 2.
      apply Rplus_le_compat_l.
      rewrite <- Ropp_0; apply Ropp_le_contravar.
      rewrite <- (Rmult_0_r y).
      apply Rmult_le_compat_l; [now apply Rlt_le|].
      now apply bpow_ge_0. }
  rewrite Rxy; ring_simplify.
  apply Rle_refl.
- (* x <= bpow (mag x - 1) *)
  assert (Xpow : x = bpow (mag x - 1)).
  { apply Rle_antisym; [exact Hx|].
    destruct (mag x) as (ex, Hex); simpl.
    rewrite <- (Rabs_right x); [|now apply Rle_ge; apply Rlt_le].
    apply Hex.
    now apply Rgt_not_eq. }
  assert (Lxy : (mag (x - y) = mag x - 1 :> Z)%Z).
  { apply Zle_antisym.
    - apply mag_le_bpow.
      + apply Rminus_eq_contra.
        now intro Hx'; rewrite Hx' in Hxy; apply (Rlt_irrefl y).
      + rewrite Rabs_right; lra.
    - apply (mag_minus_lb beta x y Px Py).
      lia. }
  assert (Hfx1 : (fexp (mag x - 1) < mag x - 1)%Z);
    [now apply (valid_exp_large fexp (mag y)); [|lia]|].
  assert (Rxy : round beta fexp Zceil (x - y) <= x).
  { rewrite Xpow at 2.
    unfold round, F2R, scaled_mantissa, cexp; simpl.
    rewrite Lxy.
    apply (Rmult_le_reg_r (bpow (- fexp (mag x - 1)%Z)));
      [now apply bpow_gt_0|].
    bpow_simplify.
    rewrite <- (IZR_Zpower beta (_ - _ - _)) by lia.
    apply IZR_le.
    apply Zceil_glb.
    rewrite IZR_Zpower by lia.
    rewrite Xpow at 1.
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    rewrite <- (Rplus_0_r (bpow _)) at 2.
    apply Rplus_le_compat_l.
    rewrite <- Ropp_0; apply Ropp_le_contravar.
    rewrite <- (Rmult_0_r y).
    apply Rmult_le_compat_l; [now apply Rlt_le|].
    now apply bpow_ge_0. }
  lra.
Qed.

(* mag y <= fexp1 (mag x) - 2 :
 * mag y <= fexp1 (mag (x - y)) - 2 :
 * round_round_gt_mid applies. *)
Lemma round_round_minus_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp1 (mag x) - 2)%Z ->
  (mag y <= fexp1 (mag (x - y)) - 2)%Z ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof.
assert (Hbeta : (2 <= beta)%Z).
{ destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le. }
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hxy Hly Hly' Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hxy).
destruct Hexp as (_,(_,(_,Hexp4))).
assert (Hf2 : (fexp2 (mag x) <= fexp1 (mag x))%Z);
  [now apply Hexp4; lia|].
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Bpow2 : bpow (- 2) <= / 2 * / 2).
{ replace (/2 * /2) with (/4) by field.
  rewrite (bpow_opp _ 2).
  apply Rinv_le; [lra|].
  apply (IZR_le (2 * 2) (beta * (beta * 1))).
  rewrite Zmult_1_r.
  now apply Zmult_le_compat; lia. }
assert (Ly : y < bpow (mag y)).
{ apply Rabs_lt_inv.
  apply bpow_mag_gt. }
unfold round_round_eq.
apply round_round_gt_mid.
- exact Vfexp1.
- exact Vfexp2.
- lra.
- apply Hexp4; lia.
- cut (fexp1 (mag (x - y)) < mag (x - y))%Z. lia.
  apply (valid_exp_large fexp1 (mag x - 1)).
  + apply (valid_exp_large fexp1 (mag y)); [|lia].
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
  + now apply mag_minus_lb; [| |lia].
- unfold midp'.
  apply (Rplus_lt_reg_r (/ 2 * ulp beta fexp1 (x - y) - (x - y))).
  ring_simplify.
  replace (_ + _) with (round beta fexp1 Zceil (x - y) - (x - y)) by ring.
  apply Rlt_le_trans with (bpow (fexp1 (mag (x - y)) - 2)).
  + apply Rle_lt_trans with y;
    [now apply round_round_minus_aux2_aux; try assumption; lia|].
    apply (Rlt_le_trans _ _ _ Ly).
    now apply bpow_le.
  + rewrite ulp_neq_0;[idtac|now apply sym_not_eq, Rlt_not_eq, Rgt_minus].
    unfold cexp.
    replace (_ - 2)%Z with (fexp1 (mag (x - y)) - 1 - 1)%Z by ring.
    unfold Zminus at 1; rewrite bpow_plus.
    rewrite Rmult_comm.
    apply Rmult_le_compat.
    * now apply bpow_ge_0.
    * now apply bpow_ge_0.
    * unfold Raux.bpow, Z.pow_pos; simpl.
      rewrite Zmult_1_r; apply Rinv_le.
      lra.
      now apply IZR_le.
    * apply bpow_le; lia.
- intro Hf2'.
  unfold midp'.
  apply (Rplus_lt_reg_r (/ 2 * ulp beta fexp1 (x - y) - (x - y)
                         - / 2 * ulp beta fexp2 (x - y))).
  ring_simplify.
  replace (_ + _) with (round beta fexp1 Zceil (x - y) - (x - y)) by ring.
  apply Rle_lt_trans with y;
    [now apply round_round_minus_aux2_aux; try assumption; lia|].
  apply (Rlt_le_trans _ _ _ Ly).
  apply Rle_trans with (bpow (fexp1 (mag (x - y)) - 2));
    [now apply bpow_le|].
  replace (_ - 2)%Z with (fexp1 (mag (x - y)) - 1 - 1)%Z by ring.
  unfold Zminus at 1; rewrite bpow_plus.
  rewrite <- Rmult_minus_distr_l.
  rewrite Rmult_comm; apply Rmult_le_compat.
  + apply bpow_ge_0.
  + apply bpow_ge_0.
  + unfold Raux.bpow, Z.pow_pos; simpl.
    rewrite Zmult_1_r; apply Rinv_le; [lra|].
    now apply IZR_le.
  + rewrite 2!ulp_neq_0; try now apply Rgt_not_eq, Rgt_minus.
    unfold cexp.
    apply (Rplus_le_reg_r (bpow (fexp2 (mag (x - y))))); ring_simplify.
    apply Rle_trans with (2 * bpow (fexp1 (mag (x - y)) - 1)).
    * rewrite double.
      apply Rplus_le_compat_l.
      now apply bpow_le.
    * unfold Zminus; rewrite bpow_plus.
      rewrite Rmult_comm; rewrite Rmult_assoc.
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l; [now apply bpow_ge_0|].
      unfold Raux.bpow, Z.pow_pos; simpl.
      rewrite Zmult_1_r.
      apply IZR_le, Rinv_le in Hbeta.
      simpl in Hbeta.
      lra.
      apply Rlt_0_2.
Qed.

(* round_round_minus_aux{0,1,2} together *)
Lemma round_round_minus_aux3 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y <= x ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hyx Fx Fy.
assert (Px := Rlt_le_trans 0 y x Py Hyx).
unfold round_round_eq.
destruct (Req_dec y x) as [Hy|Hy].
- (* y = x *)
  rewrite Hy; replace (x - x) with 0 by ring.
  rewrite round_0.
  + reflexivity.
  + now apply valid_rnd_N.
- (* y < x *)
  assert (Hyx' : y < x); [lra|].
  destruct (Zle_or_lt (mag y) (fexp1 (mag x) - 2)) as [Hly|Hly].
  + (* mag y <= fexp1 (mag x) - 2 *)
    destruct (Zle_or_lt (mag y) (fexp1 (mag (x - y)) - 2))
      as [Hly'|Hly'].
    * (* mag y <= fexp1 (mag (x - y)) - 2 *)
      now apply round_round_minus_aux2.
    * (* fexp1 (mag (x - y)) - 2 < mag y *)
      { rewrite (round_generic beta fexp2).
        - reflexivity.
        - now apply valid_rnd_N.
        - assert (Hf1 : (fexp1 (mag (x - y)) - 1 <= mag y)%Z) by lia.
          now apply (round_round_minus_aux1 fexp1). }
  + rewrite (round_generic beta fexp2).
    * reflexivity.
    * now apply valid_rnd_N.
    * assert (Hf1 : (fexp1 (mag x) - 1 <= mag y)%Z) by lia.
      now apply (round_round_minus_aux0 fexp1).
Qed.

Lemma round_round_minus_aux :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Nnx Nny Fx Fy.
unfold round_round_eq.
destruct (Req_dec x 0) as [Zx|Nzx].
- (* x = 0 *)
  rewrite Zx; unfold Rminus; rewrite Rplus_0_l.
  do 3 rewrite round_N_opp.
  rewrite (round_generic beta fexp2).
  * reflexivity.
  * now apply valid_rnd_N.
  * apply (generic_inclusion_mag beta fexp1).
    destruct Hexp as (_,(_,(_,Hexp4))).
    now intros _; apply Hexp4; lia.
    exact Fy.
- (* x <> 0 *)
  destruct (Req_dec y 0) as [Zy|Nzy].
  + (* y = 0 *)
    rewrite Zy; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
    rewrite (round_generic beta fexp2).
    * reflexivity.
    * now apply valid_rnd_N.
    * apply (generic_inclusion_mag beta fexp1).
      destruct Hexp as (_,(_,(_,Hexp4))).
      now intros _; apply Hexp4; lia.
      exact Fx.
  + (* y <> 0 *)
    assert (Px : 0 < x); [lra|].
    assert (Py : 0 < y); [lra|].
    destruct (Rlt_or_le x y) as [H|H].
    * (* x < y *)
      apply Rlt_le in H.
      replace (x - y) with (- (y - x)) by ring.
      do 3 rewrite round_N_opp.
      apply Ropp_eq_compat.
      now apply round_round_minus_aux3.
    * (* y <= x *)
      now apply round_round_minus_aux3.
Qed.

Lemma round_round_plus :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold round_round_eq.
destruct (Rlt_or_le x 0) as [Sx|Sx]; destruct (Rlt_or_le y 0) as [Sy|Sy].
- (* x < 0, y < 0 *)
  replace (x + y) with (- (- x - y)); [|ring].
  do 3 rewrite round_N_opp.
  apply Ropp_eq_compat.
  assert (Px : 0 <= - x); [lra|].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fx.
  apply generic_format_opp in Fy.
  now apply round_round_plus_aux.
- (* x < 0, 0 <= y *)
  replace (x + y) with (y - (- x)); [|ring].
  assert (Px : 0 <= - x); [lra|].
  apply generic_format_opp in Fx.
  now apply round_round_minus_aux.
- (* 0 <= x, y < 0 *)
  replace (x + y) with (x - (- y)); [|ring].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fy.
  now apply round_round_minus_aux.
- (* 0 <= x, 0 <= y *)
  now apply round_round_plus_aux.
Qed.

Lemma round_round_minus :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold Rminus.
apply generic_format_opp in Fy.
now apply round_round_plus.
Qed.

Section Double_round_plus_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_plus_hyp :
  (2 * prec + 1 <= prec')%Z ->
  round_round_plus_hyp (FLX_exp prec) (FLX_exp prec').
Proof.
intros Hprec.
unfold FLX_exp.
unfold round_round_plus_hyp; split; [|split; [|split]];
intros ex ey; try lia.
unfold Prec_gt_0 in prec_gt_0_.
lia.
Qed.

Theorem round_round_plus_FLX :
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x + y).
Proof.
intros choice1 choice2 Hprec x y Fx Fy.
apply round_round_plus.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- now apply FLX_round_round_plus_hyp.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

Theorem round_round_minus_FLX :
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x - y).
Proof.
intros choice1 choice2 Hprec x y Fx Fy.
apply round_round_minus.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- now apply FLX_round_round_plus_hyp.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

End Double_round_plus_FLX.

Section Double_round_plus_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_plus_hyp :
  (emin' <= emin)%Z -> (2 * prec + 1 <= prec')%Z ->
  round_round_plus_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof.
intros Hemin Hprec.
unfold FLT_exp.
unfold round_round_plus_hyp; split; [|split; [|split]]; intros ex ey.
- generalize (Zmax_spec (ex + 1 - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
- generalize (Zmax_spec (ex - 1 - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
- unfold Prec_gt_0 in prec_gt_0_.
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
Qed.

Theorem round_round_plus_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x + y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_plus.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- now apply FLT_round_round_plus_hyp.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

Theorem round_round_minus_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x - y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_minus.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- now apply FLT_round_round_plus_hyp.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

End Double_round_plus_FLT.

Section Double_round_plus_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_plus_hyp :
  (emin' + prec' <= emin + 1)%Z -> (2 * prec + 1 <= prec')%Z ->
  round_round_plus_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in *.
unfold round_round_plus_hyp; split; [|split; [|split]]; intros ex ey.
- destruct (Z.ltb_spec (ex + 1 - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - 1 - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
Qed.

Theorem round_round_plus_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x + y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_plus.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- now apply FTZ_round_round_plus_hyp.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

Theorem round_round_minus_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec + 1 <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x - y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_minus.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- now apply FTZ_round_round_plus_hyp.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

End Double_round_plus_FTZ.

Section Double_round_plus_radix_ge_3.

Definition round_round_plus_radix_ge_3_hyp fexp1 fexp2 :=
  (forall ex ey, (fexp1 (ex + 1) <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (fexp1 (ex - 1) + 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (fexp1 ex <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)
  /\ (forall ex ey, (ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z).

(* fexp1 (mag x) <= mag y :
 * addition is exact in the largest precision (fexp2). *)
Lemma round_round_plus_radix_ge_3_aux0 :
  forall (fexp1 fexp2 : Z -> Z), Valid_exp fexp1 ->
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  (0 < y)%R -> (y <= x)%R ->
  (fexp1 (mag x) <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x + y).
Proof.
intros fexp1 fexp2 Vfexp1 Hexp x y Py Hyx Hln Fx Fy.
assert (Px := Rlt_le_trans 0 y x Py Hyx).
assert (Nny : (0 <= y)%R); [now apply Rlt_le|].
destruct Hexp as (_,(Hexp2,(Hexp3,Hexp4))).
destruct (Z.le_gt_cases (mag y) (fexp1 (mag x))) as [Hle|Hgt].
- (* mag y <= fexp1 (mag x) *)
  assert (Lxy : mag (x + y) = mag x :> Z);
  [now apply (mag_plus_separated fexp1)|].
  apply (round_round_plus_aux0_aux fexp1);
    [| |assumption|assumption]; rewrite Lxy.
  + now apply Hexp4; lia.
  + now apply Hexp3; lia.
- (* fexp1 (mag x) < mag y *)
  apply (round_round_plus_aux0_aux fexp1); [| |assumption|assumption].
  destruct (mag_plus_disj x y Py Hyx) as [Lxy|Lxy]; rewrite Lxy.
  + now apply Hexp4; lia.
  + apply Hexp2; apply (mag_le beta y x Py) in Hyx.
    replace (_ - _)%Z with (mag x : Z) by ring.
    lia.
  + destruct (mag_plus_disj x y Py Hyx) as [Lxy|Lxy]; rewrite Lxy.
    * now apply Hexp3; lia.
    * apply Hexp2.
      replace (_ - _)%Z with (mag x : Z) by ring.
      lia.
Qed.

(* mag y <= fexp1 (mag x) - 1 : round_round_lt_mid applies. *)
Lemma round_round_plus_radix_ge_3_aux1 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  (mag y <= fexp1 (mag x) - 1)%Z ->
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Hly Fx.
assert (Lxy : mag (x + y) = mag x :> Z);
  [now apply (mag_plus_separated fexp1); [|apply Rlt_le| |lia]|].
destruct Hexp as (_,(_,(_,Hexp4))).
assert (Hf2 : (fexp2 (mag x) <= fexp1 (mag x))%Z);
  [now apply Hexp4; lia|].
assert (Bpow3 : bpow (- 1) <= / 3).
{ unfold Raux.bpow, Z.pow_pos; simpl.
  rewrite Zmult_1_r.
  apply Rinv_le; [lra|].
  now apply IZR_le. }
assert (P1 : (0 < 1)%Z) by lia.
unfold round_round_eq.
apply round_round_lt_mid.
- exact Vfexp1.
- exact Vfexp2.
- lra.
- now rewrite Lxy.
- rewrite Lxy.
  cut (fexp1 (mag x) < mag x)%Z. lia.
  now apply mag_generic_gt; [|apply Rgt_not_eq|].
- unfold midp.
  apply (Rplus_lt_reg_r (- round beta fexp1 Zfloor (x + y))).
  apply (Rlt_le_trans _ _ _ (proj2 (round_round_plus_aux1_aux 1 P1 fexp1 x y Px
                                                               Py Hly Lxy Fx))).
  ring_simplify.
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold cexp; rewrite Lxy.
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
    [now apply bpow_gt_0|].
  bpow_simplify.
  apply (Rle_trans _ _ _ Bpow3); lra.
- rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold round, F2R, scaled_mantissa, cexp; simpl; rewrite Lxy.
  intro Hf2'.
  unfold midp.
  apply (Rplus_lt_reg_r (- round beta fexp1 Zfloor (x + y))); ring_simplify.
  rewrite <- Rmult_minus_distr_l.
  apply (Rlt_le_trans _ _ _ (proj2 (round_round_plus_aux1_aux 1 P1 fexp1 x y Px
                                                               Py Hly Lxy Fx))).
  rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rplus_lt_0_compat].
  unfold cexp; rewrite Lxy.
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
    [now apply bpow_gt_0|].
  rewrite (Rmult_assoc (/ 2)).
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  apply (Rle_trans _ _ _ Bpow3).
  apply Rle_trans with (/ 2 * (2 / 3)); [lra|].
  apply Rmult_le_compat_l; [lra|].
  apply (Rplus_le_reg_r (- 1)); ring_simplify.
  replace (_ - _) with (- (/ 3)) by lra.
  apply Ropp_le_contravar.
  now apply Rle_trans with (bpow (- 1)); [apply bpow_le; lia|].
Qed.

(* round_round_plus_radix_ge_3_aux{0,1} together *)
Lemma round_round_plus_radix_ge_3_aux2 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y <= x ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hyx Fx Fy.
assert (Px := Rlt_le_trans 0 y x Py Hyx).
unfold round_round_eq.
destruct (Zle_or_lt (mag y) (fexp1 (mag x) - 1)) as [Hly|Hly].
- (* mag y <= fexp1 (mag x) - 1 *)
  now apply round_round_plus_radix_ge_3_aux1.
- (* fexp1 (mag x) - 1 < mag y *)
  rewrite (round_generic beta fexp2).
  + reflexivity.
  + now apply valid_rnd_N.
  + assert (Hf1 : (fexp1 (mag x) <= mag y)%Z) by lia.
    now apply (round_round_plus_radix_ge_3_aux0 fexp1).
Qed.

Lemma round_round_plus_radix_ge_3_aux :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Nnx Nny Fx Fy.
unfold round_round_eq.
destruct (Req_dec x 0) as [Zx|Nzx].
- (* x = 0 *)
  destruct Hexp as (_,(_,(_,Hexp4))).
  rewrite Zx; rewrite Rplus_0_l.
  rewrite (round_generic beta fexp2).
  + reflexivity.
  + now apply valid_rnd_N.
  + apply (generic_inclusion_mag beta fexp1).
    now intros _; apply Hexp4; lia.
    exact Fy.
- (* x <> 0 *)
  destruct (Req_dec y 0) as [Zy|Nzy].
  + (* y = 0 *)
    destruct Hexp as (_,(_,(_,Hexp4))).
    rewrite Zy; rewrite Rplus_0_r.
    rewrite (round_generic beta fexp2).
    * reflexivity.
    * now apply valid_rnd_N.
    * apply (generic_inclusion_mag beta fexp1).
      now intros _; apply Hexp4; lia.
      exact Fx.
  + (* y <> 0 *)
    assert (Px : 0 < x); [lra|].
    assert (Py : 0 < y); [lra|].
    destruct (Rlt_or_le x y) as [H|H].
    * (* x < y *)
      apply Rlt_le in H.
      rewrite Rplus_comm.
      now apply round_round_plus_radix_ge_3_aux2.
    * now apply round_round_plus_radix_ge_3_aux2.
Qed.

(* fexp1 (mag x) <= mag y :
 * substraction is exact in the largest precision (fexp2). *)
Lemma round_round_minus_radix_ge_3_aux0 :
  forall (fexp1 fexp2 : Z -> Z),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (fexp1 (mag x) <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof.
intros fexp1 fexp2 Hexp x y Py Hyx Hln Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hyx).
destruct Hexp as (Hexp1,(_,(Hexp3,Hexp4))).
assert (Lyx : (mag y <= mag x)%Z);
  [now apply mag_le; [|apply Rlt_le]|].
destruct (Z.lt_ge_cases (mag x - 2) (mag y)) as [Hlt|Hge].
- (* mag x - 2 < mag y *)
  assert (Hor : (mag y = mag x :> Z) \/ (mag y = mag x - 1 :> Z)%Z) by lia.
  destruct Hor as [Heq|Heqm1].
  + (* mag y = mag x *)
    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    * apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
    * rewrite Heq.
      apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
  + (* mag y = mag x - 1 *)
    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    * apply Hexp4.
      apply Z.le_trans with (mag (x - y)); [lia|].
      now apply mag_minus.
    * rewrite Heqm1.
      apply Hexp4.
      apply Zplus_le_compat_r.
      now apply mag_minus.
- (* mag y <= mag x - 2 *)
  destruct (mag_minus_disj x y Px Py Hge) as [Lxmy|Lxmy].
  + (* mag (x - y) = mag x *)
    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
    * apply Hexp4.
      lia.
    * now rewrite Lxmy; apply Hexp3.
  + (* mag (x - y) = mag x - 1 *)
    apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy];
    rewrite Lxmy.
    * apply Hexp1.
      replace (_ + _)%Z with (mag x : Z); [|ring].
      now apply Z.le_trans with (mag y).
    * apply Hexp1.
      now replace (_ + _)%Z with (mag x : Z); [|ring].
Qed.

(* mag y <= fexp1 (mag x) - 1,
 * fexp1 (mag (x - y)) <= mag y :
 * substraction is exact in the largest precision (fexp2). *)
Lemma round_round_minus_radix_ge_3_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag (x - y)) <= mag y)%Z ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  generic_format beta fexp2 (x - y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2  Hexp x y Py Hyx Hln Hln' Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hyx).
destruct Hexp as (Hexp1,(Hexp2,(Hexp3,Hexp4))).
assert (Lyx : (mag y <= mag x)%Z);
  [now apply mag_le; [|apply Rlt_le]|].
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
apply (round_round_minus_aux0_aux fexp1); [| |exact Fx|exact Fy].
- apply Z.le_trans with (fexp1 (mag (x - y))).
  + apply Hexp4; lia.
  + lia.
- now apply Hexp3.
Qed.

(* mag y <= fexp1 (mag x) - 1 :
 * mag y <= fexp1 (mag (x - y)) - 1 :
 * round_round_gt_mid applies. *)
Lemma round_round_minus_radix_ge_3_aux2 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y < x ->
  (mag y <= fexp1 (mag x) - 1)%Z ->
  (mag y <= fexp1 (mag (x - y)) - 1)%Z ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hxy Hly Hly' Fx Fy.
assert (Px := Rlt_trans 0 y x Py Hxy).
destruct Hexp as (_,(_,(_,Hexp4))).
assert (Hf2 : (fexp2 (mag x) <= fexp1 (mag x))%Z);
  [now apply Hexp4; lia|].
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Bpow3 : bpow (- 1) <= / 3).
{ unfold Raux.bpow, Z.pow_pos; simpl.
  rewrite Zmult_1_r.
  apply Rinv_le; [lra|].
  now apply IZR_le. }
assert (Ly : y < bpow (mag y)).
{ apply Rabs_lt_inv.
  apply bpow_mag_gt. }
unfold round_round_eq.
apply round_round_gt_mid.
- exact Vfexp1.
- exact Vfexp2.
- lra.
- apply Hexp4; lia.
- cut (fexp1 (mag (x - y)) < mag (x - y))%Z. lia.
  apply (valid_exp_large fexp1 (mag x - 1)).
  + apply (valid_exp_large fexp1 (mag y)); [|lia].
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
  + now apply mag_minus_lb; [| |lia].
- unfold midp'.
  apply (Rplus_lt_reg_r (/ 2 * ulp beta fexp1 (x - y) - (x - y))).
  ring_simplify.
  replace (_ + _) with (round beta fexp1 Zceil (x - y) - (x - y)) by ring.
  apply Rlt_le_trans with (bpow (fexp1 (mag (x - y)) - 1)).
  + apply Rle_lt_trans with y;
    [now apply round_round_minus_aux2_aux|].
    apply (Rlt_le_trans _ _ _ Ly).
    now apply bpow_le.
  + rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq, Rgt_minus].
    unfold cexp.
    unfold Zminus at 1; rewrite bpow_plus.
    rewrite Rmult_comm.
    apply Rmult_le_compat_r; [now apply bpow_ge_0|].
    unfold Raux.bpow, Z.pow_pos; simpl.
    rewrite Zmult_1_r; apply Rinv_le; [lra|].
    now apply IZR_le; lia.
- intro Hf2'.
  unfold midp'.
  apply (Rplus_lt_reg_r (/ 2 * (ulp beta fexp1 (x - y)
                                - ulp beta fexp2 (x - y)) - (x - y))).
  ring_simplify; rewrite <- Rmult_minus_distr_l.
  replace (_ + _) with (round beta fexp1 Zceil (x - y) - (x - y)) by ring.
  apply Rle_lt_trans with y;
    [now apply round_round_minus_aux2_aux|].
  apply (Rlt_le_trans _ _ _ Ly).
  apply Rle_trans with (bpow (fexp1 (mag (x - y)) - 1));
    [now apply bpow_le|].
  rewrite 2!ulp_neq_0; try now apply Rgt_not_eq, Rgt_minus.
  unfold cexp.
  apply (Rmult_le_reg_r (bpow (- fexp1 (mag (x - y)))));
    [now apply bpow_gt_0|].
  rewrite Rmult_assoc.
  rewrite Rmult_minus_distr_r.
  bpow_simplify.
  apply Rle_trans with (/ 3).
  + unfold Raux.bpow, Z.pow_pos; simpl.
    rewrite Zmult_1_r; apply Rinv_le; [lra|].
    now apply IZR_le.
  + replace (/ 3) with (/ 2 * (2 / 3)) by field.
    apply Rmult_le_compat_l; [lra|].
    apply (Rplus_le_reg_r (- 1)); ring_simplify.
    replace (_ - _) with (- / 3) by field.
    apply Ropp_le_contravar.
    apply Rle_trans with (bpow (- 1)).
    * apply bpow_le; lia.
    * unfold Raux.bpow, Z.pow_pos; simpl.
      rewrite Zmult_1_r; apply Rinv_le; [lra|].
      now apply IZR_le.
Qed.

(* round_round_minus_aux{0,1,2} together *)
Lemma round_round_minus_radix_ge_3_aux3 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 < y -> y <= x ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Py Hyx Fx Fy.
assert (Px := Rlt_le_trans 0 y x Py Hyx).
unfold round_round_eq.
destruct (Req_dec y x) as [Hy|Hy].
- (* y = x *)
  rewrite Hy; replace (x - x) with 0 by ring.
  rewrite round_0.
  + reflexivity.
  + now apply valid_rnd_N.
- (* y < x *)
  assert (Hyx' : y < x); [lra|].
  destruct (Zle_or_lt (mag y) (fexp1 (mag x) - 1)) as [Hly|Hly].
  + (* mag y <= fexp1 (mag x) - 1 *)
    destruct (Zle_or_lt (mag y) (fexp1 (mag (x - y)) - 1))
      as [Hly'|Hly'].
    * (* mag y <= fexp1 (mag (x - y)) - 1 *)
      now apply round_round_minus_radix_ge_3_aux2.
    * (* fexp1 (mag (x - y)) - 1 < mag y *)
      { rewrite (round_generic beta fexp2).
        - reflexivity.
        - now apply valid_rnd_N.
        - assert (Hf1 : (fexp1 (mag (x - y)) <= mag y)%Z) by lia.
          now apply (round_round_minus_radix_ge_3_aux1 fexp1). }
  + rewrite (round_generic beta fexp2).
    * reflexivity.
    * now apply valid_rnd_N.
    * assert (Hf1 : (fexp1 (mag x) <= mag y)%Z) by lia.
      now apply (round_round_minus_radix_ge_3_aux0 fexp1).
Qed.

Lemma round_round_minus_radix_ge_3_aux :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Nnx Nny Fx Fy.
unfold round_round_eq.
destruct (Req_dec x 0) as [Zx|Nzx].
- (* x = 0 *)
  rewrite Zx; unfold Rminus; rewrite Rplus_0_l.
  do 3 rewrite round_N_opp.
  rewrite (round_generic beta fexp2).
  * reflexivity.
  * now apply valid_rnd_N.
  * apply (generic_inclusion_mag beta fexp1).
    destruct Hexp as (_,(_,(_,Hexp4))).
    now intros _; apply Hexp4; lia.
    exact Fy.
- (* x <> 0 *)
  destruct (Req_dec y 0) as [Zy|Nzy].
  + (* y = 0 *)
    rewrite Zy; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
    rewrite (round_generic beta fexp2).
    * reflexivity.
    * now apply valid_rnd_N.
    * apply (generic_inclusion_mag beta fexp1).
      destruct Hexp as (_,(_,(_,Hexp4))).
      now intros _; apply Hexp4; lia.
      exact Fx.
  + (* y <> 0 *)
    assert (Px : 0 < x); [lra|].
    assert (Py : 0 < y); [lra|].
    destruct (Rlt_or_le x y) as [H|H].
    * (* x < y *)
      apply Rlt_le in H.
      replace (x - y) with (- (y - x)) by ring.
      do 3 rewrite round_N_opp.
      apply Ropp_eq_compat.
      now apply round_round_minus_radix_ge_3_aux3.
    * (* y <= x *)
      now apply round_round_minus_radix_ge_3_aux3.
Qed.

Lemma round_round_plus_radix_ge_3 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold round_round_eq.
destruct (Rlt_or_le x 0) as [Sx|Sx]; destruct (Rlt_or_le y 0) as [Sy|Sy].
- (* x < 0, y < 0 *)
  replace (x + y) with (- (- x - y)); [|ring].
  do 3 rewrite round_N_opp.
  apply Ropp_eq_compat.
  assert (Px : 0 <= - x); [lra|].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fx.
  apply generic_format_opp in Fy.
  now apply round_round_plus_radix_ge_3_aux.
- (* x < 0, 0 <= y *)
  replace (x + y) with (y - (- x)); [|ring].
  assert (Px : 0 <= - x); [lra|].
  apply generic_format_opp in Fx.
  now apply round_round_minus_radix_ge_3_aux.
- (* 0 <= x, y < 0 *)
  replace (x + y) with (x - (- y)); [|ring].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fy.
  now apply round_round_minus_radix_ge_3_aux.
- (* 0 <= x, 0 <= y *)
  now apply round_round_plus_radix_ge_3_aux.
Qed.

Lemma round_round_minus_radix_ge_3 :
  (3 <= beta)%Z ->
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_plus_radix_ge_3_hyp fexp1 fexp2 ->
  forall x y,
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold Rminus.
apply generic_format_opp in Fy.
now apply round_round_plus_radix_ge_3.
Qed.

Section Double_round_plus_radix_ge_3_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_plus_radix_ge_3_hyp :
  (2 * prec <= prec')%Z ->
  round_round_plus_radix_ge_3_hyp (FLX_exp prec) (FLX_exp prec').
Proof.
intros Hprec.
unfold FLX_exp.
unfold round_round_plus_radix_ge_3_hyp; split; [|split; [|split]];
intros ex ey; try lia.
unfold Prec_gt_0 in prec_gt_0_.
lia.
Qed.

Theorem round_round_plus_radix_ge_3_FLX :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x + y).
Proof.
intros Hbeta choice1 choice2 Hprec x y Fx Fy.
apply round_round_plus_radix_ge_3.
- exact Hbeta.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- now apply FLX_round_round_plus_radix_ge_3_hyp.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

Theorem round_round_minus_radix_ge_3_FLX :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x - y).
Proof.
intros Hbeta choice1 choice2 Hprec x y Fx Fy.
apply round_round_minus_radix_ge_3.
- exact Hbeta.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- now apply FLX_round_round_plus_radix_ge_3_hyp.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

End Double_round_plus_radix_ge_3_FLX.

Section Double_round_plus_radix_ge_3_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_plus_radix_ge_3_hyp :
  (emin' <= emin)%Z -> (2 * prec <= prec')%Z ->
  round_round_plus_radix_ge_3_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof.
intros Hemin Hprec.
unfold FLT_exp.
unfold round_round_plus_radix_ge_3_hyp; split; [|split; [|split]]; intros ex ey.
- generalize (Zmax_spec (ex + 1 - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
- generalize (Zmax_spec (ex - 1 - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
- unfold Prec_gt_0 in prec_gt_0_.
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ey - prec) emin).
  lia.
Qed.

Theorem round_round_plus_radix_ge_3_FLT :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x + y).
Proof.
intros Hbeta choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_plus_radix_ge_3.
- exact Hbeta.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- now apply FLT_round_round_plus_radix_ge_3_hyp.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

Theorem round_round_minus_radix_ge_3_FLT :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' <= emin)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x - y).
Proof.
intros Hbeta choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_minus_radix_ge_3.
- exact Hbeta.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- now apply FLT_round_round_plus_radix_ge_3_hyp.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

End Double_round_plus_radix_ge_3_FLT.

Section Double_round_plus_radix_ge_3_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_plus_radix_ge_3_hyp :
  (emin' + prec' <= emin + 1)%Z -> (2 * prec <= prec')%Z ->
  round_round_plus_radix_ge_3_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in *.
unfold round_round_plus_radix_ge_3_hyp; split; [|split; [|split]]; intros ex ey.
- destruct (Z.ltb_spec (ex + 1 - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - 1 - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ey - prec) emin);
  lia.
Qed.

Theorem round_round_plus_radix_ge_3_FTZ :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x + y).
Proof.
intros Hbeta choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_plus_radix_ge_3.
- exact Hbeta.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- now apply FTZ_round_round_plus_radix_ge_3_hyp.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

Theorem round_round_minus_radix_ge_3_FTZ :
  (3 <= beta)%Z ->
  forall choice1 choice2,
  (emin' + prec' <= emin + 1)%Z -> (2 * prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x - y).
Proof.
intros Hbeta choice1 choice2 Hemin Hprec x y Fx Fy.
apply round_round_minus_radix_ge_3.
- exact Hbeta.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- now apply FTZ_round_round_plus_radix_ge_3_hyp.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

End Double_round_plus_radix_ge_3_FTZ.

End Double_round_plus_radix_ge_3.

End Double_round_plus.

Lemma round_round_mid_cases :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  (Rabs (x - midp fexp1 x) <= / 2 * (ulp beta fexp2 x) ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1.
unfold round_round_eq, midp.
set (rd := round beta fexp1 Zfloor x).
set (u1 := ulp beta fexp1 x).
set (u2 := ulp beta fexp2 x).
intros Cmid.
destruct (generic_format_EM beta fexp1 x) as [Fx|Nfx].
- (* generic_format beta fexp1 x *)
  rewrite (round_generic beta fexp2); [reflexivity|now apply valid_rnd_N|].
  now apply (generic_inclusion_mag beta fexp1); [lia|].
- (* ~ generic_format beta fexp1 x *)
  assert (Hceil : round beta fexp1 Zceil x = rd + u1);
  [now apply round_UP_DN_ulp|].
  assert (Hf2' : (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z) by lia.
  destruct (Rlt_or_le (x - rd) (/ 2 * (u1 - u2))).
  + (* x - rd < / 2 * (u1 - u2) *)
    apply round_round_lt_mid_further_place; try assumption.
    unfold midp. fold rd; fold u1; fold u2.
    apply (Rplus_lt_reg_r (- rd)); ring_simplify.
    now rewrite <- Rmult_minus_distr_l.
  + (* / 2 * (u1 - u2) <= x - rd *)
    { destruct (Rlt_or_le (/ 2 * (u1 + u2)) (x - rd)).
      - (* / 2 * (u1 + u2) < x - rd *)
        assert (round beta fexp1 Zceil x - x
                < / 2 * (ulp beta fexp1 x - ulp beta fexp2 x)).
        { rewrite Hceil; fold u1; fold u2.
          lra. }
        apply round_round_gt_mid_further_place; try assumption.
        unfold midp'; lra.
      - (* x - rd <= / 2 * (u1 + u2) *)
        apply Cmid, Rabs_le; split; lra. }
Qed.

Section Double_round_sqrt.

Definition round_round_sqrt_hyp fexp1 fexp2 :=
  (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex))%Z)
  /\ (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex - 1))%Z)
  /\ (forall ex, (fexp1 (2 * ex) < 2 * ex)%Z ->
                 (fexp2 ex + ex <= 2 * fexp1 ex - 2)%Z).

Lemma mag_sqrt_disj :
  forall x,
  0 < x ->
  (mag x = 2 * mag (sqrt x) - 1 :> Z)%Z
  \/ (mag x = 2 * mag (sqrt x) :> Z)%Z.
Proof.
intros x Px.
rewrite (mag_sqrt beta x Px).
generalize (Zdiv2_odd_eqn (mag x + 1)).
destruct Z.odd ; intros ; lia.
Qed.

Lemma round_round_sqrt_aux :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  round_round_sqrt_hyp fexp1 fexp2 ->
  forall x,
  0 < x ->
  (fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1)%Z ->
  generic_format beta fexp1 x ->
  / 2 * ulp beta fexp2 (sqrt x) < Rabs (sqrt x - midp fexp1 (sqrt x)).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 Hexp x Px Hf2 Fx.
assert (Hbeta : (2 <= beta)%Z).
{ destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le. }
set (a := round beta fexp1 Zfloor (sqrt x)).
set (u1 := bpow (fexp1 (mag (sqrt x)))).
set (u2 := bpow (fexp2 (mag (sqrt x)))).
set (b := / 2 * (u1 - u2)).
set (b' := / 2 * (u1 + u2)).
unfold midp; rewrite 2!ulp_neq_0; try now apply Rgt_not_eq, sqrt_lt_R0.
apply Rnot_ge_lt; intro H; apply Rge_le in H.
assert (Fa : generic_format beta fexp1 a).
{ unfold a.
  apply generic_format_round.
  - exact Vfexp1.
  - now apply valid_rnd_DN. }
revert Fa; revert Fx.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (ma := Ztrunc (a * bpow (- fexp1 (mag a)))).
intros Fx Fa.
assert (Nna : 0 <= a).
{ rewrite <- (round_0 beta fexp1 Zfloor).
  unfold a; apply round_le.
  - exact Vfexp1.
  - now apply valid_rnd_DN.
  - apply sqrt_pos. }
assert (Phu1 : 0 < / 2 * u1).
{ apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
assert (Phu2 : 0 < / 2 * u2).
{ apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
assert (Pb : 0 < b).
{ unfold b.
  rewrite <- (Rmult_0_r (/ 2)).
  apply Rmult_lt_compat_l; [lra|].
  apply Rlt_Rminus.
  unfold u2, u1.
  apply bpow_lt.
  lia. }
assert (Pb' : 0 < b').
{ now unfold b'; rewrite Rmult_plus_distr_l; apply Rplus_lt_0_compat. }
assert (Hr : sqrt x <= a + b').
{ unfold b'; apply (Rplus_le_reg_r (- / 2 * u1 - a)); ring_simplify.
  replace (_ - _) with (sqrt x - (a + / 2 * u1)) by ring.
  now apply Rabs_le_inv. }
assert (Hl : a + b <= sqrt x).
{ unfold b; apply (Rplus_le_reg_r (- / 2 * u1 - a)); ring_simplify.
  replace (_ + sqrt _) with (sqrt x - (a + / 2 * u1)) by ring.
  rewrite Ropp_mult_distr_l_reverse.
  now apply Rabs_le_inv in H; destruct H. }
assert (Hf1 : (2 * fexp1 (mag (sqrt x)) <= fexp1 (mag (x)))%Z);
  [destruct (mag_sqrt_disj x Px) as [H'|H']; rewrite H'; apply Hexp|].
assert (Hlx : (fexp1 (2 * mag (sqrt x)) < 2 * mag (sqrt x))%Z).
{ destruct (mag_sqrt_disj x Px) as [Hlx|Hlx].
  - apply (valid_exp_large fexp1 (mag x)); [|lia].
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
  - rewrite <- Hlx.
    now apply mag_generic_gt; [|apply Rgt_not_eq|]. }
assert (Hsl : a * a + u1 * a - u2 * a + b * b <= x).
{ replace (_ + _) with ((a + b) * (a + b)); [|now unfold b; field].
  rewrite <- sqrt_def; [|now apply Rlt_le].
  assert (H' : 0 <= a + b); [now apply Rlt_le, Rplus_le_lt_0_compat|].
  now apply Rmult_le_compat. }
assert (Hsr : x <= a * a + u1 * a + u2 * a + b' * b').
{ replace (_ + _) with ((a + b') * (a + b')); [|now unfold b'; field].
  rewrite <- (sqrt_def x); [|now apply Rlt_le].
  assert (H' : 0 <= sqrt x); [now apply sqrt_pos|].
  now apply Rmult_le_compat. }
destruct (Req_dec a 0) as [Za|Nza].
- (* a = 0 *)
  apply (Rlt_irrefl 0).
  apply Rlt_le_trans with (b * b); [now apply Rmult_lt_0_compat|].
  apply Rle_trans with x.
  + revert Hsl; unfold Rminus; rewrite Za; do 3 rewrite Rmult_0_r.
    now rewrite Ropp_0; do 3 rewrite Rplus_0_l.
  + rewrite Fx.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_0_l; bpow_simplify.
    unfold mx.
    rewrite Ztrunc_floor;
      [|now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]].
    apply Req_le, IZR_eq.
    apply Zfloor_imp.
    split; [now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]|simpl].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite Rmult_1_l; bpow_simplify.
    apply Rlt_le_trans with (bpow (2 * fexp1 (mag (sqrt x))));
      [|now apply bpow_le].
    change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l; rewrite Zmult_1_l.
    rewrite bpow_plus.
    rewrite <- (sqrt_def x) at 1; [|now apply Rlt_le].
    assert (sqrt x < bpow (fexp1 (mag (sqrt x))));
      [|now apply Rmult_lt_compat; [apply sqrt_pos|apply sqrt_pos| |]].
    apply (Rle_lt_trans _ _ _ Hr); rewrite Za; rewrite Rplus_0_l.
    unfold b'; change (bpow _) with u1.
    apply Rlt_le_trans with (/ 2 * (u1 + u1)); [|lra].
    apply Rmult_lt_compat_l; [lra|]; apply Rplus_lt_compat_l.
    unfold u2, u1, ulp, cexp; apply bpow_lt; lia.
- (* a <> 0 *)
  assert (Pa : 0 < a); [lra|].
  assert (Hla : (mag a = mag (sqrt x) :> Z)).
  { unfold a; apply mag_DN.
    - exact Vfexp1.
    - now fold a. }
  assert (Hl' : 0 < - (u2 * a) + b * b).
  { apply (Rplus_lt_reg_r (u2 * a)); ring_simplify.
    unfold b; ring_simplify.
    apply (Rplus_lt_reg_r (/ 2 * u2 * u1)); field_simplify.
    replace (_ / 2) with (u2 * (a + / 2 * u1)) by field.
    replace (_ / 8) with (/ 4 * (u2 ^ 2 + u1 ^ 2)) by field.
    apply Rlt_le_trans with (u2 * bpow (mag (sqrt x))).
    - apply Rmult_lt_compat_l; [now unfold u2, ulp; apply bpow_gt_0|].
      unfold u1; rewrite <- Hla.
      apply Rlt_le_trans with (a + bpow (fexp1 (mag a))).
      + apply Rplus_lt_compat_l.
        rewrite <- (Rmult_1_l (bpow _)) at 2.
        apply Rmult_lt_compat_r; [apply bpow_gt_0|lra].
      + apply Rle_trans with (a+ ulp beta fexp1 a).
        right; now rewrite ulp_neq_0.
        apply (id_p_ulp_le_bpow _ _ _ _ Pa Fa).
        apply Rabs_lt_inv, bpow_mag_gt.
    - apply Rle_trans with (bpow (- 2) * u1 ^ 2).
      + unfold pow; rewrite Rmult_1_r.
        unfold u1, u2, ulp, cexp; bpow_simplify; apply bpow_le.
        now apply Hexp.
      + apply Rmult_le_compat.
        * apply bpow_ge_0.
        * apply pow2_ge_0.
        * unfold Raux.bpow, Z.pow_pos; simpl; rewrite Zmult_1_r.
          apply Rinv_le; [lra|].
          change 4%Z with (2 * 2)%Z; apply IZR_le, Zmult_le_compat; lia.
        * rewrite <- (Rplus_0_l (u1 ^ 2)) at 1; apply Rplus_le_compat_r.
          apply pow2_ge_0. }
  assert (Hr' : x <= a * a + u1 * a).
  { rewrite Hla in Fa.
    rewrite <- Rmult_plus_distr_r.
    unfold u1, ulp, cexp.
    rewrite <- (Rmult_1_l (bpow _)); rewrite Fa; rewrite <- Rmult_plus_distr_r.
    rewrite <- Rmult_assoc; rewrite (Rmult_comm _ (IZR ma)).
    rewrite <- (Rmult_assoc (IZR ma)); bpow_simplify.
    apply (Rmult_le_reg_r (bpow (- 2 * fexp1 (mag (sqrt x)))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite Fx at 1; bpow_simplify.
    rewrite <- IZR_Zpower by lia.
    rewrite <- plus_IZR, <- 2!mult_IZR.
    apply IZR_le, Zlt_succ_le, lt_IZR.
    unfold Z.succ; rewrite plus_IZR; do 2 rewrite mult_IZR; rewrite plus_IZR.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (2 * fexp1 (mag (sqrt x)))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite <- Fx.
    change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l; rewrite Zmult_1_l.
    rewrite bpow_plus; simpl.
    replace (_ * _) with (a * a + u1 * a + u1 * u1);
      [|unfold u1, ulp, cexp; rewrite Fa; ring].
    apply (Rle_lt_trans _ _ _ Hsr).
    rewrite Rplus_assoc; apply Rplus_lt_compat_l.
    apply (Rplus_lt_reg_r (- b' * b' + / 2 * u1 * u2)); ring_simplify.
    replace (_ + _) with ((a + / 2 * u1) * u2) by ring.
    apply Rlt_le_trans with (bpow (mag (sqrt x)) * u2).
    - apply Rmult_lt_compat_r; [now unfold u2, ulp; apply bpow_gt_0|].
      apply Rlt_le_trans with (a + u1); [lra|].
      unfold u1; fold (cexp beta fexp1 (sqrt x)).
      rewrite <- cexp_DN; [|exact Vfexp1|exact Pa]; fold a.
      rewrite <- ulp_neq_0; trivial.
      apply id_p_ulp_le_bpow.
      + exact Pa.
      + now apply round_DN_pt.
      + apply Rle_lt_trans with (sqrt x).
        * now apply round_DN_pt.
        * apply Rabs_lt_inv.
          apply bpow_mag_gt.
    - apply Rle_trans with (/ 2 * u1 ^ 2).
      + apply Rle_trans with (bpow (- 2) * u1 ^ 2).
        * unfold pow; rewrite Rmult_1_r.
          unfold u2, u1, ulp, cexp.
          bpow_simplify.
          apply bpow_le.
          rewrite Zplus_comm.
          now apply Hexp.
        * apply Rmult_le_compat_r; [now apply pow2_ge_0|].
          unfold Raux.bpow; simpl; unfold Z.pow_pos; simpl.
          rewrite Zmult_1_r.
          apply Rinv_le; [lra|].
          apply IZR_le.
          rewrite <- (Zmult_1_l 2).
          apply Zmult_le_compat; lia.
      + assert (u2 ^ 2 < u1 ^ 2); [|unfold b'; lra].
        unfold pow; do 2 rewrite Rmult_1_r.
        assert (H' : 0 <= u2); [unfold u2, ulp; apply bpow_ge_0|].
        assert (u2 < u1); [|now apply Rmult_lt_compat].
        unfold u1, u2, ulp, cexp; apply bpow_lt; lia. }
  apply (Rlt_irrefl (a * a + u1 * a)).
  apply Rlt_le_trans with (a * a + u1 * a - u2 * a + b * b).
  + rewrite <- (Rplus_0_r (a * a + _)) at 1.
    unfold Rminus; rewrite (Rplus_assoc _ _ (b * b)).
    now apply Rplus_lt_compat_l.
  + now apply Rle_trans with x.
Qed.


Lemma round_round_sqrt :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_sqrt_hyp fexp1 fexp2 ->
  forall x,
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (sqrt x).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x Fx.
unfold round_round_eq.
destruct (Rle_or_lt x 0) as [Npx|Px].
- (* x <= 0 *)
  rewrite (sqrt_neg _ Npx).
  now rewrite round_0; [|apply valid_rnd_N].
- (* 0 < x *)
  assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; try assumption; lra|].
  assert (Hfsx : (fexp1 (mag (sqrt x)) < mag (sqrt x))%Z).
  { destruct (Rle_or_lt x 1) as [Hx|Hx].
    - (* x <= 1 *)
      apply (valid_exp_large fexp1 (mag x)); [exact Hfx|].
      apply mag_le; [exact Px|].
      rewrite <- (sqrt_def x) at 1; [|lra].
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l.
      + apply sqrt_pos.
      + rewrite <- sqrt_1.
        now apply sqrt_le_1_alt.
    - (* 1 < x *)
      generalize ((proj1 (proj2 Hexp)) 1%Z).
      replace (_ - 1)%Z with 1%Z by ring.
      intro Hexp10.
      assert (Hf0 : (fexp1 1 < 1)%Z) by lia.
      clear Hexp10.
      apply (valid_exp_large fexp1 1); [exact Hf0|].
      apply mag_ge_bpow.
      rewrite Zeq_minus; [|reflexivity].
      unfold Raux.bpow; simpl.
      apply Rabs_ge; right.
      rewrite <- sqrt_1.
      apply sqrt_le_1_alt.
      now apply Rlt_le. }
  assert (Hf2 : (fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1)%Z).
  { assert (H : (fexp1 (2 * mag (sqrt x)) < 2 * mag (sqrt x))%Z).
    { destruct (mag_sqrt_disj x Px) as [Hlx|Hlx].
      - apply (valid_exp_large fexp1 (mag x)); [|lia].
        now apply mag_generic_gt; [|apply Rgt_not_eq|].
      - rewrite <- Hlx.
        now apply mag_generic_gt; [|apply Rgt_not_eq|]. }
    generalize ((proj2 (proj2 Hexp)) (mag (sqrt x)) H).
    lia. }
  apply round_round_mid_cases.
  + exact Vfexp1.
  + exact Vfexp2.
  + now apply sqrt_lt_R0.
  + lia.
  + lia.
  + intros Hmid; casetype False; apply (Rle_not_lt _ _ Hmid).
    apply (round_round_sqrt_aux fexp1 fexp2 Vfexp1 Vfexp2 Hexp x Px Hf2 Fx).
Qed.

Section Double_round_sqrt_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_sqrt_hyp :
  (2 * prec + 2 <= prec')%Z ->
  round_round_sqrt_hyp (FLX_exp prec) (FLX_exp prec').
Proof.
intros Hprec.
unfold FLX_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_sqrt_hyp; split; [|split]; intro ex; lia.
Qed.

Theorem round_round_sqrt_FLX :
  forall choice1 choice2,
  (2 * prec + 2 <= prec')%Z ->
  forall x,
  FLX_format beta prec x ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (sqrt x).
Proof.
intros choice1 choice2 Hprec x Fx.
apply round_round_sqrt.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- now apply FLX_round_round_sqrt_hyp.
- now apply generic_format_FLX.
Qed.

End Double_round_sqrt_FLX.

Section Double_round_sqrt_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_sqrt_hyp :
  (emin <= 0)%Z ->
  ((emin' <= emin - prec - 2)%Z
   \/ (2 * emin' <= emin - 4 * prec - 2)%Z) ->
  (2 * prec + 2 <= prec')%Z ->
  round_round_sqrt_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof.
intros Hemin Heminprec Hprec.
unfold FLT_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_sqrt_hyp; split; [|split]; intros ex.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (2 * ex - prec) emin).
  lia.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (2 * ex - 1 - prec) emin).
  lia.
- generalize (Zmax_spec (2 * ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ex - prec) emin).
  lia.
Qed.

Theorem round_round_sqrt_FLT :
  forall choice1 choice2,
  (emin <= 0)%Z ->
  ((emin' <= emin - prec - 2)%Z
   \/ (2 * emin' <= emin - 4 * prec - 2)%Z) ->
  (2 * prec + 2 <= prec')%Z ->
  forall x,
  FLT_format beta emin prec x ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof.
intros choice1 choice2 Hemin Heminprec Hprec x Fx.
apply round_round_sqrt.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- now apply FLT_round_round_sqrt_hyp.
- now apply generic_format_FLT.
Qed.

End Double_round_sqrt_FLT.

Section Double_round_sqrt_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_sqrt_hyp :
  (2 * (emin' + prec') <= emin + prec <= 1)%Z ->
  (2 * prec + 2 <= prec')%Z ->
  round_round_sqrt_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in *.
unfold round_round_sqrt_hyp; split; [|split]; intros ex.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (2 * ex - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (2 * ex - 1 - prec) emin);
  lia.
- intro H.
  destruct (Zle_or_lt emin (2 * ex - prec)) as [H'|H'].
  + destruct (Z.ltb_spec (ex - prec') emin');
    destruct (Z.ltb_spec (ex - prec) emin);
    lia.
  + casetype False.
    rewrite (Zlt_bool_true _ _ H') in H.
    lia.
Qed.

Theorem round_round_sqrt_FTZ :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (2 * (emin' + prec') <= emin + prec <= 1)%Z ->
  (2 * prec + 2 <= prec')%Z ->
  forall x,
  FTZ_format beta emin prec x ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof.
intros Hbeta choice1 choice2 Hemin Hprec x Fx.
apply round_round_sqrt.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- now apply FTZ_round_round_sqrt_hyp.
- now apply generic_format_FTZ.
Qed.

End Double_round_sqrt_FTZ.

Section Double_round_sqrt_radix_ge_4.

Definition round_round_sqrt_radix_ge_4_hyp fexp1 fexp2 :=
  (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex))%Z)
  /\ (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex - 1))%Z)
  /\ (forall ex, (fexp1 (2 * ex) < 2 * ex)%Z ->
                 (fexp2 ex + ex <= 2 * fexp1 ex - 1)%Z).

Lemma round_round_sqrt_radix_ge_4_aux :
  (4 <= beta)%Z ->
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  round_round_sqrt_radix_ge_4_hyp fexp1 fexp2 ->
  forall x,
  0 < x ->
  (fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1)%Z ->
  generic_format beta fexp1 x ->
  / 2 * ulp beta fexp2 (sqrt x) < Rabs (sqrt x - midp fexp1 (sqrt x)).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 Hexp x Px Hf2 Fx.
set (a := round beta fexp1 Zfloor (sqrt x)).
set (u1 := bpow (fexp1 (mag (sqrt x)))).
set (u2 := bpow (fexp2 (mag (sqrt x)))).
set (b := / 2 * (u1 - u2)).
set (b' := / 2 * (u1 + u2)).
unfold midp; rewrite 2!ulp_neq_0; try now apply Rgt_not_eq, sqrt_lt_R0.
apply Rnot_ge_lt; intro H; apply Rge_le in H.
assert (Fa : generic_format beta fexp1 a).
{ unfold a.
  apply generic_format_round.
  - exact Vfexp1.
  - now apply valid_rnd_DN. }
revert Fa; revert Fx.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (ma := Ztrunc (a * bpow (- fexp1 (mag a)))).
intros Fx Fa.
assert (Nna : 0 <= a).
{ rewrite <- (round_0 beta fexp1 Zfloor).
  unfold a; apply round_le.
  - exact Vfexp1.
  - now apply valid_rnd_DN.
  - apply sqrt_pos. }
assert (Phu1 : 0 < / 2 * u1).
{ apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
assert (Phu2 : 0 < / 2 * u2).
{ apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]. }
assert (Pb : 0 < b).
{ unfold b.
  rewrite <- (Rmult_0_r (/ 2)).
  apply Rmult_lt_compat_l; [lra|].
  apply Rlt_Rminus.
  unfold u2, u1, ulp, cexp.
  apply bpow_lt.
  lia. }
assert (Pb' : 0 < b').
{ now unfold b'; rewrite Rmult_plus_distr_l; apply Rplus_lt_0_compat. }
assert (Hr : sqrt x <= a + b').
{ unfold b'; apply (Rplus_le_reg_r (- / 2 * u1 - a)); ring_simplify.
  replace (_ - _) with (sqrt x - (a + / 2 * u1)) by ring.
  now apply Rabs_le_inv. }
assert (Hl : a + b <= sqrt x).
{ unfold b; apply (Rplus_le_reg_r (- / 2 * u1 - a)); ring_simplify.
  replace (_ + sqrt _) with (sqrt x - (a + / 2 * u1)) by ring.
  rewrite Ropp_mult_distr_l_reverse.
  now apply Rabs_le_inv in H; destruct H. }
assert (Hf1 : (2 * fexp1 (mag (sqrt x)) <= fexp1 (mag (x)))%Z);
  [destruct (mag_sqrt_disj x Px) as [H'|H']; rewrite H'; apply Hexp|].
assert (Hlx : (fexp1 (2 * mag (sqrt x)) < 2 * mag (sqrt x))%Z).
{ destruct (mag_sqrt_disj x Px) as [Hlx|Hlx].
  - apply (valid_exp_large fexp1 (mag x)); [|lia].
    now apply mag_generic_gt; [|apply Rgt_not_eq|].
  - rewrite <- Hlx.
    now apply mag_generic_gt; [|apply Rgt_not_eq|]. }
assert (Hsl : a * a + u1 * a - u2 * a + b * b <= x).
{ replace (_ + _) with ((a + b) * (a + b)); [|now unfold b; field].
  rewrite <- sqrt_def; [|now apply Rlt_le].
  assert (H' : 0 <= a + b); [now apply Rlt_le, Rplus_le_lt_0_compat|].
  now apply Rmult_le_compat. }
assert (Hsr : x <= a * a + u1 * a + u2 * a + b' * b').
{ replace (_ + _) with ((a + b') * (a + b')); [|now unfold b'; field].
  rewrite <- (sqrt_def x); [|now apply Rlt_le].
  assert (H' : 0 <= sqrt x); [now apply sqrt_pos|].
  now apply Rmult_le_compat. }
destruct (Req_dec a 0) as [Za|Nza].
- (* a = 0 *)
  apply (Rlt_irrefl 0).
  apply Rlt_le_trans with (b * b); [now apply Rmult_lt_0_compat|].
  apply Rle_trans with x.
  + revert Hsl; unfold Rminus; rewrite Za; do 3 rewrite Rmult_0_r.
    now rewrite Ropp_0; do 3 rewrite Rplus_0_l.
  + rewrite Fx.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_0_l; bpow_simplify.
    unfold mx.
    rewrite Ztrunc_floor;
      [|now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]].
    apply Req_le, IZR_eq.
    apply Zfloor_imp.
    split; [now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]|simpl].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x)))); [now apply bpow_gt_0|].
    rewrite Rmult_1_l; bpow_simplify.
    apply Rlt_le_trans with (bpow (2 * fexp1 (mag (sqrt x))));
      [|now apply bpow_le].
    change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l; rewrite Zmult_1_l.
    rewrite bpow_plus.
    rewrite <- (sqrt_def x) at 1; [|now apply Rlt_le].
    assert (sqrt x < bpow (fexp1 (mag (sqrt x))));
      [|now apply Rmult_lt_compat; [apply sqrt_pos|apply sqrt_pos| |]].
    apply (Rle_lt_trans _ _ _ Hr); rewrite Za; rewrite Rplus_0_l.
    unfold b'; change (bpow _) with u1.
    apply Rlt_le_trans with (/ 2 * (u1 + u1)); [|lra].
    apply Rmult_lt_compat_l; [lra|]; apply Rplus_lt_compat_l.
    unfold u2, u1, ulp, cexp; apply bpow_lt; lia.
- (* a <> 0 *)
  assert (Pa : 0 < a); [lra|].
  assert (Hla : (mag a = mag (sqrt x) :> Z)).
  { unfold a; apply mag_DN.
    - exact Vfexp1.
    - now fold a. }
  assert (Hl' : 0 < - (u2 * a) + b * b).
  { apply (Rplus_lt_reg_r (u2 * a)); ring_simplify.
    unfold b; ring_simplify.
    apply (Rplus_lt_reg_r (/ 2 * u2 * u1)); field_simplify.
    replace (_ / 2) with (u2 * (a + / 2 * u1)) by field.
    replace (_ / 8) with (/ 4 * (u2 ^ 2 + u1 ^ 2)) by field.
    apply Rlt_le_trans with (u2 * bpow (mag (sqrt x))).
    - apply Rmult_lt_compat_l; [now unfold u2, ulp; apply bpow_gt_0|].
      unfold u1; rewrite <- Hla.
      apply Rlt_le_trans with (a + ulp beta fexp1 a).
      + apply Rplus_lt_compat_l.
        rewrite <- (Rmult_1_l (ulp _ _ _)).
        rewrite ulp_neq_0; trivial.
        apply Rmult_lt_compat_r; [apply bpow_gt_0|lra].
      + apply (id_p_ulp_le_bpow _ _ _ _ Pa Fa).
        apply Rabs_lt_inv, bpow_mag_gt.
    - apply Rle_trans with (bpow (- 1) * u1 ^ 2).
      + unfold pow; rewrite Rmult_1_r.
        unfold u1, u2, ulp, cexp; bpow_simplify; apply bpow_le.
        now apply Hexp.
      + apply Rmult_le_compat.
        * apply bpow_ge_0.
        * apply pow2_ge_0.
        * unfold Raux.bpow, Z.pow_pos; simpl; rewrite Zmult_1_r.
          apply Rinv_le; [lra|].
          now apply IZR_le.
        * rewrite <- (Rplus_0_l (u1 ^ 2)) at 1; apply Rplus_le_compat_r.
          apply pow2_ge_0. }
  assert (Hr' : x <= a * a + u1 * a).
  { rewrite Hla in Fa.
    rewrite <- Rmult_plus_distr_r.
    unfold u1, ulp, cexp.
    rewrite <- (Rmult_1_l (bpow _)); rewrite Fa; rewrite <- Rmult_plus_distr_r.
    rewrite <- Rmult_assoc; rewrite (Rmult_comm _ (IZR ma)).
    rewrite <- (Rmult_assoc (IZR ma)); bpow_simplify.
    apply (Rmult_le_reg_r (bpow (- 2 * fexp1 (mag (sqrt x)))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite Fx at 1; bpow_simplify.
    rewrite <- IZR_Zpower by lia.
    rewrite <- plus_IZR, <- 2!mult_IZR.
    apply IZR_le, Zlt_succ_le, lt_IZR.
    unfold Z.succ; rewrite plus_IZR; do 2 rewrite mult_IZR; rewrite plus_IZR.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (2 * fexp1 (mag (sqrt x)))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite <- Fx.
    change 2%Z with (1 + 1)%Z; rewrite Zmult_plus_distr_l; rewrite Zmult_1_l.
    rewrite bpow_plus; simpl.
    replace (_ * _) with (a * a + u1 * a + u1 * u1);
      [|unfold u1, ulp, cexp; rewrite Fa; ring].
    apply (Rle_lt_trans _ _ _ Hsr).
    rewrite Rplus_assoc; apply Rplus_lt_compat_l.
    apply (Rplus_lt_reg_r (- b' * b' + / 2 * u1 * u2)); ring_simplify.
    replace (_ + _) with ((a + / 2 * u1) * u2) by ring.
    apply Rlt_le_trans with (bpow (mag (sqrt x)) * u2).
    - apply Rmult_lt_compat_r; [now unfold u2, ulp; apply bpow_gt_0|].
      apply Rlt_le_trans with (a + u1); [lra|].
      unfold u1; fold (cexp beta fexp1 (sqrt x)).
      rewrite <- cexp_DN; [|exact Vfexp1|exact Pa]; fold a.
      rewrite <- ulp_neq_0; trivial.
      apply id_p_ulp_le_bpow.
      + exact Pa.
      + now apply round_DN_pt.
      + apply Rle_lt_trans with (sqrt x).
        * now apply round_DN_pt.
        * apply Rabs_lt_inv.
          apply bpow_mag_gt.
    - apply Rle_trans with (/ 2 * u1 ^ 2).
      + apply Rle_trans with (bpow (- 1) * u1 ^ 2).
        * unfold pow; rewrite Rmult_1_r.
          unfold u2, u1, ulp, cexp.
          bpow_simplify.
          apply bpow_le.
          rewrite Zplus_comm.
          now apply Hexp.
        * apply Rmult_le_compat_r; [now apply pow2_ge_0|].
          unfold Raux.bpow; simpl; unfold Z.pow_pos; simpl.
          rewrite Zmult_1_r.
          apply Rinv_le; [lra|].
          apply IZR_le; lia.
      + assert (u2 ^ 2 < u1 ^ 2); [|unfold b'; lra].
        unfold pow; do 2 rewrite Rmult_1_r.
        assert (H' : 0 <= u2); [unfold u2, ulp; apply bpow_ge_0|].
        assert (u2 < u1); [|now apply Rmult_lt_compat].
        unfold u1, u2, ulp, cexp; apply bpow_lt; lia. }
  apply (Rlt_irrefl (a * a + u1 * a)).
  apply Rlt_le_trans with (a * a + u1 * a - u2 * a + b * b).
  + rewrite <- (Rplus_0_r (a * a + _)) at 1.
    unfold Rminus; rewrite (Rplus_assoc _ _ (b * b)).
    now apply Rplus_lt_compat_l.
  + now apply Rle_trans with x.
Qed.

Lemma round_round_sqrt_radix_ge_4 :
  (4 <= beta)%Z ->
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_sqrt_radix_ge_4_hyp fexp1 fexp2 ->
  forall x,
  generic_format beta fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 (sqrt x).
Proof.
intros Hbeta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x Fx.
unfold round_round_eq.
destruct (Rle_or_lt x 0) as [Npx|Px].
- (* x <= 0 *)
  assert (Hs : sqrt x = 0).
  { destruct (Req_dec x 0) as [Zx|Nzx].
    - (* x = 0 *)
      rewrite Zx.
      exact sqrt_0.
    - (* x < 0 *)
      unfold sqrt.
      destruct Rcase_abs.
      + reflexivity.
      + casetype False; lra. }
  rewrite Hs.
  rewrite round_0.
  + reflexivity.
  + now apply valid_rnd_N.
- (* 0 < x *)
  assert (Hfx : (fexp1 (mag x) < mag x)%Z);
    [now apply mag_generic_gt; try assumption; lra|].
  assert (Hfsx : (fexp1 (mag (sqrt x)) < mag (sqrt x))%Z).
  { destruct (Rle_or_lt x 1) as [Hx|Hx].
    - (* x <= 1 *)
      apply (valid_exp_large fexp1 (mag x)); [exact Hfx|].
      apply mag_le; [exact Px|].
      rewrite <- (sqrt_def x) at 1; [|lra].
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l.
      + apply sqrt_pos.
      + rewrite <- sqrt_1.
        now apply sqrt_le_1_alt.
    - (* 1 < x *)
      generalize ((proj1 (proj2 Hexp)) 1%Z).
      replace (_ - 1)%Z with 1%Z by ring.
      intro Hexp10.
      assert (Hf0 : (fexp1 1 < 1)%Z) by lia.
      clear Hexp10.
      apply (valid_exp_large fexp1 1); [exact Hf0|].
      apply mag_ge_bpow.
      rewrite Zeq_minus; [|reflexivity].
      unfold Raux.bpow; simpl.
      apply Rabs_ge; right.
      rewrite <- sqrt_1.
      apply sqrt_le_1_alt.
      now apply Rlt_le. }
  assert (Hf2 : (fexp2 (mag (sqrt x)) <= fexp1 (mag (sqrt x)) - 1)%Z).
  { assert (H : (fexp1 (2 * mag (sqrt x)) < 2 * mag (sqrt x))%Z).
    { destruct (mag_sqrt_disj x Px) as [Hlx|Hlx].
      - apply (valid_exp_large fexp1 (mag x)); [|lia].
        now apply mag_generic_gt; [|apply Rgt_not_eq|].
      - rewrite <- Hlx.
        now apply mag_generic_gt; [|apply Rgt_not_eq|]. }
    generalize ((proj2 (proj2 Hexp)) (mag (sqrt x)) H).
    lia. }
  apply round_round_mid_cases.
  + exact Vfexp1.
  + exact Vfexp2.
  + now apply sqrt_lt_R0.
  + lia.
  + lia.
  + intros Hmid; casetype False; apply (Rle_not_lt _ _ Hmid).
    apply (round_round_sqrt_radix_ge_4_aux Hbeta fexp1 fexp2 Vfexp1 Vfexp2
                                           Hexp x Px Hf2 Fx).
Qed.

Section Double_round_sqrt_radix_ge_4_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_sqrt_radix_ge_4_hyp :
  (2 * prec + 1 <= prec')%Z ->
  round_round_sqrt_radix_ge_4_hyp (FLX_exp prec) (FLX_exp prec').
Proof.
intros Hprec.
unfold FLX_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_sqrt_radix_ge_4_hyp; split; [|split]; intro ex; lia.
Qed.

Theorem round_round_sqrt_radix_ge_4_FLX :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (2 * prec + 1 <= prec')%Z ->
  forall x,
  FLX_format beta prec x ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (sqrt x).
Proof.
intros Hbeta choice1 choice2 Hprec x Fx.
apply round_round_sqrt_radix_ge_4.
- exact Hbeta.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- now apply FLX_round_round_sqrt_radix_ge_4_hyp.
- now apply generic_format_FLX.
Qed.

End Double_round_sqrt_radix_ge_4_FLX.

Section Double_round_sqrt_radix_ge_4_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_sqrt_radix_ge_4_hyp :
  (emin <= 0)%Z ->
  ((emin' <= emin - prec - 1)%Z
   \/ (2 * emin' <= emin - 4 * prec)%Z) ->
  (2 * prec + 1 <= prec')%Z ->
  round_round_sqrt_radix_ge_4_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof.
intros Hemin Heminprec Hprec.
unfold FLT_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_sqrt_radix_ge_4_hyp; split; [|split]; intros ex.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (2 * ex - prec) emin).
  lia.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (2 * ex - 1 - prec) emin).
  lia.
- generalize (Zmax_spec (2 * ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ex - prec) emin).
  lia.
Qed.

Theorem round_round_sqrt_radix_ge_4_FLT :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (emin <= 0)%Z ->
  ((emin' <= emin - prec - 1)%Z
   \/ (2 * emin' <= emin - 4 * prec)%Z) ->
  (2 * prec + 1 <= prec')%Z ->
  forall x,
  FLT_format beta emin prec x ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof.
intros Hbeta choice1 choice2 Hemin Heminprec Hprec x Fx.
apply round_round_sqrt_radix_ge_4.
- exact Hbeta.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- now apply FLT_round_round_sqrt_radix_ge_4_hyp.
- now apply generic_format_FLT.
Qed.

End Double_round_sqrt_radix_ge_4_FLT.

Section Double_round_sqrt_radix_ge_4_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_sqrt_radix_ge_4_hyp :
  (2 * (emin' + prec') <= emin + prec <= 1)%Z ->
  (2 * prec + 1 <= prec')%Z ->
  round_round_sqrt_radix_ge_4_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in *.
unfold round_round_sqrt_radix_ge_4_hyp; split; [|split]; intros ex.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (2 * ex - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (2 * ex - 1 - prec) emin);
  lia.
- intro H.
  destruct (Zle_or_lt emin (2 * ex - prec)) as [H'|H'].
  + destruct (Z.ltb_spec (ex - prec') emin');
    destruct (Z.ltb_spec (ex - prec) emin);
    lia.
  + casetype False.
    rewrite (Zlt_bool_true _ _ H') in H.
    lia.
Qed.

Theorem round_round_sqrt_radix_ge_4_FTZ :
  (4 <= beta)%Z ->
  forall choice1 choice2,
  (2 * (emin' + prec') <= emin + prec <= 1)%Z ->
  (2 * prec + 1 <= prec')%Z ->
  forall x,
  FTZ_format beta emin prec x ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof.
intros Hbeta choice1 choice2 Hemin Hprec x Fx.
apply round_round_sqrt_radix_ge_4.
- exact Hbeta.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- now apply FTZ_round_round_sqrt_radix_ge_4_hyp.
- now apply generic_format_FTZ.
Qed.

End Double_round_sqrt_radix_ge_4_FTZ.

End Double_round_sqrt_radix_ge_4.

End Double_round_sqrt.

Section Double_round_div.

Lemma round_round_eq_mid_beta_even :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (exists n, (beta = 2 * n :> Z)%Z) ->
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  (fexp1 (mag x) <= mag x)%Z ->
  x = midp fexp1 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Ebeta x Px Hf2 Hf1.
unfold round_round_eq.
unfold midp.
set (rd := round beta fexp1 Zfloor x).
set (u := ulp beta fexp1 x).
intro H; apply (Rplus_eq_compat_l (- rd)) in H.
ring_simplify in H; revert H.
rewrite Rplus_comm; fold (Rminus x rd).
intro Xmid.
destruct Ebeta as (n,Ebeta).
assert (Hbeta : (2 <= beta)%Z).
{ destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le. }
apply (Rplus_eq_compat_l rd) in Xmid; ring_simplify in Xmid.
rewrite (round_generic beta fexp2); [reflexivity|now apply valid_rnd_N|].
set (f := Float beta (Zfloor (scaled_mantissa beta fexp2 rd)
                      + n * beta ^ (fexp1 (mag x) - 1
                                    - fexp2 (mag x)))
                (cexp beta fexp2 x)).
assert (Hf : F2R f = x).
{ unfold f, F2R; simpl.
  rewrite plus_IZR.
  rewrite Rmult_plus_distr_r.
  rewrite mult_IZR.
  rewrite IZR_Zpower by lia.
  unfold cexp at 2; bpow_simplify.
  unfold Zminus; rewrite bpow_plus.
  rewrite (Rmult_comm _ (bpow (- 1))).
  rewrite <- (Rmult_assoc (IZR n)).
  change (bpow (- 1)) with (/ IZR (beta * 1)).
  rewrite Zmult_1_r.
  rewrite Ebeta.
  rewrite (mult_IZR 2).
  rewrite Rinv_mult_distr;
    [|simpl; lra | apply IZR_neq; lia].
  rewrite <- Rmult_assoc; rewrite (Rmult_comm (IZR n));
  rewrite (Rmult_assoc _ (IZR n)).
  rewrite Rinv_r;
    [rewrite Rmult_1_r | apply IZR_neq; lia].
  simpl; fold (cexp beta fexp1 x).
  rewrite <- 2!ulp_neq_0; try now apply Rgt_not_eq.
  fold u; rewrite Xmid at 2.
  apply f_equal2; [|reflexivity].
  rewrite ulp_neq_0; try now apply Rgt_not_eq.
  destruct (Req_dec rd 0) as [Zrd|Nzrd].
  - (* rd = 0 *)
    rewrite Zrd.
    rewrite scaled_mantissa_0.
    rewrite Zfloor_IZR.
    now rewrite Rmult_0_l.
  - (* rd <> 0 *)
    assert (Nnrd : 0 <= rd).
    { apply round_DN_pt.
      - exact Vfexp1.
      - apply generic_format_0.
      - now apply Rlt_le. }
    assert (Prd : 0 < rd); [lra|].
    assert (Lrd : (mag rd = mag x :> Z)).
    { apply Zle_antisym.
      - apply mag_le; [exact Prd|].
        now apply round_DN_pt.
      - apply mag_round_ge.
        + exact Vfexp1.
        + now apply valid_rnd_DN.
        + exact Nzrd. }
    unfold scaled_mantissa.
    unfold rd at 1.
    unfold round, F2R, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite Lrd.
    rewrite <- (IZR_Zpower _ (_ - _)) by lia.
    rewrite <- mult_IZR.
    rewrite (Zfloor_imp (Zfloor (x * bpow (- fexp1 (mag x))) *
                         beta ^ (fexp1 (mag x) - fexp2 (mag x)))).
    + rewrite mult_IZR.
      rewrite IZR_Zpower by lia.
      bpow_simplify.
      now unfold rd.
    + split; [now apply Rle_refl|].
      rewrite plus_IZR.
      simpl; lra. }
apply (generic_format_F2R' _ _ x f Hf).
intros _.
apply Z.le_refl.
Qed.

Lemma round_round_really_zero :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (mag x <= fexp1 (mag x) - 2)%Z ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf1.
assert (Hlx : bpow (mag x - 1) <= x < bpow (mag x)).
{ destruct (mag x) as (ex,Hex); simpl.
  rewrite <- (Rabs_right x); [|now apply Rle_ge; apply Rlt_le].
  apply Hex.
  now apply Rgt_not_eq. }
unfold round_round_eq.
rewrite (round_N_small_pos beta fexp1 _ x (mag x)); [|exact Hlx|lia].
set (x'' := round beta fexp2 (Znearest choice2) x).
destruct (Req_dec x'' 0) as [Zx''|Nzx''];
  [now rewrite Zx''; rewrite round_0; [|apply valid_rnd_N]|].
destruct (Zle_or_lt (fexp2 (mag x)) (mag x)).
- (* fexp2 (mag x) <= mag x *)
  destruct (Rlt_or_le x'' (bpow (mag x))).
  + (* x'' < bpow (mag x) *)
    rewrite (round_N_small_pos beta fexp1 _ _ (mag x));
    [reflexivity|split; [|exact H0]|lia].
    apply round_large_pos_ge_bpow; [now apply valid_rnd_N| |now apply Hlx].
    fold x''; assert (0 <= x''); [|lra]; unfold x''.
    rewrite <- (round_0 beta fexp2 (Znearest choice2)).
    now apply round_le; [|apply valid_rnd_N|apply Rlt_le].
  + (* bpow (mag x) <= x'' *)
    assert (Hx'' : x'' = bpow (mag x)).
    { apply Rle_antisym; [|exact H0].
      rewrite <- (round_generic beta fexp2 (Znearest choice2) (bpow _)).
      - now apply round_le; [|apply valid_rnd_N|apply Rlt_le].
      - now apply generic_format_bpow'. }
    rewrite Hx''.
    unfold round, F2R, scaled_mantissa, cexp; simpl.
    rewrite mag_bpow.
    assert (Hf11 : (fexp1 (mag x + 1) = fexp1 (mag x) :> Z)%Z);
      [apply Vfexp1; lia|].
    rewrite Hf11.
    apply (Rmult_eq_reg_r (bpow (- fexp1 (mag x))));
      [|now apply Rgt_not_eq; apply bpow_gt_0].
    rewrite Rmult_0_l; bpow_simplify.
    apply IZR_eq.
    apply Znearest_imp.
    simpl; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
    rewrite Rabs_right; [|now apply Rle_ge; apply bpow_ge_0].
    apply Rle_lt_trans with (bpow (- 2)); [now apply bpow_le; lia|].
    unfold Raux.bpow, Z.pow_pos; simpl; rewrite Zmult_1_r.
    assert (Hbeta : (2 <= beta)%Z).
    { destruct beta as (beta_val,beta_prop); simpl.
      now apply Zle_bool_imp_le. }
    apply Rinv_lt_contravar.
    * apply Rmult_lt_0_compat; [lra|].
      rewrite mult_IZR; apply Rmult_lt_0_compat;
      apply IZR_lt; lia.
    * apply IZR_lt.
      apply (Z.le_lt_trans _ _ _ Hbeta).
      rewrite <- (Zmult_1_r beta) at 1.
      apply Zmult_lt_compat_l; lia.
- (* mag x < fexp2 (mag x) *)
  casetype False; apply Nzx''.
  now apply (round_N_small_pos beta _ _ _ (mag x)).
Qed.

Lemma round_round_zero :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp1 (mag x) = mag x + 1 :> Z)%Z ->
  x < bpow (mag x) - / 2 * ulp beta fexp2 x ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf1.
unfold round_round_eq.
set (x'' := round beta fexp2 (Znearest choice2) x).
set (u1 := ulp beta fexp1 x).
set (u2 := ulp beta fexp2 x).
intro Hx.
assert (Hlx : bpow (mag x - 1) <= x < bpow (mag x)).
{ destruct (mag x) as (ex,Hex); simpl.
  rewrite <- (Rabs_right x); [|now apply Rle_ge; apply Rlt_le].
  apply Hex.
  now apply Rgt_not_eq. }
rewrite (round_N_small_pos beta fexp1 choice1 x (mag x));
  [|exact Hlx|lia].
destruct (Req_dec x'' 0) as [Zx''|Nzx''];
  [now rewrite Zx''; rewrite round_0; [reflexivity|apply valid_rnd_N]|].
rewrite (round_N_small_pos beta _ _ x'' (mag x));
  [reflexivity| |lia].
split.
- apply round_large_pos_ge_bpow.
  + now apply valid_rnd_N.
  + assert (0 <= x''); [|now fold x''; lra].
    rewrite <- (round_0 beta fexp2 (Znearest choice2)).
    now apply round_le; [|apply valid_rnd_N|apply Rlt_le].
  + apply Rle_trans with (Rabs x);
    [|now rewrite Rabs_right; [apply Rle_refl|apply Rle_ge; apply Rlt_le]].
    destruct (mag x) as (ex,Hex); simpl; apply Hex.
    now apply Rgt_not_eq.
- replace x'' with (x + (x'' - x)) by ring.
  replace (bpow _) with (bpow (mag x) - / 2 * u2 + / 2 * u2) by ring.
  apply Rplus_lt_le_compat; [exact Hx|].
  apply Rabs_le_inv.
  now apply error_le_half_ulp.
Qed.

Lemma round_round_all_mid_cases :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z ->
  ((fexp1 (mag x) = mag x + 1 :> Z)%Z ->
   bpow (mag x) - / 2 * ulp beta fexp2 x <= x ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  ((fexp1 (mag x) <= mag x)%Z ->
   midp fexp1 x - / 2 * ulp beta fexp2 x <= x < midp fexp1 x ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  ((fexp1 (mag x) <= mag x)%Z ->
   x = midp fexp1 x ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  ((fexp1 (mag x) <= mag x)%Z ->
   midp fexp1 x < x <= midp fexp1 x + / 2 * ulp beta fexp2 x ->
   round_round_eq fexp1 fexp2 choice1 choice2 x) ->
  round_round_eq fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2.
set (x' := round beta fexp1 Zfloor x).
set (u1 := ulp beta fexp1 x).
set (u2 := ulp beta fexp2 x).
intros Cz Clt Ceq Cgt.
destruct (Ztrichotomy (mag x) (fexp1 (mag x) - 1)) as [Hlt|[Heq|Hgt]].
- (* mag x < fexp1 (mag x) - 1 *)
  assert (H : (mag x <= fexp1 (mag x) - 2)%Z) by lia.
  now apply round_round_really_zero.
- (* mag x = fexp1 (mag x) - 1 *)
  assert (H : (fexp1 (mag x) = (mag x + 1))%Z) by lia.
  destruct (Rlt_or_le x (bpow (mag x) - / 2 * u2)) as [Hlt'|Hge'].
  + now apply round_round_zero.
  + now apply Cz.
- (* mag x > fexp1 (mag x) - 1 *)
  assert (H : (fexp1 (mag x) <= mag x)%Z) by lia.
  destruct (Rtotal_order x (midp fexp1 x)) as [Hlt'|[Heq'|Hgt']].
  + (* x < midp fexp1 x *)
    destruct (Rlt_or_le x (midp fexp1 x - / 2 * u2)) as [Hlt''|Hle''].
    * now apply round_round_lt_mid_further_place; [| | |lia| |].
    * now apply Clt; [|split].
  + (* x = midp fexp1 x *)
    now apply Ceq.
  + (* x > midp fexp1 x *)
    destruct (Rle_or_lt x (midp fexp1 x + / 2 * u2)) as [Hlt''|Hle''].
    * now apply Cgt; [|split].
    * { destruct (generic_format_EM beta fexp1 x) as [Fx|Nfx].
        - (* generic_format beta fexp1 x *)
          unfold round_round_eq; rewrite (round_generic beta fexp2);
          [reflexivity|now apply valid_rnd_N|].
          now apply (generic_inclusion_mag beta fexp1); [lia|].
        - (* ~ generic_format beta fexp1 x *)
          assert (Hceil : round beta fexp1 Zceil x = x' + u1);
          [now apply round_UP_DN_ulp|].
          assert (Hf2' : (fexp2 (mag x) <= fexp1 (mag x) - 1)%Z) by lia.
          assert (midp' fexp1 x + / 2 * ulp beta fexp2 x < x);
            [|now apply round_round_gt_mid_further_place].
          revert Hle''; unfold midp, midp'; fold x'.
          rewrite Hceil; fold u1; fold u2.
          lra. }
Qed.

Lemma mag_div_disj :
  forall x y : R,
  0 < x -> 0 < y ->
  ((mag (x / y) = mag x - mag y :> Z)%Z
   \/ (mag (x / y) = mag x - mag y + 1 :> Z)%Z).
Proof.
intros x y Px Py.
generalize (mag_div beta x y (Rgt_not_eq _ _ Px) (Rgt_not_eq _ _ Py)).
lia.
Qed.

Definition round_round_div_hyp fexp1 fexp2 :=
  (forall ex, (fexp2 ex <= fexp1 ex - 1)%Z)
  /\ (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
                    (fexp1 (ex - ey) <= ex - ey + 1)%Z ->
                    (fexp2 (ex - ey) <= fexp1 ex - ey)%Z)
  /\ (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
                    (fexp1 (ex - ey + 1) <= ex - ey + 1 + 1)%Z ->
                    (fexp2 (ex - ey + 1) <= fexp1 ex - ey)%Z)
  /\ (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
                    (fexp1 (ex - ey) <= ex - ey)%Z ->
                    (fexp2 (ex - ey) <= fexp1 (ex - ey)
                                        + fexp1 ey - ey)%Z)
  /\ (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
                    (fexp1 (ex - ey) = ex - ey + 1)%Z ->
                    (fexp2 (ex - ey) <= ex - ey - ey + fexp1 ey)%Z).

Lemma round_round_div_aux0 :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  fexp1 (mag (x / y)) = (mag (x / y) + 1)%Z ->
  ~ (bpow (mag (x / y)) - / 2 * ulp beta fexp2 (x / y) <= x / y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Fx Fy Hf1.
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
set (p := bpow (mag (x / y))).
set (u2 := bpow (fexp2 (mag (x / y)))).
revert Fx Fy.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (my := Ztrunc (y * bpow (- fexp1 (mag y)))).
intros Fx Fy.
rewrite ulp_neq_0.
2: apply Rmult_integral_contrapositive_currified; [now apply Rgt_not_eq|idtac].
2: now apply Rinv_neq_0_compat, Rgt_not_eq.
intro Hl.
assert (Hr : x / y < p);
  [now apply Rabs_lt_inv; apply bpow_mag_gt|].
apply (Rlt_irrefl (p - / 2 * u2)).
apply (Rle_lt_trans _ _ _ Hl).
apply (Rmult_lt_reg_r y _ _ Py).
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l; [|now apply Rgt_not_eq]; rewrite Rmult_1_r.
destruct (Zle_or_lt Z0 (fexp1 (mag x) - mag (x / y)
                        - fexp1 (mag y))%Z) as [He|He].
- (* mag (x / y) + fexp1 (mag y) <= fexp1 (mag x) *)
  apply Rle_lt_trans with (p * y - p * bpow (fexp1 (mag y))).
  + rewrite Fx; rewrite Fy at 1.
    rewrite <- Rmult_assoc.
    rewrite (Rmult_comm p).
    unfold p; bpow_simplify.
    apply (Rmult_le_reg_r (bpow (- mag (x / y) - fexp1 (mag y))));
      [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    rewrite <- IZR_Zpower; [|exact He].
    rewrite <- mult_IZR.
    rewrite <- minus_IZR.
    apply IZR_le.
    apply (Zplus_le_reg_r _ _ 1); ring_simplify.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite mult_IZR.
    rewrite IZR_Zpower; [|exact He].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag y) + mag (x / y))));
      [now apply bpow_gt_0|].
    bpow_simplify.
    rewrite <- Fx.
    rewrite bpow_plus.
    rewrite <- Rmult_assoc; rewrite <- Fy.
    fold p.
    apply (Rmult_lt_reg_r (/ y)); [now apply Rinv_0_lt_compat|].
    field_simplify; lra.
  + rewrite Rmult_minus_distr_r.
    unfold Rminus; apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    * rewrite <- (Rmult_1_l (u2 * _)).
      rewrite Rmult_assoc.
      { apply Rmult_lt_compat.
        - lra.
        - now apply Rmult_le_pos; [apply bpow_ge_0|apply Rlt_le].
        - lra.
        - apply Rmult_lt_compat_l; [now apply bpow_gt_0|].
          apply Rabs_lt_inv.
          apply bpow_mag_gt. }
    * unfold u2, p, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite (Zplus_comm (- _)); fold (Zminus (mag (x / y)) (mag y)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      [now apply Hexp; [| |rewrite <- Hxy]|].
      replace (_ - _ + 1)%Z with ((mag x + 1) - mag y)%Z by ring.
      apply Hexp.
      { now assert (fexp1 (mag x + 1) <= mag x)%Z;
        [apply valid_exp|lia]. }
      { assumption. }
      replace (_ + 1 - _)%Z with (mag x - mag y + 1)%Z by ring.
      now rewrite <- Hxy.
- (* fexp1 (mag x) < mag (x / y) + fexp1 (mag y) *)
  apply Rle_lt_trans with (p * y - bpow (fexp1 (mag x))).
  + rewrite Fx at 1; rewrite Fy at 1.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r.
    bpow_simplify.
    rewrite (Rmult_comm p).
    unfold p; bpow_simplify.
    rewrite <- IZR_Zpower by lia.
    rewrite <- mult_IZR.
    rewrite <- minus_IZR.
    apply IZR_le.
    apply (Zplus_le_reg_r _ _ 1); ring_simplify.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite mult_IZR.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite <- Fx.
    rewrite Zplus_comm; rewrite bpow_plus.
    rewrite <- Rmult_assoc; rewrite <- Fy.
    fold p.
    apply (Rmult_lt_reg_r (/ y)); [now apply Rinv_0_lt_compat|].
    field_simplify; lra.
  + rewrite Rmult_minus_distr_r.
    unfold Rminus; apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    * rewrite <- (Rmult_1_l (u2 * _)).
      rewrite Rmult_assoc.
      { apply Rmult_lt_compat.
        - lra.
        - now apply Rmult_le_pos; [apply bpow_ge_0|apply Rlt_le].
        - lra.
        - apply Rmult_lt_compat_l; [now apply bpow_gt_0|].
          apply Rabs_lt_inv.
          apply bpow_mag_gt. }
    * unfold u2, p, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite (Zplus_comm (- _)); fold (Zminus (mag (x / y)) (mag y)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      apply Hexp; try assumption; rewrite <- Hxy; rewrite Hf1; apply Z.le_refl.
Qed.

Lemma round_round_div_aux1 :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  (fexp1 (mag (x / y)) <= mag (x / y))%Z ->
  ~ (midp fexp1 (x / y) - / 2 * ulp beta fexp2 (x / y)
     <= x / y
     < midp fexp1 (x / y)).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Fx Fy Hf1.
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (S : (x / y <> 0)%R).
apply Rmult_integral_contrapositive_currified; [now apply Rgt_not_eq|idtac].
now apply Rinv_neq_0_compat, Rgt_not_eq.
cut (~ (/ 2 * (ulp beta fexp1 (x / y) - ulp beta fexp2 (x / y))
        <= x / y - round beta fexp1 Zfloor (x / y)
        < / 2 * ulp beta fexp1 (x / y))).
{ intro H; intro H'; apply H; split.
  - apply (Rplus_le_reg_l (round beta fexp1 Zfloor (x / y))).
    ring_simplify.
    apply H'.
  - apply (Rplus_lt_reg_l (round beta fexp1 Zfloor (x / y))).
    ring_simplify.
    apply H'. }
set (u1 := bpow (fexp1 (mag (x / y)))).
set (u2 := bpow (fexp2 (mag (x / y)))).
set (x' := round beta fexp1 Zfloor (x / y)).
rewrite 2!ulp_neq_0; trivial.
revert Fx Fy.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (my := Ztrunc (y * bpow (- fexp1 (mag y)))).
intros Fx Fy.
intro Hlr.
apply (Rlt_irrefl (/ 2 * (u1 - u2))).
apply (Rle_lt_trans _ _ _ (proj1 Hlr)).
apply (Rplus_lt_reg_r x'); ring_simplify.
apply (Rmult_lt_reg_r y _ _ Py).
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l; [|now apply Rgt_not_eq]; rewrite Rmult_1_r.
rewrite Rmult_minus_distr_r; rewrite Rmult_plus_distr_r.
apply (Rmult_lt_reg_l 2); [lra|].
rewrite Rmult_minus_distr_l; rewrite Rmult_plus_distr_l.
do 5 rewrite <- Rmult_assoc.
rewrite Rinv_r; [|lra]; do 2 rewrite Rmult_1_l.
destruct (Zle_or_lt Z0 (fexp1 (mag x) - fexp1 (mag (x / y))
                     - fexp1 (mag y))%Z) as [He|He].
- (* fexp1 (mag (x / y)) + fexp1 (mag y)) <= fexp1 (mag x) *)
  apply Rle_lt_trans with (2 * x' * y + u1 * y
                                        - bpow (fexp1 (mag (x / y))
                                                + fexp1 (mag y))).
  + rewrite Fx at 1; rewrite Fy at 1 2.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag (x / y))
                                 - fexp1 (mag y))));
      [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r; rewrite (Rmult_plus_distr_r (_ * _ * _)).
    bpow_simplify.
    replace (2 * x' * _ * _)
    with (2 * IZR my * x' * bpow (- fexp1 (mag (x / y)))) by ring.
    rewrite (Rmult_comm u1).
    unfold x', u1, round, F2R, ulp, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite <- IZR_Zpower; [|exact He].
    do 4 rewrite <- mult_IZR.
    rewrite <- plus_IZR.
    rewrite <- minus_IZR.
    apply IZR_le.
    apply (Zplus_le_reg_r _ _ 1); ring_simplify.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite plus_IZR.
    do 4 rewrite mult_IZR; simpl.
    rewrite IZR_Zpower; [|exact He].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag (x / y))
                                 + fexp1 (mag y))));
      [now apply bpow_gt_0|bpow_simplify].
    rewrite Rmult_assoc.
    rewrite <- Fx.
    rewrite (Rmult_plus_distr_r _ _ (Raux.bpow _ _)).
    rewrite Rmult_assoc.
    rewrite bpow_plus.
    rewrite <- (Rmult_assoc (IZR (Zfloor _))).
    change (IZR (Zfloor _) * _) with x'.
    do 2 rewrite (Rmult_comm _ (bpow (fexp1 (mag y)))).
    rewrite Rmult_assoc.
    do 2 rewrite <- (Rmult_assoc (IZR my)).
    rewrite <- Fy.
    change (bpow _) with u1.
    apply (Rmult_lt_reg_l (/ 2)); [lra|].
    rewrite Rmult_plus_distr_l.
    do 4 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|lra]; do 2 rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (- y * x')); ring_simplify.
    apply (Rmult_lt_reg_l (/ y)); [now apply Rinv_0_lt_compat|].
    rewrite Rmult_minus_distr_l.
    do 3 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|now apply Rgt_not_eq]; do 2 rewrite Rmult_1_l.
    now rewrite Rmult_comm.
  + apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    * { apply Rmult_lt_compat_l.
        - apply bpow_gt_0.
        - apply Rabs_lt_inv.
          apply bpow_mag_gt. }
    * unfold u2, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite <- Zplus_assoc; rewrite (Zplus_comm (- _)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      [now apply Hexp; [| |rewrite <- Hxy]|].
      replace (_ - _ + 1)%Z with ((mag x + 1) - mag y)%Z by ring.
      apply Hexp.
      { now assert (fexp1 (mag x + 1) <= mag x)%Z;
        [apply valid_exp|lia]. }
      { assumption. }
      replace (_ + 1 - _)%Z with (mag x - mag y + 1)%Z by ring.
      now rewrite <- Hxy.
- (* fexp1 (mag x) < fexp1 (mag (x / y)) + fexp1 (mag y) *)
  apply Rle_lt_trans with (2 * x' * y + u1 * y - bpow (fexp1 (mag x))).
  + rewrite Fx at 1; rewrite Fy at 1 2.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r; rewrite (Rmult_plus_distr_r (_ * _ * _)).
    bpow_simplify.
    replace (2 * x' * _ * _)
    with (2 * IZR my * x' * bpow (fexp1 (mag y) - fexp1 (mag x))) by ring.
    rewrite (Rmult_comm u1).
    unfold x', u1, round, F2R, ulp, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite <- (IZR_Zpower _ (_ - _)%Z) by lia.
    do 5 rewrite <- mult_IZR.
    rewrite <- plus_IZR.
    rewrite <- minus_IZR.
    apply IZR_le.
    apply (Zplus_le_reg_r _ _ 1); ring_simplify.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite plus_IZR.
    do 5 rewrite mult_IZR; simpl.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite Rmult_assoc.
    rewrite <- Fx.
    rewrite (Rmult_plus_distr_r _ _ (Raux.bpow _ _)).
    bpow_simplify.
    rewrite Rmult_assoc.
    rewrite bpow_plus.
    rewrite <- (Rmult_assoc (IZR (Zfloor _))).
    change (IZR (Zfloor _) * _) with x'.
    do 2 rewrite (Rmult_comm _ (bpow (fexp1 (mag y)))).
    rewrite Rmult_assoc.
    do 2 rewrite <- (Rmult_assoc (IZR my)).
    rewrite <- Fy.
    change (bpow _) with u1.
    apply (Rmult_lt_reg_l (/ 2)); [lra|].
    rewrite Rmult_plus_distr_l.
    do 4 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|lra]; do 2 rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (- y * x')); ring_simplify.
    apply (Rmult_lt_reg_l (/ y)); [now apply Rinv_0_lt_compat|].
    rewrite Rmult_minus_distr_l.
    do 3 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|now apply Rgt_not_eq]; do 2 rewrite Rmult_1_l.
    now rewrite Rmult_comm.
  + apply Rplus_lt_compat_l.
    apply Ropp_lt_contravar.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    * { apply Rmult_lt_compat_l.
        - apply bpow_gt_0.
        - apply Rabs_lt_inv.
          apply bpow_mag_gt. }
    * unfold u2, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite (Zplus_comm (- _)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      apply Hexp; try assumption; rewrite <- Hxy; lia.
Qed.

Lemma round_round_div_aux2 :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  (fexp1 (mag (x / y)) <= mag (x / y))%Z ->
  ~ (midp fexp1 (x / y)
     < x / y
     <= midp fexp1 (x / y) + / 2 * ulp beta fexp2 (x / y)).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Px Py Fx Fy Hf1.
assert (Hfx : (fexp1 (mag x) < mag x)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
assert (Hfy : (fexp1 (mag y) < mag y)%Z);
  [now apply mag_generic_gt; [|apply Rgt_not_eq|]|].
cut (~ (/ 2 * ulp beta fexp1 (x / y)
        < x / y - round beta fexp1 Zfloor (x / y)
        <= / 2 * (ulp beta fexp1 (x / y) + ulp beta fexp2 (x / y)))).
{ intro H; intro H'; apply H; split.
  - apply (Rplus_lt_reg_l (round beta fexp1 Zfloor (x / y))).
    ring_simplify.
    apply H'.
  - apply (Rplus_le_reg_l (round beta fexp1 Zfloor (x / y))).
    ring_simplify.
    apply H'. }
set (u1 := bpow (fexp1 (mag (x / y)))).
set (u2 := bpow (fexp2 (mag (x / y)))).
set (x' := round beta fexp1 Zfloor (x / y)).
assert (S : (x / y <> 0)%R).
apply Rmult_integral_contrapositive_currified; [now apply Rgt_not_eq|idtac].
now apply Rinv_neq_0_compat, Rgt_not_eq.
rewrite 2!ulp_neq_0; trivial.
revert Fx Fy.
unfold generic_format, F2R, scaled_mantissa, cexp; simpl.
set (mx := Ztrunc (x * bpow (- fexp1 (mag x)))).
set (my := Ztrunc (y * bpow (- fexp1 (mag y)))).
intros Fx Fy.
intro Hlr.
apply (Rlt_irrefl (/ 2 * (u1 + u2))).
apply Rlt_le_trans with (x / y - x'); [|now apply Hlr].
apply (Rplus_lt_reg_r x'); ring_simplify.
apply (Rmult_lt_reg_r y _ _ Py).
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l; [|now apply Rgt_not_eq]; rewrite Rmult_1_r.
do 2 rewrite Rmult_plus_distr_r.
apply (Rmult_lt_reg_l 2); [lra|].
do 2 rewrite Rmult_plus_distr_l.
do 5 rewrite <- Rmult_assoc.
rewrite Rinv_r; [|lra]; do 2 rewrite Rmult_1_l.
destruct (Zle_or_lt Z0 (fexp1 (mag x) - fexp1 (mag (x / y))
                     - fexp1 (mag y))%Z) as [He|He].
- (* fexp1 (mag (x / y)) + fexp1 (mag y) <= fexp1 (mag x) *)
  apply Rlt_le_trans with (u1 * y + bpow (fexp1 (mag (x / y))
                                          + fexp1 (mag y))
                           + 2 * x' * y).
  + apply Rplus_lt_compat_r, Rplus_lt_compat_l.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    * { apply Rmult_lt_compat_l.
        - apply bpow_gt_0.
        - apply Rabs_lt_inv.
          apply bpow_mag_gt. }
    * unfold u2, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite <- Zplus_assoc; rewrite (Zplus_comm (- _)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      [now apply Hexp; [| |rewrite <- Hxy]|].
      replace (_ - _ + 1)%Z with ((mag x + 1) - mag y)%Z by ring.
      apply Hexp.
      { now assert (fexp1 (mag x + 1) <= mag x)%Z;
        [apply valid_exp|lia]. }
      { assumption. }
      replace (_ + 1 - _)%Z with (mag x - mag y + 1)%Z by ring.
      now rewrite <- Hxy.
  + apply Rge_le; rewrite Fx at 1; apply Rle_ge.
    replace (u1 * y) with (u1 * (IZR my * bpow (fexp1 (mag y))));
      [|now apply eq_sym; rewrite Fy at 1].
    replace (2 * x' * y) with (2 * x' * (IZR my * bpow (fexp1 (mag y))));
      [|now apply eq_sym; rewrite Fy at 1].
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag (x / y))
                                 - fexp1 (mag y))));
      [now apply bpow_gt_0|].
    do 2 rewrite Rmult_plus_distr_r.
    bpow_simplify.
    rewrite (Rmult_comm u1).
    unfold u1, ulp, cexp; bpow_simplify.
    rewrite (Rmult_assoc 2).
    rewrite (Rmult_comm x').
    rewrite (Rmult_assoc 2).
    unfold x', round, F2R, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite <- (IZR_Zpower _ (_ - _)%Z); [|exact He].
    do 4 rewrite <- mult_IZR.
    do 2 rewrite <- plus_IZR.
    apply IZR_le.
    rewrite Zplus_comm, Zplus_assoc.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite plus_IZR.
    do 4 rewrite mult_IZR; simpl.
    rewrite IZR_Zpower; [|exact He].
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag y))));
      [now apply bpow_gt_0|].
    rewrite Rmult_plus_distr_r.
    rewrite (Rmult_comm _ (IZR _)).
    do 2 rewrite Rmult_assoc.
    rewrite <- Fy.
    bpow_simplify.
    unfold Zminus; rewrite bpow_plus.
    rewrite (Rmult_assoc _ (IZR mx)).
    rewrite <- (Rmult_assoc (IZR mx)).
    rewrite <- Fx.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag (x / y)))));
      [now apply bpow_gt_0|].
    rewrite Rmult_plus_distr_r.
    bpow_simplify.
    rewrite (Rmult_comm _ y).
    do 2 rewrite Rmult_assoc.
    change (IZR (Zfloor _) * _) with x'.
    change (bpow _) with u1.
    apply (Rmult_lt_reg_l (/ 2)); [lra|].
    rewrite Rmult_plus_distr_l.
    do 4 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|lra]; do 2 rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (- y * x')); ring_simplify.
    apply (Rmult_lt_reg_l (/ y)); [now apply Rinv_0_lt_compat|].
    rewrite Rmult_plus_distr_l.
    do 3 rewrite <- Rmult_assoc.
    rewrite Ropp_mult_distr_r_reverse.
    rewrite Ropp_mult_distr_l_reverse.
    rewrite Rinv_l; [|now apply Rgt_not_eq]; do 2 rewrite Rmult_1_l.
    rewrite (Rmult_comm (/ y)).
    now rewrite (Rplus_comm (- x')).
- (* fexp1 (mag x) < fexp1 (mag (x / y)) + fexp1 (mag y) *)
  apply Rlt_le_trans with (2 * x' * y + u1 * y + bpow (fexp1 (mag x))).
  + rewrite Rplus_comm, Rplus_assoc; do 2 apply Rplus_lt_compat_l.
    apply Rlt_le_trans with (u2 * bpow (mag y)).
    * apply Rmult_lt_compat_l.
      now apply bpow_gt_0.
      now apply Rabs_lt_inv; apply bpow_mag_gt.
    * unfold u2, ulp, cexp; bpow_simplify; apply bpow_le.
      apply (Zplus_le_reg_r _ _ (- mag y)); ring_simplify.
      rewrite (Zplus_comm (- _)).
      destruct (mag_div_disj x y Px Py) as [Hxy|Hxy]; rewrite Hxy;
      apply Hexp; try assumption; rewrite <- Hxy; lia.
  + apply Rge_le; rewrite Fx at 1; apply Rle_ge.
    rewrite Fy at 1 2.
    apply (Rmult_le_reg_r (bpow (- fexp1 (mag x))));
      [now apply bpow_gt_0|].
    do 2 rewrite Rmult_plus_distr_r.
    bpow_simplify.
    replace (2 * x' * _ * _)
    with (2 * IZR my * x' * bpow (fexp1 (mag y) - fexp1 (mag x))) by ring.
    rewrite (Rmult_comm u1).
    unfold x', u1, round, F2R, ulp, scaled_mantissa, cexp; simpl.
    bpow_simplify.
    rewrite <- (IZR_Zpower _ (_ - _)%Z) by lia.
    do 5 rewrite <- mult_IZR.
    do 2 rewrite <- plus_IZR.
    apply IZR_le.
    apply Zlt_le_succ.
    apply lt_IZR.
    rewrite plus_IZR.
    do 5 rewrite mult_IZR; simpl.
    rewrite IZR_Zpower by lia.
    apply (Rmult_lt_reg_r (bpow (fexp1 (mag x))));
      [now apply bpow_gt_0|].
    rewrite (Rmult_assoc _ (IZR mx)).
    rewrite <- Fx.
    rewrite Rmult_plus_distr_r.
    bpow_simplify.
    rewrite bpow_plus.
    rewrite Rmult_assoc.
    rewrite <- (Rmult_assoc (IZR _)).
    change (IZR _ * bpow _) with x'.
    do 2 rewrite (Rmult_comm _ (bpow (fexp1 (mag y)))).
    rewrite Rmult_assoc.
    do 2 rewrite <- (Rmult_assoc (IZR my)).
    rewrite <- Fy.
    change (bpow _) with u1.
    apply (Rmult_lt_reg_l (/ 2)); [lra|].
    rewrite Rmult_plus_distr_l.
    do 4 rewrite <- Rmult_assoc.
    rewrite Rinv_l; [|lra]; do 2 rewrite Rmult_1_l.
    apply (Rplus_lt_reg_r (- y * x')); ring_simplify.
    apply (Rmult_lt_reg_l (/ y)); [now apply Rinv_0_lt_compat|].
    rewrite Rmult_plus_distr_l.
    do 3 rewrite <- Rmult_assoc.
    rewrite Ropp_mult_distr_r_reverse.
    rewrite Ropp_mult_distr_l_reverse.
    rewrite Rinv_l; [|now apply Rgt_not_eq]; do 2 rewrite Rmult_1_l.
    rewrite (Rmult_comm (/ y)).
    now rewrite (Rplus_comm (- x')).
Qed.

Lemma round_round_div_aux :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (exists n, (beta = 2 * n :> Z)%Z) ->
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x / y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Ebeta Hexp x y Px Py Fx Fy.
assert (Pxy : 0 < x / y).
{ apply Rmult_lt_0_compat; [exact Px|].
  now apply Rinv_0_lt_compat. }
apply round_round_all_mid_cases.
- exact Vfexp1.
- exact Vfexp2.
- exact Pxy.
- apply Hexp.
- intros Hf1 Hlxy.
  casetype False.
  now apply (round_round_div_aux0 fexp1 fexp2 _ _ choice1 choice2 Hexp x y).
- intros Hf1 Hlxy.
  casetype False.
  now apply (round_round_div_aux1 fexp1 fexp2 _ _ choice1 choice2 Hexp x y).
- intro H.
  apply round_round_eq_mid_beta_even; try assumption.
  apply Hexp.
- intros Hf1 Hlxy.
  casetype False.
  now apply (round_round_div_aux2 fexp1 fexp2 _ _ choice1 choice2 Hexp x y).
Qed.

Lemma round_round_div :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (exists n, (beta = 2 * n :> Z)%Z) ->
  round_round_div_hyp fexp1 fexp2 ->
  forall x y,
  y <> 0 ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round_round_eq fexp1 fexp2 choice1 choice2 (x / y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Ebeta Hexp x y Nzy Fx Fy.
unfold round_round_eq.
destruct (Rtotal_order x 0) as [Nx|[Zx|Px]].
- (* x < 0 *)
  destruct (Rtotal_order y 0) as [Ny|[Zy|Py]].
  + (* y < 0 *)
    rewrite <- (Ropp_involutive x).
    rewrite <- (Ropp_involutive y).
    rewrite Ropp_div.
    unfold Rdiv; rewrite <- Ropp_inv_permute; [|lra].
    rewrite Ropp_mult_distr_r_reverse.
    rewrite Ropp_involutive.
    fold ((- x) / (- y)).
    apply Ropp_lt_contravar in Nx.
    apply Ropp_lt_contravar in Ny.
    rewrite Ropp_0 in Nx, Ny.
    apply generic_format_opp in Fx.
    apply generic_format_opp in Fy.
    now apply round_round_div_aux.
  + (* y = 0 *)
    now casetype False; apply Nzy.
  + (* y > 0 *)
    rewrite <- (Ropp_involutive x).
    rewrite Ropp_div.
    do 3 rewrite round_N_opp.
    apply Ropp_eq_compat.
    apply Ropp_lt_contravar in Nx.
    rewrite Ropp_0 in Nx.
    apply generic_format_opp in Fx.
    now apply round_round_div_aux.
- (* x = 0 *)
  rewrite Zx.
  unfold Rdiv; rewrite Rmult_0_l.
  now rewrite round_0; [|apply valid_rnd_N].
- (* x > 0 *)
  destruct (Rtotal_order y 0) as [Ny|[Zy|Py]].
  + (* y < 0 *)
    rewrite <- (Ropp_involutive y).
    unfold Rdiv; rewrite <- Ropp_inv_permute; [|lra].
    rewrite Ropp_mult_distr_r_reverse.
    do 3 rewrite round_N_opp.
    apply Ropp_eq_compat.
    apply Ropp_lt_contravar in Ny.
    rewrite Ropp_0 in Ny.
    apply generic_format_opp in Fy.
    now apply round_round_div_aux.
  + (* y = 0 *)
    now casetype False; apply Nzy.
  + (* y > 0 *)
    now apply round_round_div_aux.
Qed.

Section Double_round_div_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLX_round_round_div_hyp :
  (2 * prec <= prec')%Z ->
  round_round_div_hyp (FLX_exp prec) (FLX_exp prec').
Proof.
intros Hprec.
unfold Prec_gt_0 in prec_gt_0_.
unfold FLX_exp.
unfold round_round_div_hyp.
split; [now intro ex; lia|].
split; [|split; [|split]]; intros ex ey; lia.
Qed.

Theorem round_round_div_FLX :
  forall choice1 choice2,
  (exists n, (beta = 2 * n :> Z)%Z) ->
  (2 * prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FLX_format beta prec x -> FLX_format beta prec y ->
  round_round_eq (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x / y).
Proof.
intros choice1 choice2 Ebeta Hprec x y Nzy Fx Fy.
apply round_round_div.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- exact Ebeta.
- now apply FLX_round_round_div_hyp.
- exact Nzy.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

End Double_round_div_FLX.

Section Double_round_div_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FLT_round_round_div_hyp :
  (emin' <= emin - prec - 2)%Z ->
  (2 * prec <= prec')%Z ->
  round_round_div_hyp (FLT_exp emin prec) (FLT_exp emin' prec').
Proof.
intros Hemin Hprec.
unfold FLT_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_div_hyp.
split; [intro ex|split; [|split; [|split]]; intros ex ey].
- generalize (Zmax_spec (ex - prec') emin').
  generalize (Zmax_spec (ex - prec) emin).
  lia.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec') emin').
  lia.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ey - prec) emin).
  generalize (Zmax_spec (ex - ey + 1 - prec) emin).
  generalize (Zmax_spec (ex - ey + 1 - prec') emin').
  lia.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec') emin').
  lia.
- generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec) emin).
  generalize (Zmax_spec (ex - ey - prec') emin').
  lia.
Qed.

Theorem round_round_div_FLT :
  forall choice1 choice2,
  (exists n, (beta = 2 * n :> Z)%Z) ->
  (emin' <= emin - prec - 2)%Z ->
  (2 * prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round_round_eq (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x / y).
Proof.
intros choice1 choice2 Ebeta Hemin Hprec x y Nzy Fx Fy.
apply round_round_div.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- exact Ebeta.
- now apply FLT_round_round_div_hyp.
- exact Nzy.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

End Double_round_div_FLT.

Section Double_round_div_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Lemma FTZ_round_round_div_hyp :
  (emin' + prec' <= emin - 1)%Z ->
  (2 * prec <= prec')%Z ->
  round_round_div_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec').
Proof.
intros Hemin Hprec.
unfold FTZ_exp.
unfold Prec_gt_0 in prec_gt_0_.
unfold Prec_gt_0 in prec_gt_0_.
unfold round_round_div_hyp.
split; [intro ex|split; [|split; [|split]]; intros ex ey].
- destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ex - prec) emin);
  lia.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec') emin');
  lia.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey + 1 - prec) emin);
  destruct (Z.ltb_spec (ex - ey + 1 - prec') emin');
  lia.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec') emin');
  lia.
- destruct (Z.ltb_spec (ex - prec) emin);
  destruct (Z.ltb_spec (ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec) emin);
  destruct (Z.ltb_spec (ex - ey - prec') emin');
  lia.
Qed.

Theorem round_round_div_FTZ :
  forall choice1 choice2,
  (exists n, (beta = 2 * n :> Z)%Z) ->
  (emin' + prec' <= emin - 1)%Z ->
  (2 * prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round_round_eq (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x / y).
Proof.
intros choice1 choice2 Ebeta Hemin Hprec x y Nzy Fx Fy.
apply round_round_div.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- exact Ebeta.
- now apply FTZ_round_round_div_hyp.
- exact Nzy.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

End Double_round_div_FTZ.

End Double_round_div.

End Double_round.

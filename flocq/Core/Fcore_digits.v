(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2011-2013 Sylvie Boldo
#<br />#
Copyright (C) 2011-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import ZArith.
Require Import Zquot.
Require Import Fcore_Zaux.

(** Number of bits (radix 2) of a positive integer.

It serves as an upper bound on the number of digits to ensure termination.
*)

Fixpoint digits2_Pnat (n : positive) : nat :=
  match n with
  | xH => O
  | xO p => S (digits2_Pnat p)
  | xI p => S (digits2_Pnat p)
  end.

Theorem digits2_Pnat_correct :
  forall n,
  let d := digits2_Pnat n in
  (Zpower_nat 2 d <= Zpos n < Zpower_nat 2 (S d))%Z.
Proof.
intros n d. unfold d. clear.
assert (Hp: forall m, (Zpower_nat 2 (S m) = 2 * Zpower_nat 2 m)%Z) by easy.
induction n ; simpl digits2_Pnat.
rewrite Zpos_xI, 2!Hp.
omega.
rewrite (Zpos_xO n), 2!Hp.
omega.
now split.
Qed.

Section Fcore_digits.

Variable beta : radix.

Definition Zdigit n k := Z.rem (Z.quot n (Zpower beta k)) beta.

Theorem Zdigit_lt :
  forall n k,
  (k < 0)%Z ->
  Zdigit n k = Z0.
Proof.
intros n [|k|k] Hk ; try easy.
now case n.
Qed.

Theorem Zdigit_0 :
  forall k, Zdigit 0 k = Z0.
Proof.
intros k.
unfold Zdigit.
rewrite Zquot_0_l.
apply Zrem_0_l.
Qed.

Theorem Zdigit_opp :
  forall n k,
  Zdigit (-n) k = Zopp (Zdigit n k).
Proof.
intros n k.
unfold Zdigit.
rewrite Zquot_opp_l.
apply Zrem_opp_l.
Qed.

Theorem Zdigit_ge_Zpower_pos :
  forall e n,
  (0 <= n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof.
intros e n Hn k Hk.
unfold Zdigit.
rewrite Zquot_small.
apply Zrem_0_l.
split.
apply Hn.
apply Zlt_le_trans with (1 := proj2 Hn).
replace k with (e + (k - e))%Z by ring.
rewrite Zpower_plus.
rewrite <- (Zmult_1_r (beta ^ e)) at 1.
apply Zmult_le_compat_l.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zlt_le_weak.
now apply Zle_lt_trans with n.
generalize (Zle_lt_trans _ _ _ (proj1 Hn) (proj2 Hn)).
clear.
now destruct e as [|e|e].
now apply Zle_minus_le_0.
Qed.

Theorem Zdigit_ge_Zpower :
  forall e n,
  (Zabs n < Zpower beta e)%Z ->
  forall k, (e <= k)%Z -> Zdigit n k = Z0.
Proof.
intros e [|n|n] Hn k.
easy.
apply Zdigit_ge_Zpower_pos.
now split.
intros He.
change (Zneg n) with (Zopp (Zpos n)).
rewrite Zdigit_opp.
rewrite Zdigit_ge_Zpower_pos with (2 := He).
apply Zopp_0.
now split.
Qed.

Theorem Zdigit_not_0_pos :
  forall e n, (0 <= e)%Z ->
  (Zpower beta e <= n < Zpower beta (e + 1))%Z ->
  Zdigit n e <> Z0.
Proof.
intros e n He (Hn1,Hn2).
unfold Zdigit.
rewrite <- ZOdiv_mod_mult.
rewrite Zrem_small.
intros H.
apply Zle_not_lt with (1 := Hn1).
rewrite (Z.quot_rem' n (beta ^ e)).
rewrite H, Zmult_0_r, Zplus_0_l.
apply Zrem_lt_pos_pos.
apply Zle_trans with (2 := Hn1).
apply Zpower_ge_0.
now apply Zpower_gt_0.
split.
apply Zle_trans with (2 := Hn1).
apply Zpower_ge_0.
replace (beta ^ e * beta)%Z with (beta ^ (e + 1))%Z.
exact Hn2.
rewrite <- (Zmult_1_r beta) at 3.
now apply (Zpower_plus beta e 1).
Qed.

Theorem Zdigit_not_0 :
  forall e n, (0 <= e)%Z ->
  (Zpower beta e <= Zabs n < Zpower beta (e + 1))%Z ->
  Zdigit n e <> Z0.
Proof.
intros e n He Hn.
destruct (Zle_or_lt 0 n) as [Hn'|Hn'].
rewrite (Zabs_eq _ Hn') in Hn.
now apply Zdigit_not_0_pos.
intros H.
rewrite (Zabs_non_eq n) in Hn by now apply Zlt_le_weak.
apply (Zdigit_not_0_pos _ _ He Hn).
now rewrite Zdigit_opp, H.
Qed.

Theorem Zdigit_mul_pow :
  forall n k k', (0 <= k')%Z ->
  Zdigit (n * Zpower beta k') k = Zdigit n (k - k').
Proof.
intros n k k' Hk'.
destruct (Zle_or_lt k' k) as [H|H].
revert k H.
pattern k' ; apply Zlt_0_ind with (2 := Hk').
clear k' Hk'.
intros k' IHk' Hk' k H.
unfold Zdigit.
apply (f_equal (fun x => Z.rem x beta)).
pattern k at 1 ; replace k with (k - k' + k')%Z by ring.
rewrite Zpower_plus with (2 := Hk').
apply Zquot_mult_cancel_r.
apply Zgt_not_eq.
now apply Zpower_gt_0.
now apply Zle_minus_le_0.
destruct (Zle_or_lt 0 k) as [H0|H0].
rewrite (Zdigit_lt n) by omega.
unfold Zdigit.
replace k' with (k' - k + k)%Z by ring.
rewrite Zpower_plus with (2 := H0).
rewrite Zmult_assoc, Z_quot_mult.
replace (k' - k)%Z with (k' - k - 1 + 1)%Z by ring.
rewrite Zpower_exp by omega.
rewrite Zmult_assoc.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply Z_rem_mult.
apply Zgt_not_eq.
now apply Zpower_gt_0.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
rewrite Zdigit_lt with (1 := H0).
apply sym_eq.
apply Zdigit_lt.
omega.
Qed.

Theorem Zdigit_div_pow :
  forall n k k', (0 <= k)%Z -> (0 <= k')%Z ->
  Zdigit (Z.quot n (Zpower beta k')) k = Zdigit n (k + k').
Proof.
intros n k k' Hk Hk'.
unfold Zdigit.
rewrite Zquot_Zquot.
rewrite Zplus_comm.
now rewrite Zpower_plus.
Qed.

Theorem Zdigit_mod_pow :
  forall n k k', (k < k')%Z ->
  Zdigit (Z.rem n (Zpower beta k')) k = Zdigit n k.
Proof.
intros n k k' Hk.
destruct (Zle_or_lt 0 k) as [H|H].
unfold Zdigit.
rewrite <- 2!ZOdiv_mod_mult.
apply (f_equal (fun x => Z.quot x (beta ^ k))).
replace k' with (k + 1 + (k' - (k + 1)))%Z by ring.
rewrite Zpower_exp by omega.
rewrite Zmult_comm.
rewrite Zpower_plus by easy.
change (Zpower beta 1) with (beta * 1)%Z.
rewrite Zmult_1_r.
apply ZOmod_mod_mult.
now rewrite 2!Zdigit_lt.
Qed.

Theorem Zdigit_mod_pow_out :
  forall n k k', (0 <= k' <= k)%Z ->
  Zdigit (Z.rem n (Zpower beta k')) k = Z0.
Proof.
intros n k k' Hk.
unfold Zdigit.
rewrite ZOdiv_small_abs.
apply Zrem_0_l.
apply Zlt_le_trans with (Zpower beta k').
rewrite <- (Zabs_eq (beta ^ k')) at 2 by apply Zpower_ge_0.
apply Zrem_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
now apply Zpower_le.
Qed.

Fixpoint Zsum_digit f k :=
  match k with
  | O => Z0
  | S k => (Zsum_digit f k + f (Z_of_nat k) * Zpower beta (Z_of_nat k))%Z
  end.

Theorem Zsum_digit_digit :
  forall n k,
  Zsum_digit (Zdigit n) k = Z.rem n (Zpower beta (Z_of_nat k)).
Proof.
intros n.
induction k.
apply sym_eq.
apply Zrem_1_r.
simpl Zsum_digit.
rewrite IHk.
unfold Zdigit.
rewrite <- ZOdiv_mod_mult.
rewrite <- (ZOmod_mod_mult n beta).
rewrite Zmult_comm.
replace (beta ^ Z_of_nat k * beta)%Z with (Zpower beta (Z_of_nat (S k))).
rewrite Zplus_comm, Zmult_comm.
apply sym_eq.
apply Z.quot_rem'.
rewrite inj_S.
rewrite <- (Zmult_1_r beta) at 3.
apply Zpower_plus.
apply Zle_0_nat.
easy.
Qed.

Theorem Zpower_gt_id :
  forall n, (n < Zpower beta n)%Z.
Proof.
intros [|n|n] ; try easy.
simpl.
rewrite Zpower_pos_nat.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
induction (nat_of_P n).
easy.
rewrite inj_S.
change (Zpower_nat beta (S n0)) with (beta * Zpower_nat beta n0)%Z.
unfold Zsucc.
apply Zlt_le_trans with (beta * (Z_of_nat n0 + 1))%Z.
clear.
apply Zlt_0_minus_lt.
replace (beta * (Z_of_nat n0 + 1) - (Z_of_nat n0 + 1))%Z with ((beta - 1) * (Z_of_nat n0 + 1))%Z by ring.
apply Zmult_lt_0_compat.
cut (2 <= beta)%Z. omega.
apply Zle_bool_imp_le.
apply beta.
apply (Zle_lt_succ 0).
apply Zle_0_nat.
apply Zmult_le_compat_l.
now apply Zlt_le_succ.
apply Zle_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply beta.
Qed.

Theorem Zdigit_ext :
  forall n1 n2,
  (forall k, (0 <= k)%Z -> Zdigit n1 k = Zdigit n2 k) ->
  n1 = n2.
Proof.
intros n1 n2 H.
rewrite <- (ZOmod_small_abs n1 (Zpower beta (Zmax (Zabs n1) (Zabs n2)))).
rewrite <- (ZOmod_small_abs n2 (Zpower beta (Zmax (Zabs n1) (Zabs n2)))) at 2.
replace (Zmax (Zabs n1) (Zabs n2)) with (Z_of_nat (Zabs_nat (Zmax (Zabs n1) (Zabs n2)))).
rewrite <- 2!Zsum_digit_digit.
induction (Zabs_nat (Zmax (Zabs n1) (Zabs n2))).
easy.
simpl.
rewrite H, IHn.
apply refl_equal.
apply Zle_0_nat.
rewrite inj_Zabs_nat.
apply Zabs_eq.
apply Zle_trans with (Zabs n1).
apply Zabs_pos.
apply Zle_max_l.
apply Zlt_le_trans with (Zpower beta (Zabs n2)).
apply Zpower_gt_id.
apply Zpower_le.
apply Zle_max_r.
apply Zlt_le_trans with (Zpower beta (Zabs n1)).
apply Zpower_gt_id.
apply Zpower_le.
apply Zle_max_l.
Qed.

Theorem ZOmod_plus_pow_digit :
  forall u v n, (0 <= u * v)%Z ->
  (forall k, (0 <= k < n)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  Z.rem (u + v) (Zpower beta n) = (Z.rem u (Zpower beta n) + Z.rem v (Zpower beta n))%Z.
Proof.
intros u v n Huv Hd.
destruct (Zle_or_lt 0 n) as [Hn|Hn].
rewrite Zplus_rem with (1 := Huv).
apply ZOmod_small_abs.
generalize (Zle_refl n).
pattern n at -2 ; rewrite <- Zabs_eq with (1 := Hn).
rewrite <- (inj_Zabs_nat n).
induction (Zabs_nat n) as [|p IHp].
now rewrite 2!Zrem_1_r.
rewrite <- 2!Zsum_digit_digit.
simpl Zsum_digit.
rewrite inj_S.
intros Hn'.
replace (Zsum_digit (Zdigit u) p + Zdigit u (Z_of_nat p) * beta ^ Z_of_nat p +
  (Zsum_digit (Zdigit v) p + Zdigit v (Z_of_nat p) * beta ^ Z_of_nat p))%Z with
  (Zsum_digit (Zdigit u) p + Zsum_digit (Zdigit v) p +
  (Zdigit u (Z_of_nat p) + Zdigit v (Z_of_nat p)) * beta ^ Z_of_nat p)%Z by ring.
apply (Zle_lt_trans _ _ _ (Zabs_triangle _ _)).
replace (beta ^ Zsucc (Z_of_nat p))%Z with (beta ^ Z_of_nat p + (beta - 1) * beta ^ Z_of_nat p)%Z.
apply Zplus_lt_le_compat.
rewrite 2!Zsum_digit_digit.
apply IHp.
now apply Zle_succ_le.
rewrite Zabs_Zmult.
rewrite (Zabs_eq (beta ^ Z_of_nat p)) by apply Zpower_ge_0.
apply Zmult_le_compat_r. 2: apply Zpower_ge_0.
apply Zlt_succ_le.
assert (forall u v, Zabs (Zdigit u v) < Zsucc (beta -  1))%Z.
clear ; intros n k.
assert (0 < beta)%Z.
apply Zlt_le_trans with 2%Z.
apply refl_equal.
apply Zle_bool_imp_le.
apply beta.
replace (Zsucc (beta - 1)) with (Zabs beta).
apply Zrem_lt.
now apply Zgt_not_eq.
rewrite Zabs_eq.
apply Zsucc_pred.
now apply Zlt_le_weak.
assert (0 <= Z_of_nat p < n)%Z.
split.
apply Zle_0_nat.
apply Zgt_lt.
now apply Zle_succ_gt.
destruct (Hd (Z_of_nat p) H0) as [K|K] ; rewrite K.
apply H.
rewrite Zplus_0_r.
apply H.
unfold Zsucc.
ring_simplify.
rewrite Zpower_plus.
change (beta ^1)%Z with (beta * 1)%Z.
now rewrite Zmult_1_r.
apply Zle_0_nat.
easy.
destruct n as [|n|n] ; try easy.
now rewrite 3!Zrem_0_r.
Qed.

Theorem ZOdiv_plus_pow_digit :
  forall u v n, (0 <= u * v)%Z ->
  (forall k, (0 <= k < n)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  Z.quot (u + v) (Zpower beta n) = (Z.quot u (Zpower beta n) + Z.quot v (Zpower beta n))%Z.
Proof.
intros u v n Huv Hd.
rewrite <- (Zplus_0_r (Z.quot u (Zpower beta n) + Z.quot v (Zpower beta n))).
rewrite ZOdiv_plus with (1 := Huv).
rewrite <- ZOmod_plus_pow_digit by assumption.
apply f_equal.
destruct (Zle_or_lt 0 n) as [Hn|Hn].
apply ZOdiv_small_abs.
rewrite <- Zabs_eq.
apply Zrem_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
apply Zpower_ge_0.
clear -Hn.
destruct n as [|n|n] ; try easy.
apply Zquot_0_r.
Qed.

Theorem Zdigit_plus :
  forall u v, (0 <= u * v)%Z ->
  (forall k, (0 <= k)%Z -> Zdigit u k = Z0 \/ Zdigit v k = Z0) ->
  forall k,
  Zdigit (u + v) k = (Zdigit u k + Zdigit v k)%Z.
Proof.
intros u v Huv Hd k.
destruct (Zle_or_lt 0 k) as [Hk|Hk].
unfold Zdigit.
rewrite ZOdiv_plus_pow_digit with (1 := Huv).
rewrite <- (Zmult_1_r beta) at 3 5 7.
change (beta * 1)%Z with (beta ^1)%Z.
apply ZOmod_plus_pow_digit.
apply Zsame_sign_trans_weak with v.
intros Zv ; rewrite Zv.
apply Zquot_0_l.
rewrite Zmult_comm.
apply Zsame_sign_trans_weak with u.
intros Zu ; rewrite Zu.
apply Zquot_0_l.
now rewrite Zmult_comm.
apply Zsame_sign_odiv.
apply Zpower_ge_0.
apply Zsame_sign_odiv.
apply Zpower_ge_0.
intros k' (Hk1,Hk2).
rewrite 2!Zdigit_div_pow by assumption.
apply Hd.
now apply Zplus_le_0_compat.
intros k' (Hk1,Hk2).
now apply Hd.
now rewrite 3!Zdigit_lt.
Qed.

(** Left and right shifts *)

Definition Zscale n k :=
  if Zle_bool 0 k then (n * Zpower beta k)%Z else Z.quot n (Zpower beta (-k)).

Theorem Zdigit_scale :
  forall n k k', (0 <= k')%Z ->
  Zdigit (Zscale n k) k' = Zdigit n (k' - k).
Proof.
intros n k k' Hk'.
unfold Zscale.
case Zle_bool_spec ; intros Hk.
now apply Zdigit_mul_pow.
apply Zdigit_div_pow with (1 := Hk').
omega.
Qed.

Theorem Zscale_0 :
  forall k,
  Zscale 0 k = Z0.
Proof.
intros k.
unfold Zscale.
case Zle_bool.
apply Zmult_0_l.
apply Zquot_0_l.
Qed.

Theorem Zsame_sign_scale :
  forall n k,
  (0 <= n * Zscale n k)%Z.
Proof.
intros n k.
unfold Zscale.
case Zle_bool_spec ; intros Hk.
rewrite Zmult_assoc.
apply Zmult_le_0_compat.
apply Zsame_sign_imp ; apply Zlt_le_weak.
apply Zpower_ge_0.
apply Zsame_sign_odiv.
apply Zpower_ge_0.
Qed.

Theorem Zscale_mul_pow :
  forall n k k', (0 <= k)%Z ->
  Zscale (n * Zpower beta k) k' = Zscale n (k + k').
Proof.
intros n k k' Hk.
unfold Zscale.
case Zle_bool_spec ; intros Hk'.
rewrite Zle_bool_true.
rewrite <- Zmult_assoc.
apply f_equal.
now rewrite Zpower_plus.
now apply Zplus_le_0_compat.
case Zle_bool_spec ; intros Hk''.
pattern k at 1 ; replace k with (k + k' + -k')%Z by ring.
assert (0 <= -k')%Z by omega.
rewrite Zpower_plus by easy.
rewrite Zmult_assoc, Z_quot_mult.
apply refl_equal.
apply Zgt_not_eq.
now apply Zpower_gt_0.
replace (-k')%Z with (-(k+k') + k)%Z by ring.
rewrite Zpower_plus with (2 := Hk).
apply Zquot_mult_cancel_r.
apply Zgt_not_eq.
now apply Zpower_gt_0.
omega.
Qed.

Theorem Zscale_scale :
  forall n k k', (0 <= k)%Z ->
  Zscale (Zscale n k) k' = Zscale n (k + k').
Proof.
intros n k k' Hk.
unfold Zscale at 2.
rewrite Zle_bool_true with (1 := Hk).
now apply Zscale_mul_pow.
Qed.

(** Slice of an integer *)

Definition Zslice n k1 k2 :=
  if Zle_bool 0 k2 then Z.rem (Zscale n (-k1)) (Zpower beta k2) else Z0.

Theorem Zdigit_slice :
  forall n k1 k2 k, (0 <= k < k2)%Z ->
  Zdigit (Zslice n k1 k2) k = Zdigit n (k1 + k).
Proof.
intros n k1 k2 k Hk.
unfold Zslice.
rewrite Zle_bool_true.
rewrite Zdigit_mod_pow by apply Hk.
rewrite Zdigit_scale by apply Hk.
unfold Zminus.
now rewrite Zopp_involutive, Zplus_comm.
omega.
Qed.

Theorem Zdigit_slice_out :
  forall n k1 k2 k, (k2 <= k)%Z ->
  Zdigit (Zslice n k1 k2) k = Z0.
Proof.
intros n k1 k2 k Hk.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
apply Zdigit_mod_pow_out.
now split.
apply Zdigit_0.
Qed.

Theorem Zslice_0 :
  forall k k',
  Zslice 0 k k' = Z0.
Proof.
intros k k'.
unfold Zslice.
case Zle_bool.
rewrite Zscale_0.
apply Zrem_0_l.
apply refl_equal.
Qed.

Theorem Zsame_sign_slice :
  forall n k k',
  (0 <= n * Zslice n k k')%Z.
Proof.
intros n k k'.
unfold Zslice.
case Zle_bool.
apply Zsame_sign_trans_weak with (Zscale n (-k)).
intros H ; rewrite H.
apply Zrem_0_l.
apply Zsame_sign_scale.
rewrite Zmult_comm.
apply Zrem_sgn2.
now rewrite Zmult_0_r.
Qed.

Theorem Zslice_slice :
  forall n k1 k2 k1' k2', (0 <= k1' <= k2)%Z ->
  Zslice (Zslice n k1 k2) k1' k2' = Zslice n (k1 + k1') (Zmin (k2 - k1') k2').
Proof.
intros n k1 k2 k1' k2' Hk1'.
destruct (Zle_or_lt 0 k2') as [Hk2'|Hk2'].
apply Zdigit_ext.
intros k Hk.
destruct (Zle_or_lt (Zmin (k2 - k1') k2') k) as [Hk'|Hk'].
rewrite (Zdigit_slice_out n (k1 + k1')) with (1 := Hk').
destruct (Zle_or_lt k2' k) as [Hk''|Hk''].
now apply Zdigit_slice_out.
rewrite Zdigit_slice by now split.
apply Zdigit_slice_out.
zify ; omega.
rewrite Zdigit_slice by (zify ; omega).
rewrite (Zdigit_slice n (k1 + k1')) by now split.
rewrite Zdigit_slice.
now rewrite Zplus_assoc.
zify ; omega.
unfold Zslice.
rewrite Zmin_r.
now rewrite Zle_bool_false.
omega.
Qed.

Theorem Zslice_mul_pow :
  forall n k k1 k2, (0 <= k)%Z ->
  Zslice (n * Zpower beta k) k1 k2 = Zslice n (k1 - k) k2.
Proof.
intros n k k1 k2 Hk.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
2: apply refl_equal.
rewrite Zscale_mul_pow with (1 := Hk).
now replace (- (k1 - k))%Z with (k + -k1)%Z by ring.
Qed.

Theorem Zslice_div_pow :
  forall n k k1 k2, (0 <= k)%Z -> (0 <= k1)%Z ->
  Zslice (Z.quot n (Zpower beta k)) k1 k2 = Zslice n (k1 + k) k2.
Proof.
intros n k k1 k2 Hk Hk1.
unfold Zslice.
case Zle_bool_spec ; intros Hk2.
2: apply refl_equal.
apply (f_equal (fun x => Z.rem x (beta ^ k2))).
unfold Zscale.
case Zle_bool_spec ; intros Hk1'.
replace k1 with Z0 by omega.
case Zle_bool_spec ; intros Hk'.
replace k with Z0 by omega.
simpl.
now rewrite Zquot_1_r.
rewrite Zopp_involutive.
apply Zmult_1_r.
rewrite Zle_bool_false by omega.
rewrite 2!Zopp_involutive, Zplus_comm.
rewrite Zpower_plus by assumption.
apply Zquot_Zquot.
Qed.

Theorem Zslice_scale :
  forall n k k1 k2, (0 <= k1)%Z ->
  Zslice (Zscale n k) k1 k2 = Zslice n (k1 - k) k2.
Proof.
intros n k k1 k2 Hk1.
unfold Zscale.
case Zle_bool_spec; intros Hk.
now apply Zslice_mul_pow.
apply Zslice_div_pow with (2 := Hk1).
omega.
Qed.

Theorem Zslice_div_pow_scale :
  forall n k k1 k2, (0 <= k)%Z ->
  Zslice (Z.quot n (Zpower beta k)) k1 k2 = Zscale (Zslice n k (k1 + k2)) (-k1).
Proof.
intros n k k1 k2 Hk.
apply Zdigit_ext.
intros k' Hk'.
rewrite Zdigit_scale with (1 := Hk').
unfold Zminus.
rewrite (Zplus_comm k'), Zopp_involutive.
destruct (Zle_or_lt k2 k') as [Hk2|Hk2].
rewrite Zdigit_slice_out with (1 := Hk2).
apply sym_eq.
apply Zdigit_slice_out.
now apply Zplus_le_compat_l.
rewrite Zdigit_slice by now split.
destruct (Zle_or_lt 0 (k1 + k')) as [Hk1'|Hk1'].
rewrite Zdigit_slice by omega.
rewrite Zdigit_div_pow by assumption.
apply f_equal.
ring.
now rewrite 2!Zdigit_lt.
Qed.

Theorem Zplus_slice :
  forall n k l1 l2, (0 <= l1)%Z -> (0 <= l2)%Z ->
  (Zslice n k l1 + Zscale (Zslice n (k + l1) l2) l1)%Z = Zslice n k (l1 + l2).
Proof.
intros n k1 l1 l2 Hl1 Hl2.
clear Hl1.
apply Zdigit_ext.
intros k Hk.
rewrite Zdigit_plus.
rewrite Zdigit_scale with (1 := Hk).
destruct (Zle_or_lt (l1 + l2) k) as [Hk2|Hk2].
rewrite Zdigit_slice_out with (1 := Hk2).
now rewrite 2!Zdigit_slice_out by omega.
rewrite Zdigit_slice with (1 := conj Hk Hk2).
destruct (Zle_or_lt l1 k) as [Hk1|Hk1].
rewrite Zdigit_slice_out with (1 := Hk1).
rewrite Zdigit_slice by omega.
simpl ; apply f_equal.
ring.
rewrite Zdigit_slice with (1 := conj Hk Hk1).
rewrite (Zdigit_lt _ (k - l1)) by omega.
apply Zplus_0_r.
rewrite Zmult_comm.
apply Zsame_sign_trans_weak with n.
intros H ; rewrite H.
apply Zslice_0.
rewrite Zmult_comm.
apply Zsame_sign_trans_weak with (Zslice n (k1 + l1) l2).
intros H ; rewrite H.
apply Zscale_0.
apply Zsame_sign_slice.
apply Zsame_sign_scale.
apply Zsame_sign_slice.
clear k Hk ; intros k Hk.
rewrite Zdigit_scale with (1 := Hk).
destruct (Zle_or_lt l1 k) as [Hk1|Hk1].
left.
now apply Zdigit_slice_out.
right.
apply Zdigit_lt.
omega.
Qed.

Section digits_aux.

Variable p : Z.

Fixpoint Zdigits_aux (nb pow : Z) (n : nat) { struct n } : Z :=
  match n with
  | O => nb
  | S n => if Zlt_bool p pow then nb else Zdigits_aux (nb + 1) (Zmult beta pow) n
  end.

End digits_aux.

(** Number of digits of an integer *)

Definition Zdigits n :=
  match n with
  | Z0 => Z0
  | Zneg p => Zdigits_aux (Zpos p) 1 beta (digits2_Pnat p)
  | Zpos p => Zdigits_aux n 1 beta (digits2_Pnat p)
  end.

Theorem Zdigits_correct :
  forall n,
  (Zpower beta (Zdigits n - 1) <= Zabs n < Zpower beta (Zdigits n))%Z.
Proof.
cut (forall p, Zpower beta (Zdigits (Zpos p) - 1) <= Zpos p < Zpower beta (Zdigits (Zpos p)))%Z.
intros H [|n|n] ; try exact (H n).
now split.
intros n.
simpl.
(* *)
assert (U: (Zpos n < Zpower beta (Z_of_nat (S (digits2_Pnat n))))%Z).
apply Zlt_le_trans with (1 := proj2 (digits2_Pnat_correct n)).
rewrite Zpower_Zpower_nat.
rewrite Zabs_nat_Z_of_nat.
induction (S (digits2_Pnat n)).
easy.
rewrite 2!(Zpower_nat_S).
apply Zmult_le_compat with (2 := IHn0).
apply Zle_bool_imp_le.
apply beta.
easy.
rewrite <- (Zabs_nat_Z_of_nat n0).
rewrite <- Zpower_Zpower_nat.
apply (Zpower_ge_0 (Build_radix 2 (refl_equal true))).
apply Zle_0_nat.
apply Zle_0_nat.
(* *)
revert U.
rewrite inj_S.
unfold Zsucc.
generalize (digits2_Pnat n).
intros u U.
pattern (radix_val beta) at 2 4 ; replace (radix_val beta) with (Zpower beta 1) by apply Zmult_1_r.
assert (V: (Zpower beta (1 - 1) <= Zpos n)%Z).
now apply (Zlt_le_succ 0).
generalize (conj V U).
clear.
generalize (Zle_refl 1).
generalize 1%Z at 2 3 5 6 7 9 10.
(* *)
induction u.
easy.
rewrite inj_S; unfold Zsucc.
simpl Zdigits_aux.
intros v Hv U.
case Zlt_bool_spec ; intros K.
now split.
pattern (radix_val beta) at 2 5 ; replace (radix_val beta) with (Zpower beta 1) by apply Zmult_1_r.
rewrite <- Zpower_plus.
rewrite Zplus_comm.
apply IHu.
clear -Hv ; omega.
split.
now ring_simplify (1 + v - 1)%Z.
now rewrite Zplus_assoc.
easy.
apply Zle_succ_le with (1 := Hv).
Qed.

Theorem Zdigits_unique :
  forall n d,
  (Zpower beta (d - 1) <= Zabs n < Zpower beta d)%Z ->
  Zdigits n = d.
Proof.
intros n d Hd.
assert (Hd' := Zdigits_correct n).
apply Zle_antisym.
apply (Zpower_lt_Zpower beta).
now apply Zle_lt_trans with (Zabs n).
apply (Zpower_lt_Zpower beta).
now apply Zle_lt_trans with (Zabs n).
Qed.

Theorem Zdigits_abs :
  forall n, Zdigits (Zabs n) = Zdigits n.
Proof.
now intros [|n|n].
Qed.

Theorem Zdigits_gt_0 :
  forall n, n <> Z0 -> (0 < Zdigits n)%Z.
Proof.
intros n Zn.
rewrite <- (Zdigits_abs n).
assert (Hn: (0 < Zabs n)%Z).
destruct n ; [|easy|easy].
now elim Zn.
destruct (Zabs n) as [|p|p] ; try easy ; clear.
simpl.
generalize 1%Z (radix_val beta) (refl_equal Lt : (0 < 1)%Z).
induction (digits2_Pnat p).
easy.
simpl.
intros.
case Zlt_bool.
exact H.
apply IHn.
now apply Zlt_lt_succ.
Qed.

Theorem Zdigits_ge_0 :
  forall n, (0 <= Zdigits n)%Z.
Proof.
intros n.
destruct (Z_eq_dec n 0) as [H|H].
now rewrite H.
apply Zlt_le_weak.
now apply Zdigits_gt_0.
Qed.

Theorem Zdigit_out :
  forall n k, (Zdigits n <= k)%Z ->
  Zdigit n k = Z0.
Proof.
intros n k Hk.
apply Zdigit_ge_Zpower with (2 := Hk).
apply Zdigits_correct.
Qed.

Theorem Zdigit_digits :
  forall n, n <> Z0 ->
  Zdigit n (Zdigits n - 1) <> Z0.
Proof.
intros n Zn.
apply Zdigit_not_0.
apply Zlt_0_le_0_pred.
now apply Zdigits_gt_0.
ring_simplify (Zdigits n - 1 + 1)%Z.
apply Zdigits_correct.
Qed.

Theorem Zdigits_slice :
  forall n k l, (0 <= l)%Z ->
  (Zdigits (Zslice n k l) <= l)%Z.
Proof.
intros n k l Hl.
unfold Zslice.
rewrite Zle_bool_true with (1 := Hl).
destruct (Zdigits_correct (Z.rem (Zscale n (- k)) (Zpower beta l))) as (H1,H2).
apply Zpower_lt_Zpower with beta.
apply Zle_lt_trans with (1 := H1).
rewrite <- (Zabs_eq (beta ^ l)) at 2 by apply Zpower_ge_0.
apply Zrem_lt.
apply Zgt_not_eq.
now apply Zpower_gt_0.
Qed.

Theorem Zdigits_mult_Zpower :
  forall m e,
  m <> Z0 -> (0 <= e)%Z ->
  Zdigits (m * Zpower beta e) = (Zdigits m + e)%Z.
Proof.
intros m e Hm He.
assert (H := Zdigits_correct m).
apply Zdigits_unique.
rewrite Z.abs_mul, Z.abs_pow, (Zabs_eq beta).
2: now apply Zlt_le_weak, radix_gt_0.
split.
replace (Zdigits m + e - 1)%Z with (Zdigits m - 1 + e)%Z by ring.
rewrite Zpower_plus with (2 := He).
apply Zmult_le_compat_r.
apply H.
apply Zpower_ge_0.
now apply Zlt_0_le_0_pred, Zdigits_gt_0.
rewrite Zpower_plus with (2 := He).
apply Zmult_lt_compat_r.
now apply Zpower_gt_0.
apply H.
now apply Zlt_le_weak, Zdigits_gt_0.
Qed.

Theorem Zdigits_Zpower :
  forall e,
  (0 <= e)%Z ->
  Zdigits (Zpower beta e) = (e + 1)%Z.
Proof.
intros e He.
rewrite <- (Zmult_1_l (Zpower beta e)).
rewrite Zdigits_mult_Zpower ; try easy.
apply Zplus_comm.
Qed.

Theorem Zdigits_le :
  forall x y,
  (0 <= x)%Z -> (x <= y)%Z ->
  (Zdigits x <= Zdigits y)%Z.
Proof.
intros x y Zx Hxy.
assert (Hx := Zdigits_correct x).
assert (Hy := Zdigits_correct y).
apply (Zpower_lt_Zpower beta).
zify ; omega.
Qed.

Theorem lt_Zdigits :
  forall x y,
  (0 <= y)%Z ->
  (Zdigits x < Zdigits y)%Z ->
  (x < y)%Z.
Proof.
intros x y Hy.
cut (y <= x -> Zdigits y <= Zdigits x)%Z. omega.
now apply Zdigits_le.
Qed.

Theorem Zpower_le_Zdigits :
  forall e x,
  (e < Zdigits x)%Z ->
  (Zpower beta e <= Zabs x)%Z.
Proof.
intros e x Hex.
destruct (Zdigits_correct x) as [H1 H2].
apply Zle_trans with (2 := H1).
apply Zpower_le.
clear -Hex ; omega.
Qed.

Theorem Zdigits_le_Zpower :
  forall e x,
  (Zabs x < Zpower beta e)%Z ->
  (Zdigits x <= e)%Z.
Proof.
intros e x.
generalize (Zpower_le_Zdigits e x).
omega.
Qed.

Theorem Zpower_gt_Zdigits :
  forall e x,
  (Zdigits x <= e)%Z ->
  (Zabs x < Zpower beta e)%Z.
Proof.
intros e x Hex.
destruct (Zdigits_correct x) as [H1 H2].
apply Zlt_le_trans with (1 := H2).
now apply Zpower_le.
Qed.

Theorem Zdigits_gt_Zpower :
  forall e x,
  (Zpower beta e <= Zabs x)%Z ->
  (e < Zdigits x)%Z.
Proof.
intros e x Hex.
generalize (Zpower_gt_Zdigits e x).
omega.
Qed.

(** Number of digits of a product.

This strong version is needed for proofs of division and square root
algorithms, since they involve operation remainders.
*)

Theorem Zdigits_mult_strong :
  forall x y,
  (0 <= x)%Z -> (0 <= y)%Z ->
  (Zdigits (x + y + x * y) <= Zdigits x + Zdigits y)%Z.
Proof.
intros x y Hx Hy.
apply Zdigits_le_Zpower.
rewrite Zabs_eq.
apply Zlt_le_trans with ((x + 1) * (y + 1))%Z.
ring_simplify.
apply Zle_lt_succ, Zle_refl.
rewrite Zpower_plus by apply Zdigits_ge_0.
apply Zmult_le_compat.
apply Zlt_le_succ.
rewrite <- (Zabs_eq x) at 1 by easy.
apply Zdigits_correct.
apply Zlt_le_succ.
rewrite <- (Zabs_eq y) at 1 by easy.
apply Zdigits_correct.
clear -Hx ; omega.
clear -Hy ; omega.
change Z0 with (0 + 0 + 0)%Z.
apply Zplus_le_compat.
now apply Zplus_le_compat.
now apply Zmult_le_0_compat.
Qed.

Theorem Zdigits_mult :
  forall x y,
  (Zdigits (x * y) <= Zdigits x + Zdigits y)%Z.
Proof.
intros x y.
rewrite <- Zdigits_abs.
rewrite <- (Zdigits_abs x).
rewrite <- (Zdigits_abs y).
apply Zle_trans with (Zdigits (Zabs x + Zabs y + Zabs x * Zabs y)).
apply Zdigits_le.
apply Zabs_pos.
rewrite Zabs_Zmult.
generalize (Zabs_pos x) (Zabs_pos y).
omega.
apply Zdigits_mult_strong ; apply Zabs_pos.
Qed.

Theorem Zdigits_mult_ge :
  forall x y,
  (x <> 0)%Z -> (y <> 0)%Z ->
  (Zdigits x + Zdigits y - 1 <= Zdigits (x * y))%Z.
Proof.
intros x y Zx Zy.
cut ((Zdigits x - 1) + (Zdigits y - 1) < Zdigits (x * y))%Z. omega.
apply Zdigits_gt_Zpower.
rewrite Zabs_Zmult.
rewrite Zpower_exp.
apply Zmult_le_compat.
apply Zpower_le_Zdigits.
apply Zlt_pred.
apply Zpower_le_Zdigits.
apply Zlt_pred.
apply Zpower_ge_0.
apply Zpower_ge_0.
generalize (Zdigits_gt_0 x). omega.
generalize (Zdigits_gt_0 y). omega.
Qed.

Theorem Zdigits_div_Zpower :
  forall m e,
  (0 <= m)%Z ->
  (0 <= e <= Zdigits m)%Z ->
  Zdigits (m / Zpower beta e) = (Zdigits m - e)%Z.
Proof.
intros m e Hm He.
assert (H := Zdigits_correct m).
apply Zdigits_unique.
destruct (Zle_lt_or_eq _ _ (proj2 He)) as [He'|He'].
  rewrite Zabs_eq in H by easy.
  destruct H as [H1 H2].
  rewrite Zabs_eq.
  split.
  replace (Zdigits m - e - 1)%Z with (Zdigits m - 1 - e)%Z by ring.
  rewrite Z.pow_sub_r.
  2: apply Zgt_not_eq, radix_gt_0.
  2: clear -He He' ; omega.
  apply Z_div_le with (2 := H1).
  now apply Zlt_gt, Zpower_gt_0.
  apply Zmult_lt_reg_r with (Zpower beta e).
  now apply Zpower_gt_0.
  apply Zle_lt_trans with m.
  rewrite Zmult_comm.
  apply Z_mult_div_ge.
  now apply Zlt_gt, Zpower_gt_0.
  rewrite <- Zpower_plus.
  now replace (Zdigits m - e + e)%Z with (Zdigits m) by ring.
  now apply Zle_minus_le_0.
  apply He.
  apply Z_div_pos with (2 := Hm).
  now apply Zlt_gt, Zpower_gt_0.
rewrite He'.
rewrite (Zeq_minus _ (Zdigits m)) by reflexivity.
simpl.
rewrite Zdiv_small.
easy.
split.
exact Hm.
now rewrite <- (Zabs_eq m) at 1.
Qed.

End Fcore_digits.

(** Specialized version for computing the number of bits of an integer *)

Section Zdigits2.

Theorem Z_of_nat_S_digits2_Pnat :
  forall m : positive,
  Z_of_nat (S (digits2_Pnat m)) = Zdigits radix2 (Zpos m).
Proof.
intros m.
apply eq_sym, Zdigits_unique.
rewrite <- Zpower_nat_Z.
rewrite Nat2Z.inj_succ.
change (_ - 1)%Z with (Zpred (Zsucc (Z.of_nat (digits2_Pnat m)))).
rewrite <- Zpred_succ.
rewrite <- Zpower_nat_Z.
apply digits2_Pnat_correct.
Qed.

Fixpoint digits2_pos (n : positive) : positive :=
  match n with
  | xH => xH
  | xO p => Psucc (digits2_pos p)
  | xI p => Psucc (digits2_pos p)
  end.

Theorem Zpos_digits2_pos :
  forall m : positive,
  Zpos (digits2_pos m) = Zdigits radix2 (Zpos m).
Proof.
intros m.
rewrite <- Z_of_nat_S_digits2_Pnat.
unfold Z.of_nat.
apply f_equal.
induction m ; simpl ; try easy ;
  apply f_equal, IHm.
Qed.

Definition Zdigits2 n :=
  match n with
  | Z0 => n
  | Zpos p => Zpos (digits2_pos p)
  | Zneg p => Zpos (digits2_pos p)
  end.

Lemma Zdigits2_Zdigits :
  forall n, Zdigits2 n = Zdigits radix2 n.
Proof.
intros [|p|p] ; try easy ;
  apply Zpos_digits2_pos.
Qed.

End Zdigits2.

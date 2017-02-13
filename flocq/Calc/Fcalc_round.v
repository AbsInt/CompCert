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

(** * Helper function for computing the rounded value of a real number. *)

Require Import Fcore.
Require Import Fcore_digits.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.

Section Fcalc_round.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Section Fcalc_round_fexp.

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Notation format := (generic_format beta fexp).

(** Relates location and rounding. *)

Theorem inbetween_float_round :
  forall rnd choice,
  ( forall x m l, inbetween_int m x l -> rnd x = choice m l ) ->
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof.
intros rnd choice Hc x m l e Hl.
unfold round, F2R. simpl.
apply (f_equal (fun m => (Z2R m * bpow e)%R)).
apply Hc.
apply inbetween_mult_reg with (bpow e).
apply bpow_gt_0.
now rewrite scaled_mantissa_mult_bpow.
Qed.

Definition cond_incr (b : bool) m := if b then (m + 1)%Z else m.

Theorem inbetween_float_round_sign :
  forall rnd choice,
  ( forall x m l, inbetween_int m (Rabs x) l ->
    rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l) ) ->
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp rnd x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l)) e).
Proof.
intros rnd choice Hc x m l e Hx.
apply (f_equal (fun m => (Z2R m * bpow e)%R)).
simpl.
replace (Rlt_bool x 0) with (Rlt_bool (scaled_mantissa beta fexp x) 0).
(* *)
apply Hc.
apply inbetween_mult_reg with (bpow e).
apply bpow_gt_0.
rewrite <- (Rabs_right (bpow e)) at 3.
rewrite <- Rabs_mult.
now rewrite scaled_mantissa_mult_bpow.
apply Rle_ge.
apply bpow_ge_0.
(* *)
destruct (Rlt_bool_spec x 0) as [Zx|Zx] ; simpl.
apply Rlt_bool_true.
rewrite <- (Rmult_0_l (bpow (-e))).
apply Rmult_lt_compat_r with (2 := Zx).
apply bpow_gt_0.
apply Rlt_bool_false.
apply Rmult_le_pos with (1 := Zx).
apply bpow_ge_0.
Qed.

(** Relates location and rounding down. *)

Theorem inbetween_int_DN :
  forall x m l,
  inbetween_int m x l ->
  Zfloor x = m.
Proof.
intros x m l Hl.
refine (Zfloor_imp m _ _).
apply inbetween_bounds with (2 := Hl).
apply Z2R_lt.
apply Zlt_succ.
Qed.

Theorem inbetween_float_DN :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Zfloor x = F2R (Float beta m e).
Proof.
apply inbetween_float_round with (choice := fun m l => m).
exact inbetween_int_DN.
Qed.

Definition round_sign_DN s l :=
  match l with
  | loc_Exact => false
  | _ => s
  end.

Theorem inbetween_int_DN_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Zfloor x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_DN (Rlt_bool x 0) l) m).
Proof.
intros x m l Hl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx] .
(* *)
rewrite Rlt_bool_true with (1 := Zx).
inversion_clear Hl ; simpl.
rewrite <- (Ropp_involutive x).
rewrite H, <- Z2R_opp.
apply Zfloor_Z2R.
apply Zfloor_imp.
split.
apply Rlt_le.
rewrite Z2R_opp.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
ring_simplify (- (m + 1) + 1)%Z.
rewrite Z2R_opp.
apply Ropp_lt_cancel.
now rewrite Ropp_involutive.
(* *)
rewrite Rlt_bool_false.
inversion_clear Hl ; simpl.
rewrite H.
apply Zfloor_Z2R.
apply Zfloor_imp.
split.
now apply Rlt_le.
apply H.
now apply Rge_le.
Qed.

Theorem inbetween_float_DN_sign :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Zfloor x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_DN (Rlt_bool x 0) l) m)) e).
Proof.
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_sign_DN s l) m).
exact inbetween_int_DN_sign.
Qed.

(** Relates location and rounding up. *)

Definition round_UP l :=
  match l with
  | loc_Exact => false
  | _ => true
  end.

Theorem inbetween_int_UP :
  forall x m l,
  inbetween_int m x l ->
  Zceil x = cond_incr (round_UP l) m.
Proof.
intros x m l Hl.
assert (Hl': l = loc_Exact \/ (l <> loc_Exact /\ round_UP l = true)).
case l ; try (now left) ; now right ; split.
destruct Hl' as [Hl'|(Hl1, Hl2)].
(* Exact *)
rewrite Hl'.
destruct Hl ; try easy.
rewrite H.
exact (Zceil_Z2R _).
(* not Exact *)
rewrite Hl2.
simpl.
apply Zceil_imp.
ring_simplify (m + 1 - 1)%Z.
refine (let H := _ in conj (proj1 H) (Rlt_le _ _ (proj2 H))).
apply inbetween_bounds_not_Eq with (2 := Hl1) (1 := Hl).
Qed.

Theorem inbetween_float_UP :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Zceil x = F2R (Float beta (cond_incr (round_UP l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_UP l) m).
exact inbetween_int_UP.
Qed.

Definition round_sign_UP s l :=
  match l with
  | loc_Exact => false
  | _ => negb s
  end.

Theorem inbetween_int_UP_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Zceil x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_UP (Rlt_bool x 0) l) m).
Proof.
intros x m l Hl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx] .
(* *)
rewrite Rlt_bool_true with (1 := Zx).
simpl.
unfold Zceil.
apply f_equal.
inversion_clear Hl ; simpl.
rewrite H.
apply Zfloor_Z2R.
apply Zfloor_imp.
split.
now apply Rlt_le.
apply H.
(* *)
rewrite Rlt_bool_false.
simpl.
inversion_clear Hl ; simpl.
rewrite H.
apply Zceil_Z2R.
apply Zceil_imp.
split.
change (m + 1 - 1)%Z with (Zpred (Zsucc m)).
now rewrite <- Zpred_succ.
now apply Rlt_le.
now apply Rge_le.
Qed.

Theorem inbetween_float_UP_sign :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Zceil x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_sign_UP (Rlt_bool x 0) l) m)) e).
Proof.
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_sign_UP s l) m).
exact inbetween_int_UP_sign.
Qed.

(** Relates location and rounding toward zero. *)

Definition round_ZR (s : bool) l :=
  match l with
  | loc_Exact => false
  | _ => s
  end.

Theorem inbetween_int_ZR :
  forall x m l,
  inbetween_int m x l ->
  Ztrunc x = cond_incr (round_ZR (Zlt_bool m 0) l) m.
Proof with auto with typeclass_instances.
intros x m l Hl.
inversion_clear Hl as [Hx|l' Hx Hl'].
(* Exact *)
rewrite Hx.
rewrite Zrnd_Z2R...
(* not Exact *)
unfold Ztrunc.
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
rewrite Zceil_floor_neq.
rewrite Hm.
unfold cond_incr.
simpl.
case Rlt_bool_spec ; intros Hx' ;
  case Zlt_bool_spec ; intros Hm' ; try apply refl_equal.
elim Rlt_not_le with (1 := Hx').
apply Rlt_le.
apply Rle_lt_trans with (2 := proj1 Hx).
now apply (Z2R_le 0).
elim Rle_not_lt with (1 := Hx').
apply Rlt_le_trans with (1 := proj2 Hx).
apply (Z2R_le _ 0).
now apply Zlt_le_succ.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

Theorem inbetween_float_ZR :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp Ztrunc x = F2R (Float beta (cond_incr (round_ZR (Zlt_bool m 0) l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m).
exact inbetween_int_ZR.
Qed.

Theorem inbetween_int_ZR_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  Ztrunc x = cond_Zopp (Rlt_bool x 0) m.
Proof.
intros x m l Hl.
simpl.
unfold Ztrunc.
destruct (Rlt_le_dec x 0) as [Zx|Zx].
(* *)
rewrite Rlt_bool_true with (1 := Zx).
simpl.
unfold Zceil.
apply f_equal.
apply Zfloor_imp.
rewrite <- Rabs_left with (1 := Zx).
apply inbetween_bounds with (2 := Hl).
apply Z2R_lt.
apply Zlt_succ.
(* *)
rewrite Rlt_bool_false with (1 := Zx).
simpl.
apply Zfloor_imp.
rewrite <- Rabs_pos_eq with (1 := Zx).
apply inbetween_bounds with (2 := Hl).
apply Z2R_lt.
apply Zlt_succ.
Qed.

Theorem inbetween_float_ZR_sign :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp Ztrunc x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) m) e).
Proof.
apply inbetween_float_round_sign with (choice := fun s m l => m).
exact inbetween_int_ZR_sign.
Qed.

(** Relates location and rounding to nearest. *)

Definition round_N (p : bool) l :=
  match l with
  | loc_Exact => false
  | loc_Inexact Lt => false
  | loc_Inexact Eq => p
  | loc_Inexact Gt => true
  end.

Theorem inbetween_int_N :
  forall choice x m l,
  inbetween_int m x l ->
  Znearest choice x = cond_incr (round_N (choice m) l) m.
Proof with auto with typeclass_instances.
intros choice x m l Hl.
inversion_clear Hl as [Hx|l' Hx Hl'].
(* Exact *)
rewrite Hx.
rewrite Zrnd_Z2R...
(* not Exact *)
unfold Znearest.
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (x - Z2R m) (/2)) with l'.
now case l'.
rewrite <- Hl'.
rewrite Z2R_plus.
rewrite <- (Rcompare_plus_r (- Z2R m) x).
apply f_equal.
simpl (Z2R 1).
field.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

Theorem inbetween_int_N_sign :
  forall choice x m l,
  inbetween_int m (Rabs x) l ->
  Znearest choice x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (if Rlt_bool x 0 then negb (choice (-(m + 1))%Z) else choice m) l) m).
Proof with auto with typeclass_instances.
intros choice x m l Hl.
simpl.
unfold Rabs in Hl.
destruct (Rcase_abs x) as [Zx|Zx].
(* *)
rewrite Rlt_bool_true with (1 := Zx).
simpl.
rewrite <- (Ropp_involutive x).
rewrite Znearest_opp.
apply f_equal.
inversion_clear Hl as [Hx|l' Hx Hl'].
rewrite Hx.
apply Zrnd_Z2R...
assert (Hm: Zfloor (-x) = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
unfold Znearest.
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (- x - Z2R m) (/2)) with l'.
now case l'.
rewrite <- Hl'.
rewrite Z2R_plus.
rewrite <- (Rcompare_plus_r (- Z2R m) (-x)).
apply f_equal.
simpl (Z2R 1).
field.
rewrite Hm.
now apply Rlt_not_eq.
(* *)
generalize (Rge_le _ _ Zx).
clear Zx. intros Zx.
rewrite Rlt_bool_false with (1 := Zx).
simpl.
inversion_clear Hl as [Hx|l' Hx Hl'].
rewrite Hx.
apply Zrnd_Z2R...
assert (Hm: Zfloor x = m).
apply Zfloor_imp.
exact (conj (Rlt_le _ _ (proj1 Hx)) (proj2 Hx)).
unfold Znearest.
rewrite Zceil_floor_neq.
rewrite Hm.
replace (Rcompare (x - Z2R m) (/2)) with l'.
now case l'.
rewrite <- Hl'.
rewrite Z2R_plus.
rewrite <- (Rcompare_plus_r (- Z2R m) x).
apply f_equal.
simpl (Z2R 1).
field.
rewrite Hm.
now apply Rlt_not_eq.
Qed.

(** Relates location and rounding to nearest even. *)

Theorem inbetween_int_NE :
  forall x m l,
  inbetween_int m x l ->
  ZnearestE x = cond_incr (round_N (negb (Zeven m)) l) m.
Proof.
intros x m l Hl.
now apply inbetween_int_N with (choice := fun x => negb (Zeven x)).
Qed.

Theorem inbetween_float_NE :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp ZnearestE x = F2R (Float beta (cond_incr (round_N (negb (Zeven m)) l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_N (negb (Zeven m)) l) m).
exact inbetween_int_NE.
Qed.

Theorem inbetween_int_NE_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  ZnearestE x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (negb (Zeven m)) l) m).
Proof.
intros x m l Hl.
erewrite inbetween_int_N_sign with (choice := fun x => negb (Zeven x)).
2: eexact Hl.
apply f_equal.
case Rlt_bool.
rewrite Zeven_opp, Zeven_plus.
now case (Zeven m).
apply refl_equal.
Qed.

Theorem inbetween_float_NE_sign :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e (Rabs x) l ->
  round beta fexp ZnearestE x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (cond_incr (round_N (negb (Zeven m)) l) m)) e).
Proof.
apply inbetween_float_round_sign with (choice := fun s m l => cond_incr (round_N (negb (Zeven m)) l) m).
exact inbetween_int_NE_sign.
Qed.

(** Relates location and rounding to nearest away. *)

Theorem inbetween_int_NA :
  forall x m l,
  inbetween_int m x l ->
  ZnearestA x = cond_incr (round_N (Zle_bool 0 m) l) m.
Proof.
intros x m l Hl.
now apply inbetween_int_N with (choice := fun x => Zle_bool 0 x).
Qed.

Theorem inbetween_float_NA :
  forall x m l,
  let e := canonic_exp beta fexp x in
  inbetween_float beta m e x l ->
  round beta fexp ZnearestA x = F2R (Float beta (cond_incr (round_N (Zle_bool 0 m) l) m) e).
Proof.
apply inbetween_float_round with (choice := fun m l => cond_incr (round_N (Zle_bool 0 m) l) m).
exact inbetween_int_NA.
Qed.

Theorem inbetween_int_NA_sign :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  ZnearestA x = cond_Zopp (Rlt_bool x 0) (cond_incr (round_N true l) m).
Proof.
intros x m l Hl.
erewrite inbetween_int_N_sign with (choice := Zle_bool 0).
2: eexact Hl.
apply f_equal.
assert (Hm: (0 <= m)%Z).
apply Zlt_succ_le.
apply lt_Z2R.
apply Rle_lt_trans with (Rabs x).
apply Rabs_pos.
refine (proj2 (inbetween_bounds _ _ _ _ _ Hl)).
apply Z2R_lt.
apply Zlt_succ.
rewrite Zle_bool_true with (1 := Hm).
rewrite Zle_bool_false.
now case Rlt_bool.
omega.
Qed.

Definition truncate_aux t k :=
  let '(m, e, l) := t in
  let p := Zpower beta k in
  (Zdiv m p, (e + k)%Z, new_location p (Zmod m p) l).

Theorem truncate_aux_comp :
  forall t k1 k2,
  (0 < k1)%Z ->
  (0 < k2)%Z ->
  truncate_aux t (k1 + k2) = truncate_aux (truncate_aux t k1) k2.
Proof.
intros ((m,e),l) k1 k2 Hk1 Hk2.
unfold truncate_aux.
destruct (inbetween_float_ex beta m e l) as (x,Hx).
assert (B1 := inbetween_float_new_location _ _ _ _ _ _ Hk1 Hx).
assert (Hk3: (0 < k1 + k2)%Z).
change Z0 with (0 + 0)%Z.
now apply Zplus_lt_compat.
assert (B3 := inbetween_float_new_location _ _ _ _ _ _ Hk3 Hx).
assert (B2 := inbetween_float_new_location _ _ _ _ _ _ Hk2 B1).
rewrite Zplus_assoc in B3.
destruct (inbetween_float_unique _ _ _ _ _ _ _ B2 B3).
now rewrite H, H0, Zplus_assoc.
Qed.

(** Given a triple (mantissa, exponent, position), this function
    computes a triple with a canonic exponent, assuming the
    original triple had enough precision. *)

Definition truncate t :=
  let '(m, e, l) := t in
  let k := (fexp (Zdigits beta m + e) - e)%Z in
  if Zlt_bool 0 k then truncate_aux t k
  else t.

Theorem truncate_0 :
  forall e l,
  let '(m', e', l') := truncate (0, e, l)%Z in
  m' = Z0.
Proof.
intros e l.
unfold truncate.
case Zlt_bool.
simpl.
apply Zdiv_0_l.
apply refl_equal.
Qed.

Theorem generic_format_truncate :
  forall m e l,
  (0 <= m)%Z ->
  let '(m', e', l') := truncate (m, e, l) in
  format (F2R (Float beta m' e')).
Proof.
intros m e l Hm.
unfold truncate.
set (k := (fexp (Zdigits beta m + e) - e)%Z).
case Zlt_bool_spec ; intros Hk.
(* *)
unfold truncate_aux.
apply generic_format_F2R.
intros Hd.
unfold canonic_exp.
rewrite ln_beta_F2R_Zdigits with (1 := Hd).
rewrite Zdigits_div_Zpower with (1 := Hm).
replace (Zdigits beta m - k + (e + k))%Z with (Zdigits beta m + e)%Z by ring.
unfold k.
ring_simplify.
apply Zle_refl.
split.
now apply Zlt_le_weak.
apply Znot_gt_le.
contradict Hd.
apply Zdiv_small.
apply conj with (1 := Hm).
rewrite <- Zabs_eq with (1 := Hm).
apply Zpower_gt_Zdigits.
apply Zlt_le_weak.
now apply Zgt_lt.
(* *)
destruct (Zle_lt_or_eq _ _ Hm) as [Hm'|Hm'].
apply generic_format_F2R.
unfold canonic_exp.
rewrite ln_beta_F2R_Zdigits.
2: now apply Zgt_not_eq.
unfold k in Hk. clear -Hk.
omega.
rewrite <- Hm', F2R_0.
apply generic_format_0.
Qed.

Theorem truncate_correct_format :
  forall m e,
  m <> Z0 ->
  let x := F2R (Float beta m e) in
  generic_format beta fexp x ->
  (e <= fexp (Zdigits beta m + e))%Z ->
  let '(m', e', l') := truncate (m, e, loc_Exact) in
  x = F2R (Float beta m' e') /\ e' = canonic_exp beta fexp x.
Proof.
intros m e Hm x Fx He.
assert (Hc: canonic_exp beta fexp x = fexp (Zdigits beta m + e)).
unfold canonic_exp, x.
now rewrite ln_beta_F2R_Zdigits.
unfold truncate.
rewrite <- Hc.
set (k := (canonic_exp beta fexp x - e)%Z).
case Zlt_bool_spec ; intros Hk.
(* *)
unfold truncate_aux.
rewrite Fx at 1.
assert (H: (e + k)%Z = canonic_exp beta fexp x).
unfold k. ring.
refine (conj _ H).
rewrite <- H.
apply F2R_eq_compat.
replace (scaled_mantissa beta fexp x) with (Z2R (Zfloor (scaled_mantissa beta fexp x))).
rewrite Ztrunc_Z2R.
unfold scaled_mantissa.
rewrite <- H.
unfold x, F2R. simpl.
rewrite Rmult_assoc, <- bpow_plus.
ring_simplify (e + - (e + k))%Z.
clear -Hm Hk.
destruct k as [|k|k] ; try easy.
simpl.
apply Zfloor_div.
intros H.
generalize (Zpower_pos_gt_0 beta k) (Zle_bool_imp_le _ _ (radix_prop beta)).
omega.
rewrite scaled_mantissa_generic with (1 := Fx).
now rewrite Zfloor_Z2R.
(* *)
split.
apply refl_equal.
unfold k in Hk.
omega.
Qed.

Theorem truncate_correct_partial :
  forall x m e l,
  (0 < x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\ e' = canonic_exp beta fexp x.
Proof.
intros x m e l Hx H1 H2.
unfold truncate.
set (k := (fexp (Zdigits beta m + e) - e)%Z).
set (p := Zpower beta k).
(* *)
assert (Hx': (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R).
apply inbetween_float_bounds with (1 := H1).
(* *)
assert (Hm: (0 <= m)%Z).
cut (0 < m + 1)%Z. omega.
apply F2R_lt_reg with beta e.
rewrite F2R_0.
apply Rlt_trans with  (1 := Hx).
apply Hx'.
assert (He: (e + k = canonic_exp beta fexp x)%Z).
(* . *)
unfold canonic_exp.
destruct (Zle_lt_or_eq _ _ Hm) as [Hm'|Hm'].
(* .. 0 < m *)
rewrite ln_beta_F2R_bounds with (1 := Hm') (2 := Hx').
assert (H: m <> Z0).
apply sym_not_eq.
now apply Zlt_not_eq.
rewrite ln_beta_F2R with (1 := H).
rewrite <- Zdigits_ln_beta with (1 := H).
unfold k.
ring.
(* .. m = 0 *)
rewrite <- Hm' in H2.
destruct (ln_beta beta x) as (ex, Hex).
simpl.
specialize (Hex (Rgt_not_eq _ _ Hx)).
unfold k.
ring_simplify.
rewrite <- Hm'.
simpl.
apply sym_eq.
apply valid_exp.
exact H2.
apply Zle_trans with e.
eapply bpow_lt_bpow.
apply Rle_lt_trans with (1 := proj1 Hex).
rewrite Rabs_pos_eq.
rewrite <- F2R_bpow.
rewrite <- Hm' in Hx'.
apply Hx'.
now apply Rlt_le.
exact H2.
(* . *)
generalize (Zlt_cases 0 k).
case (Zlt_bool 0 k) ; intros Hk ; unfold k in Hk.
split.
now apply inbetween_float_new_location.
exact He.
split.
exact H1.
rewrite <- He.
unfold k.
omega.
Qed.

Theorem truncate_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = canonic_exp beta fexp x \/ (l' = loc_Exact /\ format x)).
Proof.
intros x m e l [Hx|Hx] H1 H2.
(* 0 < x *)
destruct (Zle_or_lt e (fexp (Zdigits beta m + e))) as [H3|H3].
(* . enough digits *)
generalize (truncate_correct_partial x m e l Hx H1 H3).
destruct (truncate (m, e, l)) as ((m', e'), l').
intros (H4, H5).
split.
exact H4.
now left.
(* . not enough digits but loc_Exact *)
destruct H2 as [H2|H2].
elim (Zlt_irrefl e).
now apply Zle_lt_trans with (1 := H2).
rewrite H2 in H1 |- *.
unfold truncate.
generalize (Zlt_cases 0 (fexp (Zdigits beta m + e) - e)).
case Zlt_bool.
intros H.
apply False_ind.
omega.
intros _.
split.
exact H1.
right.
split.
apply refl_equal.
inversion_clear H1.
rewrite H.
apply generic_format_F2R.
intros Zm.
unfold canonic_exp.
rewrite ln_beta_F2R_Zdigits with (1 := Zm).
now apply Zlt_le_weak.
(* x = 0 *)
assert (Hm: m = Z0).
cut (m <= 0 < m + 1)%Z. omega.
assert (Hx': (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R).
apply inbetween_float_bounds with (1 := H1).
rewrite <- Hx in Hx'.
split.
apply F2R_le_0_reg with (1 := proj1 Hx').
apply F2R_gt_0_reg with (1 := proj2 Hx').
rewrite Hm, <- Hx in H1 |- *.
clear -H1.
case H1.
(* . *)
intros _.
assert (exists e', truncate (Z0, e, loc_Exact) = (Z0, e', loc_Exact)).
unfold truncate, truncate_aux.
case Zlt_bool.
rewrite Zdiv_0_l, Zmod_0_l.
eexists.
apply f_equal.
unfold new_location.
now case Zeven.
now eexists.
destruct H as (e', H).
rewrite H.
split.
constructor.
apply sym_eq.
apply F2R_0.
right.
repeat split.
apply generic_format_0.
(* . *)
intros l' (H, _) _.
rewrite F2R_0 in H.
elim Rlt_irrefl with (1 := H).
Qed.

Section round_dir.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Variable choice : Z -> location -> Z.
Hypothesis inbetween_int_valid :
  forall x m l,
  inbetween_int m x l ->
  rnd x = choice m l.

Theorem round_any_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e = canonic_exp beta fexp x \/ (l = loc_Exact /\ format x)) ->
  round beta fexp rnd x = F2R (Float beta (choice m l) e).
Proof with auto with typeclass_instances.
intros x m e l Hin [He|(Hl,Hf)].
rewrite He in Hin |- *.
apply inbetween_float_round with (2 := Hin).
exact inbetween_int_valid.
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl.
replace (choice m loc_Exact) with m.
rewrite <- H.
apply round_generic...
rewrite <- (Zrnd_Z2R rnd m) at 1.
apply inbetween_int_valid.
now constructor.
Qed.

(** Truncating a triple is sufficient to round a real number. *)

Theorem round_trunc_any_correct :
  forall x m e l,
  (0 <= x)%R ->
  inbetween_float beta m e x l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (choice m' l') e').
Proof.
intros x m e l Hx Hl He.
generalize (truncate_correct x m e l Hx Hl He).
destruct (truncate (m, e, l)) as ((m', e'), l').
intros (H1, H2).
now apply round_any_correct.
Qed.

End round_dir.

Section round_dir_sign.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Variable choice : bool -> Z -> location -> Z.
Hypothesis inbetween_int_valid :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l).

Theorem round_sign_any_correct :
  forall x m e l,
  inbetween_float beta m e (Rabs x) l ->
  (e = canonic_exp beta fexp x \/ (l = loc_Exact /\ format x)) ->
  round beta fexp rnd x = F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l)) e).
Proof with auto with typeclass_instances.
intros x m e l Hin [He|(Hl,Hf)].
rewrite He in Hin |- *.
apply inbetween_float_round_sign with (2 := Hin).
exact inbetween_int_valid.
rewrite Hl in Hin.
inversion_clear Hin.
rewrite Hl.
replace (choice (Rlt_bool x 0) m loc_Exact) with m.
(* *)
unfold Rabs in H.
destruct (Rcase_abs x) as [Zx|Zx].
rewrite Rlt_bool_true with (1 := Zx).
simpl.
rewrite F2R_Zopp.
rewrite <- H, Ropp_involutive.
apply round_generic...
rewrite Rlt_bool_false.
simpl.
rewrite <- H.
now apply round_generic.
now apply Rge_le.
(* *)
destruct (Rlt_bool_spec x 0) as [Zx|Zx].
(* . *)
apply Zopp_inj.
change (- m = cond_Zopp true (choice true m loc_Exact))%Z.
rewrite <- (Zrnd_Z2R rnd (-m)) at 1.
assert (Z2R (-m) < 0)%R.
rewrite Z2R_opp.
apply Ropp_lt_gt_0_contravar.
apply (Z2R_lt 0).
apply F2R_gt_0_reg with beta e.
rewrite <- H.
apply Rabs_pos_lt.
now apply Rlt_not_eq.
rewrite <- Rlt_bool_true with (1 := H0).
apply inbetween_int_valid.
constructor.
rewrite Rabs_left with (1 := H0).
rewrite Z2R_opp.
apply Ropp_involutive.
(* . *)
change (m = cond_Zopp false (choice false m loc_Exact))%Z.
rewrite <- (Zrnd_Z2R rnd m) at 1.
assert (0 <= Z2R m)%R.
apply (Z2R_le 0).
apply F2R_ge_0_reg with beta e.
rewrite <- H.
apply Rabs_pos.
rewrite <- Rlt_bool_false with (1 := H0).
apply inbetween_int_valid.
constructor.
now apply Rabs_pos_eq.
Qed.

(** Truncating a triple is sufficient to round a real number. *)

Theorem round_trunc_sign_any_correct :
  forall x m e l,
  inbetween_float beta m e (Rabs x) l ->
  (e <= fexp (Zdigits beta m + e))%Z \/ l = loc_Exact ->
  round beta fexp rnd x = let '(m', e', l') := truncate (m, e, l) in F2R (Float beta (cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m' l')) e').
Proof.
intros x m e l Hl He.
generalize (truncate_correct (Rabs x) m e l (Rabs_pos _) Hl He).
destruct (truncate (m, e, l)) as ((m', e'), l').
intros (H1, H2).
apply round_sign_any_correct.
exact H1.
destruct H2 as [H2|(H2,H3)].
left.
now rewrite <- canonic_exp_abs.
right.
split.
exact H2.
unfold Rabs in H3.
destruct (Rcase_abs x) in H3.
rewrite <- Ropp_involutive.
now apply generic_format_opp.
exact H3.
Qed.

End round_dir_sign.

(** * Instances of the theorems above, for the usual rounding modes. *)

Definition round_DN_correct :=
  round_any_correct _ (fun m _ => m) inbetween_int_DN.

Definition round_trunc_DN_correct :=
  round_trunc_any_correct _ (fun m _ => m) inbetween_int_DN.

Definition round_sign_DN_correct :=
  round_sign_any_correct _ (fun s m l => cond_incr (round_sign_DN s l) m) inbetween_int_DN_sign.

Definition round_trunc_sign_DN_correct :=
  round_trunc_sign_any_correct _ (fun s m l => cond_incr (round_sign_DN s l) m) inbetween_int_DN_sign.

Definition round_UP_correct :=
  round_any_correct _ (fun m l => cond_incr (round_UP l) m) inbetween_int_UP.

Definition round_trunc_UP_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_UP l) m) inbetween_int_UP.

Definition round_sign_UP_correct :=
  round_sign_any_correct _ (fun s m l => cond_incr (round_sign_UP s l) m) inbetween_int_UP_sign.

Definition round_trunc_sign_UP_correct :=
  round_trunc_sign_any_correct _ (fun s m l => cond_incr (round_sign_UP s l) m) inbetween_int_UP_sign.

Definition round_ZR_correct :=
  round_any_correct _ (fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m) inbetween_int_ZR.

Definition round_trunc_ZR_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_ZR (Zlt_bool m 0) l) m) inbetween_int_ZR.

Definition round_sign_ZR_correct :=
  round_sign_any_correct _ (fun s m l => m) inbetween_int_ZR_sign.

Definition round_trunc_sign_ZR_correct :=
  round_trunc_sign_any_correct _ (fun s m l => m) inbetween_int_ZR_sign.

Definition round_NE_correct :=
  round_any_correct _ (fun m l => cond_incr (round_N (negb (Zeven m)) l) m) inbetween_int_NE.

Definition round_trunc_NE_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_N (negb (Zeven m)) l) m) inbetween_int_NE.

Definition round_sign_NE_correct :=
  round_sign_any_correct _ (fun s m l => cond_incr (round_N (negb (Zeven m)) l) m) inbetween_int_NE_sign.

Definition round_trunc_sign_NE_correct :=
  round_trunc_sign_any_correct _ (fun s m l => cond_incr (round_N (negb (Zeven m)) l) m) inbetween_int_NE_sign.

Definition round_NA_correct :=
  round_any_correct _ (fun m l => cond_incr (round_N (Zle_bool 0 m) l) m) inbetween_int_NA.

Definition round_trunc_NA_correct :=
  round_trunc_any_correct _ (fun m l => cond_incr (round_N (Zle_bool 0 m) l) m) inbetween_int_NA.

Definition round_sign_NA_correct :=
  round_sign_any_correct _ (fun s m l => cond_incr (round_N true l) m) inbetween_int_NA_sign.

Definition round_trunc_sign_NA_correct :=
  round_trunc_sign_any_correct _ (fun s m l => cond_incr (round_N true l) m) inbetween_int_NA_sign.

End Fcalc_round_fexp.

(** Specialization of truncate for FIX formats. *)

Variable emin : Z.

Definition truncate_FIX t :=
  let '(m, e, l) := t in
  let k := (emin - e)%Z in
  if Zlt_bool 0 k then
    let p := Zpower beta k in
    (Zdiv m p, (e + k)%Z, new_location p (Zmod m p) l)
  else t.

Theorem truncate_FIX_correct :
  forall x m e l,
  inbetween_float beta m e x l ->
  (e <= emin)%Z \/ l = loc_Exact ->
  let '(m', e', l') := truncate_FIX (m, e, l) in
  inbetween_float beta m' e' x l' /\
  (e' = canonic_exp beta (FIX_exp emin) x \/ (l' = loc_Exact /\ generic_format beta (FIX_exp emin) x)).
Proof.
intros x m e l H1 H2.
unfold truncate_FIX.
set (k := (emin - e)%Z).
set (p := Zpower beta k).
unfold canonic_exp, FIX_exp.
generalize (Zlt_cases 0 k).
case (Zlt_bool 0 k) ; intros Hk.
(* shift *)
split.
now apply inbetween_float_new_location.
clear H2.
left.
unfold k.
ring.
(* no shift *)
split.
exact H1.
unfold k in Hk.
destruct H2 as [H2|H2].
left.
omega.
right.
split.
exact H2.
rewrite H2 in H1.
inversion_clear H1.
rewrite H.
apply generic_format_F2R.
unfold canonic_exp.
omega.
Qed.

End Fcalc_round.

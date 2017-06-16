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

(** * Locations: where a real number is positioned with respect to its rounded-down value in an arbitrary format. *)

Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.

Section Fcalc_bracket.

Variable d u : R.
Hypothesis Hdu : (d < u)%R.

Inductive location := loc_Exact | loc_Inexact : comparison -> location.

Variable x : R.

Definition inbetween_loc :=
  match Rcompare x d with
  | Gt => loc_Inexact (Rcompare x ((d + u) / 2))
  | _ => loc_Exact
  end.

(** Locates a real number with respect to the middle of two other numbers. *)

Inductive inbetween : location -> Prop :=
  | inbetween_Exact : x = d -> inbetween loc_Exact
  | inbetween_Inexact l : (d < x < u)%R -> Rcompare x ((d + u) / 2)%R = l -> inbetween (loc_Inexact l).

Theorem inbetween_spec :
  (d <= x < u)%R -> inbetween inbetween_loc.
Proof.
intros Hx.
unfold inbetween_loc.
destruct (Rcompare_spec x d) as [H|H|H].
now elim Rle_not_lt with (1 := proj1 Hx).
now constructor.
constructor.
now split.
easy.
Qed.

Theorem inbetween_unique :
  forall l l',
  inbetween l -> inbetween l' -> l = l'.
Proof.
intros l l' Hl Hl'.
inversion_clear Hl ; inversion_clear Hl'.
apply refl_equal.
rewrite H in H0.
elim Rlt_irrefl with (1 := proj1 H0).
rewrite H1 in H.
elim Rlt_irrefl with (1 := proj1 H).
apply f_equal.
now rewrite <- H0.
Qed.

Section Fcalc_bracket_any.

Variable l : location.

Theorem inbetween_bounds :
  inbetween l ->
  (d <= x < u)%R.
Proof.
intros [Hx|l' Hx Hl] ; clear l.
rewrite Hx.
split.
apply Rle_refl.
exact Hdu.
now split ; try apply Rlt_le.
Qed.

Theorem inbetween_bounds_not_Eq :
  inbetween l ->
  l <> loc_Exact ->
  (d < x < u)%R.
Proof.
intros [Hx|l' Hx Hl] H.
now elim H.
exact Hx.
Qed.

End Fcalc_bracket_any.

Theorem inbetween_distance_inexact :
  forall l,
  inbetween (loc_Inexact l) ->
  Rcompare (x - d) (u - x) = l.
Proof.
intros l Hl.
inversion_clear Hl as [|l' Hl' Hx].
now rewrite Rcompare_middle.
Qed.

Theorem inbetween_distance_inexact_abs :
  forall l,
  inbetween (loc_Inexact l) ->
  Rcompare (Rabs (d - x)) (Rabs (u - x)) = l.
Proof.
intros l Hl.
rewrite Rabs_left1.
rewrite Rabs_pos_eq.
rewrite Ropp_minus_distr.
now apply inbetween_distance_inexact.
apply Rle_0_minus.
apply Rlt_le.
apply (inbetween_bounds _ Hl).
apply Rle_minus.
apply (inbetween_bounds _ Hl).
Qed.

End Fcalc_bracket.

Theorem inbetween_ex :
  forall d u l,
  (d < u)%R ->
  exists x,
  inbetween d u x l.
Proof.
intros d u [|l] Hdu.
exists d.
now constructor.
exists (d + match l with Lt => 1 | Eq => 2 | Gt => 3 end / 4 * (u - d))%R.
constructor.
(* *)
set (v := (match l with Lt => 1 | Eq => 2 | Gt => 3 end / 4)%R).
assert (0 < v < 1)%R.
split.
unfold v, Rdiv.
apply Rmult_lt_0_compat.
case l.
now apply (Z2R_lt 0 2).
now apply (Z2R_lt 0 1).
now apply (Z2R_lt 0 3).
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 4).
unfold v, Rdiv.
apply Rmult_lt_reg_r with 4%R.
now apply (Z2R_lt 0 4).
rewrite Rmult_assoc, Rinv_l.
rewrite Rmult_1_r, Rmult_1_l.
case l.
now apply (Z2R_lt 2 4).
now apply (Z2R_lt 1 4).
now apply (Z2R_lt 3 4).
apply Rgt_not_eq.
now apply (Z2R_lt 0 4).
split.
apply Rplus_lt_reg_r with (d * (v - 1))%R.
ring_simplify.
rewrite Rmult_comm.
now apply Rmult_lt_compat_l.
apply Rplus_lt_reg_l with (-u * v)%R.
replace (- u * v + (d + v * (u - d)))%R with (d * (1 - v))%R by ring.
replace (- u * v + u)%R with (u * (1 - v))%R by ring.
apply Rmult_lt_compat_r.
apply Rplus_lt_reg_r with v.
now ring_simplify.
exact Hdu.
(* *)
set (v := (match l with Lt => 1 | Eq => 2 | Gt => 3 end)%R).
rewrite <- (Rcompare_plus_r (- (d + u) / 2)).
rewrite <- (Rcompare_mult_r 4).
2: now apply (Z2R_lt 0 4).
replace (((d + u) / 2 + - (d + u) / 2) * 4)%R with ((u - d) * 0)%R by field.
replace ((d + v / 4 * (u - d) + - (d + u) / 2) * 4)%R with ((u - d) * (v - 2))%R by field.
rewrite Rcompare_mult_l.
2: now apply Rlt_Rminus.
rewrite <- (Rcompare_plus_r 2).
ring_simplify (v - 2 + 2)%R (0 + 2)%R.
unfold v.
case l.
exact (Rcompare_Z2R 2 2).
exact (Rcompare_Z2R 1 2).
exact (Rcompare_Z2R 3 2).
Qed.

Section Fcalc_bracket_step.

Variable start step : R.
Variable nb_steps : Z.
Variable Hstep : (0 < step)%R.

Lemma ordered_steps :
  forall k,
  (start + Z2R k * step < start + Z2R (k + 1) * step)%R.
Proof.
intros k.
apply Rplus_lt_compat_l.
apply Rmult_lt_compat_r.
exact Hstep.
apply Z2R_lt.
apply Zlt_succ.
Qed.

Lemma middle_range :
  forall k,
  ((start + (start + Z2R k * step)) / 2 = start + (Z2R k / 2 * step))%R.
Proof.
intros k.
field.
Qed.

Hypothesis (Hnb_steps : (1 < nb_steps)%Z).

Lemma inbetween_step_not_Eq :
  forall x k l l',
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  (0 < k < nb_steps)%Z ->
  Rcompare x (start + (Z2R nb_steps / 2 * step))%R = l' ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact l').
Proof.
intros x k l l' Hx Hk Hl'.
constructor.
(* . *)
assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
split.
apply Rlt_le_trans with (2 := proj1 Hx').
rewrite <- (Rplus_0_r start) at 1.
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
now apply (Z2R_lt 0).
exact Hstep.
apply Rlt_le_trans with (1 := proj2 Hx').
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Z2R_le.
omega.
(* . *)
now rewrite middle_range.
Qed.

Theorem inbetween_step_Lo :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  (0 < k)%Z -> (2 * k + 1 < nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Lt).
Proof.
intros x k l Hx Hk1 Hk2.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
apply Rcompare_Lt.
assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
apply Rlt_le_trans with (1 := proj2 Hx').
apply Rcompare_not_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
apply Rcompare_not_Lt.
change 2%R with (Z2R 2).
rewrite <- Z2R_mult.
apply Z2R_le.
omega.
exact Hstep.
Qed.

Theorem inbetween_step_Hi :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  (nb_steps < 2 * k)%Z -> (k < nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Gt).
Proof.
intros x k l Hx Hk1 Hk2.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
apply Rcompare_Gt.
assert (Hx' := inbetween_bounds _ _ (ordered_steps _) _ _ Hx).
apply Rlt_le_trans with (2 := proj1 Hx').
apply Rcompare_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
apply Rcompare_Lt.
change 2%R with (Z2R 2).
rewrite <- Z2R_mult.
apply Z2R_lt.
omega.
exact Hstep.
Qed.

Theorem inbetween_step_Lo_not_Eq :
  forall x l,
  inbetween start (start + step) x l ->
  l <> loc_Exact ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Lt).
Proof.
intros x l Hx Hl.
assert (Hx' := inbetween_bounds_not_Eq _ _ _ _ Hx Hl).
constructor.
(* . *)
split.
apply Hx'.
apply Rlt_trans with (1 := proj2 Hx').
apply Rplus_lt_compat_l.
rewrite <- (Rmult_1_l step) at 1.
apply Rmult_lt_compat_r.
exact Hstep.
now apply (Z2R_lt 1).
(* . *)
apply Rcompare_Lt.
apply Rlt_le_trans with (1 := proj2 Hx').
rewrite middle_range.
apply Rcompare_not_Lt_inv.
rewrite <- (Rmult_1_l step) at 2.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_l.
rewrite Rmult_1_r.
apply Rcompare_not_Lt.
apply (Z2R_le 2).
now apply (Zlt_le_succ 1).
exact Hstep.
Qed.

Lemma middle_odd :
  forall k,
  (2 * k + 1 = nb_steps)%Z ->
  (((start + Z2R k * step) + (start + Z2R (k + 1) * step))/2 = start + Z2R nb_steps /2 * step)%R.
Proof.
intros k Hk.
rewrite <- Hk.
rewrite 2!Z2R_plus, Z2R_mult.
simpl. field.
Qed.

Theorem inbetween_step_any_Mi_odd :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x (loc_Inexact l) ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact l).
Proof.
intros x k l Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
inversion_clear Hx as [|l' _ Hl].
now rewrite (middle_odd _ Hk) in Hl.
Qed.

Theorem inbetween_step_Lo_Mi_Eq_odd :
  forall x k,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x loc_Exact ->
  (2 * k + 1 = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Lt).
Proof.
intros x k Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
inversion_clear Hx as [Hl|].
rewrite Hl.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_r.
apply Rcompare_Lt.
change 2%R with (Z2R 2).
rewrite <- Z2R_mult.
apply Z2R_lt.
rewrite <- Hk.
apply Zlt_succ.
exact Hstep.
Qed.

Theorem inbetween_step_Hi_Mi_even :
  forall x k l,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  l <> loc_Exact ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Gt).
Proof.
intros x k l Hx Hl Hk.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
apply Rcompare_Gt.
assert (Hx' := inbetween_bounds_not_Eq _ _ _ _ Hx Hl).
apply Rle_lt_trans with (2 := proj1 Hx').
apply Rcompare_not_Lt_inv.
rewrite Rcompare_plus_l, Rcompare_mult_r, Rcompare_half_r.
change 2%R with (Z2R 2).
rewrite <- Z2R_mult.
apply Rcompare_not_Lt.
apply Z2R_le.
rewrite Hk.
apply Zle_refl.
exact Hstep.
Qed.

Theorem inbetween_step_Mi_Mi_even :
  forall x k,
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x loc_Exact ->
  (2 * k = nb_steps)%Z ->
  inbetween start (start + Z2R nb_steps * step) x (loc_Inexact Eq).
Proof.
intros x k Hx Hk.
apply inbetween_step_not_Eq with (1 := Hx).
omega.
apply Rcompare_Eq.
inversion_clear Hx as [Hx'|].
rewrite Hx', <- Hk, Z2R_mult.
simpl (Z2R 2).
field.
Qed.

(** Computes a new location when the interval containing a real
    number is split into nb_steps subintervals and the real is
    in the k-th one. (Even radix.) *)

Definition new_location_even k l :=
  if Zeq_bool k 0 then
    match l with loc_Exact => l | _ => loc_Inexact Lt end
  else
    loc_Inexact
    match Zcompare (2 * k) nb_steps with
    | Lt => Lt
    | Eq => match l with loc_Exact => Eq | _ => Gt end
    | Gt => Gt
    end.

Theorem new_location_even_correct :
  Zeven nb_steps = true ->
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  inbetween start (start + Z2R nb_steps * step) x (new_location_even k l).
Proof.
intros He x k l Hk Hx.
unfold new_location_even.
destruct (Zeq_bool_spec k 0) as [Hk0|Hk0].
(* k = 0 *)
rewrite Hk0 in Hx.
rewrite Rmult_0_l, Rplus_0_r, Rmult_1_l in Hx.
set (l' := match l with loc_Exact => l | _ => loc_Inexact Lt end).
assert ((l = loc_Exact /\ l' = loc_Exact) \/ (l <> loc_Exact /\ l' = loc_Inexact Lt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
constructor.
rewrite H1 in Hx.
now inversion_clear Hx.
now apply inbetween_step_Lo_not_Eq with (2 := H1).
(* k <> 0 *)
destruct (Zcompare_spec (2 * k) nb_steps) as [Hk1|Hk1|Hk1].
(* . 2 * k < nb_steps *)
apply inbetween_step_Lo with (1 := Hx).
omega.
destruct (Zeven_ex nb_steps).
rewrite He in H.
omega.
(* . 2 * k = nb_steps *)
set (l' := match l with loc_Exact => Eq | _ => Gt end).
assert ((l = loc_Exact /\ l' = Eq) \/ (l <> loc_Exact /\ l' = Gt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
rewrite H1 in Hx.
now apply inbetween_step_Mi_Mi_even with (1 := Hx).
now apply inbetween_step_Hi_Mi_even with (1 := Hx).
(* . 2 * k > nb_steps *)
apply inbetween_step_Hi with (1 := Hx).
exact Hk1.
apply Hk.
Qed.

(** Computes a new location when the interval containing a real
    number is split into nb_steps subintervals and the real is
    in the k-th one. (Odd radix.) *)

Definition new_location_odd k l :=
  if Zeq_bool k 0 then
    match l with loc_Exact => l | _ => loc_Inexact Lt end
  else
    loc_Inexact
    match Zcompare (2 * k + 1) nb_steps with
    | Lt => Lt
    | Eq => match l with loc_Inexact l => l | loc_Exact => Lt end
    | Gt => Gt
    end.

Theorem new_location_odd_correct :
  Zeven nb_steps = false ->
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  inbetween start (start + Z2R nb_steps * step) x (new_location_odd k l).
Proof.
intros Ho x k l Hk Hx.
unfold new_location_odd.
destruct (Zeq_bool_spec k 0) as [Hk0|Hk0].
(* k = 0 *)
rewrite Hk0 in Hx.
rewrite Rmult_0_l, Rplus_0_r, Rmult_1_l in Hx.
set (l' := match l with loc_Exact => l | _ => loc_Inexact Lt end).
assert ((l = loc_Exact /\ l' = loc_Exact) \/ (l <> loc_Exact /\ l' = loc_Inexact Lt)).
unfold l' ; case l ; try (now left) ; right ; now split.
destruct H as [(H1,H2)|(H1,H2)] ; rewrite H2.
constructor.
rewrite H1 in Hx.
now inversion_clear Hx.
now apply inbetween_step_Lo_not_Eq with (2 := H1).
(* k <> 0 *)
destruct (Zcompare_spec (2 * k + 1) nb_steps) as [Hk1|Hk1|Hk1].
(* . 2 * k + 1 < nb_steps *)
apply inbetween_step_Lo with (1 := Hx) (3 := Hk1).
omega.
(* . 2 * k + 1 = nb_steps *)
destruct l.
apply inbetween_step_Lo_Mi_Eq_odd with (1 := Hx) (2 := Hk1).
apply inbetween_step_any_Mi_odd with (1 := Hx) (2 := Hk1).
(* . 2 * k + 1 > nb_steps *)
apply inbetween_step_Hi with (1 := Hx).
destruct (Zeven_ex nb_steps).
rewrite Ho in H.
omega.
apply Hk.
Qed.

Definition new_location :=
  if Zeven nb_steps then new_location_even else new_location_odd.

Theorem new_location_correct :
  forall x k l, (0 <= k < nb_steps)%Z ->
  inbetween (start + Z2R k * step) (start + Z2R (k + 1) * step) x l ->
  inbetween start (start + Z2R nb_steps * step) x (new_location k l).
Proof.
intros x k l Hk Hx.
unfold new_location.
generalize (refl_equal nb_steps) (Zle_lt_trans _ _ _ (proj1 Hk) (proj2 Hk)).
pattern nb_steps at 2 3 5 ; case nb_steps.
now intros _.
(* . *)
intros [p|p|] Hp _.
apply new_location_odd_correct with (2 := Hk) (3 := Hx).
now rewrite Hp.
apply new_location_even_correct with (2 := Hk) (3 := Hx).
now rewrite Hp.
now rewrite Hp in Hnb_steps.
(* . *)
now intros p _.
Qed.

End Fcalc_bracket_step.

Section Fcalc_bracket_scale.

Lemma inbetween_mult_aux :
  forall x d s,
  ((x * s + d * s) / 2 = (x + d) / 2 * s)%R.
Proof.
intros x d s.
field.
Qed.

Theorem inbetween_mult_compat :
  forall x d u l s,
  (0 < s)%R ->
  inbetween x d u l ->
  inbetween (x * s) (d * s) (u * s) l.
Proof.
intros x d u l s Hs [Hx|l' Hx Hl] ; constructor.
now rewrite Hx.
now split ; apply Rmult_lt_compat_r.
rewrite inbetween_mult_aux.
now rewrite Rcompare_mult_r.
Qed.

Theorem inbetween_mult_reg :
  forall x d u l s,
  (0 < s)%R ->
  inbetween (x * s) (d * s) (u * s) l ->
  inbetween x d u l.
Proof.
intros x d u l s Hs [Hx|l' Hx Hl] ; constructor.
apply Rmult_eq_reg_r with (1 := Hx).
now apply Rgt_not_eq.
now split ; apply Rmult_lt_reg_r with s.
rewrite <- Rcompare_mult_r with (1 := Hs).
now rewrite inbetween_mult_aux in Hl.
Qed.

End Fcalc_bracket_scale.

Section Fcalc_bracket_generic.

Variable beta : radix.
Notation bpow e := (bpow beta e).

(** Specialization of inbetween for two consecutive floating-point numbers. *)

Definition inbetween_float m e x l :=
  inbetween (F2R (Float beta m e)) (F2R (Float beta (m + 1) e)) x l.

Theorem inbetween_float_bounds :
  forall x m e l,
  inbetween_float m e x l ->
  (F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e))%R.
Proof.
intros x m e l [Hx|l' Hx Hl].
rewrite Hx.
split.
apply Rle_refl.
apply F2R_lt_compat.
apply Zlt_succ.
split.
now apply Rlt_le.
apply Hx.
Qed.

(** Specialization of inbetween for two consecutive integers. *)

Definition inbetween_int m x l :=
  inbetween (Z2R m) (Z2R (m + 1)) x l.

Theorem inbetween_float_new_location :
  forall x m e l k,
  (0 < k)%Z ->
  inbetween_float m e x l ->
  inbetween_float (Zdiv m (Zpower beta k)) (e + k) x (new_location (Zpower beta k) (Zmod m (Zpower beta k)) l).
Proof.
intros x m e l k Hk Hx.
unfold inbetween_float in *.
assert (Hr: forall m, F2R (Float beta m (e + k)) = F2R (Float beta (m * Zpower beta k) e)).
clear -Hk. intros m.
rewrite (F2R_change_exp beta e).
apply (f_equal (fun r => F2R (Float beta (m * Zpower _ r) e))).
ring.
omega.
assert (Hp: (Zpower beta k > 0)%Z).
apply Zlt_gt.
apply Zpower_gt_0.
now apply Zlt_le_weak.
(* . *)
rewrite 2!Hr.
rewrite Zmult_plus_distr_l, Zmult_1_l.
unfold F2R at 2. simpl.
rewrite Z2R_plus, Rmult_plus_distr_r.
apply new_location_correct.
apply bpow_gt_0.
now apply Zpower_gt_1.
now apply Z_mod_lt.
rewrite <- 2!Rmult_plus_distr_r, <- 2!Z2R_plus.
rewrite Zmult_comm, Zplus_assoc.
now rewrite <- Z_div_mod_eq.
Qed.

Theorem inbetween_float_new_location_single :
  forall x m e l,
  inbetween_float m e x l ->
  inbetween_float (Zdiv m beta) (e + 1) x (new_location beta (Zmod m beta) l).
Proof.
intros x m e l Hx.
replace (radix_val beta) with (Zpower beta 1).
now apply inbetween_float_new_location.
apply Zmult_1_r.
Qed.

Theorem inbetween_float_ex :
  forall m e l,
  exists x,
  inbetween_float m e x l.
Proof.
intros m e l.
apply inbetween_ex.
apply F2R_lt_compat.
apply Zlt_succ.
Qed.

Theorem inbetween_float_unique :
  forall x e m l m' l',
  inbetween_float m e x l ->
  inbetween_float m' e x l' ->
  m = m' /\ l = l'.
Proof.
intros x e m l m' l' H H'.
refine ((fun Hm => conj Hm _) _).
rewrite <- Hm in H'. clear -H H'.
apply inbetween_unique with (1 := H) (2 := H').
destruct (inbetween_float_bounds x m e l H) as (H1,H2).
destruct (inbetween_float_bounds x m' e l' H') as (H3,H4).
cut (m < m' + 1 /\ m' < m + 1)%Z. clear ; omega.
now split ; apply F2R_lt_reg with beta e ; apply Rle_lt_trans with x.
Qed.

End Fcalc_bracket_generic.

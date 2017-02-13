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

(** * Roundings: properties and/or functions *)
Require Import Fcore_Raux.
Require Import Fcore_defs.

Section RND_prop.

Open Scope R_scope.

Theorem round_val_of_pred :
  forall rnd : R -> R -> Prop,
  round_pred rnd ->
  forall x, { f : R | rnd x f }.
Proof.
intros rnd (H1,H2) x.
specialize (H1 x).
(* . *)
assert (H3 : bound (rnd x)).
destruct H1 as (f, H1).
exists f.
intros g Hg.
now apply H2 with (3 := Rle_refl x).
(* . *)
exists (proj1_sig (completeness _ H3 H1)).
destruct completeness as (f1, (H4, H5)).
simpl.
destruct H1 as (f2, H1).
assert (f1 = f2).
apply Rle_antisym.
apply H5.
intros f3 H.
now apply H2 with (3 := Rle_refl x).
now apply H4.
now rewrite H.
Qed.

Theorem round_fun_of_pred :
  forall rnd : R -> R -> Prop,
  round_pred rnd ->
  { f : R -> R | forall x, rnd x (f x) }.
Proof.
intros rnd H.
exists (fun x => proj1_sig (round_val_of_pred rnd H x)).
intros x.
now destruct round_val_of_pred as (f, H1).
Qed.

Theorem round_unicity :
  forall rnd : R -> R -> Prop,
  round_pred_monotone rnd ->
  forall x f1 f2,
  rnd x f1 ->
  rnd x f2 ->
  f1 = f2.
Proof.
intros rnd Hr x f1 f2 H1 H2.
apply Rle_antisym.
now apply Hr with (3 := Rle_refl x).
now apply Hr with (3 := Rle_refl x).
Qed.

Theorem Rnd_DN_pt_monotone :
  forall F : R -> Prop,
  round_pred_monotone (Rnd_DN_pt F).
Proof.
intros F x y f g (Hx1,(Hx2,_)) (Hy1,(_,Hy2)) Hxy.
apply Hy2.
apply Hx1.
now apply Rle_trans with (2 := Hxy).
Qed.

Theorem Rnd_DN_pt_unicity :
  forall F : R -> Prop,
  forall x f1 f2 : R,
  Rnd_DN_pt F x f1 -> Rnd_DN_pt F x f2 ->
  f1 = f2.
Proof.
intros F.
apply round_unicity.
apply Rnd_DN_pt_monotone.
Qed.

Theorem Rnd_DN_unicity :
  forall F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_DN F rnd1 -> Rnd_DN F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F rnd1 rnd2 H1 H2 x.
now eapply Rnd_DN_pt_unicity.
Qed.

Theorem Rnd_UP_pt_monotone :
  forall F : R -> Prop,
  round_pred_monotone (Rnd_UP_pt F).
Proof.
intros F x y f g (Hx1,(_,Hx2)) (Hy1,(Hy2,_)) Hxy.
apply Hx2.
apply Hy1.
now apply Rle_trans with (1 := Hxy).
Qed.

Theorem Rnd_UP_pt_unicity :
  forall F : R -> Prop,
  forall x f1 f2 : R,
  Rnd_UP_pt F x f1 -> Rnd_UP_pt F x f2 ->
  f1 = f2.
Proof.
intros F.
apply round_unicity.
apply Rnd_UP_pt_monotone.
Qed.

Theorem Rnd_UP_unicity :
  forall F : R -> Prop,
  forall rnd1 rnd2 : R -> R,
  Rnd_UP F rnd1 -> Rnd_UP F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F rnd1 rnd2 H1 H2 x.
now eapply Rnd_UP_pt_unicity.
Qed.

Theorem Rnd_DN_UP_pt_sym :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_DN_pt F x f -> Rnd_UP_pt F (-x) (-f).
Proof.
intros F HF x f H.
repeat split.
apply HF.
apply H.
apply Ropp_le_contravar.
apply H.
intros g Hg.
rewrite <- (Ropp_involutive g).
intros Hxg.
apply Ropp_le_contravar.
apply H.
now apply HF.
now apply Ropp_le_cancel.
Qed.

Theorem Rnd_UP_DN_pt_sym :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_UP_pt F x f -> Rnd_DN_pt F (-x) (-f).
Proof.
intros F HF x f H.
repeat split.
apply HF.
apply H.
apply Ropp_le_contravar.
apply H.
intros g Hg.
rewrite <- (Ropp_involutive g).
intros Hxg.
apply Ropp_le_contravar.
apply H.
now apply HF.
now apply Ropp_le_cancel.
Qed.

Theorem Rnd_DN_UP_sym :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall rnd1 rnd2 : R -> R,
  Rnd_DN F rnd1 -> Rnd_UP F rnd2 ->
  forall x, rnd1 (- x) = - rnd2 x.
Proof.
intros F HF rnd1 rnd2 H1 H2 x.
rewrite <- (Ropp_involutive (rnd1 (-x))).
apply f_equal.
apply (Rnd_UP_unicity F (fun x => - rnd1 (-x))) ; trivial.
intros y.
pattern y at 1 ; rewrite <- Ropp_involutive.
apply Rnd_DN_UP_pt_sym.
apply HF.
apply H1.
Qed.

Theorem Rnd_DN_UP_pt_split :
  forall F : R -> Prop,
  forall x d u,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  forall f, F f ->
  (f <= d) \/ (u <= f).
Proof.
intros F x d u Hd Hu f Hf.
destruct (Rle_or_lt f x).
left.
now apply Hd.
right.
assert (H' := Rlt_le _ _ H).
now apply Hu.
Qed.

Theorem Rnd_DN_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_DN_pt F x x.
Proof.
intros F x Hx.
repeat split.
exact Hx.
apply Rle_refl.
now intros.
Qed.

Theorem Rnd_DN_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_DN_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,(Hx1,Hx2)) Hx.
apply Rle_antisym.
exact Hx1.
apply Hx2.
exact Hx.
apply Rle_refl.
Qed.

Theorem Rnd_UP_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_UP_pt F x x.
Proof.
intros F x Hx.
repeat split.
exact Hx.
apply Rle_refl.
now intros.
Qed.

Theorem Rnd_UP_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_UP_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,(Hx1,Hx2)) Hx.
apply Rle_antisym.
apply Hx2.
exact Hx.
apply Rle_refl.
exact Hx1.
Qed.

Theorem Only_DN_or_UP :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  F f -> (fd <= f <= fu)%R ->
  f = fd \/ f = fu.
Proof.
intros F x fd fu f Hd Hu Hf [Hdf Hfu].
destruct (Rle_or_lt x f) ; [right|left].
apply Rle_antisym with (1 := Hfu).
now apply Hu.
apply Rlt_le in H.
apply Rle_antisym with (2 := Hdf).
now apply Hd.
Qed.

Theorem Rnd_ZR_abs :
  forall (F : R -> Prop) (rnd: R-> R),
  Rnd_ZR F rnd ->
  forall x : R,  (Rabs (rnd x) <= Rabs x)%R.
Proof.
intros F rnd H x.
assert (F 0%R).
replace 0%R with (rnd 0%R).
eapply H.
apply Rle_refl.
destruct (H 0%R) as (H1, H2).
apply Rle_antisym.
apply H1.
apply Rle_refl.
apply H2.
apply Rle_refl.
(* . *)
destruct (Rle_or_lt 0 x).
(* positive *)
rewrite Rabs_right.
rewrite Rabs_right; auto with real.
now apply (proj1 (H x)).
apply Rle_ge.
now apply (proj1 (H x)).
(* negative *)
rewrite Rabs_left1.
rewrite Rabs_left1 ; auto with real.
apply Ropp_le_contravar.
apply (proj2 (H x)).
auto with real.
apply (proj2 (H x)) ; auto with real.
Qed.

Theorem Rnd_ZR_pt_monotone :
  forall F : R -> Prop, F 0 ->
  round_pred_monotone (Rnd_ZR_pt F).
Proof.
intros F F0 x y f g (Hx1, Hx2) (Hy1, Hy2) Hxy.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
(* . *)
apply Hy1.
now apply Rle_trans with x.
now apply Hx1.
apply Rle_trans with (2 := Hxy).
now apply Hx1.
(* . *)
apply Rlt_le in Hx.
destruct (Rle_or_lt 0 y) as [Hy|Hy].
apply Rle_trans with 0.
now apply Hx2.
now apply Hy1.
apply Rlt_le in Hy.
apply Hx2.
exact Hx.
now apply Hy2.
apply Rle_trans with (1 := Hxy).
now apply Hy2.
Qed.

Theorem Rnd_N_pt_DN_or_UP :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N_pt F x f ->
  Rnd_DN_pt F x f \/ Rnd_UP_pt F x f.
Proof.
intros F x f (Hf1,Hf2).
destruct (Rle_or_lt x f) as [Hxf|Hxf].
(* . *)
right.
repeat split ; try assumption.
intros g Hg Hxg.
specialize (Hf2 g Hg).
rewrite 2!Rabs_pos_eq in Hf2.
now apply Rplus_le_reg_r with (-x)%R.
now apply Rle_0_minus.
now apply Rle_0_minus.
(* . *)
left.
repeat split ; try assumption.
now apply Rlt_le.
intros g Hg Hxg.
specialize (Hf2 g Hg).
rewrite 2!Rabs_left1 in Hf2.
generalize (Ropp_le_cancel _ _ Hf2).
intros H.
now apply Rplus_le_reg_r with (-x)%R.
now apply Rle_minus.
apply Rlt_le.
now apply Rlt_minus.
Qed.

Theorem Rnd_N_pt_DN_or_UP_eq :
  forall F : R -> Prop,
  forall x fd fu f : R,
  Rnd_DN_pt F x fd -> Rnd_UP_pt F x fu ->
  Rnd_N_pt F x f ->
  f = fd \/ f = fu.
Proof.
intros F x fd fu f Hd Hu Hf.
destruct (Rnd_N_pt_DN_or_UP F x f Hf) as [H|H].
left.
apply Rnd_DN_pt_unicity with (1 := H) (2 := Hd).
right.
apply Rnd_UP_pt_unicity with (1 := H) (2 := Hu).
Qed.

Theorem Rnd_N_pt_sym :
  forall F : R -> Prop,
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_N_pt F (-x) (-f) -> Rnd_N_pt F x f.
Proof.
intros F HF x f (H1,H2).
rewrite <- (Ropp_involutive f).
repeat split.
apply HF.
apply H1.
intros g H3.
rewrite Ropp_involutive.
replace (f - x)%R with (-(-f - -x))%R by ring.
replace (g - x)%R with (-(-g - -x))%R by ring.
rewrite 2!Rabs_Ropp.
apply H2.
now apply HF.
Qed.

Theorem Rnd_N_pt_monotone :
  forall F : R -> Prop,
  forall x y f g : R,
  Rnd_N_pt F x f -> Rnd_N_pt F y g ->
  x < y -> f <= g.
Proof.
intros F x y f g (Hf,Hx) (Hg,Hy) Hxy.
apply Rnot_lt_le.
intros Hgf.
assert (Hfgx := Hx g Hg).
assert (Hgfy := Hy f Hf).
clear F Hf Hg Hx Hy.
destruct (Rle_or_lt x g) as [Hxg|Hgx].
(* x <= g < f *)
apply Rle_not_lt with (1 := Hfgx).
rewrite 2!Rabs_pos_eq.
now apply Rplus_lt_compat_r.
apply Rle_0_minus.
apply Rlt_le.
now apply Rle_lt_trans with (1 := Hxg).
now apply Rle_0_minus.
assert (Hgy := Rlt_trans _ _ _ Hgx Hxy).
destruct (Rle_or_lt f y) as [Hfy|Hyf].
(* g < f <= y *)
apply Rle_not_lt with (1 := Hgfy).
rewrite (Rabs_left (g - y)).
2: now apply Rlt_minus.
rewrite Rabs_left1.
apply Ropp_lt_contravar.
now apply Rplus_lt_compat_r.
now apply Rle_minus.
(* g < x < y < f *)
rewrite Rabs_left, Rabs_pos_eq, Ropp_minus_distr in Hgfy.
rewrite Rabs_pos_eq, Rabs_left, Ropp_minus_distr in Hfgx.
apply Rle_not_lt with (1 := Rplus_le_compat _ _ _ _ Hfgx Hgfy).
apply Rminus_lt.
ring_simplify.
apply Rlt_minus.
apply Rmult_lt_compat_l.
now apply (Z2R_lt 0 2).
exact Hxy.
now apply Rlt_minus.
apply Rle_0_minus.
apply Rlt_le.
now apply Rlt_trans with (1 := Hxy).
apply Rle_0_minus.
now apply Rlt_le.
now apply Rlt_minus.
Qed.

Theorem Rnd_N_pt_unicity :
  forall F : R -> Prop,
  forall x d u f1 f2 : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  x - d <> u - x ->
  Rnd_N_pt F x f1 ->
  Rnd_N_pt F x f2 ->
  f1 = f2.
Proof.
intros F x d u f1 f2 Hd Hu Hdu.
assert (forall f1 f2, Rnd_N_pt F x f1 -> Rnd_N_pt F x f2 -> f1 < f2 -> False).
clear f1 f2. intros f1 f2 Hf1 Hf2 H12.
destruct (Rnd_N_pt_DN_or_UP F x f1 Hf1) as [Hd1|Hu1] ;
  destruct (Rnd_N_pt_DN_or_UP F x f2 Hf2) as [Hd2|Hu2].
apply Rlt_not_eq with (1 := H12).
now apply Rnd_DN_pt_unicity with (1 := Hd1).
apply Hdu.
rewrite Rnd_DN_pt_unicity with (1 := Hd) (2 := Hd1).
rewrite Rnd_UP_pt_unicity with (1 := Hu) (2 := Hu2).
rewrite <- (Rabs_pos_eq (x - f1)).
rewrite <- (Rabs_pos_eq (f2 - x)).
rewrite Rabs_minus_sym.
apply Rle_antisym.
apply Hf1. apply Hf2.
apply Hf2. apply Hf1.
apply Rle_0_minus.
apply Hu2.
apply Rle_0_minus.
apply Hd1.
apply Rlt_not_le with (1 := H12).
apply Rle_trans with x.
apply Hd2.
apply Hu1.
apply Rgt_not_eq with (1 := H12).
now apply Rnd_UP_pt_unicity with (1 := Hu2).
intros Hf1 Hf2.
now apply Rle_antisym ; apply Rnot_lt_le ; refine (H _ _ _ _).
Qed.

Theorem Rnd_N_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_N_pt F x x.
Proof.
intros F x Hx.
repeat split.
exact Hx.
intros g _.
unfold Rminus at 1.
rewrite Rplus_opp_r, Rabs_R0.
apply Rabs_pos.
Qed.

Theorem Rnd_N_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_N_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (_,Hf) Hx.
apply Rminus_diag_uniq.
destruct (Req_dec (f - x) 0) as [H|H].
exact H.
elim Rabs_no_R0 with (1 := H).
apply Rle_antisym.
replace 0 with (Rabs (x - x)).
now apply Hf.
unfold Rminus.
rewrite Rplus_opp_r.
apply Rabs_R0.
apply Rabs_pos.
Qed.

Theorem Rnd_N_pt_0 :
  forall F : R -> Prop,
  F 0 ->
  Rnd_N_pt F 0 0.
Proof.
intros F HF.
split.
exact HF.
intros g _.
rewrite 2!Rminus_0_r, Rabs_R0.
apply Rabs_pos.
Qed.

Theorem Rnd_N_pt_pos :
  forall F : R -> Prop, F 0 ->
  forall x f, 0 <= x ->
  Rnd_N_pt F x f ->
  0 <= f.
Proof.
intros F HF x f [Hx|Hx] Hxf.
eapply Rnd_N_pt_monotone ; try eassumption.
now apply Rnd_N_pt_0.
right.
apply sym_eq.
apply Rnd_N_pt_idempotent with F.
now rewrite Hx.
exact HF.
Qed.

Theorem Rnd_N_pt_neg :
  forall F : R -> Prop, F 0 ->
  forall x f, x <= 0 ->
  Rnd_N_pt F x f ->
  f <= 0.
Proof.
intros F HF x f [Hx|Hx] Hxf.
eapply Rnd_N_pt_monotone ; try eassumption.
now apply Rnd_N_pt_0.
right.
apply Rnd_N_pt_idempotent with F.
now rewrite <- Hx.
exact HF.
Qed.

Theorem Rnd_N_pt_abs :
  forall F : R -> Prop,
  F 0 ->
  ( forall x, F x -> F (- x) ) ->
  forall x f : R,
  Rnd_N_pt F x f -> Rnd_N_pt F (Rabs x) (Rabs f).
Proof.
intros F HF0 HF x f Hxf.
unfold Rabs at 1.
destruct (Rcase_abs x) as [Hx|Hx].
rewrite Rabs_left1.
apply Rnd_N_pt_sym.
exact HF.
now rewrite 2!Ropp_involutive.
apply Rnd_N_pt_neg with (3 := Hxf).
exact HF0.
now apply Rlt_le.
rewrite Rabs_pos_eq.
exact Hxf.
apply Rnd_N_pt_pos with (3 := Hxf).
exact HF0.
now apply Rge_le.
Qed.

Theorem Rnd_DN_UP_pt_N :
  forall F : R -> Prop,
  forall x d u f : R,
  F f ->
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (Rabs (f - x) <= x - d)%R ->
  (Rabs (f - x) <= u - x)%R ->
  Rnd_N_pt F x f.
Proof.
intros F x d u f Hf Hxd Hxu Hd Hu.
split.
exact Hf.
intros g Hg.
destruct (Rnd_DN_UP_pt_split F x d u Hxd Hxu g Hg) as [Hgd|Hgu].
(* g <= d *)
apply Rle_trans with (1 := Hd).
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rplus_le_compat_l.
now apply Ropp_le_contravar.
apply Rle_minus.
apply Rle_trans with (1 := Hgd).
apply Hxd.
(* u <= g *)
apply Rle_trans with (1 := Hu).
rewrite Rabs_pos_eq.
now apply Rplus_le_compat_r.
apply Rle_0_minus.
apply Rle_trans with (2 := Hgu).
apply Hxu.
Qed.

Theorem Rnd_DN_pt_N :
  forall F : R -> Prop,
  forall x d u : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (x - d <= u - x)%R ->
  Rnd_N_pt F x d.
Proof.
intros F x d u Hd Hu Hx.
assert (Hdx: (Rabs (d - x) = x - d)%R).
rewrite Rabs_minus_sym.
apply Rabs_pos_eq.
apply Rle_0_minus.
apply Hd.
apply Rnd_DN_UP_pt_N with (2 := Hd) (3 := Hu).
apply Hd.
rewrite Hdx.
apply Rle_refl.
now rewrite Hdx.
Qed.

Theorem Rnd_UP_pt_N :
  forall F : R -> Prop,
  forall x d u : R,
  Rnd_DN_pt F x d ->
  Rnd_UP_pt F x u ->
  (u - x <= x - d)%R ->
  Rnd_N_pt F x u.
Proof.
intros F x d u Hd Hu Hx.
assert (Hux: (Rabs (u - x) = u - x)%R).
apply Rabs_pos_eq.
apply Rle_0_minus.
apply Hu.
apply Rnd_DN_UP_pt_N with (2 := Hd) (3 := Hu).
apply Hu.
now rewrite Hux.
rewrite Hux.
apply Rle_refl.
Qed.

Definition Rnd_NG_pt_unicity_prop F P :=
  forall x d u,
  Rnd_DN_pt F x d -> Rnd_N_pt F x d ->
  Rnd_UP_pt F x u -> Rnd_N_pt F x u ->
  P x d -> P x u -> d = u.

Theorem Rnd_NG_pt_unicity :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unicity_prop F P ->
  forall x f1 f2 : R,
  Rnd_NG_pt F P x f1 -> Rnd_NG_pt F P x f2 ->
  f1 = f2.
Proof.
intros F P HP x f1 f2 (H1a,H1b) (H2a,H2b).
destruct H1b as [H1b|H1b].
destruct H2b as [H2b|H2b].
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1a) as [H1c|H1c] ;
  destruct (Rnd_N_pt_DN_or_UP _ _ _ H2a) as [H2c|H2c].
eapply Rnd_DN_pt_unicity ; eassumption.
now apply (HP x f1 f2).
apply sym_eq.
now apply (HP x f2 f1 H2c H2a H1c H1a).
eapply Rnd_UP_pt_unicity ; eassumption.
now apply H2b.
apply sym_eq.
now apply H1b.
Qed.

Theorem Rnd_NG_pt_monotone :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unicity_prop F P ->
  round_pred_monotone (Rnd_NG_pt F P).
Proof.
intros F P HP x y f g (Hf,Hx) (Hg,Hy) [Hxy|Hxy].
now apply Rnd_N_pt_monotone with F x y.
apply Req_le.
rewrite <- Hxy in Hg, Hy.
eapply Rnd_NG_pt_unicity ; try split ; eassumption.
Qed.

Theorem Rnd_NG_pt_refl :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  forall x, F x -> Rnd_NG_pt F P x x.
Proof.
intros F P x Hx.
split.
now apply Rnd_N_pt_refl.
right.
intros f2 Hf2.
now apply Rnd_N_pt_idempotent with F.
Qed.

Theorem Rnd_NG_pt_sym :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  ( forall x, F x -> F (-x) ) ->
  ( forall x f, P x f -> P (-x) (-f) ) ->
  forall x f : R,
  Rnd_NG_pt F P (-x) (-f) -> Rnd_NG_pt F P x f.
Proof.
intros F P HF HP x f (H1,H2).
split.
now apply Rnd_N_pt_sym.
destruct H2 as [H2|H2].
left.
rewrite <- (Ropp_involutive x), <- (Ropp_involutive f).
now apply HP.
right.
intros f2 Hxf2.
rewrite <- (Ropp_involutive f).
rewrite <- H2 with (-f2).
apply sym_eq.
apply Ropp_involutive.
apply Rnd_N_pt_sym.
exact HF.
now rewrite 2!Ropp_involutive.
Qed.

Theorem Rnd_NG_unicity :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  Rnd_NG_pt_unicity_prop F P ->
  forall rnd1 rnd2 : R -> R,
  Rnd_NG F P rnd1 -> Rnd_NG F P rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F P HP rnd1 rnd2 H1 H2 x.
now apply Rnd_NG_pt_unicity with F P x.
Qed.

Theorem Rnd_NA_NG_pt :
  forall F : R -> Prop,
  F 0 ->
  forall x f,
  Rnd_NA_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs x <= Rabs f) x f.
Proof.
intros F HF x f.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
(* *)
split ; intros (H1, H2).
(* . *)
assert (Hf := Rnd_N_pt_pos F HF x f Hx H1).
split.
exact H1.
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1) as [H3|H3].
(* . . *)
right.
intros f2 Hxf2.
specialize (H2 _ Hxf2).
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H4|H4].
eapply Rnd_DN_pt_unicity ; eassumption.
apply Rle_antisym.
rewrite Rabs_pos_eq with (1 := Hf) in H2.
rewrite Rabs_pos_eq in H2.
exact H2.
now apply Rnd_N_pt_pos with F x.
apply Rle_trans with x.
apply H3.
apply H4.
(* . . *)
left.
rewrite Rabs_pos_eq with (1 := Hf).
rewrite Rabs_pos_eq with (1 := Hx).
apply H3.
(* . *)
split.
exact H1.
intros f2 Hxf2.
destruct H2 as [H2|H2].
assert (Hf := Rnd_N_pt_pos F HF x f Hx H1).
assert (Hf2 := Rnd_N_pt_pos F HF x f2 Hx Hxf2).
rewrite 2!Rabs_pos_eq ; trivial.
rewrite 2!Rabs_pos_eq in H2 ; trivial.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H3|H3].
apply Rle_trans with (2 := H2).
apply H3.
apply H3.
apply H1.
apply H2.
rewrite (H2 _ Hxf2).
apply Rle_refl.
(* *)
assert (Hx' := Rlt_le _ _ Hx).
clear Hx. rename Hx' into Hx.
split ; intros (H1, H2).
(* . *)
assert (Hf := Rnd_N_pt_neg F HF x f Hx H1).
split.
exact H1.
destruct (Rnd_N_pt_DN_or_UP _ _ _ H1) as [H3|H3].
(* . . *)
left.
rewrite Rabs_left1 with (1 := Hf).
rewrite Rabs_left1 with (1 := Hx).
apply Ropp_le_contravar.
apply H3.
(* . . *)
right.
intros f2 Hxf2.
specialize (H2 _ Hxf2).
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H4|H4].
apply Rle_antisym.
apply Rle_trans with x.
apply H4.
apply H3.
rewrite Rabs_left1 with (1 := Hf) in H2.
rewrite Rabs_left1 in H2.
now apply Ropp_le_cancel.
now apply Rnd_N_pt_neg with F x.
eapply Rnd_UP_pt_unicity ; eassumption.
(* . *)
split.
exact H1.
intros f2 Hxf2.
destruct H2 as [H2|H2].
assert (Hf := Rnd_N_pt_neg F HF x f Hx H1).
assert (Hf2 := Rnd_N_pt_neg F HF x f2 Hx Hxf2).
rewrite 2!Rabs_left1 ; trivial.
rewrite 2!Rabs_left1 in H2 ; trivial.
apply Ropp_le_contravar.
apply Ropp_le_cancel in H2.
destruct (Rnd_N_pt_DN_or_UP _ _ _ Hxf2) as [H3|H3].
apply H3.
apply H1.
apply H2.
apply Rle_trans with (1 := H2).
apply H3.
rewrite (H2 _ Hxf2).
apply Rle_refl.
Qed.

Theorem Rnd_NA_pt_unicity_prop :
  forall F : R -> Prop,
  F 0 ->
  Rnd_NG_pt_unicity_prop F (fun a b => (Rabs a <= Rabs b)%R).
Proof.
intros F HF x d u Hxd1 Hxd2 Hxu1 Hxu2 Hd Hu.
apply Rle_antisym.
apply Rle_trans with x.
apply Hxd1.
apply Hxu1.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
apply Hxu1.
apply Hxd1.
rewrite Rabs_pos_eq with (1 := Hx) in Hd.
rewrite Rabs_pos_eq in Hd.
exact Hd.
now apply Hxd1.
apply Hxd1.
apply Hxu1.
rewrite Rabs_left with (1 := Hx) in Hu.
rewrite Rabs_left1 in Hu.
now apply Ropp_le_cancel.
apply Hxu1.
apply HF.
now apply Rlt_le.
Qed.

Theorem Rnd_NA_pt_unicity :
  forall F : R -> Prop,
  F 0 ->
  forall x f1 f2 : R,
  Rnd_NA_pt F x f1 -> Rnd_NA_pt F x f2 ->
  f1 = f2.
Proof.
intros F HF x f1 f2 H1 H2.
apply (Rnd_NG_pt_unicity F _ (Rnd_NA_pt_unicity_prop F HF) x).
now apply -> Rnd_NA_NG_pt.
now apply -> Rnd_NA_NG_pt.
Qed.

Theorem Rnd_NA_N_pt :
  forall F : R -> Prop,
  F 0 ->
  forall x f : R,
  Rnd_N_pt F x f ->
  (Rabs x <= Rabs f)%R ->
  Rnd_NA_pt F x f.
Proof.
intros F HF x f Rxf Hxf.
split.
apply Rxf.
intros g Rxg.
destruct (Rabs_eq_Rabs (f - x) (g - x)) as [H|H].
apply Rle_antisym.
apply Rxf.
apply Rxg.
apply Rxg.
apply Rxf.
(* *)
replace g with f.
apply Rle_refl.
apply Rplus_eq_reg_r with (1 := H).
(* *)
assert (g = 2 * x - f)%R.
replace (2 * x - f)%R with (x - (f - x))%R by ring.
rewrite H.
ring.
destruct (Rle_lt_dec 0 x) as [Hx|Hx].
(* . *)
revert Hxf.
rewrite Rabs_pos_eq with (1 := Hx).
rewrite 2!Rabs_pos_eq ; try ( apply (Rnd_N_pt_pos F HF x) ; assumption ).
intros Hxf.
rewrite H0.
apply Rplus_le_reg_r with f.
ring_simplify.
apply Rmult_le_compat_l with (2 := Hxf).
now apply (Z2R_le 0 2).
(* . *)
revert Hxf.
apply Rlt_le in Hx.
rewrite Rabs_left1 with (1 := Hx).
rewrite 2!Rabs_left1 ; try ( apply (Rnd_N_pt_neg F HF x) ; assumption ).
intros Hxf.
rewrite H0.
apply Ropp_le_contravar.
apply Rplus_le_reg_r with f.
ring_simplify.
apply Rmult_le_compat_l.
now apply (Z2R_le 0 2).
now apply Ropp_le_cancel.
Qed.

Theorem Rnd_NA_unicity :
  forall (F : R -> Prop),
  F 0 ->
  forall rnd1 rnd2 : R -> R,
  Rnd_NA F rnd1 -> Rnd_NA F rnd2 ->
  forall x, rnd1 x = rnd2 x.
Proof.
intros F HF rnd1 rnd2 H1 H2 x.
now apply Rnd_NA_pt_unicity with F x.
Qed.

Theorem Rnd_NA_pt_monotone :
  forall F : R -> Prop,
  F 0 ->
  round_pred_monotone (Rnd_NA_pt F).
Proof.
intros F HF x y f g Hxf Hyg Hxy.
apply (Rnd_NG_pt_monotone F _ (Rnd_NA_pt_unicity_prop F HF) x y).
now apply -> Rnd_NA_NG_pt.
now apply -> Rnd_NA_NG_pt.
exact Hxy.
Qed.

Theorem Rnd_NA_pt_refl :
  forall F : R -> Prop,
  forall x : R, F x ->
  Rnd_NA_pt F x x.
Proof.
intros F x Hx.
split.
now apply Rnd_N_pt_refl.
intros f Hxf.
apply Req_le.
apply f_equal.
now apply Rnd_N_pt_idempotent with (1 := Hxf).
Qed.

Theorem Rnd_NA_pt_idempotent :
  forall F : R -> Prop,
  forall x f : R,
  Rnd_NA_pt F x f -> F x ->
  f = x.
Proof.
intros F x f (Hf,_) Hx.
now apply Rnd_N_pt_idempotent with F.
Qed.

Theorem round_pred_ge_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> 0 <= x -> 0 <= f.
Proof.
intros P HP HP0 x f Hxf Hx.
now apply (HP 0 x).
Qed.

Theorem round_pred_gt_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> 0 < f -> 0 < x.
Proof.
intros P HP HP0 x f Hxf Hf.
apply Rnot_le_lt.
intros Hx.
apply Rlt_not_le with (1 := Hf).
now apply (HP x 0).
Qed.

Theorem round_pred_le_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> x <= 0 -> f <= 0.
Proof.
intros P HP HP0 x f Hxf Hx.
now apply (HP x 0).
Qed.

Theorem round_pred_lt_0 :
  forall P : R -> R -> Prop,
  round_pred_monotone P ->
  P 0 0 ->
  forall x f, P x f -> f < 0 -> x < 0.
Proof.
intros P HP HP0 x f Hxf Hf.
apply Rnot_le_lt.
intros Hx.
apply Rlt_not_le with (1 := Hf).
now apply (HP 0 x).
Qed.

Theorem Rnd_DN_pt_equiv_format :
  forall F1 F2 : R -> Prop,
  forall a b : R,
  F1 a ->
  ( forall x, a <= x <= b -> (F1 x <-> F2 x) ) ->
  forall x f, a <= x <= b -> Rnd_DN_pt F1 x f -> Rnd_DN_pt F2 x f.
Proof.
intros F1 F2 a b Ha HF x f Hx (H1, (H2, H3)).
split.
apply -> HF.
exact H1.
split.
now apply H3.
now apply Rle_trans with (1 := H2).
split.
exact H2.
intros k Hk Hl.
destruct (Rlt_or_le k a) as [H|H].
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
now apply H3.
apply H3.
apply <- HF.
exact Hk.
split.
exact H.
now apply Rle_trans with (1 := Hl).
exact Hl.
Qed.

Theorem Rnd_UP_pt_equiv_format :
  forall F1 F2 : R -> Prop,
  forall a b : R,
  F1 b ->
  ( forall x, a <= x <= b -> (F1 x <-> F2 x) ) ->
  forall x f, a <= x <= b -> Rnd_UP_pt F1 x f -> Rnd_UP_pt F2 x f.
Proof.
intros F1 F2 a b Hb HF x f Hx (H1, (H2, H3)).
split.
apply -> HF.
exact H1.
split.
now apply Rle_trans with (2 := H2).
now apply H3.
split.
exact H2.
intros k Hk Hl.
destruct (Rle_or_lt k b) as [H|H].
apply H3.
apply <- HF.
exact Hk.
split.
now apply Rle_trans with (2 := Hl).
exact H.
exact Hl.
apply Rlt_le.
apply Rle_lt_trans with (2 := H).
now apply H3.
Qed.

(** ensures a real number can always be rounded *)
Inductive satisfies_any (F : R -> Prop) :=
  Satisfies_any :
    F 0 -> ( forall x : R, F x -> F (-x) ) ->
    round_pred_total (Rnd_DN_pt F) -> satisfies_any F.

Theorem satisfies_any_eq :
  forall F1 F2 : R -> Prop,
  ( forall x, F1 x <-> F2 x ) ->
  satisfies_any F1 ->
  satisfies_any F2.
Proof.
intros F1 F2 Heq (Hzero, Hsym, Hrnd).
split.
now apply -> Heq.
intros x Hx.
apply -> Heq.
apply Hsym.
now apply <- Heq.
intros x.
destruct (Hrnd x) as (f, (H1, (H2, H3))).
exists f.
split.
now apply -> Heq.
split.
exact H2.
intros g Hg Hgx.
apply H3.
now apply <- Heq.
exact Hgx.
Qed.

Theorem satisfies_any_imp_DN :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_DN_pt F).
Proof.
intros F (_,_,Hrnd).
split.
apply Hrnd.
apply Rnd_DN_pt_monotone.
Qed.

Theorem satisfies_any_imp_UP :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_UP_pt F).
Proof.
intros F Hany.
split.
intros x.
destruct (proj1 (satisfies_any_imp_DN F Hany) (-x)) as (f, Hf).
exists (-f).
rewrite <- (Ropp_involutive x).
apply Rnd_DN_UP_pt_sym.
apply Hany.
exact Hf.
apply Rnd_UP_pt_monotone.
Qed.

Theorem satisfies_any_imp_ZR :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_ZR_pt F).
Proof.
intros F Hany.
split.
intros x.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
(* positive *)
destruct (proj1 (satisfies_any_imp_DN F Hany) x) as (f, Hf).
exists f.
split.
now intros _.
intros Hx'.
(* zero *)
assert (x = 0).
now apply Rle_antisym.
rewrite H in Hf |- *.
clear H Hx Hx'.
rewrite Rnd_DN_pt_idempotent with (1 := Hf).
apply Rnd_UP_pt_refl.
apply Hany.
apply Hany.
(* negative *)
destruct (proj1 (satisfies_any_imp_UP F Hany) x) as (f, Hf).
exists f.
split.
intros Hx'.
elim (Rlt_irrefl 0).
now apply Rle_lt_trans with x.
now intros _.
(* . *)
apply Rnd_ZR_pt_monotone.
apply Hany.
Qed.

Definition NG_existence_prop (F : R -> Prop) (P : R -> R -> Prop) :=
  forall x d u, ~F x -> Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> P x u \/ P x d.

Theorem satisfies_any_imp_NG :
  forall (F : R -> Prop) (P : R -> R -> Prop),
  satisfies_any F ->
  NG_existence_prop F P ->
  round_pred_total (Rnd_NG_pt F P).
Proof.
intros F P Hany HP x.
destruct (proj1 (satisfies_any_imp_DN F Hany) x) as (d, Hd).
destruct (proj1 (satisfies_any_imp_UP F Hany) x) as (u, Hu).
destruct (total_order_T (Rabs (u - x)) (Rabs (d - x))) as [[H|H]|H].
(* |up(x) - x| < |dn(x) - x| *)
exists u.
split.
(* - . *)
split.
apply Hu.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
do 2 rewrite <- (Rabs_minus_sym x).
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
now apply Hd.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hd.
(* - . *)
right.
intros f Hf.
destruct (Rnd_N_pt_DN_or_UP_eq F x _ _ _ Hd Hu Hf) as [K|K] ; rewrite K.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hf.
apply Hu.
apply refl_equal.
(* |up(x) - x| = |dn(x) - x| *)
destruct (Req_dec x d) as [He|Hne].
(* - x = d = u *)
exists x.
split.
apply Rnd_N_pt_refl.
rewrite He.
apply Hd.
right.
intros.
apply Rnd_N_pt_idempotent with (1 := H0).
rewrite He.
apply Hd.
assert (Hf : ~F x).
intros Hf.
apply Hne.
apply sym_eq.
now apply Rnd_DN_pt_idempotent with (1 := Hd).
destruct (HP x _ _ Hf Hd Hu) as [H'|H'].
(* - u >> d *)
exists u.
split.
split.
apply Hu.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite H.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
now left.
(* - d >> u *)
exists d.
split.
split.
apply Hd.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
rewrite <- H.
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
now left.
(* |up(x) - x| > |dn(x) - x| *)
exists d.
split.
split.
apply Hd.
intros g Hg.
destruct (Rle_or_lt x g) as [Hxg|Hxg].
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
rewrite 2!Rabs_pos_eq.
apply Rplus_le_compat_r.
now apply Hu.
now apply Rle_0_minus.
apply Rle_0_minus.
apply Hu.
apply Rlt_le in Hxg.
rewrite 2!Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
now apply Hd.
now apply Rle_minus.
apply Rle_minus.
apply Hd.
right.
intros f Hf.
destruct (Rnd_N_pt_DN_or_UP_eq F x _ _ _ Hd Hu Hf) as [K|K] ; rewrite K.
apply refl_equal.
elim Rlt_not_le with (1 := H).
rewrite <- K.
apply Hf.
apply Hd.
Qed.

Theorem satisfies_any_imp_NA :
  forall F : R -> Prop,
  satisfies_any F ->
  round_pred (Rnd_NA_pt F).
Proof.
intros F Hany.
split.
assert (H : round_pred_total (Rnd_NG_pt F (fun a b => (Rabs a <= Rabs b)%R))).
apply satisfies_any_imp_NG.
apply Hany.
intros x d u Hf Hd Hu.
destruct (Rle_lt_dec 0 x) as [Hx|Hx].
left.
rewrite Rabs_pos_eq with (1 := Hx).
rewrite Rabs_pos_eq.
apply Hu.
apply Rle_trans with (1 := Hx).
apply Hu.
right.
rewrite Rabs_left with (1 := Hx).
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Hd.
apply Rlt_le in Hx.
apply Rle_trans with (2 := Hx).
apply Hd.
intros x.
destruct (H x) as (f, Hf).
exists f.
apply <- Rnd_NA_NG_pt.
apply Hf.
apply Hany.
apply Rnd_NA_pt_monotone.
apply Hany.
Qed.

End RND_prop.

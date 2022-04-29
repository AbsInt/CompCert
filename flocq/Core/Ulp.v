(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2009-2018 Sylvie Boldo
#<br />#
Copyright (C) 2009-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Unit in the Last Place: our definition using fexp and its properties, successor and predecessor *)

From Coq Require Import ZArith Reals Psatz.

Require Import Zaux Raux Defs Round_pred Generic_fmt Float_prop.

Section Fcore_ulp.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

(** Definition and basic properties about the minimal exponent, when it exists *)

Lemma Z_le_dec_aux: forall x y : Z, (x <= y)%Z \/ ~ (x <= y)%Z.
Proof.
intros.
destruct (Z_le_dec x y).
now left.
now right.
Qed.

(** [negligible_exp] is either none (as in FLX) or Some n such that n <= fexp n. *)
Definition negligible_exp: option Z :=
  match (LPO_Z _ (fun z => Z_le_dec_aux z (fexp z))) with
   | inleft N => Some (proj1_sig N)
   | inright _ => None
 end.


Inductive negligible_exp_prop: option Z -> Prop :=
  | negligible_None: (forall n, (fexp n < n)%Z) -> negligible_exp_prop None
  | negligible_Some: forall n, (n <= fexp n)%Z -> negligible_exp_prop (Some n).


Lemma negligible_exp_spec: negligible_exp_prop negligible_exp.
Proof.
unfold negligible_exp; destruct LPO_Z as [(n,Hn)|Hn].
now apply negligible_Some.
apply negligible_None.
intros n; specialize (Hn n); lia.
Qed.

Lemma negligible_exp_spec': (negligible_exp = None /\ forall n, (fexp n < n)%Z)
           \/ exists n, (negligible_exp = Some n /\ (n <= fexp n)%Z).
Proof.
unfold negligible_exp; destruct LPO_Z as [(n,Hn)|Hn].
right; simpl; exists n; now split.
left; split; trivial.
intros n; specialize (Hn n); lia.
Qed.

Context { valid_exp : Valid_exp fexp }.

Lemma fexp_negligible_exp_eq: forall n m, (n <= fexp n)%Z -> (m <= fexp m)%Z -> fexp n = fexp m.
Proof.
intros n m Hn Hm.
case (Zle_or_lt n m); intros H.
apply valid_exp; lia.
apply sym_eq, valid_exp; lia.
Qed.


(** Definition and basic properties about the ulp *)
(** Now includes a nice ulp(0): ulp(0) is now 0 when there is no minimal
   exponent, such as in FLX, and beta^(fexp n) when there is a n such
   that n <= fexp n. For instance, the value of ulp(O) is then
   beta^emin in FIX and FLT. The main lemma to use is ulp_neq_0 that
   is equivalent to the previous "unfold ulp" provided the value is
   not zero. *)

Definition ulp x := match Req_bool x 0 with
  | true   => match negligible_exp with
            | Some n => bpow (fexp n)
            | None => 0%R
            end
  | false  => bpow (cexp beta fexp x)
 end.

Lemma ulp_neq_0 :
  forall x, x <> 0%R ->
  ulp x = bpow (cexp beta fexp x).
Proof.
intros  x Hx.
unfold ulp; case (Req_bool_spec x); trivial.
intros H; now contradict H.
Qed.

Notation F := (generic_format beta fexp).

Theorem ulp_opp :
  forall x, ulp (- x) = ulp x.
Proof.
intros x.
unfold ulp.
case Req_bool_spec; intros H1.
rewrite Req_bool_true; trivial.
rewrite <- (Ropp_involutive x), H1; ring.
rewrite Req_bool_false.
now rewrite cexp_opp.
intros H2; apply H1; rewrite H2; ring.
Qed.

Theorem ulp_abs :
  forall x, ulp (Rabs x) = ulp x.
Proof.
intros x.
unfold ulp; case (Req_bool_spec x 0); intros H1.
rewrite Req_bool_true; trivial.
now rewrite H1, Rabs_R0.
rewrite Req_bool_false.
now rewrite cexp_abs.
now apply Rabs_no_R0.
Qed.

Theorem ulp_ge_0:
  forall x, (0 <= ulp x)%R.
Proof.
intros x; unfold ulp; case Req_bool_spec; intros.
case negligible_exp; intros.
apply bpow_ge_0.
apply Rle_refl.
apply bpow_ge_0.
Qed.


Theorem ulp_le_id:
  forall x,
    (0 < x)%R ->
    F x ->
    (ulp x <= x)%R.
Proof.
intros x Zx Fx.
rewrite <- (Rmult_1_l (ulp x)).
pattern x at 2; rewrite Fx.
rewrite ulp_neq_0.
2: now apply Rgt_not_eq.
unfold F2R; simpl.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le, (Zlt_le_succ 0).
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
Qed.

Theorem ulp_le_abs:
  forall x,
    (x <> 0)%R ->
    F x ->
    (ulp x <= Rabs x)%R.
Proof.
intros x Zx Fx.
rewrite <- ulp_abs.
apply ulp_le_id.
now apply Rabs_pos_lt.
now apply generic_format_abs.
Qed.

Theorem round_UP_DN_ulp :
  forall x, ~ F x ->
  round beta fexp Zceil x = (round beta fexp Zfloor x + ulp x)%R.
Proof.
intros x Fx.
rewrite ulp_neq_0.
unfold round. simpl.
unfold F2R. simpl.
rewrite Zceil_floor_neq.
rewrite plus_IZR. simpl.
ring.
intros H.
apply Fx.
unfold generic_format, F2R. simpl.
rewrite <- H.
rewrite Ztrunc_IZR.
rewrite H.
now rewrite scaled_mantissa_mult_bpow.
intros V; apply Fx.
rewrite V.
apply generic_format_0.
Qed.

Theorem ulp_canonical :
  forall m e,
  m <> 0%Z ->
  canonical beta fexp (Float beta m e) ->
  ulp (F2R (Float beta m e)) = bpow e.
Proof.
intros m e Hm Hc.
rewrite ulp_neq_0 by now apply F2R_neq_0.
apply f_equal.
now apply sym_eq.
Qed.

Theorem ulp_bpow :
  forall e, ulp (bpow e) = bpow (fexp (e + 1)).
Proof.
intros e.
rewrite ulp_neq_0.
apply f_equal.
apply cexp_fexp.
rewrite Rabs_pos_eq.
split.
ring_simplify (e + 1 - 1)%Z.
apply Rle_refl.
apply bpow_lt.
apply Zlt_succ.
apply bpow_ge_0.
apply Rgt_not_eq, Rlt_gt, bpow_gt_0.
Qed.

Lemma generic_format_ulp_0 :
  F (ulp 0).
Proof.
unfold ulp.
rewrite Req_bool_true; trivial.
case negligible_exp_spec.
intros _; apply generic_format_0.
intros n H1.
apply generic_format_bpow.
now apply valid_exp.
Qed.

Lemma generic_format_bpow_ge_ulp_0 :
  forall e, (ulp 0 <= bpow e)%R ->
  F (bpow e).
Proof.
intros e; unfold ulp.
rewrite Req_bool_true; trivial.
case negligible_exp_spec.
intros H1 _.
apply generic_format_bpow.
specialize (H1 (e+1)%Z); lia.
intros n H1 H2.
apply generic_format_bpow.
case (Zle_or_lt (e+1) (fexp (e+1))); intros H4.
absurd (e+1 <= e)%Z.
lia.
apply Z.le_trans with (1:=H4).
replace (fexp (e+1)) with (fexp n).
now apply le_bpow with beta.
now apply fexp_negligible_exp_eq.
lia.
Qed.

(** The three following properties are equivalent:
      [Exp_not_FTZ] ;  forall x, F (ulp x) ; forall x, ulp 0 <= ulp x *)

Lemma generic_format_ulp :
  Exp_not_FTZ fexp ->
  forall x, F (ulp x).
Proof.
unfold Exp_not_FTZ; intros H x.
case (Req_dec x 0); intros Hx.
rewrite Hx; apply generic_format_ulp_0.
rewrite (ulp_neq_0 _ Hx).
apply generic_format_bpow.
apply H.
Qed.

Lemma not_FTZ_generic_format_ulp :
  (forall x,  F (ulp x)) ->
  Exp_not_FTZ fexp.
Proof.
intros H e.
specialize (H (bpow (e-1))).
rewrite ulp_neq_0 in H.
2: apply Rgt_not_eq, bpow_gt_0.
unfold cexp in H.
rewrite mag_bpow in H.
apply generic_format_bpow_inv' in H.
now replace (e-1+1)%Z with e in H by ring.
Qed.


Lemma ulp_ge_ulp_0 :
  Exp_not_FTZ fexp ->
  forall x, (ulp 0 <= ulp x)%R.
Proof.
unfold Exp_not_FTZ; intros H x.
case (Req_dec x 0); intros Hx.
rewrite Hx; now right.
unfold ulp at 1.
rewrite Req_bool_true; trivial.
case negligible_exp_spec'.
intros (H1,H2); rewrite H1; apply ulp_ge_0.
intros (n,(H1,H2)); rewrite H1.
rewrite ulp_neq_0; trivial.
apply bpow_le; unfold cexp.
generalize (mag beta x); intros l.
case (Zle_or_lt l (fexp l)); intros Hl.
rewrite (fexp_negligible_exp_eq n l); trivial; apply Z.le_refl.
case (Zle_or_lt (fexp n) (fexp l)); trivial; intros K.
absurd (fexp n <= fexp l)%Z.
lia.
apply Z.le_trans with (2:= H _).
apply Zeq_le, sym_eq, valid_exp; trivial.
lia.
Qed.

Lemma not_FTZ_ulp_ge_ulp_0:
  (forall x, (ulp 0 <= ulp x)%R) ->
  Exp_not_FTZ fexp.
Proof.
intros H e.
apply generic_format_bpow_inv' with beta.
apply generic_format_bpow_ge_ulp_0.
replace e with ((e-1)+1)%Z by ring.
rewrite <- ulp_bpow.
apply H.
Qed.

Lemma ulp_le_pos :
  forall { Hm : Monotone_exp fexp },
  forall x y: R,
  (0 <= x)%R -> (x <= y)%R ->
  (ulp x <= ulp y)%R.
Proof with auto with typeclass_instances.
intros Hm x y Hx Hxy.
destruct Hx as [Hx|Hx].
rewrite ulp_neq_0.
rewrite ulp_neq_0.
apply bpow_le.
apply Hm.
now apply mag_le.
apply Rgt_not_eq, Rlt_gt.
now apply Rlt_le_trans with (1:=Hx).
now apply Rgt_not_eq.
rewrite <- Hx.
apply ulp_ge_ulp_0.
apply monotone_exp_not_FTZ...
Qed.

Theorem ulp_le :
  forall { Hm : Monotone_exp fexp },
  forall x y: R,
  (Rabs x <= Rabs y)%R ->
  (ulp x <= ulp y)%R.
Proof.
intros Hm x y Hxy.
rewrite <- ulp_abs.
rewrite <- (ulp_abs y).
apply ulp_le_pos; trivial.
apply Rabs_pos.
Qed.

(** Properties when there is no minimal exponent *)
Theorem eq_0_round_0_negligible_exp :
   negligible_exp = None -> forall rnd {Vr: Valid_rnd rnd} x,
     round beta fexp rnd x = 0%R -> x = 0%R.
Proof.
intros H rnd Vr x Hx.
case (Req_dec x 0); try easy; intros Hx2.
absurd (Rabs (round beta fexp rnd x) = 0%R).
2: rewrite Hx, Rabs_R0; easy.
apply Rgt_not_eq.
apply Rlt_le_trans with (bpow (mag beta x - 1)).
apply bpow_gt_0.
apply abs_round_ge_generic; try assumption.
apply generic_format_bpow.
case negligible_exp_spec'; [intros (K1,K2)|idtac].
ring_simplify (mag beta x-1+1)%Z.
specialize (K2 (mag beta x)); now auto with zarith.
intros (n,(Hn1,Hn2)).
rewrite Hn1 in H; discriminate.
now apply bpow_mag_le.
Qed.

(** Definition and properties of pred and succ *)

Definition pred_pos x :=
  if Req_bool x (bpow (mag beta x - 1)) then
    (x - bpow (fexp (mag beta x - 1)))%R
  else
    (x - ulp x)%R.

Definition succ x :=
  if (Rle_bool 0 x) then
    (x+ulp x)%R
  else
    (- pred_pos (-x))%R.

Definition pred x := (- succ (-x))%R.

Theorem pred_eq_pos :
  forall x, (0 <= x)%R ->
  pred x = pred_pos x.
Proof.
intros x Hx; unfold pred, succ.
case Rle_bool_spec; intros Hx'.
assert (K:(x = 0)%R).
apply Rle_antisym; try assumption.
apply Ropp_le_cancel.
now rewrite Ropp_0.
rewrite K; unfold pred_pos.
rewrite Req_bool_false.
2: apply Rlt_not_eq, bpow_gt_0.
rewrite Ropp_0; ring.
now rewrite 2!Ropp_involutive.
Qed.

Theorem succ_eq_pos :
  forall x, (0 <= x)%R ->
  succ x = (x + ulp x)%R.
Proof.
intros x Hx; unfold succ.
now rewrite Rle_bool_true.
Qed.

Theorem succ_opp :
  forall x, succ (-x) = (- pred x)%R.
Proof.
intros x.
now apply sym_eq, Ropp_involutive.
Qed.

Theorem pred_opp :
  forall x, pred (-x) = (- succ x)%R.
Proof.
intros x.
unfold pred.
now rewrite Ropp_involutive.
Qed.

Theorem pred_bpow :
  forall e, pred (bpow e) = (bpow e - bpow (fexp e))%R.
Proof.
intros e.
rewrite pred_eq_pos by apply bpow_ge_0.
unfold pred_pos.
rewrite mag_bpow.
replace (e + 1 - 1)%Z with e by ring.
now rewrite Req_bool_true.
Qed.

(** pred and succ are in the format *)

(* cannont be x <> ulp 0, due to the counter-example 1-bit FP format fexp: e -> e-1 *)
(* was pred_ge_bpow *)
Theorem id_m_ulp_ge_bpow :
  forall x e,  F x ->
  x <> ulp x ->
  (bpow e < x)%R ->
  (bpow e <= x - ulp x)%R.
Proof.
intros x e Fx Hx' Hx.
(* *)
assert (1 <= Ztrunc (scaled_mantissa beta fexp x))%Z.
assert (0 <  Ztrunc (scaled_mantissa beta fexp x))%Z.
apply gt_0_F2R with beta (cexp beta fexp x).
rewrite <- Fx.
apply Rle_lt_trans with (2:=Hx).
apply bpow_ge_0.
lia.
case (Zle_lt_or_eq _ _ H); intros Hm.
(* *)
pattern x at 1 ; rewrite Fx.
rewrite ulp_neq_0.
unfold F2R. simpl.
pattern (bpow (cexp beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_minus_distr_r.
rewrite <- minus_IZR.
apply bpow_le_F2R_m1.
easy.
now rewrite <- Fx.
apply Rgt_not_eq, Rlt_gt.
apply Rlt_trans with (2:=Hx), bpow_gt_0.
(* *)
contradict Hx'.
pattern x at 1; rewrite Fx.
rewrite  <- Hm.
rewrite ulp_neq_0.
unfold F2R; simpl.
now rewrite Rmult_1_l.
apply Rgt_not_eq, Rlt_gt.
apply Rlt_trans with (2:=Hx), bpow_gt_0.
Qed.

(* was succ_le_bpow *)
Theorem id_p_ulp_le_bpow :
  forall x e, (0 < x)%R -> F x ->
  (x < bpow e)%R ->
  (x + ulp x <= bpow e)%R.
Proof.
intros x e Zx Fx Hx.
pattern x at 1 ; rewrite Fx.
rewrite ulp_neq_0.
unfold F2R. simpl.
pattern (bpow (cexp beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
rewrite <- plus_IZR.
apply F2R_p1_le_bpow.
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
now rewrite <- Fx.
now apply Rgt_not_eq.
Qed.

Lemma generic_format_pred_aux1:
  forall x, (0 < x)%R -> F x ->
  x <> bpow (mag beta x - 1) ->
  F (x - ulp x).
Proof.
intros x Zx Fx Hx.
destruct (mag beta x) as (ex, Ex).
simpl in Hx.
specialize (Ex (Rgt_not_eq _ _ Zx)).
assert (Ex' : (bpow (ex - 1) < x < bpow ex)%R).
rewrite Rabs_pos_eq in Ex.
destruct Ex as (H,H'); destruct H; split; trivial.
contradict Hx; easy.
now apply Rlt_le.
unfold generic_format, scaled_mantissa, cexp.
rewrite mag_unique with beta (x - ulp x)%R ex.
pattern x at 1 3 ; rewrite Fx.
rewrite ulp_neq_0.
unfold scaled_mantissa.
rewrite cexp_fexp with (1 := Ex).
unfold F2R. simpl.
rewrite Rmult_minus_distr_r.
rewrite Rmult_assoc.
rewrite <- bpow_plus, Zplus_opp_r, Rmult_1_r.
change (bpow 0) with 1%R.
rewrite <- minus_IZR.
rewrite Ztrunc_IZR.
rewrite minus_IZR.
rewrite Rmult_minus_distr_r.
now rewrite Rmult_1_l.
now apply Rgt_not_eq.
rewrite Rabs_pos_eq.
split.
apply id_m_ulp_ge_bpow; trivial.
rewrite ulp_neq_0.
intro H.
assert (ex-1 < cexp beta fexp x  < ex)%Z.
split ; apply (lt_bpow beta) ; rewrite <- H ; easy.
clear -H0. lia.
now apply Rgt_not_eq.
apply Ex'.
apply Rle_lt_trans with (2 := proj2 Ex').
pattern x at 3 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
rewrite <-Ropp_0.
apply Ropp_le_contravar.
apply ulp_ge_0.
apply Rle_0_minus.
pattern x at 2; rewrite Fx.
rewrite ulp_neq_0.
unfold F2R; simpl.
pattern (bpow (cexp beta fexp x)) at 1; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le.
assert (0 <  Ztrunc (scaled_mantissa beta fexp x))%Z.
apply gt_0_F2R with beta (cexp beta fexp x).
rewrite <- Fx.
apply Rle_lt_trans with (2:=proj1 Ex').
apply bpow_ge_0.
lia.
now apply Rgt_not_eq.
Qed.

Lemma generic_format_pred_aux2 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x = bpow (e - 1) ->
  F (x - bpow (fexp (e - 1))).
Proof.
intros x Zx Fx e Hx.
pose (f:=(x - bpow (fexp (e - 1)))%R).
fold f.
assert (He:(fexp (e-1) <= e-1)%Z).
apply generic_format_bpow_inv with beta; trivial.
rewrite <- Hx; assumption.
case (Zle_lt_or_eq _ _ He); clear He; intros He.
assert (f = F2R (Float beta (Zpower beta (e-1-(fexp (e-1))) -1) (fexp (e-1))))%R.
unfold f; rewrite Hx.
unfold F2R; simpl.
rewrite minus_IZR, IZR_Zpower.
rewrite Rmult_minus_distr_r, Rmult_1_l.
rewrite <- bpow_plus.
now replace (e - 1 - fexp (e - 1) + fexp (e - 1))%Z with (e-1)%Z by ring.
lia.
rewrite H.
apply generic_format_F2R.
intros _.
apply Zeq_le.
apply cexp_fexp.
rewrite <- H.
unfold f; rewrite Hx.
rewrite Rabs_right.
split.
apply Rplus_le_reg_l with (bpow (fexp (e-1))).
ring_simplify.
apply Rle_trans with (bpow (e - 2) + bpow (e - 2))%R.
apply Rplus_le_compat ; apply bpow_le ; lia.
apply Rle_trans with (2*bpow (e - 2))%R;[right; ring|idtac].
apply Rle_trans with (bpow 1*bpow (e - 2))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace (bpow 1) with (IZR beta).
apply IZR_le.
apply <- Zle_is_le_bool.
now destruct beta.
simpl.
unfold Zpower_pos; simpl.
now rewrite Zmult_1_r.
rewrite <- bpow_plus.
replace (1+(e-2))%Z with (e-1)%Z by ring.
now right.
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
apply Rle_ge; apply Rle_0_minus.
apply bpow_le.
lia.
replace f with 0%R.
apply generic_format_0.
unfold f.
rewrite Hx, He.
ring.
Qed.

Lemma generic_format_succ_aux1 :
  forall x, (0 < x)%R -> F x ->
  F (x + ulp x).
Proof.
intros x Zx Fx.
destruct (mag beta x) as (ex, Ex).
specialize (Ex (Rgt_not_eq _ _ Zx)).
assert (Ex' := Ex).
rewrite Rabs_pos_eq in Ex'.
destruct (id_p_ulp_le_bpow x ex) ; try easy.
unfold generic_format, scaled_mantissa, cexp.
rewrite mag_unique with beta (x + ulp x)%R ex.
pattern x at 1 3 ; rewrite Fx.
rewrite ulp_neq_0.
unfold scaled_mantissa.
rewrite cexp_fexp with (1 := Ex).
unfold F2R. simpl.
rewrite Rmult_plus_distr_r.
rewrite Rmult_assoc.
rewrite <- bpow_plus, Zplus_opp_r, Rmult_1_r.
change (bpow 0) with 1%R.
rewrite <- plus_IZR.
rewrite Ztrunc_IZR.
rewrite plus_IZR.
rewrite Rmult_plus_distr_r.
now rewrite Rmult_1_l.
now apply Rgt_not_eq.
rewrite Rabs_pos_eq.
split.
apply Rle_trans with (1 := proj1 Ex').
pattern x at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
apply ulp_ge_0.
exact H.
apply Rplus_le_le_0_compat.
now apply Rlt_le.
apply ulp_ge_0.
rewrite H.
apply generic_format_bpow.
apply valid_exp.
destruct (Zle_or_lt ex (fexp ex)) ; trivial.
elim Rlt_not_le with (1 := Zx).
rewrite Fx.
replace (Ztrunc (scaled_mantissa beta fexp x)) with Z0.
rewrite F2R_0.
apply Rle_refl.
unfold scaled_mantissa.
rewrite cexp_fexp with (1 := Ex).
destruct (mantissa_small_pos beta fexp x ex) ; trivial.
rewrite Ztrunc_floor.
apply sym_eq.
apply Zfloor_imp.
split.
now apply Rlt_le.
exact H2.
now apply Rlt_le.
now apply Rlt_le.
Qed.

Lemma generic_format_pred_pos :
  forall x, F x -> (0 < x)%R ->
  F (pred_pos x).
Proof.
intros x Fx Zx.
unfold pred_pos; case Req_bool_spec; intros H.
now apply generic_format_pred_aux2.
now apply generic_format_pred_aux1.
Qed.

Theorem generic_format_succ :
  forall x, F x ->
  F (succ x).
Proof.
intros x Fx.
unfold succ; case Rle_bool_spec; intros Zx.
destruct Zx as [Zx|Zx].
now apply generic_format_succ_aux1.
rewrite <- Zx, Rplus_0_l.
apply generic_format_ulp_0.
apply generic_format_opp.
apply generic_format_pred_pos.
now apply generic_format_opp.
now apply Ropp_0_gt_lt_contravar.
Qed.

Theorem generic_format_pred :
  forall x, F x ->
  F (pred x).
Proof.
intros x Fx.
unfold pred.
apply generic_format_opp.
apply generic_format_succ.
now apply generic_format_opp.
Qed.

Lemma pred_pos_lt_id :
  forall x, (x <> 0)%R ->
  (pred_pos x < x)%R.
Proof.
intros x Zx.
unfold pred_pos.
case Req_bool_spec; intros H.
(* *)
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
(* *)
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
rewrite ulp_neq_0; trivial.
apply bpow_gt_0.
Qed.

Theorem succ_gt_id :
  forall x, (x <> 0)%R ->
  (x < succ x)%R.
Proof.
intros x Zx; unfold succ.
case Rle_bool_spec; intros Hx.
pattern x at 1; rewrite <- (Rplus_0_r x).
apply Rplus_lt_compat_l.
rewrite ulp_neq_0; trivial.
apply bpow_gt_0.
pattern x at 1; rewrite <- (Ropp_involutive x).
apply Ropp_lt_contravar.
apply pred_pos_lt_id.
auto with real.
Qed.


Theorem pred_lt_id :
  forall x,  (x <> 0)%R ->
  (pred x < x)%R.
Proof.
intros x Zx; unfold pred.
pattern x at 2; rewrite <- (Ropp_involutive x).
apply Ropp_lt_contravar.
apply succ_gt_id.
auto with real.
Qed.

Theorem succ_ge_id :
  forall x, (x <= succ x)%R.
Proof.
intros x; case (Req_dec x 0).
intros V; rewrite V.
unfold succ; rewrite Rle_bool_true;[idtac|now right].
rewrite Rplus_0_l; apply ulp_ge_0.
intros; left; now apply succ_gt_id.
Qed.


Theorem pred_le_id :
  forall x, (pred x <= x)%R.
Proof.
intros x; unfold pred.
pattern x at 2; rewrite <- (Ropp_involutive x).
apply Ropp_le_contravar.
apply succ_ge_id.
Qed.


Lemma pred_pos_ge_0 :
  forall x,
  (0 < x)%R -> F x -> (0 <= pred_pos x)%R.
Proof.
intros x Zx Fx.
unfold pred_pos.
case Req_bool_spec; intros H.
(* *)
apply Rle_0_minus.
rewrite H.
apply bpow_le.
destruct (mag beta x) as (ex,Ex) ; simpl.
rewrite mag_bpow.
ring_simplify (ex - 1 + 1 - 1)%Z.
apply generic_format_bpow_inv with beta; trivial.
simpl in H.
rewrite <- H; assumption.
apply Rle_0_minus.
now apply ulp_le_id.
Qed.

Theorem pred_ge_0 :
  forall x,
  (0 < x)%R -> F x -> (0 <= pred x)%R.
Proof.
intros x Zx Fx.
rewrite pred_eq_pos.
now apply pred_pos_ge_0.
now left.
Qed.


Lemma pred_pos_plus_ulp_aux1 :
  forall x, (0 < x)%R -> F x ->
  x <> bpow (mag beta x - 1) ->
  ((x - ulp x) + ulp (x-ulp x) = x)%R.
Proof.
intros x Zx Fx Hx.
replace (ulp (x - ulp x)) with (ulp x).
ring.
assert (H : x <> 0%R) by now apply Rgt_not_eq.
assert (H' : x <> bpow (cexp beta fexp x)).
unfold cexp ; intros M.
case_eq (mag beta x); intros ex Hex T.
assert (Lex:(mag_val beta x (mag beta x) = ex)%Z).
rewrite T; reflexivity.
rewrite Lex in *.
clear T; simpl in *; specialize (Hex H).
rewrite Rabs_pos_eq in Hex by now apply Rlt_le.
assert (ex - 1 < fexp ex < ex)%Z.
  split ; apply (lt_bpow beta) ; rewrite <- M by easy.
  lra.
  apply Hex.
lia.
rewrite 2!ulp_neq_0 by lra.
apply f_equal.
unfold cexp ; apply f_equal.
case_eq (mag beta x); intros ex Hex T.
assert (Lex:(mag_val beta x (mag beta x) = ex)%Z).
rewrite T; reflexivity.
rewrite Lex in *; simpl in *; clear T.
specialize (Hex H).
apply sym_eq, mag_unique.
rewrite Rabs_right.
rewrite Rabs_right in Hex.
2: apply Rle_ge; apply Rlt_le; easy.
split.
destruct Hex as ([H1|H1],H2).
apply Rle_trans with (x-ulp x)%R.
apply id_m_ulp_ge_bpow; trivial.
rewrite ulp_neq_0; trivial.
rewrite ulp_neq_0; trivial.
right; unfold cexp; now rewrite Lex.
lra.
apply Rle_lt_trans with (2:=proj2 Hex).
rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply bpow_ge_0.
apply Rle_ge.
apply Rle_0_minus.
rewrite Fx.
unfold F2R, cexp; simpl.
rewrite Lex.
pattern (bpow (fexp ex)) at 1; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply IZR_le, (Zlt_le_succ 0).
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
Qed.

Lemma pred_pos_plus_ulp_aux2 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x =  bpow (e - 1) ->
  (x - bpow (fexp (e-1)) <> 0)%R ->
  ((x - bpow (fexp (e-1))) + ulp (x - bpow (fexp (e-1))) = x)%R.
Proof.
intros x Zx Fx e Hxe Zp.
replace (ulp (x - bpow (fexp (e - 1)))) with (bpow (fexp (e - 1))).
ring.
assert (He:(fexp (e-1) <= e-1)%Z).
apply generic_format_bpow_inv with beta; trivial.
rewrite <- Hxe; assumption.
case (Zle_lt_or_eq _ _ He); clear He; intros He.
(* *)
rewrite ulp_neq_0; trivial.
apply f_equal.
unfold cexp ; apply f_equal.
apply sym_eq.
apply mag_unique.
rewrite Rabs_right.
split.
apply Rplus_le_reg_l with (bpow (fexp (e-1))).
ring_simplify.
apply Rle_trans with (bpow (e - 2) + bpow (e - 2))%R.
apply Rplus_le_compat; apply bpow_le; lia.
apply Rle_trans with (2*bpow (e - 2))%R;[right; ring|idtac].
apply Rle_trans with (bpow 1*bpow (e - 2))%R.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace (bpow 1) with (IZR beta).
apply IZR_le.
apply <- Zle_is_le_bool.
now destruct beta.
simpl.
unfold Zpower_pos; simpl.
now rewrite Zmult_1_r.
rewrite <- bpow_plus.
replace (1+(e-2))%Z with (e-1)%Z by ring.
now right.
rewrite <- Rplus_0_r, Hxe.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply bpow_gt_0.
apply Rle_ge; apply Rle_0_minus.
rewrite Hxe.
apply bpow_le.
lia.
(* *)
contradict Zp.
rewrite Hxe, He; ring.
Qed.

Lemma pred_pos_plus_ulp_aux3 :
  forall x, (0 < x)%R -> F x ->
  let e := mag_val beta x (mag beta x) in
  x =  bpow (e - 1) ->
  (x - bpow (fexp (e-1)) = 0)%R ->
  (ulp 0 = x)%R.
Proof.
intros x Hx Fx e H1 H2.
assert (H3:(x = bpow (fexp (e - 1)))).
now apply Rminus_diag_uniq.
assert (H4: (fexp (e-1) = e-1)%Z).
apply bpow_inj with beta.
now rewrite <- H1.
unfold ulp; rewrite Req_bool_true; trivial.
case negligible_exp_spec.
intros K.
specialize (K (e-1)%Z).
contradict K; lia.
intros n Hn.
rewrite H3; apply f_equal.
case (Zle_or_lt n (e-1)); intros H6.
apply valid_exp; lia.
apply sym_eq, valid_exp; lia.
Qed.

(** The following one is false for x = 0 in FTZ *)

Lemma pred_pos_plus_ulp :
  forall x, (0 < x)%R -> F x ->
  (pred_pos x + ulp (pred_pos x) = x)%R.
Proof.
intros x Zx Fx.
unfold pred_pos.
case Req_bool_spec; intros H.
case (Req_EM_T (x - bpow (fexp (mag_val beta x (mag beta x) -1))) 0); intros H1.
rewrite H1, Rplus_0_l.
now apply pred_pos_plus_ulp_aux3.
now apply pred_pos_plus_ulp_aux2.
now apply pred_pos_plus_ulp_aux1.
Qed.

Theorem pred_plus_ulp :
  forall x, (0 < x)%R -> F x ->
  (pred x + ulp (pred x))%R = x.
Proof.
intros x Hx Fx.
rewrite pred_eq_pos.
now apply pred_pos_plus_ulp.
now apply Rlt_le.
Qed.

(** Rounding x + small epsilon *)

Theorem mag_plus_eps :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  mag beta (x + eps) = mag beta x :> Z.
Proof.
intros x Zx Fx eps Heps.
destruct (mag beta x) as (ex, He).
simpl.
specialize (He (Rgt_not_eq _ _ Zx)).
apply mag_unique.
rewrite Rabs_pos_eq.
rewrite Rabs_pos_eq in He.
split.
apply Rle_trans with (1 := proj1 He).
pattern x at 1 ; rewrite <- Rplus_0_r.
now apply Rplus_le_compat_l.
apply Rlt_le_trans with (x + ulp x)%R.
now apply Rplus_lt_compat_l.
pattern x at 1 ; rewrite Fx.
rewrite ulp_neq_0.
unfold F2R. simpl.
pattern (bpow (cexp beta fexp x)) at 2 ; rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
rewrite <- plus_IZR.
apply F2R_p1_le_bpow.
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
now rewrite <- Fx.
now apply Rgt_not_eq.
now apply Rlt_le.
apply Rplus_le_le_0_compat.
now apply Rlt_le.
apply Heps.
Qed.

Theorem round_DN_plus_eps_pos :
  forall x, (0 <= x)%R -> F x ->
  forall eps, (0 <= eps < ulp x)%R ->
  round beta fexp Zfloor (x + eps) = x.
Proof.
intros x Zx Fx eps Heps.
destruct Zx as [Zx|Zx].
(* . 0 < x *)
pattern x at 2 ; rewrite Fx.
unfold round.
unfold scaled_mantissa. simpl.
unfold cexp at 1 2.
rewrite mag_plus_eps ; trivial.
apply (f_equal (fun m => F2R (Float beta m _))).
rewrite Ztrunc_floor.
apply Zfloor_imp.
split.
apply (Rle_trans _ _ _ (Zfloor_lb _)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
pattern x at 1 ; rewrite <- Rplus_0_r.
now apply Rplus_le_compat_l.
apply Rlt_le_trans with ((x + ulp x) * bpow (- cexp beta fexp x))%R.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
now apply Rplus_lt_compat_l.
rewrite Rmult_plus_distr_r.
rewrite plus_IZR.
apply Rplus_le_compat.
pattern x at 1 3 ; rewrite Fx.
unfold F2R. simpl.
rewrite Rmult_assoc.
rewrite <- bpow_plus.
rewrite Zplus_opp_r.
rewrite Rmult_1_r.
rewrite Zfloor_IZR.
apply Rle_refl.
rewrite ulp_neq_0.
2: now apply Rgt_not_eq.
rewrite <- bpow_plus.
rewrite Zplus_opp_r.
apply Rle_refl.
apply Rmult_le_pos.
now apply Rlt_le.
apply bpow_ge_0.
(* . x=0 *)
rewrite <- Zx, Rplus_0_l; rewrite <- Zx in Heps.
case (proj1 Heps); intros P.
unfold round, scaled_mantissa, cexp.
revert Heps; unfold ulp.
rewrite Req_bool_true; trivial.
case negligible_exp_spec.
intros _ (H1,H2).
exfalso ; lra.
intros n Hn H.
assert (fexp (mag beta eps) = fexp n).
apply valid_exp; try assumption.
cut (mag beta eps-1 < fexp n)%Z. lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (2:=proj2 H).
destruct (mag beta eps) as (e,He).
simpl; rewrite Rabs_pos_eq in He.
now apply He, Rgt_not_eq.
now left.
replace (Zfloor (eps * bpow (- fexp (mag beta eps)))) with 0%Z.
unfold F2R; simpl; ring.
apply sym_eq, Zfloor_imp.
split.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
apply Rmult_lt_reg_r with (bpow (fexp n)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus.
rewrite H0; ring_simplify (-fexp n + fexp n)%Z.
simpl; rewrite Rmult_1_l, Rmult_1_r.
apply H.
rewrite <- P, round_0; trivial.
apply valid_rnd_DN.
Qed.

Theorem round_UP_plus_eps_pos :
  forall x, (0 <= x)%R -> F x ->
  forall eps, (0 < eps <= ulp x)%R ->
  round beta fexp Zceil (x + eps) = (x + ulp x)%R.
Proof with auto with typeclass_instances.
intros x Zx Fx eps.
case Zx; intros Zx1.
(* . 0 < x *)
intros (Heps1,[Heps2|Heps2]).
assert (Heps: (0 <= eps < ulp x)%R).
split.
now apply Rlt_le.
exact Heps2.
assert (Hd := round_DN_plus_eps_pos x Zx Fx eps Heps).
rewrite round_UP_DN_ulp.
rewrite Hd.
rewrite 2!ulp_neq_0.
unfold cexp.
now rewrite mag_plus_eps.
now apply Rgt_not_eq.
now apply Rgt_not_eq, Rplus_lt_0_compat.
intros Fs.
rewrite round_generic in Hd...
apply Rgt_not_eq with (2 := Hd).
pattern x at 2 ; rewrite <- Rplus_0_r.
now apply Rplus_lt_compat_l.
rewrite Heps2.
apply round_generic...
now apply generic_format_succ_aux1.
(* . x=0 *)
rewrite <- Zx1, 2!Rplus_0_l.
intros Heps.
case (proj2 Heps).
unfold round, scaled_mantissa, cexp.
unfold ulp.
rewrite Req_bool_true; trivial.
case negligible_exp_spec.
lra.
intros n Hn H.
assert (fexp (mag beta eps) = fexp n).
apply valid_exp; try assumption.
cut (mag beta eps-1 < fexp n)%Z. lia.
apply lt_bpow with beta.
apply Rle_lt_trans with (2:=H).
destruct (mag beta eps) as (e,He).
simpl; rewrite Rabs_pos_eq in He.
now apply He, Rgt_not_eq.
now left.
replace (Zceil (eps * bpow (- fexp (mag beta eps)))) with 1%Z.
unfold F2R; simpl; rewrite H0; ring.
apply sym_eq, Zceil_imp.
split.
simpl; apply Rmult_lt_0_compat.
apply Heps.
apply bpow_gt_0.
apply Rmult_le_reg_r with (bpow (fexp n)).
apply bpow_gt_0.
rewrite Rmult_assoc, <- bpow_plus.
rewrite H0; ring_simplify (-fexp n + fexp n)%Z.
simpl; rewrite Rmult_1_l, Rmult_1_r.
now left.
intros P; rewrite P.
apply round_generic...
apply generic_format_ulp_0.
Qed.

Theorem round_UP_pred_plus_eps_pos :
  forall x, (0 < x)%R -> F x ->
  forall eps, (0 < eps <= ulp (pred x) )%R ->
  round beta fexp Zceil (pred x + eps) = x.
Proof.
intros x Hx Fx eps Heps.
rewrite round_UP_plus_eps_pos; trivial.
rewrite pred_eq_pos.
apply pred_pos_plus_ulp; trivial.
now left.
now apply pred_ge_0.
apply generic_format_pred; trivial.
Qed.

Theorem round_DN_minus_eps_pos :
  forall x,  (0 < x)%R -> F x ->
  forall eps, (0 < eps <= ulp (pred x))%R ->
  round beta fexp Zfloor (x - eps) = pred x.
Proof.
intros x Hpx Fx eps.
rewrite pred_eq_pos;[intros Heps|now left].
replace (x-eps)%R with (pred_pos x + (ulp (pred_pos x)-eps))%R.
2: pattern x at 3; rewrite <- (pred_pos_plus_ulp x); trivial.
2: ring.
rewrite round_DN_plus_eps_pos; trivial.
now apply pred_pos_ge_0.
now apply generic_format_pred_pos.
split.
apply Rle_0_minus.
now apply Heps.
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
now apply Heps.
Qed.

Theorem round_DN_plus_eps:
  forall x, F x ->
  forall eps, (0 <= eps < if (Rle_bool 0 x) then (ulp x)
                                     else (ulp (pred (-x))))%R ->
  round beta fexp Zfloor (x + eps) = x.
Proof.
intros x Fx eps Heps.
case (Rle_or_lt 0 x); intros Zx.
apply round_DN_plus_eps_pos; try assumption.
split; try apply Heps.
rewrite Rle_bool_true in Heps; trivial.
now apply Heps.
(* *)
rewrite Rle_bool_false in Heps; trivial.
rewrite <- (Ropp_involutive (x+eps)).
pattern x at 2; rewrite <- (Ropp_involutive x).
rewrite round_DN_opp.
apply f_equal.
replace (-(x+eps))%R with (pred (-x) + (ulp (pred (-x)) - eps))%R.
rewrite round_UP_pred_plus_eps_pos; try reflexivity.
now apply Ropp_0_gt_lt_contravar.
now apply generic_format_opp.
split.
apply Rplus_lt_reg_l with eps; ring_simplify.
apply Heps.
apply Rplus_le_reg_l with (eps-ulp (pred (- x)))%R; ring_simplify.
apply Heps.
unfold pred.
rewrite Ropp_involutive.
unfold succ; rewrite Rle_bool_false; try assumption.
rewrite Ropp_involutive; unfold Rminus.
rewrite <- Rplus_assoc, pred_pos_plus_ulp.
ring.
now apply Ropp_0_gt_lt_contravar.
now apply generic_format_opp.
Qed.

Theorem round_UP_plus_eps :
  forall x, F x ->
  forall eps, (0 < eps <= if (Rle_bool 0 x) then (ulp x)
                                     else (ulp (pred (-x))))%R ->
  round beta fexp Zceil (x + eps) = (succ x)%R.
Proof with auto with typeclass_instances.
intros x Fx eps Heps.
case (Rle_or_lt 0 x); intros Zx.
rewrite succ_eq_pos; try assumption.
rewrite Rle_bool_true in Heps; trivial.
apply round_UP_plus_eps_pos; assumption.
(* *)
rewrite Rle_bool_false in Heps; trivial.
rewrite <- (Ropp_involutive (x+eps)).
rewrite <- (Ropp_involutive (succ x)).
rewrite round_UP_opp.
apply f_equal.
replace (-(x+eps))%R with (-succ x + (-eps + ulp (pred (-x))))%R.
apply round_DN_plus_eps_pos.
rewrite <- pred_opp.
apply pred_ge_0.
now apply Ropp_0_gt_lt_contravar.
now apply generic_format_opp.
now apply generic_format_opp, generic_format_succ.
split.
apply Rplus_le_reg_l with eps; ring_simplify.
apply Heps.
unfold pred; rewrite Ropp_involutive.
apply Rplus_lt_reg_l with (eps-ulp (- succ x))%R; ring_simplify.
apply Heps.
unfold succ; rewrite Rle_bool_false; try assumption.
apply trans_eq with (-x +-eps)%R;[idtac|ring].
pattern (-x)%R at 3; rewrite <- (pred_pos_plus_ulp (-x)).
rewrite pred_eq_pos.
ring.
left; now apply Ropp_0_gt_lt_contravar.
now apply Ropp_0_gt_lt_contravar.
now apply generic_format_opp.
Qed.


Lemma le_pred_pos_lt :
  forall x y,
  F x -> F y ->
  (0 <= x < y)%R ->
  (x <= pred_pos y)%R.
Proof with auto with typeclass_instances.
intros x y Fx Fy H.
case (proj1 H); intros V.
assert (Zy:(0 < y)%R).
apply Rle_lt_trans with (1:=proj1 H).
apply H.
(* *)
assert (Zp: (0 < pred y)%R).
assert (Zp:(0 <= pred y)%R).
apply pred_ge_0 ; trivial.
destruct Zp; trivial.
generalize H0.
rewrite pred_eq_pos;[idtac|now left].
unfold pred_pos.
destruct (mag beta y) as (ey,Hey); simpl.
case Req_bool_spec; intros Hy2.
(* . *)
intros Hy3.
assert (ey-1 = fexp (ey -1))%Z.
apply bpow_inj with beta.
rewrite <- Hy2, <- Rplus_0_l, Hy3.
ring.
assert (Zx: (x <> 0)%R).
now apply Rgt_not_eq.
destruct (mag beta x) as (ex,Hex).
specialize (Hex Zx).
assert (ex <= ey)%Z.
apply bpow_lt_bpow with beta.
apply Rle_lt_trans with (1:=proj1 Hex).
apply Rlt_trans with (Rabs y).
rewrite 2!Rabs_right.
apply H.
now apply Rgt_ge.
now apply Rgt_ge.
apply Hey.
now apply Rgt_not_eq.
case (Zle_lt_or_eq _ _ H2); intros Hexy.
assert (fexp ex = fexp (ey-1))%Z.
apply valid_exp.
lia.
rewrite <- H1.
lia.
absurd (0 < Ztrunc (scaled_mantissa beta fexp x) < 1)%Z.
lia.
split.
apply gt_0_F2R with beta (cexp beta fexp x).
now rewrite <- Fx.
apply lt_IZR.
apply Rmult_lt_reg_r with (bpow (cexp beta fexp x)).
apply bpow_gt_0.
replace (IZR (Ztrunc (scaled_mantissa beta fexp x)) *
  bpow (cexp beta fexp x))%R with x.
rewrite Rmult_1_l.
unfold cexp.
rewrite mag_unique with beta x ex.
rewrite H3,<-H1, <- Hy2.
apply H.
exact Hex.
absurd (y <= x)%R.
now apply Rlt_not_le.
rewrite Rabs_right in Hex.
apply Rle_trans with (2:=proj1 Hex).
rewrite Hexy, Hy2.
now apply Rle_refl.
now apply Rgt_ge.
(* . *)
intros Hy3.
assert (y = bpow (fexp ey))%R.
apply Rminus_diag_uniq.
rewrite Hy3.
rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
unfold cexp.
rewrite (mag_unique beta y ey); trivial.
apply Hey.
now apply Rgt_not_eq.
contradict Hy2.
rewrite H1.
apply f_equal.
apply Zplus_reg_l with 1%Z.
ring_simplify.
apply trans_eq with (mag beta y).
apply sym_eq; apply mag_unique.
rewrite H1, Rabs_right.
split.
apply bpow_le.
lia.
apply bpow_lt.
lia.
apply Rle_ge; apply bpow_ge_0.
apply mag_unique.
apply Hey.
now apply Rgt_not_eq.
(* *)
case (Rle_or_lt (ulp (pred_pos y)) (y-x)); intros H1.
(* . *)
apply Rplus_le_reg_r with (-x + ulp (pred_pos y))%R.
ring_simplify (x+(-x+ulp (pred_pos y)))%R.
apply Rle_trans with (1:=H1).
rewrite <- (pred_pos_plus_ulp y) at 1; trivial.
apply Req_le; ring.
(* . *)
replace x with (y-(y-x))%R by ring.
rewrite <- pred_eq_pos;[idtac|now left].
rewrite <- round_DN_minus_eps_pos with (eps:=(y-x)%R); try easy.
ring_simplify (y-(y-x))%R.
apply Req_le.
apply sym_eq.
apply round_generic...
split; trivial.
now apply Rlt_Rminus.
rewrite pred_eq_pos;[idtac|now left].
now apply Rlt_le.
rewrite <- V; apply pred_pos_ge_0; trivial.
apply Rle_lt_trans with (1:=proj1 H); apply H.
Qed.

Lemma succ_le_lt_aux:
  forall x y,
  F x -> F y ->
  (0 <= x)%R -> (x < y)%R ->
  (succ x <= y)%R.
Proof with auto with typeclass_instances.
intros x y Hx Hy Zx H.
rewrite succ_eq_pos; trivial.
case (Rle_or_lt (ulp x) (y-x)); intros H1.
apply Rplus_le_reg_r with (-x)%R.
now ring_simplify (x+ulp x + -x)%R.
replace y with (x+(y-x))%R by ring.
absurd (x < y)%R.
2: apply H.
apply Rle_not_lt; apply Req_le.
rewrite <- round_DN_plus_eps_pos with (eps:=(y-x)%R); try easy.
ring_simplify (x+(y-x))%R.
apply sym_eq.
apply round_generic...
split; trivial.
apply Rlt_le; now apply Rlt_Rminus.
Qed.

Theorem succ_le_lt:
  forall x y,
  F x -> F y ->
  (x < y)%R ->
  (succ x <= y)%R.
Proof with auto with typeclass_instances.
intros x y Fx Fy H.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
now apply succ_le_lt_aux.
unfold succ; rewrite Rle_bool_false; try assumption.
case (Rle_or_lt y 0); intros Hy.
rewrite <- (Ropp_involutive y).
apply Ropp_le_contravar.
apply le_pred_pos_lt.
now apply generic_format_opp.
now apply generic_format_opp.
split.
rewrite <- Ropp_0; now apply Ropp_le_contravar.
now apply Ropp_lt_contravar.
apply Rle_trans with (-0)%R.
apply Ropp_le_contravar.
apply pred_pos_ge_0.
rewrite <- Ropp_0; now apply Ropp_lt_contravar.
now apply generic_format_opp.
rewrite Ropp_0; now left.
Qed.

Theorem pred_ge_gt :
  forall x y,
  F x -> F y ->
  (x < y)%R ->
  (x <= pred y)%R.
Proof.
intros x y Fx Fy Hxy.
rewrite <- (Ropp_involutive x).
unfold pred; apply Ropp_le_contravar.
apply succ_le_lt.
now apply generic_format_opp.
now apply generic_format_opp.
now apply Ropp_lt_contravar.
Qed.

Theorem succ_gt_ge :
  forall x y,
  (y <> 0)%R ->
  (x <= y)%R ->
  (x < succ y)%R.
Proof.
intros x y Zy Hxy.
apply Rle_lt_trans with (1 := Hxy).
now apply succ_gt_id.
Qed.

Theorem pred_lt_le :
  forall x y,
  (x <> 0)%R ->
  (x <= y)%R ->
  (pred x < y)%R.
Proof.
intros x y Zy Hxy.
apply Rlt_le_trans with (2 := Hxy).
now apply pred_lt_id.
Qed.

Lemma succ_pred_pos :
  forall x, F x -> (0 < x)%R -> succ (pred x) = x.
Proof.
intros x Fx Hx.
rewrite pred_eq_pos by now left.
rewrite succ_eq_pos by now apply pred_pos_ge_0.
now apply pred_pos_plus_ulp.
Qed.

Theorem pred_ulp_0 :
  pred (ulp 0) = 0%R.
Proof.
rewrite pred_eq_pos.
2: apply ulp_ge_0.
unfold ulp; rewrite Req_bool_true; trivial.
case negligible_exp_spec'.
(* *)
intros [H1 _]; rewrite H1.
unfold pred_pos; rewrite Req_bool_false.
2: apply Rlt_not_eq, bpow_gt_0.
unfold ulp; rewrite Req_bool_true; trivial.
rewrite H1; ring.
(* *)
intros (n,(H1,H2)); rewrite H1.
unfold pred_pos.
rewrite mag_bpow.
replace (fexp n + 1 - 1)%Z with (fexp n) by ring.
rewrite Req_bool_true; trivial.
apply Rminus_diag_eq, f_equal.
apply sym_eq, valid_exp; lia.
Qed.

Theorem succ_0 :
  succ 0 = ulp 0.
Proof.
unfold succ.
rewrite Rle_bool_true.
apply Rplus_0_l.
apply Rle_refl.
Qed.

Theorem pred_0 :
  pred 0 = Ropp (ulp 0).
Proof.
rewrite <- succ_0.
rewrite <- Ropp_0 at 1.
apply pred_opp.
Qed.

Lemma pred_succ_pos :
  forall x, F x -> (0 < x)%R ->
  pred (succ x) = x.
Proof.
intros x Fx Hx.
apply Rle_antisym.
- apply Rnot_lt_le.
  intros H.
  apply succ_le_lt with (1 := Fx) in H.
  revert H.
  apply Rlt_not_le.
  apply pred_lt_id.
  apply Rgt_not_eq.
  apply Rlt_le_trans with (1 := Hx).
  apply succ_ge_id.
  now apply generic_format_pred, generic_format_succ.
- apply pred_ge_gt with (1 := Fx).
  now apply generic_format_succ.
  apply succ_gt_id.
  now apply Rgt_not_eq.
Qed.

Theorem succ_pred :
  forall x, F x ->
  succ (pred x) = x.
Proof.
intros x Fx.
destruct (Rle_or_lt 0 x) as [[Hx|Hx]|Hx].
now apply succ_pred_pos.
rewrite <- Hx.
rewrite pred_0, succ_opp, pred_ulp_0.
apply Ropp_0.
unfold pred.
rewrite succ_opp, pred_succ_pos.
apply Ropp_involutive.
now apply generic_format_opp.
now apply Ropp_0_gt_lt_contravar.
Qed.

Theorem pred_succ :
  forall x, F x ->
  pred (succ x) = x.
Proof.
intros x Fx.
rewrite <- (Ropp_involutive x).
rewrite succ_opp, pred_opp.
apply f_equal, succ_pred.
now apply generic_format_opp.
Qed.

Theorem round_UP_pred_plus_eps :
  forall x, F x ->
  forall eps, (0 < eps <= if Rle_bool x 0 then ulp x
                          else ulp (pred x))%R ->
  round beta fexp Zceil (pred x + eps) = x.
Proof.
intros x Fx eps Heps.
rewrite round_UP_plus_eps.
now apply succ_pred.
now apply generic_format_pred.
unfold pred at 4.
rewrite Ropp_involutive, pred_succ.
rewrite ulp_opp.
generalize Heps; case (Rle_bool_spec x 0); intros H1 H2.
rewrite Rle_bool_false; trivial.
case H1; intros H1'.
apply Rlt_le_trans with (2:=H1).
apply pred_lt_id.
now apply Rlt_not_eq.
rewrite H1'; unfold pred, succ.
rewrite Ropp_0; rewrite Rle_bool_true;[idtac|now right].
rewrite Rplus_0_l.
rewrite <- Ropp_0; apply Ropp_lt_contravar.
apply Rlt_le_trans with (1:=proj1 H2).
apply Rle_trans with (1:=proj2 H2).
rewrite Ropp_0, H1'.
now right.
rewrite Rle_bool_true; trivial.
now apply pred_ge_0.
now apply generic_format_opp.
Qed.

Theorem round_DN_minus_eps:
  forall x,  F x ->
  forall eps, (0 < eps <= if (Rle_bool x 0) then (ulp x)
                                     else (ulp (pred x)))%R ->
  round beta fexp Zfloor (x - eps) = pred x.
Proof.
intros x Fx eps Heps.
replace (x-eps)%R with (-(-x+eps))%R by ring.
rewrite round_DN_opp.
unfold pred; apply f_equal.
pattern (-x)%R at 1; rewrite <- (pred_succ (-x)).
apply round_UP_pred_plus_eps.
now apply generic_format_succ, generic_format_opp.
rewrite pred_succ.
rewrite ulp_opp.
generalize Heps; case (Rle_bool_spec x 0); intros H1 H2.
rewrite Rle_bool_false; trivial.
case H1; intros H1'.
apply Rlt_le_trans with (-x)%R.
now apply Ropp_0_gt_lt_contravar.
apply succ_ge_id.
rewrite H1', Ropp_0, succ_eq_pos;[idtac|now right].
rewrite Rplus_0_l.
apply Rlt_le_trans with (1:=proj1 H2).
rewrite H1' in H2; apply H2.
rewrite Rle_bool_true.
now rewrite succ_opp, ulp_opp.
rewrite succ_opp.
rewrite <- Ropp_0; apply Ropp_le_contravar.
now apply pred_ge_0.
now apply generic_format_opp.
now apply generic_format_opp.
Qed.

(** Error of a rounding, expressed in number of ulps *)
(** false for x=0 in the FLX format *)
(* was ulp_error *)
Theorem error_lt_ulp :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < ulp x)%R.
Proof with auto with typeclass_instances.
intros rnd Zrnd x Zx.
destruct (generic_format_EM beta fexp x) as [Hx|Hx].
(* x = rnd x *)
rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
rewrite ulp_neq_0; trivial.
apply bpow_gt_0.
(* x <> rnd x *)
destruct (round_DN_or_UP beta fexp rnd x) as [H|H] ; rewrite H ; clear H.
(* . *)
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rplus_lt_reg_l with (round beta fexp Zfloor x).
rewrite <- round_UP_DN_ulp with (1 := Hx).
ring_simplify.
assert (Hu: (x <= round beta fexp Zceil x)%R).
apply round_UP_pt...
destruct Hu as [Hu|Hu].
exact Hu.
elim Hx.
rewrite Hu.
apply generic_format_round...
apply Rle_minus.
apply round_DN_pt...
(* . *)
rewrite Rabs_pos_eq.
rewrite round_UP_DN_ulp with (1 := Hx).
apply Rplus_lt_reg_r with (x - ulp x)%R.
ring_simplify.
assert (Hd: (round beta fexp Zfloor x <= x)%R).
apply round_DN_pt...
destruct Hd as [Hd|Hd].
exact Hd.
elim Hx.
rewrite <- Hd.
apply generic_format_round...
apply Rle_0_minus.
apply round_UP_pt...
Qed.

(* was ulp_error_le *)
Theorem error_le_ulp :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (Rabs (round beta fexp rnd x - x) <= ulp x)%R.
Proof with auto with typeclass_instances.
intros  rnd Zrnd x.
case (Req_dec x 0).
intros Zx; rewrite Zx, round_0...
unfold Rminus; rewrite Rplus_0_l, Ropp_0, Rabs_R0.
apply ulp_ge_0.
intros Zx; left.
now apply error_lt_ulp.
Qed.

Theorem error_le_half_ulp :
  forall choice x,
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * ulp x)%R.
Proof with auto with typeclass_instances.
intros choice x.
destruct (generic_format_EM beta fexp x) as [Hx|Hx].
(* x = rnd x *)
rewrite round_generic...
unfold Rminus.
rewrite Rplus_opp_r, Rabs_R0.
apply Rmult_le_pos.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
apply ulp_ge_0.
(* x <> rnd x *)
set (d := round beta fexp Zfloor x).
destruct (round_N_pt beta fexp choice x) as (Hr1, Hr2).
destruct (Rle_or_lt (x - d) (d + ulp x - x)) as [H|H].
(* . rnd(x) = rndd(x) *)
apply Rle_trans with (Rabs (d - x)).
apply Hr2.
apply (round_DN_pt beta fexp x).
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rmult_le_reg_r with 2%R.
now apply IZR_lt.
apply Rplus_le_reg_r with (d - x)%R.
ring_simplify.
apply Rle_trans with (1 := H).
right. field.
apply Rle_minus.
apply (round_DN_pt beta fexp x).
(* . rnd(x) = rndu(x) *)
assert (Hu: (d + ulp x)%R = round beta fexp Zceil x).
unfold d.
now rewrite <- round_UP_DN_ulp.
apply Rle_trans with (Rabs (d + ulp x - x)).
apply Hr2.
rewrite Hu.
apply (round_UP_pt beta fexp x).
rewrite Rabs_pos_eq.
apply Rmult_le_reg_r with 2%R.
now apply IZR_lt.
apply Rplus_le_reg_r with (- (d + ulp x - x))%R.
ring_simplify.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
right. field.
apply Rle_0_minus.
rewrite Hu.
apply (round_UP_pt beta fexp x).
Qed.

Theorem ulp_DN :
  forall x, (0 <= x)%R ->
  ulp (round beta fexp Zfloor x) = ulp x.
Proof with auto with typeclass_instances.
intros x [Hx|Hx].
- rewrite (ulp_neq_0 x) by now apply Rgt_not_eq.
  destruct (round_ge_generic beta fexp Zfloor 0 x) as [Hd|Hd].
    apply generic_format_0.
    now apply Rlt_le.
  + rewrite ulp_neq_0 by now apply Rgt_not_eq.
    now rewrite cexp_DN with (2 := Hd).
  + rewrite <- Hd.
    unfold cexp.
    destruct (mag beta x) as [e He].
    simpl.
    specialize (He (Rgt_not_eq _ _ Hx)).
    apply sym_eq in Hd.
    assert (H := exp_small_round_0 _ _ _ _ _ He Hd).
    unfold ulp.
    rewrite Req_bool_true by easy.
    destruct negligible_exp_spec as [H0|k Hk].
    now elim Zlt_not_le with (1 := H0 e).
    now apply f_equal, fexp_negligible_exp_eq.
- rewrite <- Hx, round_0...
Qed.

Theorem round_neq_0_negligible_exp :
  negligible_exp = None -> forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R -> (round beta fexp rnd x <> 0)%R.
Proof with auto with typeclass_instances.
intros H rndn Hrnd x Hx K.
case negligible_exp_spec'.
intros (_,Hn).
destruct (mag beta x) as (e,He).
absurd (fexp e < e)%Z.
apply Zle_not_lt.
apply exp_small_round_0 with beta rndn x...
apply (Hn e).
intros (n,(H1,_)).
rewrite H in H1; discriminate.
Qed.

(** allows rnd x to be 0 *)
Theorem error_lt_ulp_round :
  forall { Hm : Monotone_exp fexp } rnd { Zrnd : Valid_rnd rnd } x,
  (x <> 0)%R ->
  (Rabs (round beta fexp rnd x - x) < ulp (round beta fexp rnd x))%R.
Proof with auto with typeclass_instances.
intros Hm.
(* wlog *)
cut (forall rnd : R -> Z, Valid_rnd rnd -> forall x : R, (0 < x)%R  ->
    (Rabs (round beta fexp rnd x - x) < ulp (round beta fexp rnd x))%R).
intros M rnd Hrnd x Zx.
case (Rle_or_lt 0 x).
intros H; destruct H.
now apply M.
contradict H; now apply sym_not_eq.
intros H.
rewrite <- (Ropp_involutive x).
rewrite round_opp, ulp_opp.
replace (- round beta fexp (Zrnd_opp rnd) (- x) - - - x)%R with
    (-(round beta fexp (Zrnd_opp rnd) (- x) - (-x)))%R by ring.
rewrite Rabs_Ropp.
apply M.
now apply valid_rnd_opp.
now apply Ropp_0_gt_lt_contravar.
(* 0 < x *)
intros rnd Hrnd x Hx.
apply Rlt_le_trans with (ulp x).
apply error_lt_ulp...
now apply Rgt_not_eq.
rewrite <- ulp_DN; trivial.
apply ulp_le_pos.
apply round_ge_generic...
apply generic_format_0.
now apply Rlt_le.
case (round_DN_or_UP beta fexp rnd x); intros V; rewrite V.
apply Rle_refl.
apply Rle_trans with x.
apply round_DN_pt...
apply round_UP_pt...
now apply Rlt_le.
Qed.

Lemma error_le_ulp_round :
  forall { Hm : Monotone_exp fexp } rnd { Zrnd : Valid_rnd rnd } x,
  (Rabs (round beta fexp rnd x - x) <= ulp (round beta fexp rnd x))%R.
Proof.
intros Mexp rnd Vrnd x.
destruct (Req_dec x 0) as [Zx|Nzx].
{ rewrite Zx, round_0; [|exact Vrnd].
  unfold Rminus; rewrite Ropp_0, Rplus_0_l, Rabs_R0; apply ulp_ge_0. }
now apply Rlt_le, error_lt_ulp_round.
Qed.

(** allows both x and rnd x to be 0 *)
Theorem error_le_half_ulp_round :
  forall { Hm : Monotone_exp fexp },
  forall choice x,
  (Rabs (round beta fexp (Znearest choice) x - x) <= /2 * ulp (round beta fexp (Znearest choice) x))%R.
Proof with auto with typeclass_instances.
intros Hm choice x.
case (Req_dec (round beta fexp (Znearest choice) x) 0); intros Hfx.
(* *)
case (Req_dec x 0); intros Hx.
apply Rle_trans with (1:=error_le_half_ulp _ _).
rewrite Hx, round_0...
right; ring.
generalize (error_le_half_ulp choice x).
rewrite Hfx.
unfold Rminus; rewrite Rplus_0_l, Rabs_Ropp.
intros N.
unfold ulp; rewrite Req_bool_true; trivial.
case negligible_exp_spec'.
intros (H1,H2).
contradict Hfx.
apply round_neq_0_negligible_exp...
intros (n,(H1,Hn)); rewrite H1.
apply Rle_trans with (1:=N).
right; apply f_equal.
rewrite ulp_neq_0; trivial.
apply f_equal.
unfold cexp.
apply valid_exp; trivial.
cut (mag beta x -1 < fexp n)%Z. lia.
apply lt_bpow with beta.
destruct (mag beta x) as (e,He).
simpl.
apply Rle_lt_trans with (Rabs x).
now apply He.
apply Rle_lt_trans with (Rabs (round beta fexp (Znearest choice) x - x)).
right; rewrite Hfx; unfold Rminus; rewrite Rplus_0_l.
apply sym_eq, Rabs_Ropp.
apply Rlt_le_trans with (ulp 0).
rewrite <- Hfx.
apply error_lt_ulp_round...
unfold ulp; rewrite Req_bool_true, H1; trivial.
now right.
(* *)
case (round_DN_or_UP beta fexp (Znearest choice) x); intros Hx.
(* . *)
destruct (Rle_or_lt 0 x) as [H|H].
rewrite Hx at 2.
rewrite ulp_DN by easy.
apply error_le_half_ulp.
apply Rle_trans with (1:=error_le_half_ulp _ _).
apply Rmult_le_compat_l.
apply Rlt_le, pos_half_prf.
apply ulp_le.
rewrite Rabs_left1 by now apply Rlt_le.
rewrite Hx.
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply round_DN_pt...
apply round_le_generic...
apply generic_format_0.
now apply Rlt_le.
(* . *)
destruct (Rle_or_lt 0 x) as [H|H].
apply Rle_trans with (1:=error_le_half_ulp _ _).
apply Rmult_le_compat_l.
apply Rlt_le, pos_half_prf.
apply ulp_le_pos; trivial.
rewrite Hx; apply (round_UP_pt beta fexp x).
rewrite Hx at 2; rewrite <- (ulp_opp (round beta fexp Zceil x)).
rewrite <- round_DN_opp.
rewrite ulp_DN; trivial.
pattern x at 1 2; rewrite <- Ropp_involutive.
rewrite round_N_opp.
unfold Rminus.
rewrite <- Ropp_plus_distr, Rabs_Ropp.
apply error_le_half_ulp.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
Qed.

Theorem pred_le :
  forall x y, F x -> F y -> (x <= y)%R ->
  (pred x <= pred y)%R.
Proof.
intros x y Fx Fy [Hxy| ->].
2: apply Rle_refl.
apply pred_ge_gt with (2 := Fy).
now apply generic_format_pred.
apply Rle_lt_trans with (2 := Hxy).
apply pred_le_id.
Qed.

Theorem succ_le :
  forall x y, F x -> F y -> (x <= y)%R ->
  (succ x <= succ y)%R.
Proof.
intros x y Fx Fy Hxy.
apply Ropp_le_cancel.
rewrite <- 2!pred_opp.
apply pred_le.
now apply generic_format_opp.
now apply generic_format_opp.
now apply Ropp_le_contravar.
Qed.

Theorem pred_le_inv: forall x y, F x -> F y
   -> (pred x <= pred y)%R -> (x <= y)%R.
Proof.
intros x y Fx Fy Hxy.
rewrite <- (succ_pred x), <- (succ_pred y); try assumption.
apply succ_le; trivial; now apply generic_format_pred.
Qed.

Theorem succ_le_inv: forall x y, F x -> F y
   -> (succ x <= succ y)%R -> (x <= y)%R.
Proof.
intros x y Fx Fy Hxy.
rewrite <- (pred_succ x), <- (pred_succ y); try assumption.
apply pred_le; trivial; now apply generic_format_succ.
Qed.

Theorem pred_lt :
  forall x y, F x -> F y -> (x < y)%R ->
  (pred x < pred y)%R.
Proof.
intros x y Fx Fy Hxy.
apply Rnot_le_lt.
intros H.
apply Rgt_not_le with (1 := Hxy).
now apply pred_le_inv.
Qed.

Theorem succ_lt :
  forall x y, F x -> F y -> (x < y)%R ->
  (succ x < succ y)%R.
Proof.
intros x y Fx Fy Hxy.
apply Rnot_le_lt.
intros H.
apply Rgt_not_le with (1 := Hxy).
now apply succ_le_inv.
Qed.

(** Adding [ulp] is a, somewhat reasonable, overapproximation of [succ]. *)
Lemma succ_le_plus_ulp :
  forall { Hm : Monotone_exp fexp } x,
  (succ x <= x + ulp x)%R.
Proof.
intros Mexp x.
destruct (Rle_or_lt 0 x) as [Px|Nx]; [now right; apply succ_eq_pos|].
replace (_ + _)%R with (- (-x - ulp x))%R by ring.
unfold succ; rewrite (Rle_bool_false _ _ Nx), <-ulp_opp.
apply Ropp_le_contravar; unfold pred_pos.
destruct (Req_dec (-x) (bpow (mag beta (-x) - 1))) as [Hx|Hx].
{ rewrite (Req_bool_true _ _ Hx).
   apply (Rplus_le_reg_r x); ring_simplify; apply Ropp_le_contravar.
   unfold ulp; rewrite Req_bool_false; [|lra].
   apply bpow_le, Mexp; lia. }
 now rewrite (Req_bool_false _ _ Hx); right.
Qed.

(** And it also lies in the format. *)
Lemma generic_format_plus_ulp :
  forall { Hm : Monotone_exp fexp } x,
  generic_format beta fexp x ->
  generic_format beta fexp (x + ulp x).
Proof.
intros Mexp x Fx.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{ now rewrite <-(succ_eq_pos _ Px); apply generic_format_succ. }
apply generic_format_opp in Fx.
replace (_ + _)%R with (- (-x - ulp x))%R by ring.
apply generic_format_opp; rewrite <-ulp_opp.
destruct (Req_dec (-x) (bpow (mag beta (-x) - 1))) as [Hx|Hx].
{ unfold ulp; rewrite Req_bool_false; [|lra].
  rewrite Hx at 1.
  unfold cexp.
  set (e := mag _ _).
  assert (Hfe : (fexp e < e)%Z).
  { now apply mag_generic_gt; [|lra|]. }
  replace (e - 1)%Z with (e - 1 - fexp e + fexp e)%Z by ring.
  rewrite bpow_plus.
  set (m := bpow (_ - _)).
  replace (_ - _)%R with ((m - 1) * bpow (fexp e))%R; [|unfold m; ring].
  case_eq (e - 1 - fexp e)%Z.
  { intro He; unfold m; rewrite He; simpl; ring_simplify (1 - 1)%R.
    rewrite Rmult_0_l; apply generic_format_0. }
  { intros p Hp; unfold m; rewrite Hp; simpl.
    pose (f := {| Defs.Fnum := (Z.pow_pos beta p - 1)%Z;
                  Defs.Fexp := fexp e |} : Defs.float beta).
    apply (generic_format_F2R' _ _ _ f); [|intro Hm'; unfold f; simpl].
    { now unfold Defs.F2R; simpl; rewrite minus_IZR. }
    unfold cexp.
    replace (IZR _) with (bpow (Z.pos p)); [|now simpl].
    rewrite <-Hp.
    assert (He : (1 <= e - 1 - fexp e)%Z); [lia|].
    set (e' := mag _ (_ * _)).
    assert (H : (e' = e - 1 :> Z)%Z); [|rewrite H; apply Mexp; lia].
    unfold e'; apply mag_unique.
    rewrite Rabs_mult, (Rabs_pos_eq (bpow _)); [|apply bpow_ge_0].
    rewrite Rabs_pos_eq;
      [|apply (Rplus_le_reg_r 1); ring_simplify;
        change 1%R with (bpow 0); apply bpow_le; lia].
    assert (beta_pos : (0 < IZR beta)%R).
    { apply (Rlt_le_trans _ 2); [lra|].
      apply IZR_le, Z.leb_le, radix_prop. }
    split.
    { replace (e - 1 - 1)%Z with (e - 1 - fexp e + -1  + fexp e)%Z by ring.
      rewrite bpow_plus.
      apply Rmult_le_compat_r; [apply bpow_ge_0|].
      rewrite bpow_plus; simpl; unfold Z.pow_pos; simpl.
      rewrite Zmult_1_r.
      apply (Rmult_le_reg_r _ _ _ beta_pos).
      rewrite Rmult_assoc, Rinv_l; [|lra]; rewrite Rmult_1_r.
      apply (Rplus_le_reg_r (IZR beta)); ring_simplify.
      apply (Rle_trans _ (2 * bpow (e - 1 - fexp e))).
      { change 2%R with (1 + 1)%R; rewrite Rmult_plus_distr_r, Rmult_1_l.
        apply Rplus_le_compat_l.
        rewrite <-bpow_1; apply bpow_le; lia. }
      rewrite Rmult_comm; apply Rmult_le_compat_l; [apply bpow_ge_0|].
      apply IZR_le, Z.leb_le, radix_prop. }
    apply (Rmult_lt_reg_r (bpow (- fexp e))); [apply bpow_gt_0|].
    rewrite Rmult_assoc, <-!bpow_plus.
    replace (fexp e + - fexp e)%Z with 0%Z by ring; simpl.
    rewrite Rmult_1_r; unfold Zminus; lra. }
  intros p Hp; exfalso; lia. }
replace (_ - _)%R with (pred_pos (-x)).
{ now apply generic_format_pred_pos; [|lra]. }
now unfold pred_pos; rewrite Req_bool_false.
Qed.

Theorem round_DN_ge_UP_gt :
  forall x y, F y ->
  (y < round beta fexp Zceil x -> y <= round beta fexp Zfloor x)%R.
Proof with auto with typeclass_instances.
intros x y Fy Hlt.
apply round_DN_pt...
apply Rnot_lt_le.
contradict Hlt.
apply RIneq.Rle_not_lt.
apply round_UP_pt...
now apply Rlt_le.
Qed.

Theorem round_UP_le_DN_lt :
  forall x y, F y ->
  (round beta fexp Zfloor x < y -> round beta fexp Zceil x <= y)%R.
Proof with auto with typeclass_instances.
intros x y Fy Hlt.
apply round_UP_pt...
apply Rnot_lt_le.
contradict Hlt.
apply RIneq.Rle_not_lt.
apply round_DN_pt...
now apply Rlt_le.
Qed.

Theorem pred_UP_le_DN :
  forall x, (pred (round beta fexp Zceil x) <= round beta fexp Zfloor x)%R.
Proof with auto with typeclass_instances.
intros x.
destruct (generic_format_EM beta fexp x) as [Fx|Fx].
rewrite !round_generic...
apply pred_le_id.
case (Req_dec (round beta fexp Zceil x) 0); intros Zx.
rewrite Zx; unfold pred; rewrite Ropp_0.
unfold succ; rewrite Rle_bool_true;[idtac|now right].
rewrite Rplus_0_l; unfold ulp; rewrite Req_bool_true; trivial.
case negligible_exp_spec'.
intros (H1,H2).
contradict Zx; apply round_neq_0_negligible_exp...
intros L; apply Fx; rewrite L; apply generic_format_0.
intros (n,(H1,Hn)); rewrite H1.
case (Rle_or_lt (- bpow (fexp n)) (round beta fexp Zfloor x)); trivial; intros K.
absurd (round beta fexp Zceil x <= - bpow (fexp n))%R.
apply Rlt_not_le.
rewrite Zx, <- Ropp_0.
apply Ropp_lt_contravar, bpow_gt_0.
apply round_UP_le_DN_lt; try assumption.
apply generic_format_opp, generic_format_bpow.
now apply valid_exp.
assert (let u := round beta fexp Zceil x in pred u < u)%R as Hup.
now apply pred_lt_id.
apply round_DN_ge_UP_gt...
apply generic_format_pred...
now apply round_UP_pt.
Qed.

Theorem UP_le_succ_DN :
  forall x, (round beta fexp Zceil x <= succ (round beta fexp Zfloor x))%R.
Proof.
intros x.
rewrite <- (Ropp_involutive x).
rewrite round_DN_opp, round_UP_opp, succ_opp.
apply Ropp_le_contravar.
apply pred_UP_le_DN.
Qed.

Theorem pred_UP_eq_DN :
  forall x,  ~ F x ->
  (pred (round beta fexp Zceil x) = round beta fexp Zfloor x)%R.
Proof with auto with typeclass_instances.
intros x Fx.
apply Rle_antisym.
now apply pred_UP_le_DN.
apply pred_ge_gt; try apply generic_format_round...
pose proof round_DN_UP_lt _ _ _ Fx as HE.
now apply Rlt_trans with (1 := proj1 HE) (2 := proj2 HE).
Qed.

Theorem succ_DN_eq_UP :
  forall x,  ~ F x ->
  (succ (round beta fexp Zfloor x) = round beta fexp Zceil x)%R.
Proof with auto with typeclass_instances.
intros x Fx.
rewrite <- pred_UP_eq_DN; trivial.
rewrite succ_pred; trivial.
apply generic_format_round...
Qed.

Theorem round_DN_eq :
  forall x d, F d -> (d <= x < succ d)%R ->
  round beta fexp Zfloor x = d.
Proof with auto with typeclass_instances.
intros x d Fd (Hxd1,Hxd2).
generalize (round_DN_pt beta fexp x); intros (T1,(T2,T3)).
apply sym_eq, Rle_antisym.
now apply T3.
destruct (generic_format_EM beta fexp x) as [Fx|NFx].
rewrite round_generic...
apply succ_le_inv; try assumption.
apply succ_le_lt; try assumption.
apply generic_format_succ...
apply succ_le_inv; try assumption.
rewrite succ_DN_eq_UP; trivial.
apply round_UP_pt...
apply generic_format_succ...
now left.
Qed.

Theorem round_UP_eq :
  forall x u, F u -> (pred u < x <= u)%R ->
  round beta fexp Zceil x = u.
Proof with auto with typeclass_instances.
intros x u Fu Hux.
rewrite <- (Ropp_involutive (round beta fexp Zceil x)).
rewrite <- round_DN_opp.
rewrite <- (Ropp_involutive u).
apply f_equal.
apply round_DN_eq; try assumption.
now apply generic_format_opp.
split;[now apply Ropp_le_contravar|idtac].
rewrite succ_opp.
now apply Ropp_lt_contravar.
Qed.

Lemma ulp_ulp_0 : forall {H : Exp_not_FTZ fexp},
  ulp (ulp 0) = ulp 0.
Proof.
intros H; case (negligible_exp_spec').
intros (K1,K2).
replace (ulp 0) with 0%R at 1; try easy.
apply sym_eq; unfold ulp; rewrite Req_bool_true; try easy.
now rewrite K1.
intros (n,(Hn1,Hn2)).
apply Rle_antisym.
replace (ulp 0) with (bpow (fexp n)).
rewrite ulp_bpow.
apply bpow_le.
now apply valid_exp.
unfold ulp; rewrite Req_bool_true; try easy.
rewrite Hn1; easy.
now apply ulp_ge_ulp_0.
Qed.

Lemma ulp_succ_pos :
  forall x, F x -> (0 < x)%R ->
  ulp (succ x) = ulp x \/ succ x = bpow (mag beta x).
Proof with auto with typeclass_instances.
intros x Fx Hx.
generalize (Rlt_le _ _ Hx); intros Hx'.
rewrite succ_eq_pos;[idtac|now left].
destruct (mag beta x) as (e,He); simpl.
rewrite Rabs_pos_eq in He; try easy.
specialize (He (Rgt_not_eq _ _ Hx)).
assert (H:(x+ulp x <= bpow e)%R).
apply id_p_ulp_le_bpow; try assumption.
apply He.
destruct H;[left|now right].
rewrite ulp_neq_0 at 1.
2: apply Rgt_not_eq, Rgt_lt, Rlt_le_trans with x...
2: rewrite <- (Rplus_0_r x) at 1; apply Rplus_le_compat_l.
2: apply ulp_ge_0.
rewrite ulp_neq_0 at 2.
2: now apply Rgt_not_eq.
f_equal; unfold cexp; f_equal.
apply trans_eq with e.
apply mag_unique_pos; split; try assumption.
apply Rle_trans with (1:=proj1 He).
rewrite <- (Rplus_0_r x) at 1; apply Rplus_le_compat_l.
apply ulp_ge_0.
now apply sym_eq, mag_unique_pos.
Qed.

Theorem ulp_pred_pos :
  forall x, F x -> (0 < pred x)%R ->
  ulp (pred x) = ulp x \/ x = bpow (mag beta x - 1).
Proof.
intros x Fx Hx.
assert (Hx': (0 < x)%R).
  apply Rlt_le_trans with (1 := Hx).
  apply pred_le_id.
assert (Zx : x <> 0%R).
  now apply Rgt_not_eq.
rewrite (ulp_neq_0 x) by easy.
unfold cexp.
destruct (mag beta x) as [e He].
simpl.
assert (bpow (e - 1) <= x < bpow e)%R.
  rewrite <- (Rabs_pos_eq x) by now apply Rlt_le.
  now apply He.
destruct (proj1 H) as [H1|H1].
2: now right.
left.
apply pred_ge_gt with (2 := Fx) in H1.
rewrite ulp_neq_0 by now apply Rgt_not_eq.
apply (f_equal (fun e => bpow (fexp e))).
apply mag_unique_pos.
apply (conj H1).
apply Rle_lt_trans with (2 := proj2 H).
apply pred_le_id.
apply generic_format_bpow.
apply Z.lt_le_pred.
replace (_ + 1)%Z with e by ring.
rewrite <- (mag_unique_pos _ _ _ H).
now apply mag_generic_gt.
Qed.

Lemma ulp_round_pos :
  forall { Not_FTZ_ : Exp_not_FTZ fexp},
   forall rnd { Zrnd : Valid_rnd rnd } x,
  (0 < x)%R -> ulp (round beta fexp rnd x) = ulp x
     \/ round beta fexp rnd x = bpow (mag beta x).
Proof with auto with typeclass_instances.
intros Not_FTZ_ rnd Zrnd x Hx.
case (generic_format_EM beta fexp x); intros Fx.
rewrite round_generic...
case (round_DN_or_UP beta fexp rnd x); intros Hr; rewrite Hr.
left.
apply ulp_DN; now left...
assert (M:(0 <= round beta fexp Zfloor x)%R).
apply round_ge_generic...
apply generic_format_0...
apply Rlt_le...
destruct M as [M|M].
rewrite <- (succ_DN_eq_UP x)...
case (ulp_succ_pos (round beta fexp Zfloor x)); try intros Y.
apply generic_format_round...
assumption.
rewrite ulp_DN in Y...
now apply Rlt_le.
right; rewrite Y.
apply f_equal, mag_DN...
left; rewrite <- (succ_DN_eq_UP x)...
rewrite <- M, succ_0.
rewrite ulp_ulp_0...
case (negligible_exp_spec').
intros (K1,K2).
absurd (x = 0)%R.
now apply Rgt_not_eq.
apply eq_0_round_0_negligible_exp with Zfloor...
intros (n,(Hn1,Hn2)).
replace (ulp 0) with (bpow (fexp n)).
2: unfold ulp; rewrite Req_bool_true; try easy.
2: now rewrite Hn1.
rewrite ulp_neq_0.
2: apply Rgt_not_eq...
unfold cexp; f_equal.
destruct (mag beta x) as (e,He); simpl.
apply sym_eq, valid_exp...
assert (e <= fexp e)%Z.
apply exp_small_round_0_pos with beta Zfloor x...
rewrite <- (Rabs_pos_eq x).
apply He, Rgt_not_eq...
apply Rlt_le...
replace (fexp n) with (fexp e); try assumption.
now apply fexp_negligible_exp_eq.
Qed.

Theorem ulp_round : forall { Not_FTZ_ : Exp_not_FTZ fexp},
   forall rnd { Zrnd : Valid_rnd rnd } x,
     ulp (round beta fexp rnd x) = ulp x
         \/ Rabs (round beta fexp rnd x) = bpow (mag beta x).
Proof with auto with typeclass_instances.
intros Not_FTZ_ rnd Zrnd x.
case (Rtotal_order x 0); intros Zx.
case (ulp_round_pos (Zrnd_opp rnd) (-x)).
now apply Ropp_0_gt_lt_contravar.
rewrite ulp_opp, <- ulp_opp.
rewrite <- round_opp, Ropp_involutive.
intros Y;now left.
rewrite mag_opp.
intros Y; right.
rewrite <- (Ropp_involutive x) at 1.
rewrite round_opp, Y.
rewrite Rabs_Ropp, Rabs_right...
apply Rle_ge, bpow_ge_0.
destruct Zx as [Zx|Zx].
left; rewrite Zx; rewrite round_0...
rewrite Rabs_right.
apply ulp_round_pos...
apply Rle_ge, round_ge_generic...
apply generic_format_0...
now apply Rlt_le.
Qed.

Lemma succ_round_ge_id :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (x <= succ (round beta fexp rnd x))%R.
Proof.
intros rnd Vrnd x.
apply (Rle_trans _ (round beta fexp Raux.Zceil x)).
{ now apply round_UP_pt. }
destruct (round_DN_or_UP beta fexp rnd x) as [Hr|Hr]; rewrite Hr.
{ now apply UP_le_succ_DN. }
apply succ_ge_id.
Qed.

Lemma pred_round_le_id :
  forall rnd { Zrnd : Valid_rnd rnd } x,
  (pred (round beta fexp rnd x) <= x)%R.
Proof.
intros rnd Vrnd x.
apply (Rle_trans _ (round beta fexp Raux.Zfloor x)).
2: now apply round_DN_pt.
destruct (round_DN_or_UP beta fexp rnd x) as [Hr|Hr]; rewrite Hr.
2: now apply pred_UP_le_DN.
apply pred_le_id.
Qed.

(** Properties of rounding to nearest and ulp *)

Theorem round_N_le_midp: forall choice u v,
  F u -> (v < (u + succ u)/2)%R
      -> (round beta fexp (Znearest choice)  v <= u)%R.
Proof with auto with typeclass_instances.
intros choice u v Fu H.
(* . *)
assert (V: ((succ u = 0 /\ u = 0) \/ u < succ u)%R).
specialize (succ_ge_id u); intros P; destruct P as [P|P].
now right.
case (Req_dec u 0); intros Zu.
left; split; trivial.
now rewrite <- P.
right; now apply succ_gt_id.
(* *)
destruct V as [(V1,V2)|V].
rewrite V2; apply round_le_generic...
apply generic_format_0.
left; apply Rlt_le_trans with (1:=H).
rewrite V1,V2; right; field.
(* *)
assert (T: (u < (u + succ u) / 2 < succ u)%R) by lra.
destruct T as (T1,T2).
apply Rnd_N_pt_monotone with F v ((u + succ u) / 2)%R...
apply round_N_pt...
apply Rnd_N_pt_DN with (succ u)%R.
pattern u at 3; replace u with (round beta fexp Zfloor ((u + succ u) / 2)).
apply round_DN_pt...
apply round_DN_eq; trivial.
split; try left; assumption.
pattern (succ u) at 2; replace (succ u) with (round beta fexp Zceil ((u + succ u) / 2)).
apply round_UP_pt...
apply round_UP_eq; trivial.
apply generic_format_succ...
rewrite pred_succ; trivial.
split; try left; assumption.
right; field.
Qed.


Theorem round_N_ge_midp: forall choice u v,
 F u ->  ((u + pred u)/2 < v)%R
      -> (u <= round beta fexp (Znearest choice)  v)%R.
Proof with auto with typeclass_instances.
intros choice u v Fu H.
rewrite <- (Ropp_involutive v).
rewrite round_N_opp.
rewrite <- (Ropp_involutive u).
apply Ropp_le_contravar.
apply round_N_le_midp.
now apply generic_format_opp.
apply Ropp_lt_cancel.
rewrite Ropp_involutive.
apply Rle_lt_trans with (2:=H).
unfold pred.
right; field.
Qed.

Lemma round_N_ge_ge_midp : forall choice u v,
       F u ->
       (u <= round beta fexp (Znearest choice) v)%R ->
       ((u + pred u) / 2 <= v)%R.
Proof with auto with typeclass_instances.
intros choice u v Hu H2.
assert (K: ((u=0)%R /\ negligible_exp = None) \/ (pred u < u)%R).
case (Req_dec u 0); intros Zu.
case_eq (negligible_exp).
intros n Hn; right.
rewrite Zu, pred_0.
unfold ulp; rewrite Req_bool_true, Hn; try easy.
rewrite <- Ropp_0.
apply Ropp_lt_contravar, bpow_gt_0.
intros _; left; split; easy.
right.
apply pred_lt_id...
(* *)
case K.
intros (K1,K2).
(* . *)
rewrite K1, pred_0.
unfold ulp; rewrite Req_bool_true, K2; try easy.
replace ((0+-0)/2)%R with 0%R by field.
case (Rle_or_lt 0 v); try easy.
intros H3; contradict H2.
rewrite K1; apply Rlt_not_le.
assert (H4: (round beta fexp (Znearest choice) v <= 0)%R).
apply round_le_generic...
apply generic_format_0...
now left.
case H4; try easy.
intros H5.
absurd (v=0)%R; try auto with real.
apply eq_0_round_0_negligible_exp with (Znearest choice)...
(* . *)
intros K1.
case (Rle_or_lt ((u + pred u) / 2) v); try easy.
intros H3.
absurd (u <= round beta fexp (Znearest choice) v)%R; try easy.
apply Rlt_not_le.
apply Rle_lt_trans with (2:=K1).
apply round_N_le_midp...
apply generic_format_pred...
rewrite succ_pred...
apply Rlt_le_trans with (1:=H3).
right; f_equal; ring.
Qed.


Lemma round_N_le_le_midp : forall choice u v,
       F u ->
       (round beta fexp (Znearest choice) v <= u)%R ->
       (v <= (u + succ u) / 2)%R.
Proof with auto with typeclass_instances.
intros choice u v Hu H2.
apply Ropp_le_cancel.
apply Rle_trans with (((-u)+pred (-u))/2)%R.
rewrite pred_opp; right; field.
apply round_N_ge_ge_midp with
   (choice := fun t:Z => negb (choice (- (t + 1))%Z))...
apply generic_format_opp...
rewrite <- (Ropp_involutive (round _ _ _ _)).
rewrite <- round_N_opp, Ropp_involutive.
apply Ropp_le_contravar; easy.
Qed.


Lemma round_N_eq_DN: forall choice x,
       let d:=round beta fexp Zfloor x in
       let u:=round beta fexp Zceil x in
      (x<(d+u)/2)%R ->
     round beta fexp (Znearest choice) x = d.
Proof with auto with typeclass_instances.
intros choice x d u H.
apply Rle_antisym.
destruct (generic_format_EM beta fexp x) as [Fx|Fx].
rewrite round_generic...
apply round_DN_pt; trivial; now right.
apply round_N_le_midp.
apply round_DN_pt...
apply Rlt_le_trans with (1:=H).
right; apply f_equal2; trivial; apply f_equal.
now apply sym_eq, succ_DN_eq_UP.
apply round_ge_generic; try apply round_DN_pt...
Qed.

Lemma round_N_eq_DN_pt: forall choice x d u,
      Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
      (x<(d+u)/2)%R ->
     round beta fexp (Znearest choice) x = d.
Proof with auto with typeclass_instances.
intros choice x d u Hd Hu H.
assert (H0:(d = round beta fexp Zfloor x)%R).
apply Rnd_DN_pt_unique with (1:=Hd).
apply round_DN_pt...
rewrite H0.
apply round_N_eq_DN.
rewrite <- H0.
rewrite Rnd_UP_pt_unique with F x (round beta fexp Zceil x) u; try assumption.
apply round_UP_pt...
Qed.

Lemma round_N_eq_UP: forall choice x,
      let d:=round beta fexp Zfloor x in
      let u:=round beta fexp Zceil x in
     ((d+u)/2 < x)%R ->
     round beta fexp (Znearest choice) x = u.
Proof with auto with typeclass_instances.
intros choice x d u H.
apply Rle_antisym.
apply round_le_generic; try apply round_UP_pt...
destruct (generic_format_EM beta fexp x) as [Fx|Fx].
rewrite round_generic...
apply round_UP_pt; trivial; now right.
apply round_N_ge_midp.
apply round_UP_pt...
apply Rle_lt_trans with (2:=H).
right; apply f_equal2; trivial; rewrite Rplus_comm; apply f_equal2; trivial.
now apply pred_UP_eq_DN.
Qed.

Lemma round_N_eq_UP_pt: forall choice x d u,
      Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
      ((d+u)/2 < x)%R ->
     round beta fexp (Znearest choice) x = u.
Proof with auto with typeclass_instances.
intros choice x d u Hd Hu H.
assert (H0:(u = round beta fexp Zceil x)%R).
apply Rnd_UP_pt_unique with (1:=Hu).
apply round_UP_pt...
rewrite H0.
apply round_N_eq_UP.
rewrite <- H0.
rewrite Rnd_DN_pt_unique with F x (round beta fexp Zfloor x) d; try assumption.
apply round_DN_pt...
Qed.

Lemma round_N_plus_ulp_ge :
  forall { Hm : Monotone_exp fexp } choice1 choice2 x,
  let rx := round beta fexp (Znearest choice2) x in
  (x <= round beta fexp (Znearest choice1) (rx + ulp rx))%R.
Proof.
intros Hm choice1 choice2 x.
simpl.
set (rx := round _ _ _ x).
assert (Vrnd1 : Valid_rnd (Znearest choice1)) by now apply valid_rnd_N.
assert (Vrnd2 : Valid_rnd (Znearest choice2)) by now apply valid_rnd_N.
apply (Rle_trans _ (succ rx)); [now apply succ_round_ge_id|].
rewrite round_generic; [now apply succ_le_plus_ulp|now simpl|].
now apply generic_format_plus_ulp, generic_format_round.
Qed.


Lemma round_N_eq_ties: forall c1 c2 x,
   (x - round beta fexp Zfloor x <> round beta fexp Zceil x - x)%R ->
   (round beta fexp (Znearest c1) x = round beta fexp (Znearest c2) x)%R.
Proof with auto with typeclass_instances.
intros c1 c2 x.
pose (d:=round beta fexp Zfloor x); pose (u:=round beta fexp Zceil x); fold d; fold u; intros H.
case (Rle_or_lt ((d+u)/2) x); intros L.
2:rewrite 2!round_N_eq_DN...
destruct L as [L|L].
rewrite 2!round_N_eq_UP...
contradict H; rewrite <- L; field.
Qed.

End Fcore_ulp.

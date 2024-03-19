(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: https://flocq.gitlabpages.inria.fr/

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

(** * IEEE-754 arithmetic *)

From Coq Require Import ZArith Reals Psatz SpecFloat.

Require Import Core Round Bracket Operations Div Sqrt Relative.

Definition SF2R beta x :=
  match x with
  | S754_finite s m e => F2R (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

Class Prec_lt_emax prec emax := prec_lt_emax : (prec < emax)%Z.
Arguments prec_lt_emax prec emax {Prec_lt_emax}.

Section Binary.

(** [prec] is the number of bits of the mantissa including the implicit one;
    [emax] is the exponent of the infinities.
    For instance, binary32 is defined by [prec = 24] and [emax = 128]. *)
Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Context (prec_lt_emax_ : Prec_lt_emax prec emax).

Notation emin := (emin prec emax).
Notation fexp := (fexp prec emax).
Instance fexp_correct : Valid_exp fexp := FLT_exp_valid emin prec.
Instance fexp_monotone : Monotone_exp fexp := FLT_exp_monotone emin prec.

Notation canonical_mantissa := (canonical_mantissa prec emax).

Notation bounded := (SpecFloat.bounded prec emax).

Notation valid_binary := (valid_binary prec emax).

(** Basic type used for representing binary FP numbers.
    Note that there is exactly one such object per FP datum. *)

Inductive binary_float :=
  | B754_zero (s : bool)
  | B754_infinity (s : bool)
  | B754_nan : binary_float
  | B754_finite (s : bool) (m : positive) (e : Z) :
    bounded m e = true -> binary_float.

Definition SF2B x :=
  match x as x return valid_binary x = true -> binary_float with
  | S754_finite s m e => B754_finite s m e
  | S754_infinity s => fun _ => B754_infinity s
  | S754_zero s => fun _ => B754_zero s
  | S754_nan => fun _ => B754_nan
  end.

Definition B2SF x :=
  match x with
  | B754_finite s m e _ => S754_finite s m e
  | B754_infinity s => S754_infinity s
  | B754_zero s => S754_zero s
  | B754_nan => S754_nan
  end.

Definition B2R f :=
  match f with
  | B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

Theorem SF2R_B2SF :
  forall x,
  SF2R radix2 (B2SF x) = B2R x.
Proof.
now intros [sx|sx| |sx mx ex Hx].
Qed.

Theorem B2SF_SF2B :
  forall x Hx,
  B2SF (SF2B x Hx) = x.
Proof.
now intros [sx|sx| |sx mx ex] Hx.
Qed.

Theorem valid_binary_B2SF :
  forall x,
  valid_binary (B2SF x) = true.
Proof.
now intros [sx|sx| |sx mx ex Hx].
Qed.

Theorem SF2B_B2SF :
  forall x H,
  SF2B (B2SF x) H = x.
Proof.
intros [sx|sx| |sx mx ex Hx] H ; try easy.
apply f_equal, eqbool_irrelevance.
Qed.

Theorem SF2B_B2SF_valid :
  forall x,
  SF2B (B2SF x) (valid_binary_B2SF x) = x.
Proof.
intros x.
apply SF2B_B2SF.
Qed.

Theorem B2R_SF2B :
  forall x Hx,
  B2R (SF2B x Hx) = SF2R radix2 x.
Proof.
now intros [sx|sx| |sx mx ex] Hx.
Qed.

Theorem match_SF2B :
  forall {T} fz fi fn ff x Hx,
  match SF2B x Hx return T with
  | B754_zero sx => fz sx
  | B754_infinity sx => fi sx
  | B754_nan => fn
  | B754_finite sx mx ex _ => ff sx mx ex
  end =
  match x with
  | S754_zero sx => fz sx
  | S754_infinity sx => fi sx
  | S754_nan => fn
  | S754_finite sx mx ex => ff sx mx ex
  end.
Proof.
now intros T fz fi fn ff [sx|sx| |sx mx ex] Hx.
Qed.

Theorem canonical_canonical_mantissa :
  forall (sx : bool) mx ex,
  canonical_mantissa mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof.
intros sx mx ex H.
assert (Hx := Zeq_bool_eq _ _ H). clear H.
apply sym_eq.
simpl.
pattern ex at 2 ; rewrite <- Hx.
apply (f_equal fexp).
rewrite mag_F2R_Zdigits.
rewrite <- Zdigits_abs.
rewrite Zpos_digits2_pos.
now case sx.
now case sx.
Qed.

Theorem canonical_bounded :
  forall sx mx ex,
  bounded mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof.
intros sx mx ex H.
apply canonical_canonical_mantissa.
now apply andb_prop in H.
Qed.

Lemma emin_lt_emax :
  (emin < emax)%Z.
Proof.
unfold emin.
unfold Prec_gt_0 in prec_gt_0_.
unfold Prec_lt_emax in prec_lt_emax_.
lia.
Qed.

Lemma fexp_emax :
  fexp emax = (emax - prec)%Z.
Proof.
apply Z.max_l.
unfold emin.
unfold Prec_gt_0 in prec_gt_0_.
unfold Prec_lt_emax in prec_lt_emax_.
lia.
Qed.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof.
intros [sx|sx| |sx mx ex Hx] ; try apply generic_format_0.
simpl.
apply generic_format_canonical.
now apply canonical_bounded.
Qed.

Theorem FLT_format_B2R :
  forall x,
  FLT_format radix2 emin prec (B2R x).
Proof with auto with typeclass_instances.
intros x.
apply FLT_format_generic...
apply generic_format_B2R.
Qed.

Theorem B2SF_inj :
  forall x y : binary_float,
  B2SF x = B2SF y ->
  x = y.
Proof.
intros [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy.
(* *)
intros H.
now inversion H.
(* *)
intros H.
now inversion H.
(* *)
intros H.
inversion H.
clear H.
revert Hx.
rewrite H2, H3.
intros Hx.
apply f_equal, eqbool_irrelevance.
Qed.

Definition is_finite_strict f :=
  match f with
  | B754_finite _ _ _ _ => true
  | _ => false
  end.

Definition is_finite_strict_SF f :=
  match f with
  | S754_finite _ _ _ => true
  | _ => false
  end.

Theorem is_finite_strict_B2R :
  forall x,
  B2R x <> 0%R ->
  is_finite_strict x = true.
Proof.
now intros [sx|sx| |sx mx ex Bx] Hx.
Qed.

Theorem is_finite_strict_SF2B :
  forall x Hx,
  is_finite_strict (SF2B x Hx) = is_finite_strict_SF x.
Proof.
now intros [sx|sx| |sx mx ex] Hx.
Qed.

Theorem B2R_inj:
  forall x y : binary_float,
  is_finite_strict x = true ->
  is_finite_strict y = true ->
  B2R x = B2R y ->
  x = y.
Proof.
intros [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy.
simpl.
intros _ _ Heq.
assert (Hs: sx = sy).
(* *)
revert Heq. clear.
case sx ; case sy ; try easy ;
  intros Heq ; apply False_ind ; revert Heq.
apply Rlt_not_eq.
apply Rlt_trans with R0.
now apply F2R_lt_0.
now apply F2R_gt_0.
apply Rgt_not_eq.
apply Rgt_trans with R0.
now apply F2R_gt_0.
now apply F2R_lt_0.
assert (mx = my /\ ex = ey).
(* *)
refine (_ (canonical_unique _ fexp _ _ _ _ Heq)).
rewrite Hs.
now case sy ; intro H ; injection H ; split.
now apply canonical_bounded.
now apply canonical_bounded.
(* *)
revert Hx.
rewrite Hs, (proj1 H), (proj2 H).
intros Hx.
apply f_equal.
apply eqbool_irrelevance.
Qed.

Definition Bsign x :=
  match x with
  | B754_nan => false
  | B754_zero s => s
  | B754_infinity s => s
  | B754_finite s _ _ _ => s
  end.

Definition sign_SF x :=
  match x with
  | S754_nan => false
  | S754_zero s => s
  | S754_infinity s => s
  | S754_finite s _ _ => s
  end.

Theorem Bsign_SF2B :
  forall x H,
  Bsign (SF2B x H) = sign_SF x.
Proof.
now intros [sx|sx| |sx mx ex] H.
Qed.

Definition is_finite f :=
  match f with
  | B754_finite _ _ _ _ => true
  | B754_zero _ => true
  | _ => false
  end.

Definition is_finite_SF f :=
  match f with
  | S754_finite _ _ _ => true
  | S754_zero _ => true
  | _ => false
  end.

Theorem is_finite_SF2B :
  forall x Hx,
  is_finite (SF2B x Hx) = is_finite_SF x.
Proof.
now intros [| | |].
Qed.

Theorem is_finite_SF_B2SF :
  forall x,
  is_finite_SF (B2SF x) = is_finite x.
Proof.
now intros [| | |].
Qed.

Theorem B2R_Bsign_inj:
  forall x y : binary_float,
    is_finite x = true ->
    is_finite y = true ->
    B2R x = B2R y ->
    Bsign x = Bsign y ->
    x = y.
Proof.
intros. destruct x, y; try (apply B2R_inj; now eauto).
- simpl in H2. congruence.
- symmetry in H1. apply Rmult_integral in H1.
  destruct H1. apply (eq_IZR _ 0) in H1. destruct s0; discriminate H1.
  simpl in H1. pose proof (bpow_gt_0 radix2 e).
  rewrite H1 in H3. apply Rlt_irrefl in H3. destruct H3.
- apply Rmult_integral in H1.
  destruct H1. apply (eq_IZR _ 0) in H1. destruct s; discriminate H1.
  simpl in H1. pose proof (bpow_gt_0 radix2 e).
  rewrite H1 in H3. apply Rlt_irrefl in H3. destruct H3.
Qed.

Definition is_nan f :=
  match f with
  | B754_nan => true
  | _ => false
  end.

Definition is_nan_SF f :=
  match f with
  | S754_nan => true
  | _ => false
  end.

Theorem is_nan_SF2B :
  forall x Hx,
  is_nan (SF2B x Hx) = is_nan_SF x.
Proof.
now intros [| | |].
Qed.

Theorem is_nan_SF_B2SF :
  forall x,
  is_nan_SF (B2SF x) = is_nan x.
Proof.
now intros [| | |].
Qed.

Definition erase (x : binary_float) : binary_float.
Proof.
destruct x as [s|s| |s m e H].
- exact (B754_zero s).
- exact (B754_infinity s).
- exact B754_nan.
- apply (B754_finite s m e).
  destruct bounded.
  apply eq_refl.
  exact H.
Defined.

Theorem erase_correct :
  forall x, erase x = x.
Proof.
destruct x as [s|s| |s m e H] ; try easy ; simpl.
- apply f_equal, eqbool_irrelevance.
Qed.

(** Opposite *)

Definition Bopp x :=
  match x with
  | B754_nan => x
  | B754_infinity sx => B754_infinity (negb sx)
  | B754_finite sx mx ex Hx => B754_finite (negb sx) mx ex Hx
  | B754_zero sx => B754_zero (negb sx)
  end.

Theorem Bopp_involutive :
  forall x,
  Bopp (Bopp x) = x.
Proof.
now intros [sx|sx| |sx mx ex Hx] ; simpl ; try rewrite Bool.negb_involutive.
Qed.

Theorem B2R_Bopp :
  forall x,
  B2R (Bopp x) = (- B2R x)%R.
Proof.
intros [sx|sx| |sx mx ex Hx]; apply sym_eq ; try apply Ropp_0.
simpl.
rewrite <- F2R_opp.
now case sx.
Qed.

Theorem is_nan_Bopp :
  forall x,
  is_nan (Bopp x) = is_nan x.
Proof.
now intros [| | |].
Qed.

Theorem is_finite_Bopp :
  forall x,
  is_finite (Bopp x) = is_finite x.
Proof.
now intros [| | |].
Qed.

Theorem is_finite_strict_Bopp :
  forall x,
  is_finite_strict (Bopp x) = is_finite_strict x.
Proof.
now intros [| | |].
Qed.

Lemma Bsign_Bopp :
  forall x, is_nan x = false -> Bsign (Bopp x) = negb (Bsign x).
Proof. now intros [s|s| |s m e H]. Qed.

(** Absolute value *)

Definition Babs (x : binary_float) : binary_float :=
  match x with
  | B754_nan => x
  | B754_infinity sx => B754_infinity false
  | B754_finite sx mx ex Hx => B754_finite false mx ex Hx
  | B754_zero sx => B754_zero false
  end.

Theorem B2R_Babs :
  forall x,
  B2R (Babs x) = Rabs (B2R x).
Proof.
intros [sx|sx| |sx mx ex Hx]; apply sym_eq ; try apply Rabs_R0.
simpl. rewrite <- F2R_abs. now destruct sx.
Qed.

Theorem is_nan_Babs :
  forall x,
  is_nan (Babs x) = is_nan x.
Proof.
now intros [| | |].
Qed.

Theorem is_finite_Babs :
  forall x,
  is_finite (Babs x) = is_finite x.
Proof.
now intros [| | |].
Qed.

Theorem is_finite_strict_Babs :
  forall x,
  is_finite_strict (Babs x) = is_finite_strict x.
Proof.
now intros [| | |].
Qed.

Theorem Bsign_Babs :
  forall x,
  Bsign (Babs x) = false.
Proof.
now intros [| | |].
Qed.

Theorem Babs_idempotent :
  forall (x: binary_float),
  Babs (Babs x) = Babs x.
Proof.
now intros [sx|sx| |sx mx ex Hx].
Qed.

Theorem Babs_Bopp :
  forall x,
  Babs (Bopp x) = Babs x.
Proof.
now intros [| | |].
Qed.

(** Comparison

[Some c] means ordered as per [c]; [None] means unordered. *)

Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  SFcompare (B2SF f1) (B2SF f2).

Theorem Bcompare_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bcompare f1 f2 = Some (Rcompare (B2R f1) (B2R f2)).
Proof.
assert (Hb: forall m1 e1 m2 e2, bounded m1 e1 = true -> bounded m2 e2 = true -> (e1 < e2)%Z ->
  (F2R (Float radix2 (Zpos m1) e1) < F2R (Float radix2 (Zpos m2) e2))%R).
{ intros m1 e1 m2 e2 B1 B2 He.
  apply (lt_cexp_pos radix2 fexp).
  now apply F2R_gt_0.
  rewrite <- (canonical_bounded false _ _ B1).
  rewrite <- (canonical_bounded false _ _ B2).
  easy. }
assert (Hc: forall m1 e1 m2 e2, bounded m1 e1 = true -> bounded m2 e2 = true ->
  Rcompare (F2R (Float radix2 (Zpos m1) e1)) (F2R (Float radix2 (Zpos m2) e2)) =
  match Z.compare e1 e2 with Eq => Z.compare (Zpos m1) (Zpos m2) | Lt => Lt | Gt => Gt end).
{ intros m1 e1 m2 e2 B1 B2.
  case Zcompare_spec ; intros He.
  + apply Rcompare_Lt.
    now apply Hb.
  + now rewrite He, Rcompare_F2R.
  + apply Rcompare_Gt.
    now apply Hb. }
intros [s1|[|]| |[|] m1 e1 B1] ; try easy ;
  intros [s2|[|]| |[|] m2 e2 B2] ; try easy ;
  intros _ _ ; apply (f_equal Some), eq_sym.
- now apply Rcompare_Eq.
- apply Rcompare_Gt.
  now apply F2R_lt_0.
- apply Rcompare_Lt.
  now apply F2R_gt_0.
- apply Rcompare_Lt.
  now apply F2R_lt_0.
- unfold B2R.
  rewrite 2!F2R_cond_Zopp.
  rewrite Rcompare_opp.
  rewrite Hc by easy.
  rewrite (Z.compare_antisym e1), (Z.compare_antisym (Zpos m1)).
  now case Z.compare.
- apply Rcompare_Lt.
  apply Rlt_trans with 0%R.
  now apply F2R_lt_0.
  now apply F2R_gt_0.
- apply Rcompare_Gt.
  now apply F2R_gt_0.
- apply Rcompare_Gt.
  apply Rlt_trans with 0%R.
  now apply F2R_lt_0.
  now apply F2R_gt_0.
- now apply Hc.
Qed.

Theorem Bcompare_swap :
  forall x y,
  Bcompare y x = match Bcompare x y with Some c => Some (CompOpp c) | None => None end.
Proof.
  intros.
  unfold Bcompare.
  destruct x as [ ? | [] | | [] mx ex Bx ];
  destruct y as [ ? | [] | | [] my ey By ]; simpl; try easy.
- rewrite <- (Zcompare_antisym ex ey). destruct (ex ?= ey)%Z; try easy.
  now rewrite (Pcompare_antisym mx my).
- rewrite <- (Zcompare_antisym ex ey). destruct (ex ?= ey)%Z; try easy.
  now rewrite Pcompare_antisym.
Qed.

Definition Beqb (f1 f2 : binary_float) : bool := SFeqb (B2SF f1) (B2SF f2).

Theorem Beqb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Beqb f1 f2 = Req_bool (B2R f1) (B2R f2).
Proof.
intros f1 f2 F1 F2.
generalize (Bcompare_correct _ _ F1 F2).
unfold Beqb, SFeqb, Bcompare.
intros ->.
case Rcompare_spec; intro H; case Req_bool_spec; intro H'; try reflexivity; lra.
Qed.

Theorem Beqb_refl :
  forall f, Beqb f f = negb (is_nan f).
Proof.
intros f.
generalize (fun H => Beqb_correct f f H H).
destruct f as [s|[|]| |s m e H] ; try easy.
intros ->. 2: easy.
now apply Req_bool_true.
Qed.

Definition Bltb (f1 f2 : binary_float) : bool := SFltb (B2SF f1) (B2SF f2).

Theorem Bltb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bltb f1 f2 = Rlt_bool (B2R f1) (B2R f2).
Proof.
intros f1 f2 F1 F2.
generalize (Bcompare_correct _ _ F1 F2).
unfold Bltb, SFltb, Bcompare.
intros ->.
case Rcompare_spec; intro H; case Rlt_bool_spec; intro H'; try reflexivity; lra.
Qed.

Definition Bleb (f1 f2 : binary_float) : bool := SFleb (B2SF f1) (B2SF f2).

Theorem Bleb_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bleb f1 f2 = Rle_bool (B2R f1) (B2R f2).
Proof.
intros f1 f2 F1 F2.
generalize (Bcompare_correct _ _ F1 F2).
unfold Bleb, SFleb, Bcompare.
intros ->.
case Rcompare_spec; intro H; case Rle_bool_spec; intro H'; try reflexivity; lra.
Qed.

Theorem bounded_le_emax_minus_prec :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex)
   <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof.
clear prec_lt_emax_.
intros mx ex Hx.
apply Rle_trans with ((bpow radix2 (Zdigits radix2 (Z.pos mx)) - 1) * bpow radix2 ex)%R.
- apply Rmult_le_compat_r.
  apply bpow_ge_0.
  rewrite <- IZR_Zpower by apply Zdigits_ge_0.
  rewrite <- minus_IZR.
  apply IZR_le.
  apply Z.lt_le_pred.
  rewrite <- (Z.abs_eq (Z.pos mx)) by easy.
  apply Zdigits_correct.
- destruct (andb_prop _ _ Hx) as [H1 H2].
  apply Rle_trans with (bpow radix2 (ex + prec) - bpow radix2 ex)%R.
  { rewrite Rmult_minus_distr_r, Rmult_1_l, <- bpow_plus.
    apply Rplus_le_compat_r.
    apply bpow_le.
    apply Zeq_bool_eq in H1.
    rewrite Zpos_digits2_pos in H1.
    unfold fexp, FLT_exp in H1.
    clear -H1 ; lia. }
  replace emax with (emax - prec - ex + (ex + prec))%Z at 1 by ring.
  replace (emax - prec)%Z with (emax - prec - ex + ex)%Z at 2 by ring.
  do 2 rewrite (bpow_plus _ (emax - prec - ex)).
  rewrite <- Rmult_minus_distr_l.
  rewrite <- (Rmult_1_l (_ - _)) at 1.
  apply Rmult_le_compat_r.
  + apply Rle_0_minus, bpow_le.
    unfold Prec_gt_0 in prec_gt_0_.
    clear -prec_gt_0_ ; lia.
  + apply (bpow_le radix2 0).
    apply Zle_minus_le_0.
    now apply Zle_bool_imp_le.
Qed.

Theorem bounded_lt_emax :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R.
Proof.
intros mx ex Hx.
destruct (andb_prop _ _ Hx) as (H1,H2).
generalize (Zeq_bool_eq _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
generalize (mag_F2R_Zdigits radix2 (Zpos mx) ex).
destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex).
unfold mag_val.
intros H.
apply Rlt_le_trans with (bpow radix2 e').
change (Zpos mx) with (Z.abs (Zpos mx)).
rewrite F2R_Zabs.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0.
apply bpow_le.
rewrite H. 2: discriminate.
revert H1. clear -H2.
rewrite Zpos_digits2_pos.
unfold fexp, FLT_exp.
intros ; lia.
Qed.

(* needs prec_lt_emax_, so backward-incompatible
Theorem bounded_le_emax_minus_prec :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex)
   <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof.
intros mx ex Bx.
rewrite <- fexp_emax.
rewrite <- pred_bpow.
apply pred_ge_gt.
- exact fexp_correct.
- apply generic_format_canonical.
  now apply (canonical_bounded false).
- apply generic_format_FLT_bpow.
  exact prec_gt_0_.
  apply Zlt_le_weak, emin_lt_emax.
- now apply bounded_lt_emax.
Qed.
*)

Theorem bounded_ge_emin :
  forall mx ex,
  bounded mx ex = true ->
  (bpow radix2 emin <= F2R (Float radix2 (Zpos mx) ex))%R.
Proof.
intros mx ex Hx.
destruct (andb_prop _ _ Hx) as [H1 _].
apply Zeq_bool_eq in H1.
generalize (mag_F2R_Zdigits radix2 (Zpos mx) ex).
destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as [e' Ex].
unfold mag_val.
intros H.
assert (H0 : Zpos mx <> 0%Z) by easy.
rewrite Rabs_pos_eq in Ex by now apply F2R_ge_0.
refine (Rle_trans _ _ _ _ (proj1 (Ex _))).
2: now apply F2R_neq_0.
apply bpow_le.
rewrite H by easy.
revert H1.
rewrite Zpos_digits2_pos.
generalize (Zdigits radix2 (Zpos mx)) (Zdigits_gt_0 radix2 (Zpos mx) H0).
unfold fexp, FLT_exp.
clear -prec_gt_0_.
unfold Prec_gt_0 in prec_gt_0_.
intros ; lia.
Qed.

Theorem abs_B2R_le_emax_minus_prec :
  forall x,
  (Rabs (B2R x) <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; simpl ;
  [rewrite Rabs_R0 ; apply Rle_0_minus, bpow_le ;
   revert prec_gt_0_; unfold Prec_gt_0; lia..|].
rewrite <- F2R_Zabs, abs_cond_Zopp.
now apply bounded_le_emax_minus_prec.
Qed.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; simpl ; try ( rewrite Rabs_R0 ; apply bpow_gt_0 ).
rewrite <- F2R_Zabs, abs_cond_Zopp.
now apply bounded_lt_emax.
Qed.

Theorem abs_B2R_ge_emin :
  forall x,
  is_finite_strict x = true ->
  (bpow radix2 emin <= Rabs (B2R x))%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; simpl ; try discriminate.
intros; case sx; simpl.
- unfold F2R; simpl; rewrite Rabs_mult, <-abs_IZR; simpl.
  rewrite Rabs_pos_eq; [|apply bpow_ge_0].
  now apply bounded_ge_emin.
- unfold F2R; simpl; rewrite Rabs_mult, <-abs_IZR; simpl.
  rewrite Rabs_pos_eq; [|apply bpow_ge_0].
  now apply bounded_ge_emin.
Qed.

Theorem bounded_canonical_lt_emax :
  forall mx ex,
  canonical radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R ->
  bounded mx ex = true.
Proof.
intros mx ex Cx Bx.
apply andb_true_intro.
split.
unfold canonical_mantissa.
unfold canonical, Fexp in Cx.
rewrite Cx at 2.
rewrite Zpos_digits2_pos.
unfold cexp.
rewrite mag_F2R_Zdigits. 2: discriminate.
now apply -> Zeq_is_eq_bool.
apply Zle_bool_true.
unfold canonical, Fexp in Cx.
rewrite Cx.
unfold cexp, fexp, FLT_exp.
destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex). simpl.
apply Z.max_lub.
cut (e' - 1 < emax)%Z. clear ; lia.
apply lt_bpow with radix2.
apply Rle_lt_trans with (2 := Bx).
change (Zpos mx) with (Z.abs (Zpos mx)).
rewrite F2R_Zabs.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0.
apply Z.max_l_iff, fexp_emax.
Qed.

(** Truncation *)

Theorem shr_m_shr_record_of_loc :
  forall m l,
  shr_m (shr_record_of_loc m l) = m.
Proof.
now intros m [|[| |]].
Qed.

Theorem loc_of_shr_record_of_loc :
  forall m l,
  loc_of_shr_record (shr_record_of_loc m l) = l.
Proof.
now intros m [|[| |]].
Qed.

Lemma inbetween_shr_1 :
  forall x mrs e,
  (0 <= shr_m mrs)%Z ->
  inbetween_float radix2 (shr_m mrs) e x (loc_of_shr_record mrs) ->
  inbetween_float radix2 (shr_m (shr_1 mrs)) (e + 1) x (loc_of_shr_record (shr_1 mrs)).
Proof.
intros x mrs e Hm Hl.
refine (_ (new_location_even_correct (F2R (Float radix2 (shr_m (shr_1 mrs)) (e + 1))) (bpow radix2 e) 2 _ _ _ x (if shr_r (shr_1 mrs) then 1 else 0) (loc_of_shr_record mrs) _ _)) ; try easy.
2: apply bpow_gt_0.
2: now case (shr_r (shr_1 mrs)) ; split.
change 2%R with (bpow radix2 1).
rewrite <- bpow_plus.
rewrite (Zplus_comm 1), <- (F2R_bpow radix2 (e + 1)).
unfold inbetween_float, F2R. simpl.
rewrite plus_IZR, Rmult_plus_distr_r.
replace (Bracket.new_location_even 2 (if shr_r (shr_1 mrs) then 1%Z else 0%Z) (loc_of_shr_record mrs)) with (loc_of_shr_record (shr_1 mrs)).
easy.
clear -Hm.
destruct mrs as (m, r, s).
now destruct m as [|[m|m|]|m] ; try (now elim Hm) ; destruct r as [|] ; destruct s as [|].
rewrite (F2R_change_exp radix2 e).
2: apply Zle_succ.
unfold F2R. simpl.
rewrite <- 2!Rmult_plus_distr_r, <- 2!plus_IZR.
rewrite Zplus_assoc.
replace (shr_m (shr_1 mrs) * 2 ^ (e + 1 - e) + (if shr_r (shr_1 mrs) then 1%Z else 0%Z))%Z with (shr_m mrs).
exact Hl.
ring_simplify (e + 1 - e)%Z.
change (2^1)%Z with 2%Z.
rewrite Zmult_comm.
clear -Hm.
destruct mrs as (m, r, s).
now destruct m as [|[m|m|]|m] ; try (now elim Hm) ; destruct r as [|] ; destruct s as [|].
Qed.

Theorem inbetween_shr :
  forall x m e l n,
  (0 <= m)%Z ->
  inbetween_float radix2 m e x l ->
  let '(mrs, e') := shr (shr_record_of_loc m l) e n in
  inbetween_float radix2 (shr_m mrs) e' x (loc_of_shr_record mrs).
Proof.
intros x m e l n Hm Hl.
destruct n as [|n|n].
now destruct l as [|[| |]].
2: now destruct l as [|[| |]].
unfold shr.
rewrite iter_pos_nat.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
induction (nat_of_P n).
simpl.
rewrite Zplus_0_r.
now destruct l as [|[| |]].
rewrite iter_nat_S.
rewrite inj_S.
unfold Z.succ.
rewrite Zplus_assoc.
revert IHn0.
apply inbetween_shr_1.
clear -Hm.
induction n0.
now destruct l as [|[| |]].
rewrite iter_nat_S.
revert IHn0.
generalize (iter_nat shr_1 n0 (shr_record_of_loc m l)).
clear.
intros (m, r, s) Hm.
now destruct m as [|[m|m|]|m] ; try (now elim Hm) ; destruct r as [|] ; destruct s as [|].
Qed.

Lemma le_shr1_le :
  forall mrs, (0 <= shr_m mrs)%Z ->
  (0 <= 2 * shr_m (shr_1 mrs) <= shr_m mrs)%Z /\
  (shr_m mrs < 2 * (shr_m (shr_1 mrs) + 1))%Z.
Proof.
  destruct mrs as [m r s]. simpl.
  destruct m as [| p | p]; [simpl; lia | intros _ | intros; easy].
  destruct p; simpl; [| | lia].
  - rewrite Pos2Z.inj_xO, Pos2Z.inj_xI. lia.
  - rewrite Pos2Z.inj_xO. lia.
Qed.

Lemma le_shr_le :
  forall mrs e n,
  (0 <= shr_m mrs)%Z -> (0 <= n)%Z ->
  (0 <= 2 ^ n * shr_m (fst (shr mrs e n)) <= shr_m mrs)%Z /\
  (shr_m mrs < 2 ^ n * (shr_m (fst (shr mrs e n)) + 1))%Z.
Proof.
  intros mrs e n Hmrs.
  destruct n as [| n | n ];
    [intros _; simpl; now destruct (shr_m mrs); simpl; lia | intro Hn | lia].
  unfold shr.
  rewrite iter_pos_nat. rewrite <-!(positive_nat_Z n). simpl fst.
  induction (nat_of_P n) as [| n' IHn']; [simpl; destruct (shr_m mrs); simpl; lia |].
  rewrite !Nat2Z.inj_succ. rewrite Z.pow_succ_r; [| apply Zle_0_nat].

  rewrite iter_nat_S. rewrite (Z.mul_comm 2%Z _), <-Z.mul_assoc.
  destruct IHn' as [[IHn'1 IHn'2] IHn'3]. apply Z.mul_nonneg_cancel_l in IHn'1; [| lia].
  repeat split;
    [| transitivity (2 ^ Z.of_nat n' * shr_m (iter_nat shr_1 n' mrs))%Z; [| auto] |].
  - apply Z.mul_nonneg_nonneg; [lia |]. now apply le_shr1_le.
  - apply Z.mul_le_mono_nonneg_l; [lia |]. now apply le_shr1_le.
  - apply Z.lt_le_trans with
      (2 ^ Z.of_nat n' * (shr_m (iter_nat shr_1 n' mrs) + 1))%Z; [assumption |].
    rewrite <-Z.mul_assoc. apply Z.mul_le_mono_nonneg_l; [lia |].
    apply Ztac.Zlt_le_add_1. now apply le_shr1_le.
Qed.

Lemma shr_limit :
  forall mrs e n,
  ((0 < shr_m mrs)%Z \/ shr_m mrs = 0%Z /\ (shr_r mrs || shr_s mrs = true)%bool) ->
  (shr_m mrs < radix2 ^ (n - 1))%Z ->
  fst (shr mrs e n) = {| shr_m := 0%Z; shr_r := false; shr_s := true |}.
Proof.
  intros mrs e n Hmrs0. set (n' := (n - 1)%Z). replace n with (n' + 1)%Z; [| lia].
  destruct n' as [| p | p ].
  - simpl. destruct Hmrs0 as [Hmrs0 | Hmrs0]; [lia | intros _].
    destruct mrs as [m r s]. simpl in Hmrs0. destruct Hmrs0 as [Hmrs00 Hmrs01].
    rewrite Hmrs00. simpl. now rewrite Hmrs01.
  - intros Hmrs1. rewrite !Z.add_1_r. rewrite <-Pos2Z.inj_succ. simpl shr.
    rewrite iter_pos_nat. rewrite Pos2Nat.inj_succ. simpl iter_nat.
    rewrite <-(positive_nat_Z p) in Hmrs1. rewrite <-(Pos2Nat.id p) at 2.
    revert Hmrs1. revert Hmrs0. revert mrs.
    induction (nat_of_P p) as [| n'' IHn''].
    + simpl in *. intros mrs [Hmrs0 | [Hmrs00 Hmrs01]] Hmrs1; [lia |].
      destruct mrs as [m r s]. simpl in Hmrs00, Hmrs01, Hmrs1. rewrite Hmrs00.
      simpl. now rewrite Hmrs01.
    + intros mrs Hmrs0 Hmrs1. simpl iter_nat.
      destruct (le_shr1_le mrs) as [[Hmrs'0 Hmrs'1] Hmrs'2]; [destruct Hmrs0; lia |].
      set (mrs' := shr_1 mrs). apply IHn''.
      * case (0 <? shr_m (shr_1 mrs))%Z eqn:Hmrs'3;
         [apply Zlt_is_lt_bool in Hmrs'3; now left |].
        fold mrs' in Hmrs'0, Hmrs'1, Hmrs'2, Hmrs'3.
        apply Z.ltb_ge in Hmrs'3. apply Z.mul_nonneg_cancel_l in Hmrs'0; [| easy].
        apply (Z.le_antisymm _ _ Hmrs'3) in Hmrs'0. right. split; [assumption |].
        destruct Hmrs0 as [Hmrs0 | [Hmrs00 Hmrs01]].
        -- rewrite Hmrs'0 in Hmrs'2. simpl in Hmrs'2.
           assert (Hmrs2 : shr_m mrs = 1%Z) by lia. destruct mrs as [m r s].
           simpl in Hmrs2. unfold mrs'. now rewrite Hmrs2.
        -- destruct mrs as [m r s]. simpl in Hmrs00, Hmrs01. unfold mrs'.
           now rewrite Hmrs00.
      * simpl Z.of_nat in Hmrs1. unfold mrs'. rewrite Zpos_P_of_succ_nat in Hmrs1.
        rewrite Z.pow_succ_r in Hmrs1; [| lia]. apply (Z.le_lt_trans _ _ _ Hmrs'1) in Hmrs1.
        apply Z.mul_lt_mono_pos_l in Hmrs1; [assumption | easy].
  - simpl. destruct Hmrs0 as [Hmrs0 | Hmrs0]; lia.
Qed.

Theorem shr_truncate :
  forall f m e l,
  Valid_exp f ->
  (0 <= m)%Z ->
  shr (shr_record_of_loc m l) e (f (Zdigits2 m + e) - e)%Z =
  let '(m', e', l') := truncate radix2 f (m, e, l) in (shr_record_of_loc m' l', e').
Proof.
  intros f m e l Hf Hm. case_eq (truncate radix2 f (m, e, l)). intros (m', e') l'.
  unfold shr_fexp. rewrite Zdigits2_Zdigits. case_eq (f (Zdigits radix2 m + e) - e)%Z.
  - intros He. unfold truncate. rewrite He. simpl. intros H. now inversion H.
  - intros p Hp. assert (He: (e <= f (Zdigits radix2 m + e))%Z); [ clear -Hp; lia |].
    destruct (inbetween_float_ex radix2 m e l) as (x, Hx).
    generalize (inbetween_shr x m e l (f (Zdigits radix2 m + e) - e) Hm Hx)%Z.
    assert (Hx0 : (0 <= x)%R);
     [apply Rle_trans with (F2R (Float radix2 m e));
       [now apply F2R_ge_0
       |exact (proj1 (inbetween_float_bounds _ _ _ _ _ Hx))]
     |].
    case_eq (shr (shr_record_of_loc m l) e (f (Zdigits radix2 m + e) - e))%Z.
    intros mrs e'' H3 H4 H1.
    generalize (truncate_correct radix2 _ x m e l Hx0 Hx (or_introl _ He)).
    rewrite H1. intros (H2,_). rewrite <- Hp, H3.
    assert (e'' = e').
    { change (snd (mrs, e'') = snd (fst (m',e',l'))).  rewrite <- H1, <- H3.
      unfold truncate. now rewrite Hp. }
    rewrite H in H4 |- *. apply (f_equal (fun v => (v, _))).
    destruct (inbetween_float_unique _ _ _ _ _ _ _ H2 H4) as (H5, H6).
    rewrite H5, H6. case mrs. now intros m0 [|] [|].
  - intros p Hp. unfold truncate. rewrite Hp. simpl. intros H. now inversion H.
Qed.

Notation shr_fexp := (shr_fexp prec emax).

Theorem shr_fexp_truncate :
  forall m e l,
  (0 <= m)%Z ->
  shr_fexp m e l =
  let '(m', e', l') := truncate radix2 fexp (m, e, l) in (shr_record_of_loc m' l', e').
Proof.
intros m e l Hm.
case_eq (truncate radix2 fexp (m, e, l)).
intros (m', e') l'.
unfold shr_fexp.
rewrite Zdigits2_Zdigits.
case_eq (fexp (Zdigits radix2 m + e) - e)%Z.
(* *)
intros He.
unfold truncate.
rewrite He.
simpl.
intros H.
now inversion H.
(* *)
intros p Hp.
assert (He: (e <= fexp (Zdigits radix2 m + e))%Z).
clear -Hp ; lia.
destruct (inbetween_float_ex radix2 m e l) as (x, Hx).
generalize (inbetween_shr x m e l (fexp (Zdigits radix2 m + e) - e) Hm Hx).
assert (Hx0 : (0 <= x)%R).
apply Rle_trans with (F2R (Float radix2 m e)).
now apply F2R_ge_0.
exact (proj1 (inbetween_float_bounds _ _ _ _ _ Hx)).
case_eq (shr (shr_record_of_loc m l) e (fexp (Zdigits radix2 m + e) - e)).
intros mrs e'' H3 H4 H1.
generalize (truncate_correct radix2 _ x m e l Hx0 Hx (or_introl _ He)).
rewrite H1.
intros (H2,_).
rewrite <- Hp, H3.
assert (e'' = e').
change (snd (mrs, e'') = snd (fst (m',e',l'))).
rewrite <- H1, <- H3.
unfold truncate.
now rewrite Hp.
rewrite H in H4 |- *.
apply (f_equal (fun v => (v, _))).
destruct (inbetween_float_unique _ _ _ _ _ _ _ H2 H4) as (H5, H6).
rewrite H5, H6.
case mrs.
now intros m0 [|] [|].
(* *)
intros p Hp.
unfold truncate.
rewrite Hp.
simpl.
intros H.
now inversion H.
Qed.

(** Rounding modes *)

Inductive mode := mode_NE | mode_ZR | mode_DN | mode_UP | mode_NA.

Definition round_mode m :=
  match m with
  | mode_NE => ZnearestE
  | mode_ZR => Ztrunc
  | mode_DN => Zfloor
  | mode_UP => Zceil
  | mode_NA => ZnearestA
  end.

Definition choice_mode m sx mx lx :=
  match m with
  | mode_NE => cond_incr (round_N (negb (Z.even mx)) lx) mx
  | mode_ZR => mx
  | mode_DN => cond_incr (round_sign_DN sx lx) mx
  | mode_UP => cond_incr (round_sign_UP sx lx) mx
  | mode_NA => cond_incr (round_N true lx) mx
  end.

Lemma le_choice_mode_le :
  forall m sx mx lx, (mx <= choice_mode m sx mx lx <= mx + 1)%Z.
Proof.
  unfold choice_mode; intros m sx mx lx; case m; simpl; try lia; apply le_cond_incr_le.
Qed.

Lemma round_mode_choice_mode :
  forall md x m l,
  inbetween_int m (Rabs x) l ->
  round_mode md x = cond_Zopp (Rlt_bool x 0) (choice_mode md (Rlt_bool x 0) m l).
Proof.
  destruct md.
  - exact inbetween_int_NE_sign.
  - exact inbetween_int_ZR_sign.
  - exact inbetween_int_DN_sign.
  - exact inbetween_int_UP_sign.
  - exact inbetween_int_NA_sign.
Qed.

Global Instance valid_rnd_round_mode : forall m, Valid_rnd (round_mode m).
Proof.
destruct m ; unfold round_mode ; auto with typeclass_instances.
Qed.

Definition overflow_to_inf m s :=
  match m with
  | mode_NE => true
  | mode_NA => true
  | mode_ZR => false
  | mode_UP => negb s
  | mode_DN => s
  end.

Definition binary_overflow m s :=
  if overflow_to_inf m s then S754_infinity s
  else S754_finite s (Z.to_pos (Zpower 2 prec - 1)%Z) (emax - prec).

Theorem is_nan_binary_overflow :
  forall mode s,
  is_nan_SF (binary_overflow mode s) = false.
Proof.
intros mode s.
unfold binary_overflow.
now destruct overflow_to_inf.
Qed.

Theorem binary_overflow_correct :
  forall m s,
  valid_binary (binary_overflow m s) = true.
Proof.
intros m s.
unfold binary_overflow.
case overflow_to_inf.
easy.
unfold valid_binary, bounded.
rewrite Zle_bool_refl.
rewrite Bool.andb_true_r.
apply Zeq_bool_true.
rewrite Zpos_digits2_pos.
replace (Zdigits radix2 _) with prec.
ring_simplify (prec + (emax - prec))%Z.
apply fexp_emax.
change 2%Z with (radix_val radix2).
assert (H: (0 < radix2 ^ prec - 1)%Z).
  apply Zlt_succ_pred.
  now apply Zpower_gt_1.
rewrite Z2Pos.id by exact H.
apply Zle_antisym.
- apply Z.lt_pred_le.
  apply Zdigits_gt_Zpower.
  rewrite Z.abs_eq by now apply Zlt_le_weak.
  apply Z.lt_le_pred.
  apply Zpower_lt.
  now apply Zlt_le_weak.
  apply Z.lt_pred_l.
- apply Zdigits_le_Zpower.
  rewrite Z.abs_eq by now apply Zlt_le_weak.
  apply Z.lt_pred_l.
Qed.

Definition binary_fit_aux mode sx mx ex :=
  if Zle_bool ex (emax - prec) then S754_finite sx mx ex
  else binary_overflow mode sx.

Theorem binary_fit_aux_correct :
  forall mode sx mx ex,
  canonical_mantissa mx ex = true ->
  let x := SF2R radix2 (S754_finite sx mx ex) in
  let z := binary_fit_aux mode sx mx ex in
  valid_binary z = true /\
  if Rlt_bool (Rabs x) (bpow radix2 emax) then
    SF2R radix2 z = x /\ is_finite_SF z = true /\ sign_SF z = sx
  else
    z = binary_overflow mode sx.
Proof.
intros m sx mx ex Cx.
unfold binary_fit_aux.
simpl.
rewrite F2R_cond_Zopp.
rewrite abs_cond_Ropp.
rewrite Rabs_pos_eq by now apply F2R_ge_0.
destruct Zle_bool eqn:He.
- assert (Hb: bounded mx ex = true).
  { unfold bounded. now rewrite Cx. }
  apply (conj Hb).
  rewrite Rlt_bool_true.
  repeat split.
  apply F2R_cond_Zopp.
  now apply bounded_lt_emax.
- rewrite Rlt_bool_false.
  { repeat split.
    apply binary_overflow_correct. }
  apply Rnot_lt_le.
  intros Hx.
  apply bounded_canonical_lt_emax in Hx.
  revert Hx.
  unfold bounded.
  now rewrite Cx, He.
  now apply (canonical_canonical_mantissa false).
Qed.

Definition binary_round_aux mode sx mx ex lx :=
  let '(mrs', e') := shr_fexp mx ex lx in
  let '(mrs'', e'') := shr_fexp (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact in
  match shr_m mrs'' with
  | Z0 => S754_zero sx
  | Zpos m => binary_fit_aux mode sx m e''
  | _ => S754_nan
  end.

Theorem binary_round_aux_correct' :
  forall mode x mx ex lx,
  (x <> 0)%R ->
  inbetween_float radix2 mx ex (Rabs x) lx ->
  (ex <= cexp radix2 fexp x)%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) mx ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_SF z = true /\ sign_SF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof with auto with typeclass_instances.
intros m x mx ex lx Px Bx Ex z.
unfold binary_round_aux in z.
revert z.
rewrite shr_fexp_truncate.
refine (_ (round_trunc_sign_any_correct' _ _ (round_mode m) (choice_mode m) _ x mx ex lx Bx (or_introl _ Ex))).
rewrite <- cexp_abs in Ex.
refine (_ (truncate_correct_partial' _ fexp _ _ _ _ _ Bx Ex)).
destruct (truncate radix2 fexp (mx, ex, lx)) as ((m1, e1), l1).
rewrite loc_of_shr_record_of_loc, shr_m_shr_record_of_loc.
set (m1' := choice_mode m (Rlt_bool x 0) m1 l1).
intros (H1a,H1b) H1c.
rewrite H1c.
assert (Hm: (m1 <= m1')%Z).
(* . *)
unfold m1', choice_mode, cond_incr.
case m ;
  try apply Z.le_refl ;
  match goal with |- (m1 <= if ?b then _ else _)%Z =>
    case b ; [ apply Zle_succ | apply Z.le_refl ] end.
assert (Hr: Rabs (round radix2 fexp (round_mode m) x) = F2R (Float radix2 m1' e1)).
(* . *)
rewrite <- (Z.abs_eq m1').
rewrite <- (abs_cond_Zopp (Rlt_bool x 0) m1').
rewrite F2R_Zabs.
now apply f_equal.
apply Z.le_trans with (2 := Hm).
apply Zlt_succ_le.
apply gt_0_F2R with radix2 e1.
apply Rle_lt_trans with (1 := Rabs_pos x).
exact (proj2 (inbetween_float_bounds _ _ _ _ _ H1a)).
(* . *)
assert (Br: inbetween_float radix2 m1' e1 (Rabs (round radix2 fexp (round_mode m) x)) loc_Exact).
now apply inbetween_Exact.
destruct m1' as [|m1'|m1'].
(* . m1' = 0 *)
rewrite shr_fexp_truncate. 2: apply Z.le_refl.
generalize (truncate_0 radix2 fexp e1 loc_Exact).
destruct (truncate radix2 fexp (Z0, e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros Hm2.
rewrite Hm2.
repeat split.
rewrite Rlt_bool_true.
repeat split.
apply sym_eq.
case Rlt_bool ; apply F2R_0.
rewrite <- F2R_Zabs, abs_cond_Zopp, F2R_0.
apply bpow_gt_0.
(* . 0 < m1' *)
assert (He: (e1 <= fexp (Zdigits radix2 (Zpos m1') + e1))%Z).
rewrite <- mag_F2R_Zdigits, <- Hr, mag_abs.
2: discriminate.
rewrite H1b.
rewrite cexp_abs.
fold (cexp radix2 fexp (round radix2 fexp (round_mode m) x)).
apply cexp_round_ge...
rewrite H1c.
case (Rlt_bool x 0).
apply Rlt_not_eq.
now apply F2R_lt_0.
apply Rgt_not_eq.
now apply F2R_gt_0.
refine (_ (truncate_correct_partial _ _ _ _ _ _ _ Br He)).
2: now rewrite Hr ; apply F2R_gt_0.
refine (_ (truncate_correct_format radix2 fexp (Zpos m1') e1 _ _ He)).
2: discriminate.
rewrite shr_fexp_truncate. 2: easy.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0.
destruct (binary_fit_aux_correct m (Rlt_bool x 0) m2 e2) as [H5 H6].
  apply Zeq_bool_true.
  rewrite Zpos_digits2_pos.
  rewrite <- mag_F2R_Zdigits by easy.
  now rewrite <- H3.
apply (conj H5).
revert H6.
simpl.
rewrite 2!F2R_cond_Zopp.
now rewrite <- H3.
elim Rgt_not_eq with (2 := H3).
apply Rlt_trans with R0.
now apply F2R_lt_0.
now apply F2R_gt_0.
rewrite <- Hr.
apply generic_format_abs...
apply generic_format_round...
(* . not m1' < 0 *)
elim Rgt_not_eq with (2 := Hr).
apply Rlt_le_trans with R0.
now apply F2R_lt_0.
apply Rabs_pos.
(* *)
now apply Rabs_pos_lt.
(* all the modes are valid *)
clear. case m.
exact inbetween_int_NE_sign.
exact inbetween_int_ZR_sign.
exact inbetween_int_DN_sign.
exact inbetween_int_UP_sign.
exact inbetween_int_NA_sign.
(* *)
apply inbetween_float_bounds in Bx.
apply Zlt_succ_le.
eapply gt_0_F2R.
apply Rle_lt_trans with (2 := proj2 Bx).
apply Rabs_pos.
Qed.

Theorem binary_round_aux_correct :
  forall mode x mx ex lx,
  inbetween_float radix2 (Zpos mx) ex (Rabs x) lx ->
  (ex <= fexp (Zdigits radix2 (Zpos mx) + ex))%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) (Zpos mx) ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_SF z = true /\ sign_SF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof with auto with typeclass_instances.
intros m x mx ex lx Bx Ex z.
unfold binary_round_aux in z.
revert z.
rewrite shr_fexp_truncate. 2: easy.
refine (_ (round_trunc_sign_any_correct _ _ (round_mode m) (choice_mode m) _ x (Zpos mx) ex lx Bx (or_introl _ Ex))).
refine (_ (truncate_correct_partial _ _ _ _ _ _ _ Bx Ex)).
destruct (truncate radix2 fexp (Zpos mx, ex, lx)) as ((m1, e1), l1).
rewrite loc_of_shr_record_of_loc, shr_m_shr_record_of_loc.
set (m1' := choice_mode m (Rlt_bool x 0) m1 l1).
intros (H1a,H1b) H1c.
rewrite H1c.
assert (Hm: (m1 <= m1')%Z).
(* . *)
unfold m1', choice_mode, cond_incr.
case m ;
  try apply Z.le_refl ;
  match goal with |- (m1 <= if ?b then _ else _)%Z =>
    case b ; [ apply Zle_succ | apply Z.le_refl ] end.
assert (Hr: Rabs (round radix2 fexp (round_mode m) x) = F2R (Float radix2 m1' e1)).
(* . *)
rewrite <- (Z.abs_eq m1').
rewrite <- (abs_cond_Zopp (Rlt_bool x 0) m1').
rewrite F2R_Zabs.
now apply f_equal.
apply Z.le_trans with (2 := Hm).
apply Zlt_succ_le.
apply gt_0_F2R with radix2 e1.
apply Rle_lt_trans with (1 := Rabs_pos x).
exact (proj2 (inbetween_float_bounds _ _ _ _ _ H1a)).
(* . *)
assert (Br: inbetween_float radix2 m1' e1 (Rabs (round radix2 fexp (round_mode m) x)) loc_Exact).
now apply inbetween_Exact.
destruct m1' as [|m1'|m1'].
(* . m1' = 0 *)
rewrite shr_fexp_truncate. 2: apply Z.le_refl.
generalize (truncate_0 radix2 fexp e1 loc_Exact).
destruct (truncate radix2 fexp (Z0, e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros Hm2.
rewrite Hm2.
repeat split.
rewrite Rlt_bool_true.
repeat split.
apply sym_eq.
case Rlt_bool ; apply F2R_0.
rewrite <- F2R_Zabs, abs_cond_Zopp, F2R_0.
apply bpow_gt_0.
(* . 0 < m1' *)
assert (He: (e1 <= fexp (Zdigits radix2 (Zpos m1') + e1))%Z).
rewrite <- mag_F2R_Zdigits, <- Hr, mag_abs.
2: discriminate.
rewrite H1b.
rewrite cexp_abs.
fold (cexp radix2 fexp (round radix2 fexp (round_mode m) x)).
apply cexp_round_ge...
rewrite H1c.
case (Rlt_bool x 0).
apply Rlt_not_eq.
now apply F2R_lt_0.
apply Rgt_not_eq.
now apply F2R_gt_0.
refine (_ (truncate_correct_partial _ _ _ _ _ _ _ Br He)).
2: now rewrite Hr ; apply F2R_gt_0.
refine (_ (truncate_correct_format radix2 fexp (Zpos m1') e1 _ _ He)).
2: discriminate.
rewrite shr_fexp_truncate. 2: easy.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0.
destruct (binary_fit_aux_correct m (Rlt_bool x 0) m2 e2) as [H5 H6].
  apply Zeq_bool_true.
  rewrite Zpos_digits2_pos.
  rewrite <- mag_F2R_Zdigits by easy.
  now rewrite <- H3.
apply (conj H5).
revert H6.
simpl.
rewrite 2!F2R_cond_Zopp.
now rewrite <- H3.
elim Rgt_not_eq with (2 := H3).
apply Rlt_trans with R0.
now apply F2R_lt_0.
now apply F2R_gt_0.
rewrite <- Hr.
apply generic_format_abs...
apply generic_format_round...
(* . not m1' < 0 *)
elim Rgt_not_eq with (2 := Hr).
apply Rlt_le_trans with R0.
now apply F2R_lt_0.
apply Rabs_pos.
(* *)
apply Rlt_le_trans with (2 := proj1 (inbetween_float_bounds _ _ _ _ _ Bx)).
now apply F2R_gt_0.
(* all the modes are valid *)
clear. case m.
exact inbetween_int_NE_sign.
exact inbetween_int_ZR_sign.
exact inbetween_int_DN_sign.
exact inbetween_int_UP_sign.
exact inbetween_int_NA_sign.
Qed.

(** Multiplication *)

Lemma Bmult_correct_aux :
  forall m sx mx ex (Hx : bounded mx ex = true) sy my ey (Hy : bounded my ey = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  let z := binary_round_aux m (xorb sx sy) (Zpos (mx * my)) (ex + ey) loc_Exact in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (x * y))) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode m) (x * y) /\
    is_finite_SF z = true /\ sign_SF z = xorb sx sy
  else
    z = binary_overflow m (xorb sx sy).
Proof.
intros m sx mx ex Hx sy my ey Hy x y.
unfold x, y.
rewrite <- F2R_mult.
simpl.
replace (xorb sx sy) with (Rlt_bool (F2R (Float radix2 (cond_Zopp sx (Zpos mx) * cond_Zopp sy (Zpos my)) (ex + ey))) 0).
apply binary_round_aux_correct.
constructor.
rewrite <- F2R_abs.
apply F2R_eq.
rewrite Zabs_Zmult.
now rewrite 2!abs_cond_Zopp.
(* *)
change (Zpos (mx * my)) with (Zpos mx * Zpos my)%Z.
assert (forall m e, bounded m e = true -> fexp (Zdigits radix2 (Zpos m) + e) = e)%Z.
clear. intros m e Hb.
destruct (andb_prop _ _ Hb) as (H,_).
apply Zeq_bool_eq.
now rewrite <- Zpos_digits2_pos.
generalize (H _ _ Hx) (H _ _ Hy).
clear x y sx sy Hx Hy H.
unfold fexp, FLT_exp.
refine (_ (Zdigits_mult_ge radix2 (Zpos mx) (Zpos my) _ _)) ; try discriminate.
refine (_ (Zdigits_gt_0 radix2 (Zpos mx) _) (Zdigits_gt_0 radix2 (Zpos my) _)) ; try discriminate.
generalize (Zdigits radix2 (Zpos mx)) (Zdigits radix2 (Zpos my)) (Zdigits radix2 (Zpos mx * Zpos my)).
intros dx dy dxy Hx Hy Hxy.
unfold emin.
generalize (prec_lt_emax prec emax).
lia.
(* *)
case sx ; case sy.
apply Rlt_bool_false.
now apply F2R_ge_0.
apply Rlt_bool_true.
now apply F2R_lt_0.
apply Rlt_bool_true.
now apply F2R_lt_0.
apply Rlt_bool_false.
now apply F2R_ge_0.
Qed.

Definition Bmult m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity _, B754_zero _ => B754_nan
  | B754_zero _, B754_infinity _ => B754_nan
  | B754_finite sx _ _ _, B754_zero sy => B754_zero (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_zero (xorb sx sy)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    SF2B _ (proj1 (Bmult_correct_aux m sx mx ex Hx sy my ey Hy))
  end.

(* TODO: lemme d'equivalence *)

Theorem Bmult_correct :
  forall m x y,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x * B2R y))) (bpow radix2 emax) then
    B2R (Bmult m x y) = round radix2 fexp (round_mode m) (B2R x * B2R y) /\
    is_finite (Bmult m x y) = andb (is_finite x) (is_finite y) /\
    (is_nan (Bmult m x y) = false ->
      Bsign (Bmult m x y) = xorb (Bsign x) (Bsign y))
  else
    B2SF (Bmult m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ;
  try ( rewrite ?Rmult_0_r, ?Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ simpl ; try easy ; now rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan | apply bpow_gt_0 | now auto with typeclass_instances ] ).
simpl.
case Bmult_correct_aux.
intros H1.
case Rlt_bool.
intros (H2, (H3, H4)).
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
rewrite Bsign_SF2B. auto.
intros H2.
now rewrite B2SF_SF2B.
Qed.

(** Normalization and rounding *)

Theorem shl_align_correct':
  forall mx ex e,
  (e <= ex)%Z ->
  let (mx', ex') := shl_align mx ex e in
  F2R (Float radix2 (Zpos mx') e) = F2R (Float radix2 (Zpos mx) ex) /\
  ex' = e.
Proof.
intros mx ex ex' He.
unfold shl_align.
destruct (ex' - ex)%Z as [|d|d] eqn:Hd ; simpl.
- now replace ex with ex' by lia.
- exfalso ; lia.
- refine (conj _ eq_refl).
  rewrite shift_pos_correct, Zmult_comm.
  change (Zpower_pos 2 d) with (Zpower radix2 (Z.opp (Z.neg d))).
  rewrite <- Hd.
  replace (- (ex' - ex))%Z with (ex - ex')%Z by ring.
  now apply eq_sym, F2R_change_exp.
Qed.

Theorem shl_align_correct :
  forall mx ex ex',
  let (mx', ex'') := shl_align mx ex ex' in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex'') /\
  (ex'' <= ex')%Z.
Proof.
intros mx ex ex'.
generalize (shl_align_correct' mx ex ex').
unfold shl_align.
destruct (ex' - ex)%Z as [|d|d] eqn:Hd ; simpl.
- refine (fun H => _ (H _)).
  2: clear -Hd; lia.
  clear.
  intros [H1 ->].
  now split.
- intros _.
  refine (conj eq_refl _).
  lia.
- refine (fun H => _ (H _)).
  2: clear -Hd; lia.
  clear.
  now split.
Qed.

Theorem snd_shl_align :
  forall mx ex ex',
  (ex' <= ex)%Z ->
  snd (shl_align mx ex ex') = ex'.
Proof.
intros mx ex ex' He.
generalize (shl_align_correct' mx ex ex' He).
now destruct shl_align as [m e].
Qed.

Definition shl_align_fexp mx ex :=
  shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex)).

Theorem shl_align_fexp_correct :
  forall mx ex,
  let (mx', ex') := shl_align_fexp mx ex in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') /\
  (ex' <= fexp (Zdigits radix2 (Zpos mx') + ex'))%Z.
Proof.
intros mx ex.
unfold shl_align_fexp.
generalize (shl_align_correct mx ex (fexp (Zpos (digits2_pos mx) + ex))).
rewrite Zpos_digits2_pos.
case shl_align.
intros mx' ex' (H1, H2).
split.
exact H1.
rewrite <- mag_F2R_Zdigits. 2: easy.
rewrite <- H1.
now rewrite mag_F2R_Zdigits.
Qed.

(* TODO: lemme equivalence pour le cas mode_NE *)
Definition binary_round m sx mx ex :=
  let '(mz, ez) := shl_align_fexp mx ex in binary_round_aux m sx (Zpos mz) ez loc_Exact.

Theorem binary_round_correct :
  forall m sx mx ex,
  let z := binary_round m sx mx ex in
  valid_binary z = true /\
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) x)) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode m) x /\
    is_finite_SF z = true /\
    sign_SF z = sx
  else
    z = binary_overflow m sx.
Proof.
intros m sx mx ex.
unfold binary_round.
generalize (shl_align_fexp_correct mx ex).
destruct (shl_align_fexp mx ex) as (mz, ez).
intros (H1, H2).
set (x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex)).
replace sx with (Rlt_bool x 0).
apply binary_round_aux_correct.
constructor.
unfold x.
now rewrite <- F2R_Zabs, abs_cond_Zopp.
exact H2.
unfold x.
case sx.
apply Rlt_bool_true.
now apply F2R_lt_0.
apply Rlt_bool_false.
now apply F2R_ge_0.
Qed.

Theorem is_nan_binary_round :
  forall mode sx mx ex,
  is_nan_SF (binary_round mode sx mx ex) = false.
Proof.
intros mode sx mx ex.
generalize (binary_round_correct mode sx mx ex).
simpl.
destruct binary_round ; try easy.
intros [_ H].
destruct Rlt_bool ; try easy.
unfold binary_overflow in H.
now destruct overflow_to_inf.
Qed.

(* TODO: lemme equivalence pour le cas mode_NE *)
Definition binary_normalize mode m e szero :=
  match m with
  | Z0 => B754_zero szero
  | Zpos m => SF2B _ (proj1 (binary_round_correct mode false m e))
  | Zneg m => SF2B _ (proj1 (binary_round_correct mode true m e))
  end.

Theorem binary_normalize_correct :
  forall m mx ex szero,
  let x := F2R (Float radix2 mx ex) in
  let z := binary_normalize m mx ex szero in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) x)) (bpow radix2 emax) then
    B2R z = round radix2 fexp (round_mode m) x /\
    is_finite z = true /\
    Bsign z =
      match Rcompare x 0 with
        | Eq => szero
        | Lt => true
        | Gt => false
      end
  else
    B2SF z = binary_overflow m (Rlt_bool x 0).
Proof with auto with typeclass_instances.
intros m mx ez szero.
destruct mx as [|mz|mz] ; simpl.
rewrite F2R_0, round_0, Rabs_R0, Rlt_bool_true...
split... split...
rewrite Rcompare_Eq...
apply bpow_gt_0.
(* . mz > 0 *)
generalize (binary_round_correct m false mz ez).
simpl.
case Rlt_bool_spec.
intros _ (Vz, (Rz, (Rz', Rz''))).
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
rewrite Bsign_SF2B, Rz''.
rewrite Rcompare_Gt...
now apply F2R_gt_0.
intros Hz' (Vz, Rz).
rewrite B2SF_SF2B, Rz.
apply f_equal.
apply sym_eq.
apply Rlt_bool_false.
now apply F2R_ge_0.
(* . mz < 0 *)
generalize (binary_round_correct m true mz ez).
simpl.
case Rlt_bool_spec.
intros _ (Vz, (Rz, (Rz', Rz''))).
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
rewrite Bsign_SF2B, Rz''.
rewrite Rcompare_Lt...
now apply F2R_lt_0.
intros Hz' (Vz, Rz).
rewrite B2SF_SF2B, Rz.
apply f_equal.
apply sym_eq.
apply Rlt_bool_true.
now apply F2R_lt_0.
Qed.

Theorem is_nan_binary_normalize :
  forall mode m e szero,
  is_nan (binary_normalize mode m e szero) = false.
Proof.
intros mode m e szero.
generalize (binary_normalize_correct mode m e szero).
simpl.
destruct Rlt_bool.
- intros [_ [H _]].
  now destruct binary_normalize.
- intros H.
  rewrite <- is_nan_SF_B2SF.
  rewrite H.
  unfold binary_overflow.
  now destruct overflow_to_inf.
Qed.

(** Addition *)

Definition Fplus_naive sx mx ex sy my ey ez :=
  (Zplus (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))).

Lemma Fplus_naive_correct :
  forall sx mx ex sy my ey ez,
  (ez <= ex)%Z -> (ez <= ey)%Z ->
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  F2R (Float radix2 (Fplus_naive sx mx ex sy my ey ez) ez) = (x + y)%R.
Proof.
intros sx mx ex sy my ey ez Ex Ey.
unfold Fplus_naive, F2R. simpl.
generalize (shl_align_correct' mx ex ez Ex).
generalize (shl_align_correct' my ey ez Ey).
destruct shl_align as [my' ey'].
destruct shl_align as [mx' ex'].
intros [Hy _].
intros [Hx _].
simpl.
rewrite plus_IZR, Rmult_plus_distr_r.
generalize (f_equal (cond_Ropp sx) Hx).
generalize (f_equal (cond_Ropp sy) Hy).
rewrite <- 4!F2R_cond_Zopp.
unfold F2R. simpl.
now intros -> ->.
Qed.

Lemma sign_plus_overflow :
  forall m sx mx ex sy my ey,
  bounded mx ex = true ->
  bounded my ey = true ->
  let z := (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) + F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey))%R in
  (bpow radix2 emax <= Rabs (round radix2 fexp (round_mode m) z))%R ->
  sx = Rlt_bool z 0 /\ sx = sy.
Proof with auto with typeclass_instances.
intros m sx mx ex sy my ey Hx Hy z Bz.
destruct (Bool.bool_dec sx sy) as [Hs|Hs].
(* .. *)
refine (conj _ Hs).
unfold z.
rewrite Hs.
apply sym_eq.
case sy.
apply Rlt_bool_true.
rewrite <- (Rplus_0_r 0).
apply Rplus_lt_compat.
now apply F2R_lt_0.
now apply F2R_lt_0.
apply Rlt_bool_false.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
now apply F2R_ge_0.
now apply F2R_ge_0.
(* .. *)
elim Rle_not_lt with (1 := Bz).
generalize (bounded_lt_emax _ _ Hx) (bounded_lt_emax _ _ Hy).
intros Bx By.
generalize (canonical_bounded sx _ _ Hx) (canonical_bounded sy _ _ Hy).
clear -Bx By Hs prec_gt_0_.
intros Cx Cy.
destruct sx.
(* ... *)
destruct sy.
now elim Hs.
clear Hs.
apply Rabs_lt.
split.
apply Rlt_le_trans with (F2R (Float radix2 (cond_Zopp true (Zpos mx)) ex)).
rewrite F2R_Zopp.
now apply Ropp_lt_contravar.
apply round_ge_generic...
now apply generic_format_canonical.
pattern (F2R (Float radix2 (cond_Zopp true (Zpos mx)) ex)) at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
now apply F2R_ge_0.
apply Rle_lt_trans with (2 := By).
apply round_le_generic...
now apply generic_format_canonical.
rewrite <- (Rplus_0_l (F2R (Float radix2 (Zpos my) ey))).
apply Rplus_le_compat_r.
now apply F2R_le_0.
(* ... *)
destruct sy.
2: now elim Hs.
clear Hs.
apply Rabs_lt.
split.
apply Rlt_le_trans with (F2R (Float radix2 (cond_Zopp true (Zpos my)) ey)).
rewrite F2R_Zopp.
now apply Ropp_lt_contravar.
apply round_ge_generic...
now apply generic_format_canonical.
pattern (F2R (Float radix2 (cond_Zopp true (Zpos my)) ey)) at 1 ; rewrite <- Rplus_0_l.
apply Rplus_le_compat_r.
now apply F2R_ge_0.
apply Rle_lt_trans with (2 := Bx).
apply round_le_generic...
now apply generic_format_canonical.
rewrite <- (Rplus_0_r (F2R (Float radix2 (Zpos mx) ex))).
apply Rplus_le_compat_l.
now apply F2R_le_0.
Qed.

Definition Bplus m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy => if Bool.eqb sx sy then x else B754_nan
  | B754_infinity _, _ => x
  | _, B754_infinity _ => y
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx sy then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, _ => y
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Z.min ex ey in
    binary_normalize m (Fplus_naive sx mx ex sy my ey ez)
      ez (match m with mode_DN => true | _ => false end)
  end.

Theorem Bplus_correct :
  forall m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x + B2R y))) (bpow radix2 emax) then
    B2R (Bplus m x y) = round radix2 fexp (round_mode m) (B2R x + B2R y) /\
    is_finite (Bplus m x y) = true /\
    Bsign (Bplus m x y) =
      match Rcompare (B2R x + B2R y) 0 with
        | Eq => match m with mode_DN => orb (Bsign x) (Bsign y)
                                 | _ => andb (Bsign x) (Bsign y) end
        | Lt => true
        | Gt => false
      end
  else
    (B2SF (Bplus m x y) = binary_overflow m (Bsign x) /\ Bsign x = Bsign y).
Proof with auto with typeclass_instances.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] Fx Fy ; try easy.
(* *)
rewrite Rplus_0_r, round_0, Rabs_R0, Rlt_bool_true...
simpl.
rewrite Rcompare_Eq by auto.
destruct sx, sy; try easy; now case m.
apply bpow_gt_0.
(* *)
rewrite Rplus_0_l, round_generic, Rlt_bool_true...
split... split...
simpl. unfold F2R.
erewrite <- Rmult_0_l, Rcompare_mult_r.
rewrite Rcompare_IZR with (y:=0%Z).
destruct sy...
apply bpow_gt_0.
apply abs_B2R_lt_emax.
apply generic_format_B2R.
(* *)
rewrite Rplus_0_r, round_generic, Rlt_bool_true...
split... split...
simpl. unfold F2R.
erewrite <- Rmult_0_l, Rcompare_mult_r.
rewrite Rcompare_IZR with (y:=0%Z).
destruct sx...
apply bpow_gt_0.
apply abs_B2R_lt_emax.
apply generic_format_B2R.
(* *)
clear Fx Fy.
simpl.
set (szero := match m with mode_DN => true | _ => false end).
set (ez := Z.min ex ey).
assert (Hp := Fplus_naive_correct sx mx ex sy my ey ez (Z.le_min_l _ _) (Z.le_min_r _ _)).
set (mz := Fplus_naive sx mx ex sy my ey ez).
simpl in Hp.
fold mz in Hp.
rewrite <- Hp.
generalize (binary_normalize_correct m mz ez szero).
simpl.
case Rlt_bool_spec ; intros Hz.
intros [H1 [H2 H3]].
apply (conj H1).
apply (conj H2).
rewrite H3.
case Rcompare_spec ; try easy.
intros Hz'.
rewrite Hz' in Hp.
apply eq_sym, Rplus_opp_r_uniq in Hp.
rewrite <- F2R_Zopp in Hp.
eapply canonical_unique in Hp.
inversion Hp.
clear -H0.
destruct sy, sx, m ; easy.
now apply canonical_bounded.
rewrite <- cond_Zopp_negb.
now apply canonical_bounded.
intros Vz.
rewrite Hp in Hz.
assert (Sz := sign_plus_overflow m sx mx ex sy my ey Hx Hy Hz).
split.
rewrite Vz.
apply f_equal.
now rewrite Hp.
apply Sz.
Qed.

(** Subtraction *)

Definition Bminus m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy =>
    if Bool.eqb sx (negb sy) then x else B754_nan
  | B754_infinity _, _ => x
  | _, B754_infinity sy => B754_infinity (negb sy)
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx (negb sy) then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, B754_finite sy my ey Hy => B754_finite (negb sy) my ey Hy
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Z.min ex ey in
    binary_normalize m (Fplus_naive sx mx ex (negb sy) my ey ez)
      ez (match m with mode_DN => true | _ => false end)
  end.

Theorem Bminus_correct :
  forall m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x - B2R y))) (bpow radix2 emax) then
    B2R (Bminus m x y) = round radix2 fexp (round_mode m) (B2R x - B2R y) /\
    is_finite (Bminus m x y) = true /\
    Bsign (Bminus m x y) =
      match Rcompare (B2R x - B2R y) 0 with
        | Eq => match m with mode_DN => orb (Bsign x) (negb (Bsign y))
                                 | _ => andb (Bsign x) (negb (Bsign y)) end
        | Lt => true
        | Gt => false
      end
  else
    (B2SF (Bminus m x y) = binary_overflow m (Bsign x) /\ Bsign x = negb (Bsign y)).
Proof with auto with typeclass_instances.
intros m x y Fx Fy.
generalize (Bplus_correct m x (Bopp y) Fx).
rewrite is_finite_Bopp, B2R_Bopp.
intros H.
specialize (H Fy).
rewrite <- Bsign_Bopp.
destruct x as [| | |sx mx ex Hx], y as [| | |sy my ey Hy] ; try easy.
now clear -Fy; destruct y as [ | | | ].
Qed.

(** Fused Multiply-Add *)

Definition Bfma_szero m (x y z: binary_float) : bool :=
  let s_xy := xorb (Bsign x) (Bsign y) in  (* sign of product x*y *)
  if Bool.eqb s_xy (Bsign z) then s_xy
  else match m with mode_DN => true | _ => false end.

Definition Bfma m (x y z: binary_float) :=
  match x, y with
  | B754_nan, _ | _, B754_nan
  | B754_infinity _, B754_zero _
  | B754_zero _, B754_infinity _ =>
      (* Multiplication produces NaN *)
      B754_nan
  | B754_infinity sx, B754_infinity sy
  | B754_infinity sx, B754_finite sy _ _ _
  | B754_finite sx _ _ _, B754_infinity sy =>
      let s := xorb sx sy in
      (* Multiplication produces infinity with sign [s] *)
      match z with
      | B754_nan => B754_nan
      | B754_infinity sz => if Bool.eqb s sz then z else B754_nan
      | _ => B754_infinity s
      end
  | B754_finite sx _ _ _, B754_zero sy
  | B754_zero sx, B754_finite sy _ _ _
  | B754_zero sx, B754_zero sy =>
      (* Multiplication produces zero *)
      match z with
      | B754_nan => B754_nan
      | B754_zero _ => B754_zero (Bfma_szero m x y z)
      | _ => z
      end
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>
      (* Multiplication produces a finite, non-zero result *)
      match z with
      | B754_nan => B754_nan
      | B754_infinity sz => z
      | B754_zero _ =>
         let X := Float radix2 (cond_Zopp sx (Zpos mx)) ex in
         let Y := Float radix2 (cond_Zopp sy (Zpos my)) ey in
         let '(Float _ mr er) := Fmult X Y in
         binary_normalize m mr er (Bfma_szero m x y z)
      | B754_finite sz mz ez _ =>
         let X := Float radix2 (cond_Zopp sx (Zpos mx)) ex in
         let Y := Float radix2 (cond_Zopp sy (Zpos my)) ey in
         let Z := Float radix2 (cond_Zopp sz (Zpos mz)) ez in
         let '(Float _ mr er) := Fplus (Fmult X Y) Z in
         binary_normalize m mr er (Bfma_szero m x y z)
      end
  end.

Theorem Bfma_correct:
  forall m x y z,
  is_finite x = true ->
  is_finite y = true ->
  is_finite z = true ->
  let res := (B2R x * B2R y + B2R z)%R in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) res)) (bpow radix2 emax) then
    B2R (Bfma m x y z) = round radix2 fexp (round_mode m) res /\
    is_finite (Bfma m x y z) = true /\
    Bsign (Bfma m x y z) =
      match Rcompare res 0 with
        | Eq => Bfma_szero m x y z
        | Lt => true
        | Gt => false
      end
  else
    B2SF (Bfma m x y z) = binary_overflow m (Rlt_bool res 0).
Proof.
  intros. pattern (Bfma m x y z).
  match goal with |- ?p ?x => set (PROP := p) end.
  set (szero := Bfma_szero m x y z).
  assert (BINORM: forall mr er, F2R (Float radix2 mr er) = res ->
       PROP (binary_normalize m mr er szero)).
  { intros mr er E.
    specialize (binary_normalize_correct m mr er szero).
    change (FLT_exp (3 - emax - prec) prec) with fexp. rewrite E. tauto.
  }
  set (add_zero :=
    match z with
    | B754_nan => B754_nan
    | B754_zero sz => B754_zero szero
    | _ => z
    end).
  assert (ADDZERO: B2R x = 0%R \/ B2R y = 0%R -> PROP add_zero).
  {
    intros Z.
    assert (RES: res = B2R z).
    { unfold res. destruct Z as [E|E]; rewrite E, ?Rmult_0_l, ?Rmult_0_r, Rplus_0_l; auto. }
    unfold PROP, add_zero; destruct z as [ sz | sz | | sz mz ez Bz]; try discriminate.
  - simpl in RES; rewrite RES; rewrite round_0 by apply valid_rnd_round_mode.
    rewrite Rlt_bool_true. split. reflexivity. split. reflexivity.
    rewrite Rcompare_Eq by auto. reflexivity.
    rewrite Rabs_R0; apply bpow_gt_0.
  - rewrite RES, round_generic, Rlt_bool_true.
    split. reflexivity. split. reflexivity.
    unfold B2R. destruct sz.
    rewrite Rcompare_Lt. auto. apply F2R_lt_0. reflexivity.
    rewrite Rcompare_Gt. auto. apply F2R_gt_0. reflexivity.
    apply abs_B2R_lt_emax. apply valid_rnd_round_mode. apply generic_format_B2R.
  }
  destruct x as [ sx | sx | | sx mx ex Bx];
  destruct y as [ sy | sy | | sy my ey By];
  try discriminate.
- apply ADDZERO; auto.
- apply ADDZERO; auto.
- apply ADDZERO; auto.
- destruct z as [ sz | sz | | sz mz ez Bz]; try discriminate; unfold Bfma.
+ set (X := Float radix2 (cond_Zopp sx (Zpos mx)) ex).
  set (Y := Float radix2 (cond_Zopp sy (Zpos my)) ey).
  destruct (Fmult X Y) as [mr er] eqn:FRES.
  apply BINORM. unfold res. rewrite <- FRES, F2R_mult, Rplus_0_r. auto.
+ set (X := Float radix2 (cond_Zopp sx (Zpos mx)) ex).
  set (Y := Float radix2 (cond_Zopp sy (Zpos my)) ey).
  set (Z := Float radix2 (cond_Zopp sz (Zpos mz)) ez).
  destruct (Fplus (Fmult X Y) Z) as [mr er] eqn:FRES.
  apply BINORM. unfold res. rewrite <- FRES, F2R_plus, F2R_mult. auto.
Qed.

(** Division *)

Lemma Bdiv_correct_aux :
  forall m sx mx ex sy my ey,
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  let z :=
    let '(mz, ez, lz) := SFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey in
    binary_round_aux m (xorb sx sy) mz ez lz in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (x / y))) (bpow radix2 emax) then
    SF2R radix2 z = round radix2 fexp (round_mode m) (x / y) /\
    is_finite_SF z = true /\ sign_SF z = xorb sx sy
  else
    z = binary_overflow m (xorb sx sy).
Proof.
intros m sx mx ex sy my ey.
unfold SFdiv_core_binary.
rewrite 2!Zdigits2_Zdigits.
set (e' := Z.min _ _).
match goal with |- context [Z.div_eucl ?m _] => set (mx' := m) end.
generalize (Fdiv_core_correct radix2 (Zpos mx) ex (Zpos my) ey e' eq_refl eq_refl).
unfold Fdiv_core.
rewrite Zle_bool_true by apply Z.le_min_r.
assert (mx' = Zpos mx * Zpower radix2 (ex - ey - e'))%Z as <-.
{ unfold mx'.
  destruct (ex - ey - e')%Z as [|p|p].
  now rewrite Zmult_1_r.
  now rewrite Z.shiftl_mul_pow2.
  easy. }
clearbody mx'.
destruct Z.div_eucl as [q r].
intros Bz.
assert (xorb sx sy = Rlt_bool (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) *
  / F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey)) 0) as ->.
{ apply eq_sym.
case sy ; simpl.
change (Zneg my) with (Z.opp (Zpos my)).
rewrite F2R_Zopp.
rewrite <- Ropp_inv_permute.
rewrite Ropp_mult_distr_r_reverse.
case sx ; simpl.
apply Rlt_bool_false.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rmult_le_pos.
rewrite <- F2R_opp.
now apply F2R_ge_0.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0.
apply Rlt_bool_true.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
now apply F2R_gt_0.
apply Rinv_0_lt_compat.
now apply F2R_gt_0.
apply Rgt_not_eq.
now apply F2R_gt_0.
case sx.
apply Rlt_bool_true.
rewrite F2R_Zopp.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
now apply F2R_gt_0.
apply Rinv_0_lt_compat.
now apply F2R_gt_0.
apply Rlt_bool_false.
apply Rmult_le_pos.
now apply F2R_ge_0.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0. }
unfold Rdiv.
apply binary_round_aux_correct'.
- apply Rmult_integral_contrapositive_currified.
  now apply F2R_neq_0 ; case sx.
  apply Rinv_neq_0_compat.
  now apply F2R_neq_0 ; case sy.
- rewrite Rabs_mult, Rabs_Rinv.
  + rewrite <- 2!F2R_Zabs, 2!abs_cond_Zopp; simpl.
    replace (SpecFloat.new_location _ _) with (Bracket.new_location (Z.pos my) r loc_Exact);
      [exact Bz|].
    case my as [p|p|]; [reflexivity| |reflexivity].
    unfold Bracket.new_location, SpecFloat.new_location; simpl.
    unfold Bracket.new_location_even, SpecFloat.new_location_even; simpl.
    now case Zeq_bool; [|case r as [|rp|rp]; case Z.compare].
  + now apply F2R_neq_0 ; case sy.
- rewrite <- cexp_abs, Rabs_mult, Rabs_Rinv.
  rewrite 2!F2R_cond_Zopp, 2!abs_cond_Ropp, <- Rabs_Rinv.
  rewrite <- Rabs_mult, cexp_abs.
  apply Z.le_trans with (1 := Z.le_min_l _ _).
  apply FLT_exp_monotone.
  now apply mag_div_F2R.
  now apply F2R_neq_0.
  now apply F2R_neq_0 ; case sy.
Qed.

Definition Bdiv m x y :=
  match x, y with
  | B754_nan, _ | _, B754_nan => B754_nan
  | B754_infinity sx, B754_infinity sy => B754_nan
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_infinity sx, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_finite sx _ _ _, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_nan
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>
    SF2B _ (proj1 (Bdiv_correct_aux m sx mx ex sy my ey))
  end.

Theorem Bdiv_correct :
  forall m x y,
  B2R y <> 0%R ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x / B2R y))) (bpow radix2 emax) then
    B2R (Bdiv m x y) = round radix2 fexp (round_mode m) (B2R x / B2R y) /\
    is_finite (Bdiv m x y) = is_finite x /\
    (is_nan (Bdiv m x y) = false ->
      Bsign (Bdiv m x y) = xorb (Bsign x) (Bsign y))
  else
    B2SF (Bdiv m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof.
intros m x [sy|sy| |sy my ey Hy] Zy ; try now elim Zy.
revert x.
unfold Rdiv.
intros [sx|sx| |sx mx ex Hx] ;
  try ( rewrite Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ simpl ; try easy ; now rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan | apply bpow_gt_0 | auto with typeclass_instances ] ).
simpl.
case Bdiv_correct_aux.
intros H1.
unfold Rdiv.
case Rlt_bool.
intros (H2, (H3, H4)).
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
rewrite Bsign_SF2B. congruence.
intros H2.
now rewrite B2SF_SF2B.
Qed.

(** Square root *)

Lemma Bsqrt_correct_aux :
  forall m mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (Zpos mx) ex) in
  let z :=
    let '(mz, ez, lz) := SFsqrt_core_binary prec emax (Zpos mx) ex in
    binary_round_aux m false mz ez lz in
  valid_binary z = true /\
  SF2R radix2 z = round radix2 fexp (round_mode m) (sqrt x) /\
  is_finite_SF z = true /\ sign_SF z = false.
Proof with auto with typeclass_instances.
intros m mx ex Hx.
unfold SFsqrt_core_binary.
rewrite Zdigits2_Zdigits.
set (e' := Z.min _ _).
assert (2 * e' <= ex)%Z as He.
{ assert (e' <= Z.div2 ex)%Z by apply Z.le_min_r.
  rewrite (Zdiv2_odd_eqn ex).
  destruct Z.odd ; lia. }
generalize (Fsqrt_core_correct radix2 (Zpos mx) ex e' eq_refl He).
unfold Fsqrt_core.
set (mx' := match (ex - 2 * e')%Z with Z0 => _ | _ => _ end).
assert (mx' = Zpos mx * Zpower radix2 (ex - 2 * e'))%Z as <-.
{ unfold mx'.
  destruct (ex - 2 * e')%Z as [|p|p].
  now rewrite Zmult_1_r.
  now rewrite Z.shiftl_mul_pow2.
  easy. }
clearbody mx'.
destruct Z.sqrtrem as [mz r].
set (lz := if Zeq_bool r 0 then _ else _).
clearbody lz.
intros Bz.
refine (_ (binary_round_aux_correct' m (sqrt (F2R (Float radix2 (Zpos mx) ex))) mz e' lz _ _ _)) ; cycle 1.
  now apply Rgt_not_eq, sqrt_lt_R0, F2R_gt_0.
  rewrite Rabs_pos_eq.
  exact Bz.
  apply sqrt_ge_0.
  apply Z.le_trans with (1 := Z.le_min_l _ _).
  apply FLT_exp_monotone.
  rewrite mag_sqrt_F2R by easy.
  apply Z.le_refl.
rewrite Rlt_bool_false by apply sqrt_ge_0.
rewrite Rlt_bool_true.
easy.
rewrite Rabs_pos_eq.
refine (_ (relative_error_FLT_ex radix2 emin prec (prec_gt_0 prec) (round_mode m) (sqrt (F2R (Float radix2 (Zpos mx) ex))) _)).
fold fexp.
intros (eps, (Heps, Hr)).
change fexp with (FLT_exp emin prec).
rewrite Hr.
assert (Heps': (Rabs eps < 1)%R).
apply Rlt_le_trans with (1 := Heps).
fold (bpow radix2 0).
apply bpow_le.
generalize (prec_gt_0 prec).
clear ; lia.
apply Rsqr_incrst_0.
3: apply bpow_ge_0.
rewrite Rsqr_mult.
rewrite Rsqr_sqrt.
2: now apply F2R_ge_0.
unfold Rsqr.
apply Rmult_ge_0_gt_0_lt_compat.
apply Rle_ge.
apply Rle_0_sqr.
apply bpow_gt_0.
now apply bounded_lt_emax.
apply Rlt_le_trans with 4%R.
apply (Rsqr_incrst_1 _ 2).
apply Rplus_lt_compat_l.
apply (Rabs_lt_inv _ _ Heps').
rewrite <- (Rplus_opp_r 1).
apply Rplus_le_compat_l.
apply Rlt_le.
apply (Rabs_lt_inv _ _ Heps').
now apply IZR_le.
change 4%R with (bpow radix2 2).
apply bpow_le.
generalize (prec_gt_0 prec) (prec_lt_emax prec emax).
clear ; lia.
apply Rmult_le_pos.
apply sqrt_ge_0.
rewrite <- (Rplus_opp_r 1).
apply Rplus_le_compat_l.
apply Rlt_le.
apply (Rabs_lt_inv _ _ Heps').
rewrite Rabs_pos_eq.
2: apply sqrt_ge_0.
apply Rsqr_incr_0.
2: apply bpow_ge_0.
2: apply sqrt_ge_0.
rewrite Rsqr_sqrt.
2: now apply F2R_ge_0.
apply Rle_trans with (bpow radix2 emin).
unfold Rsqr.
rewrite <- bpow_plus.
apply bpow_le.
unfold emin.
generalize (prec_lt_emax prec emax).
clear ; lia.
apply generic_format_ge_bpow with fexp.
intros.
apply Z.le_max_r.
now apply F2R_gt_0.
apply generic_format_canonical.
now apply (canonical_bounded false).
apply round_ge_generic...
apply generic_format_0.
apply sqrt_ge_0.
Qed.

Definition Bsqrt m x :=
  match x with
  | B754_nan => B754_nan
  | B754_infinity false => x
  | B754_infinity true => B754_nan
  | B754_finite true _ _ _ => B754_nan
  | B754_zero _ => x
  | B754_finite sx mx ex Hx =>
    SF2B _ (proj1 (Bsqrt_correct_aux m mx ex Hx))
  end.

Theorem Bsqrt_correct :
  forall m x,
  B2R (Bsqrt m x) = round radix2 fexp (round_mode m) (sqrt (B2R x)) /\
  is_finite (Bsqrt m x) = match x with B754_zero _ => true | B754_finite false _ _ _ => true | _ => false end /\
  (is_nan (Bsqrt m x) = false -> Bsign (Bsqrt m x) = Bsign x).
Proof.
intros m [sx|[|]| |sx mx ex Hx] ;
  try ( simpl ; rewrite sqrt_0, round_0, ?B2R_build_nan, ?is_finite_build_nan, ?is_nan_build_nan ; intuition auto with typeclass_instances ; easy).
simpl.
case Bsqrt_correct_aux.
intros H1 (H2, (H3, H4)).
case sx.
refine (conj _ (conj (refl_equal false) _)).
apply sym_eq.
unfold sqrt.
case Rcase_abs.
intros _.
apply round_0.
auto with typeclass_instances.
intros H.
elim Rge_not_lt with (1 := H).
now apply F2R_lt_0.
easy.
split.
now rewrite B2R_SF2B.
split.
now rewrite is_finite_SF2B.
intros _.
now rewrite Bsign_SF2B.
Qed.

(** NearbyInt and Trunc **)

Definition SFnearbyint_binary_aux m sx mx ex :=
  if (0 <=? ex)%Z then ((Z.pos mx) * 2 ^ ex)%Z else
  let mrs := {| shr_m := Z.pos mx; shr_r := false; shr_s := false |} in
  let mrs' := if (ex <? - prec)%Z then
    {| shr_m := Z0; shr_r := false; shr_s := true |} else
    fst (shr mrs ex (- ex)) in
  let l' := loc_of_shr_record mrs' in
  let mx' := shr_m mrs' in
  choice_mode m sx mx' l'.

Definition SFnearbyint_binary m sx mx ex :=
  if (0 <=? ex)%Z then S754_finite sx mx ex else
  let mx'' := SFnearbyint_binary_aux m sx mx ex in
  match mx'' with
  | Z.pos n =>
    let (mx''', ex''') := shl_align_fexp n 0 in
    S754_finite sx mx''' ex'''
  | Z.neg n => S754_nan
  | Z0      => S754_zero sx
  end.

Lemma Bnearbyint_correct_aux :
  forall md sx mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let z := SFnearbyint_binary md sx mx ex in
  valid_binary z = true /\
  SF2R radix2 z = (round radix2 (FIX_exp 0) (round_mode md) x) /\
  is_finite_SF z = true /\ (is_nan_SF z = false -> sign_SF z = sx).
Proof.
  intros md sx mx ex Hmxex. simpl.
  set (mrs' := if (ex <? - prec)%Z then
    {| shr_m := Z0; shr_r := false; shr_s := true |} else
    fst (shr {| shr_m := Z.pos mx; shr_r := false; shr_s := false |} ex (- ex))).
  assert (mrs'_simpl : mrs' = fst (shr {| shr_m := Z.pos mx; shr_r := false; shr_s := false |} ex (- ex))).
  { unfold mrs'. case Zlt_bool_spec; [ | easy]. intros Hex1. symmetry.
    apply shr_limit; simpl; [now left |]. apply Z.lt_le_trans with (radix2 ^ prec)%Z.
    - unfold bounded, canonical_mantissa, fexp in Hmxex. apply andb_prop in Hmxex.
      destruct Hmxex as [Hmxex _]. apply Zeq_bool_eq in Hmxex.
      rewrite Zpos_digits2_pos in Hmxex. apply Z.eq_le_incl in Hmxex.
      apply Z.max_lub_l in Hmxex.
      assert (Hmx : (Zdigits radix2 (Z.pos mx) <= prec)%Z) by lia.
      replace (Z.pos mx) with (Z.abs (Z.pos mx)); [| now simpl].
      now apply Zpower_gt_Zdigits.
    - apply Zpower_le. lia.
    }
  assert (mrs'_ge_0 : (ex < 0)%Z -> (0 <= shr_m mrs')%Z).
  (* N.B.: The hypothesis (ex < 0)%Z is only here to make the proof simpler. *)
  { intros Hex.
    rewrite mrs'_simpl.
    apply (Z.mul_le_mono_pos_l _ _ (2 ^ (- ex))).
    apply (Zpower_gt_0 radix2).
    lia.
    rewrite Z.mul_0_r.
    apply le_shr_le.
    easy.
    lia. }
  repeat split; unfold SFnearbyint_binary, SFnearbyint_binary_aux;
  case Zle_bool_spec; intros Hex0; fold mrs'; auto.

  - destruct choice_mode eqn:H0; auto.
    unfold shl_align_fexp. destruct shl_align as [mx''' ex'''] eqn:H1; simpl.
    unfold bounded, canonical_mantissa in Hmxex. apply andb_prop in Hmxex.
    destruct Hmxex as [Hmxex Hex'].
    unfold bounded, canonical_mantissa.
    assert (A : (fexp (Z.pos (digits2_pos p) + 0) <= 0)%Z).
    { rewrite Z.add_0_r in *. rewrite Zpos_digits2_pos in *.
      destruct (le_shr_le mrs' ex (- ex)) as [H2 H3]; [now apply mrs'_ge_0 | lia |].
      destruct (le_choice_mode_le md sx (shr_m mrs') (loc_of_shr_record mrs')) as [H4 H5].
      rewrite H0 in H4, H5.
      transitivity (fexp (Zdigits radix2 (shr_m mrs' + 1)));
        [apply fexp_monotone; apply Zdigits_le; [lia | assumption] |
      transitivity (fexp ((Zdigits radix2 (shr_m mrs') + 1)));
        [apply fexp_monotone; apply Zdigits_succ_le; now apply mrs'_ge_0 |
      transitivity (fexp (Zdigits radix2 ((shr_m {| shr_m := Z.pos mx; shr_r := false; shr_s := false |}) / (2 ^ (- ex))) + 1));
        [apply fexp_monotone; apply Zplus_le_compat_r; apply Zdigits_le; simpl; auto | simpl
      ]]].
      - apply Zdiv.Zdiv_le_lower_bound; [lia |]. rewrite Z.mul_comm. rewrite mrs'_simpl.
        apply le_shr_le; simpl; lia.
      - transitivity (fexp (Zdigits radix2 (Z.pos mx / 2 ^ 1) + 1)).
        + apply fexp_monotone. apply Zplus_le_compat_r. apply Zdigits_le.
          * apply Z.div_pos; lia.
          * apply Z.opp_pos_neg in Hex0. apply Z.div_le_compat_l; [lia |].
            split; [lia |]. apply Z.pow_le_mono_r; lia.
        + rewrite Zdigits_div_Zpower; [| lia |].
          * rewrite Z.sub_add. apply Zeq_bool_eq in Hmxex. unfold fexp in *.
            rewrite Z.max_lub_iff. split; [| lia]. apply (Zplus_le_reg_l _ _ ex).
            rewrite Zplus_0_r. rewrite Z.add_sub_assoc. rewrite Z.add_comm.
            rewrite <-Hmxex at 2. apply Z.le_max_l.
          * split; [lia |]. replace 1%Z with (Zdigits radix2 (Z.pos 1)); [| easy].
            apply Zdigits_le; lia. }
    refine (_ (shl_align_correct' p 0 (fexp (Z.pos (digits2_pos p) + 0)) _)).
    + rewrite H1. intros [H2 H3]. rewrite <-H3 in H2.
      apply andb_true_intro; split.
      * apply Zeq_bool_true. rewrite H3 at 2. rewrite !Zpos_digits2_pos.
        rewrite <-!mag_F2R_Zdigits; [| lia | lia].
        now apply (f_equal (fun f => fexp (mag radix2 f))).
      * apply Zle_bool_true. rewrite H3. transitivity 0%Z; [assumption|].
        apply Zle_minus_le_0. apply Z.lt_le_incl. apply prec_lt_emax_.
    + assumption.

  - symmetry. apply round_generic; auto.
    + apply valid_rnd_round_mode.
    + apply generic_format_FIX.
      exists (Float radix2 (cond_Zopp sx (Z.pos mx) * Z.pow 2 ex) 0); auto.
      simpl. rewrite <-(Z.sub_0_r ex) at 2. now apply F2R_change_exp.

  - rewrite round_trunc_sign_any_correct with (choice := choice_mode md)
      (m := Z.pos mx) (e := ex) (l := loc_Exact).
    + fold (shr_record_of_loc (Z.pos mx) loc_Exact) in mrs'_simpl. rewrite mrs'_simpl.
      replace (- ex)%Z with (FIX_exp 0 (Zdigits2 (Z.pos mx) + ex) - ex)%Z; [| auto].
      rewrite !shr_truncate; [ | apply FIX_exp_valid | easy ].
      destruct truncate as (rec, loc) eqn:H0. destruct rec as (z0, z1) eqn:H1.
      simpl. rewrite shr_m_shr_record_of_loc. rewrite loc_of_shr_record_of_loc.
      replace (Rlt_bool (F2R {| Fnum := cond_Zopp sx (Z.pos mx); Fexp := ex |}) 0) with sx.
      * destruct choice_mode as [| p0 | p0] eqn:H2.
        -- simpl. symmetry. rewrite cond_Zopp_0. apply F2R_0.
        -- generalize (shl_align_fexp_correct p0 0).
           destruct shl_align_fexp as (p1, z2). simpl. intros [H3 _].
           rewrite !F2R_cond_Zopp. apply f_equal. simpl in H0.
           rewrite Zlt_bool_true in H0; [| lia].
           rewrite Z.add_opp_diag_r in H0. injection H0.
           intros _ H4 _. now rewrite <-H4.
        -- destruct (le_choice_mode_le md sx z0 loc) as [H3 _].
           rewrite H2 in H3. simpl in H0.
           rewrite Zlt_bool_true in H0 by lia.
           injection H0. intros _ _ H4.
           elim (Zle_not_lt 0 z0).
           rewrite <- H4.
           apply Z_div_pos.
           apply Z.lt_gt, (Zpower_gt_0 radix2). lia.
           easy.
           now apply Z.le_lt_trans with (1 := H3).
      * rewrite F2R_cond_Zopp. apply eq_sym, Rlt_bool_cond_Ropp.
        now apply F2R_gt_0.
    + apply FIX_exp_valid.
    + apply valid_rnd_round_mode.
    + apply round_mode_choice_mode.
    + rewrite <-F2R_abs. simpl. rewrite abs_cond_Zopp. simpl. now apply inbetween_Exact.
    + auto.

  - destruct choice_mode eqn:H0; [easy | now destruct shl_align_fexp |].
    apply mrs'_ge_0 in Hex0.
    destruct (le_choice_mode_le md sx (shr_m mrs') (loc_of_shr_record mrs')) as [H2 H3].
    rewrite H0 in H2, H3. lia.

  - destruct choice_mode eqn:H0; [easy | now destruct shl_align_fexp | easy].
Qed.

Definition Bnearbyint md (x : binary_float) :=
  match x with
  | B754_nan => B754_nan
  | B754_zero s => B754_zero s
  | B754_infinity s => B754_infinity s
  | B754_finite s m e H =>
    SF2B _ (proj1 (Bnearbyint_correct_aux md s m e H))
  end.

Theorem Bnearbyint_correct :
  forall md x,
  B2R (Bnearbyint md x) = round radix2 (FIX_exp 0) (round_mode md) (B2R x) /\
  is_finite (Bnearbyint md x) = is_finite x /\
  (is_nan (Bnearbyint md x) = false -> Bsign (Bnearbyint md x) = Bsign x).
Proof.
  intros md.
  assert (round_0_ : 0%R = (round radix2 (FIX_exp 0) (round_mode md) 0)).
  { symmetry.
    apply round_0.
    apply valid_rnd_round_mode. }
  intros [sx | sx | | sx mx ex Hx]; try easy.
  unfold Bnearbyint. destruct Bnearbyint_correct_aux as [H1 [H2 [H3 H4]]]. repeat split.
  - rewrite B2R_SF2B. easy.
  - rewrite is_finite_SF2B. easy.
  - rewrite is_nan_SF2B. rewrite Bsign_SF2B. easy.
Qed.

Definition Btrunc (x : binary_float) :=
  match x with
  | B754_finite s m e _ =>
    cond_Zopp s (SFnearbyint_binary_aux mode_ZR s m e)
  | _ => 0%Z
  end.

Theorem Btrunc_correct :
  forall x,
  IZR (Btrunc x) = round radix2 (FIX_exp 0) Ztrunc (B2R x).
Proof.
  assert (round_0_to_0 : 0%R = (round radix2 (FIX_exp 0) Ztrunc 0)).
  { symmetry. apply round_0. apply valid_rnd_ZR. }
  intros [sx | sx | | sx mx ex Hx]; simpl; try assumption.
  destruct (Bnearbyint_correct_aux mode_ZR sx mx ex) as [_ [H0 _]]; [easy |].
  simpl round_mode in H0. rewrite <-H0. unfold SFnearbyint_binary, SFnearbyint_binary_aux.
  set (mrs' :=
   (if (ex <? - prec)%Z
    then {| shr_m := 0; shr_r := false; shr_s := true |}
    else fst (shr {| shr_m := Z.pos mx; shr_r := false; shr_s := false |} ex (- ex)))).
  fold mrs'.
  set (n := choice_mode mode_ZR sx (shr_m mrs') (loc_of_shr_record mrs')).
  fold n. case Zle_bool_spec; intros H1.
  - simpl SF2R. unfold F2R. simpl Fnum. simpl bpow. destruct sx; unfold cond_Zopp;
    [rewrite Zopp_mult_distr_l |]; rewrite mult_IZR; apply f_equal; destruct ex; easy.
  - destruct n as [ | p | p] eqn:H2; [now destruct sx | |].
    + generalize (shl_align_fexp_correct p 0). destruct shl_align_fexp.
      simpl SF2R. unfold F2R. simpl. intros [H3 H4]. rewrite Rmult_1_r in H3.
      destruct sx; unfold cond_Zopp; [| assumption].
      rewrite 2Ropp_Ropp_IZR. rewrite <-Ropp_mult_distr_l. now rewrite H3.
    + unfold n in H2.
      destruct (le_choice_mode_le mode_ZR sx (shr_m mrs') (loc_of_shr_record mrs')) as [H3 _].
      rewrite H2 in H3. unfold mrs' in H3. case (ex <? - prec)%Z in H3.
      * simpl in H3. lia.
      * destruct (le_shr_le ({| shr_m := Z.pos mx; shr_r := false; shr_s := false |})
          ex (- ex)) as [[H4 _] _]; [simpl; lia | lia |].
        elim (Zle_not_lt 0 (Z.neg p)). 2: easy.
        apply Z.le_trans with (2 := H3).
        apply Zmult_le_0_reg_r with (2 ^ (- ex))%Z.
        apply Z.lt_gt, (Zpower_gt_0 radix2). lia.
        now rewrite Zmult_comm.
Qed.

(** A few values *)

Definition Bone := SF2B _ (proj1 (binary_round_correct mode_NE false 1 0)).

Theorem Bone_correct : B2R Bone = 1%R.
Proof.
unfold Bone; simpl.
set (Hr := binary_round_correct _ _ _ _).
unfold Hr; rewrite B2R_SF2B.
destruct Hr as (Vz, Hr).
revert Hr.
fold emin; simpl.
rewrite round_generic; [|now apply valid_rnd_N|].
- unfold F2R; simpl; rewrite Rmult_1_r.
  rewrite Rlt_bool_true.
  + now intros (Hr, Hr'); rewrite Hr.
  + rewrite Rabs_R1.
    change 1%R with (bpow radix2 0); apply bpow_lt.
    generalize (prec_gt_0 prec) (prec_lt_emax prec emax).
    lia.
- apply generic_format_F2R; intros _.
  unfold cexp, fexp, FLT_exp, F2R; simpl; rewrite Rmult_1_r, mag_1.
  unfold emin.
  generalize (prec_gt_0 prec) (prec_lt_emax prec emax).
  lia.
Qed.

Theorem is_finite_strict_Bone :
  is_finite_strict Bone = true.
Proof.
apply is_finite_strict_B2R.
rewrite Bone_correct.
apply R1_neq_R0.
Qed.

Theorem is_nan_Bone :
  is_nan Bone = false.
Proof.
unfold Bone.
rewrite is_nan_SF2B.
apply is_nan_binary_round.
Qed.

Theorem is_finite_Bone :
  is_finite Bone = true.
Proof.
generalize is_finite_strict_Bone.
now destruct Bone.
Qed.

Theorem Bsign_Bone :
  Bsign Bone = false.
Proof.
generalize Bone_correct is_finite_strict_Bone.
destruct Bone as [sx|sx| |[|] mx ex Bx] ; try easy.
intros H _.
contradict H.
apply Rlt_not_eq, Rlt_trans with (2 := Rlt_0_1).
now apply F2R_lt_0.
Qed.

Lemma Bmax_float_proof :
  valid_binary
    (S754_finite false (shift_pos (Z.to_pos prec) 1 - 1) (emax - prec))
  = true.
Proof.
unfold valid_binary, bounded; apply andb_true_intro; split.
- unfold canonical_mantissa; apply Zeq_bool_true.
  set (p := Z.pos (digits2_pos _)).
  assert (H : p = prec).
  { unfold p; rewrite Zpos_digits2_pos, Pos2Z.inj_sub.
    - rewrite shift_pos_correct, Z.mul_1_r.
      assert (P2pm1 : (0 <= 2 ^ prec - 1)%Z).
      { apply Z.lt_le_pred.
        apply (Zpower_gt_0 radix2).
        now apply Zlt_le_weak. }
      apply Zdigits_unique ;
        rewrite Z.pow_pos_fold, Z2Pos.id; [|exact prec_gt_0_]; simpl; split.
      + rewrite (Z.abs_eq _ P2pm1).
        apply Z.lt_le_pred.
        apply (Zpower_lt radix2).
        now apply Zlt_le_weak.
        apply Z.lt_pred_l.
      + rewrite Z.abs_eq by easy.
        apply Z.lt_pred_l.
    - change (Z.pos 1 < Z.pos (shift_pos (Z.to_pos prec) 1))%Z.
      rewrite shift_pos_correct, Z.mul_1_r, Z.pow_pos_fold.
      rewrite Z2Pos.id; [|exact prec_gt_0_].
      now apply (Zpower_gt_1 radix2). }
  rewrite H.
  ring_simplify (prec + (emax - prec))%Z.
  apply fexp_emax.
- apply Zle_bool_true, Z.le_refl.
Qed.

Definition Bmax_float := SF2B _ Bmax_float_proof.

(** Extraction/modification of mantissa/exponent *)

Definition Bnormfr_mantissa x := SFnormfr_mantissa prec (B2SF x).

Lemma Bnormfr_mantissa_correct :
  forall x,
  (/ 2 <= Rabs (B2R x) < 1)%R ->
  match x with
  | B754_finite _ m e _ =>
    Bnormfr_mantissa x = N.pos m
    /\ Z.pos (digits2_pos m) = prec /\ (e = - prec)%Z
  | _ => False
  end.
Proof.
intro x.
destruct x as [s|s| |s m e B]; [now simpl; rewrite Rabs_R0; lra..| ].
unfold Bnormfr_mantissa, SFnormfr_mantissa; simpl.
intro Hx.
cut (e = -prec /\ Z.pos (digits2_pos m) = prec)%Z.
{ now intros [-> ->]; rewrite Z.eqb_refl. }
revert Hx.
change (/ 2)%R with (bpow radix2 (0 - 1)); change 1%R with (bpow radix2 0).
intro H; generalize (mag_unique _ _ _ H); clear H.
rewrite Float_prop.mag_F2R_Zdigits; [ |now case s].
replace (Digits.Zdigits _ _)
  with (Digits.Zdigits radix2 (Z.pos m)); [ |now case s].
clear s.
rewrite <-Digits.Zpos_digits2_pos.
intro He; replace e with (e - 0)%Z by ring; rewrite <-He.
cut (Z.pos (digits2_pos m) = prec)%Z.
{ now intro H; split; [ |exact H]; ring_simplify; rewrite H. }
revert B; unfold bounded, canonical_mantissa.
intro H; generalize (andb_prop _ _ H); clear H; intros [H _]; revert H.
intro H; generalize (Zeq_bool_eq _ _ H); clear H.
unfold fexp, emin.
unfold Prec_gt_0 in prec_gt_0_; unfold Prec_lt_emax in prec_lt_emax_.
lia.
Qed.

Definition Bldexp mode f e :=
  match f with
  | B754_finite sx mx ex _ =>
    SF2B _ (proj1 (binary_round_correct mode sx mx (ex+e)))
  | _ => f
  end.

Theorem is_nan_Bldexp :
  forall mode x e,
  is_nan (Bldexp mode x e) = is_nan x.
Proof.
intros mode [sx|sx| |sx mx ex Bx] e ; try easy.
unfold Bldexp.
rewrite is_nan_SF2B.
apply is_nan_binary_round.
Qed.

Theorem Bldexp_correct :
  forall m (f : binary_float) e,
  if Rlt_bool
       (Rabs (round radix2 fexp (round_mode m) (B2R f * bpow radix2 e)))
       (bpow radix2 emax) then
    (B2R (Bldexp m f e)
     = round radix2 fexp (round_mode m) (B2R f * bpow radix2 e))%R /\
    is_finite (Bldexp m f e) = is_finite f /\
    Bsign (Bldexp m f e) = Bsign f
  else
    B2SF (Bldexp m f e) = binary_overflow m (Bsign f).
Proof.
intros m f e.
case f.
- intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- intros s mf ef Hmef.
  case (Rlt_bool_spec _ _); intro Hover.
  + unfold Bldexp; rewrite B2R_SF2B, is_finite_SF2B, Bsign_SF2B.
    simpl; unfold F2R; simpl; rewrite Rmult_assoc, <-bpow_plus.
    destruct (binary_round_correct m s mf (ef + e)) as (Hf, Hr).
    fold emin in Hr; simpl in Hr; rewrite Rlt_bool_true in Hr.
    * now destruct Hr as (Hr, (Hfr, Hsr)); rewrite Hr, Hfr, Hsr.
    * now revert Hover; unfold B2R, F2R; simpl; rewrite Rmult_assoc, bpow_plus.
  + unfold Bldexp; rewrite B2SF_SF2B; simpl.
    destruct (binary_round_correct m s mf (ef + e)) as (Hf, Hr).
    fold emin in Hr; simpl in Hr; rewrite Rlt_bool_false in Hr; [exact Hr|].
    now revert Hover; unfold B2R, F2R; simpl; rewrite Rmult_assoc, bpow_plus.
Qed.

Lemma Bldexp_Bopp_NE x e : Bldexp mode_NE (Bopp x) e = Bopp (Bldexp mode_NE x e).
Proof.
case x as [s|s| |s m e' B]; [now simpl..| ].
apply B2SF_inj.
replace (B2SF (Bopp _)) with (SFopp (B2SF (Bldexp mode_NE (B754_finite s m e' B) e))).
{ unfold Bldexp, Bopp; rewrite !B2SF_SF2B.
  unfold binary_round.
  set (shl := shl_align_fexp _ _); case shl; intros mz ez.
  unfold binary_round_aux.
  set (shr := shr_fexp _ _ _); case shr; intros mrs e''.
  unfold choice_mode.
  set (shr' := shr_fexp _ _ _); case shr'; intros mrs' e'''.
  unfold binary_fit_aux.
  now case (shr_m mrs') as [|p|p]; [|case Z.leb|]. }
now case Bldexp as [s'|s'| |s' m' e'' B'].
Qed.

Definition Ffrexp_core_binary s m e :=
  if Zlt_bool (-prec) emin then
    (S754_finite s m e, 0%Z)
  else if (Z.to_pos prec <=? digits2_pos m)%positive then
    (S754_finite s m (-prec), (e + prec)%Z)
  else
    let d := (prec - Z.pos (digits2_pos m))%Z in
    (S754_finite s (shift_pos (Z.to_pos d) m) (-prec), (e + prec - d)%Z).

Lemma Bfrexp_correct_aux :
  forall sx mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Z.pos mx)) ex) in
  let z := fst (Ffrexp_core_binary sx mx ex) in
  let e := snd (Ffrexp_core_binary sx mx ex) in
  valid_binary z = true /\
  ((2 < emax)%Z -> (/2 <= Rabs (SF2R radix2 z) < 1)%R) /\
  (x = SF2R radix2 z * bpow radix2 e)%R.
Proof.
intros sx mx ex Bx.
set (x := F2R _).
set (z := fst _).
set (e := snd _); simpl.
assert (Dmx_le_prec : (Z.pos (digits2_pos mx) <= prec)%Z).
{ revert Bx; unfold bounded; rewrite Bool.andb_true_iff.
  unfold canonical_mantissa; rewrite <-Zeq_is_eq_bool; unfold fexp, FLT_exp.
  case (Z.max_spec (Z.pos (digits2_pos mx) + ex - prec) emin); lia. }
assert (Dmx_le_prec' : (digits2_pos mx <= Z.to_pos prec)%positive).
{ change (_ <= _)%positive
    with (Z.pos (digits2_pos mx) <= Z.pos (Z.to_pos prec))%Z.
  now rewrite Z2Pos.id; [|now apply prec_gt_0_]. }
unfold z, e, Ffrexp_core_binary.
case Z.ltb_spec ; intros Hp ; unfold emin in Hp.
{ apply (conj Bx).
  split.
  clear -Hp ; lia.
  now rewrite Rmult_1_r. }
case (Pos.leb_spec _ _); simpl; intro Dmx.
- unfold bounded, F2R; simpl.
  assert (Dmx' : digits2_pos mx = Z.to_pos prec).
  { now apply Pos.le_antisym. }
  assert (Dmx'' : Z.pos (digits2_pos mx) = prec).
  { now rewrite Dmx', Z2Pos.id; [|apply prec_gt_0_]. }
  split; [|split].
  + apply andb_true_intro.
    split ; cycle 1.
    { apply Zle_bool_true. clear -Hp ; lia. }
    apply Zeq_bool_true; unfold fexp, FLT_exp.
    rewrite Dmx', Z2Pos.id by apply prec_gt_0_.
    rewrite Z.max_l.
    ring.
    clear -Hp.
    unfold emin ; lia.
  + intros _.
    rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by now apply bpow_ge_0.
    rewrite <-abs_IZR, abs_cond_Zopp; simpl; split.
    * apply (Rmult_le_reg_r (bpow radix2 prec)); [now apply bpow_gt_0|].
      rewrite Rmult_assoc, <-bpow_plus, Z.add_opp_diag_l; simpl.
      rewrite Rmult_1_r.
      change (/ 2)%R with (bpow radix2 (- 1)); rewrite <-bpow_plus.
      rewrite <-Dmx'', Z.add_comm, Zpos_digits2_pos, Zdigits_mag; [|lia].
      set (b := bpow _ _).
      rewrite <- (Rabs_pos_eq (IZR _)) by now apply IZR_le.
      now apply bpow_mag_le, IZR_neq.
    * apply (Rmult_lt_reg_r (bpow radix2 prec)); [now apply bpow_gt_0|].
      rewrite Rmult_assoc, <-bpow_plus, Z.add_opp_diag_l; simpl.
      rewrite Rmult_1_l, Rmult_1_r.
      rewrite <-Dmx'', Zpos_digits2_pos, Zdigits_mag; [|lia].
      set (b := bpow _ _).
      rewrite <- (Rabs_pos_eq (IZR _)) by now apply IZR_le.
      apply bpow_mag_gt.
  + rewrite Rmult_assoc, <- bpow_plus.
    now replace (_ + _)%Z with ex by ring.
- unfold bounded, F2R; simpl.
  assert (Dmx' : (Z.pos (digits2_pos mx) < prec)%Z).
  { now rewrite <-(Z2Pos.id prec); [|now apply prec_gt_0_]. }
  split; [|split].
  + unfold bounded; apply andb_true_intro.
    split ; cycle 1.
    { apply Zle_bool_true. clear -Hp ; lia. }
    apply Zeq_bool_true; unfold fexp, FLT_exp.
    rewrite Zpos_digits2_pos, shift_pos_correct, Z.pow_pos_fold.
    rewrite Z2Pos.id; [|lia].
    rewrite Z.mul_comm; change 2%Z with (radix2 : Z).
    rewrite Zdigits_mult_Zpower; [|lia|lia].
    rewrite Zpos_digits2_pos; replace (_ - _)%Z with (- prec)%Z by ring.
    now apply Z.max_l.
  + rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)); [|now apply bpow_ge_0].
    rewrite <-abs_IZR, abs_cond_Zopp; simpl.
    rewrite shift_pos_correct, mult_IZR.
    change (IZR (Z.pow_pos _ _))
      with (bpow radix2 (Z.pos (Z.to_pos ((prec - Z.pos (digits2_pos mx)))))).
    rewrite Z2Pos.id; [|lia].
    rewrite Rmult_comm, <-Rmult_assoc, <-bpow_plus.
    set (d := Z.pos (digits2_pos mx)).
    replace (_ + _)%Z with (- d)%Z by ring; split.
    * apply (Rmult_le_reg_l (bpow radix2 d)); [now apply bpow_gt_0|].
      rewrite <-Rmult_assoc, <-bpow_plus, Z.add_opp_diag_r.
      rewrite Rmult_1_l.
      change (/ 2)%R with (bpow radix2 (- 1)); rewrite <-bpow_plus.
      rewrite <- (Rabs_pos_eq (IZR _)) by now apply IZR_le.
      unfold d; rewrite Zpos_digits2_pos, Zdigits_mag; [|lia].
      now apply bpow_mag_le, IZR_neq.
    * apply (Rmult_lt_reg_l (bpow radix2 d)); [now apply bpow_gt_0|].
      rewrite <-Rmult_assoc, <-bpow_plus, Z.add_opp_diag_r.
      rewrite Rmult_1_l, Rmult_1_r.
      rewrite <- (Rabs_pos_eq (IZR _)) by now apply IZR_le.
      unfold d; rewrite Zpos_digits2_pos, Zdigits_mag; [|lia].
      apply bpow_mag_gt.
  + rewrite Rmult_assoc, <-bpow_plus, shift_pos_correct.
    rewrite IZR_cond_Zopp, mult_IZR, cond_Ropp_mult_r, <-IZR_cond_Zopp.
    change (IZR (Z.pow_pos _ _))
      with (bpow radix2 (Z.pos (Z.to_pos (prec - Z.pos (digits2_pos mx))))).
    rewrite Z2Pos.id; [|lia].
    rewrite Rmult_comm, <-Rmult_assoc, <-bpow_plus.
    now replace (_ + _)%Z with ex by ring; rewrite Rmult_comm.
Qed.

Definition Bfrexp f :=
  match f with
  | B754_finite s m e H =>
    let e' := snd (Ffrexp_core_binary s m e) in
    (SF2B _ (proj1 (Bfrexp_correct_aux s m e H)), e')
  | _ => (f, (-2*emax-prec)%Z)
  end.

Theorem is_nan_Bfrexp :
  forall x,
  is_nan (fst (Bfrexp x)) = is_nan x.
Proof.
intros [sx|sx| |sx mx ex Bx] ; try easy.
simpl.
rewrite is_nan_SF2B.
unfold Ffrexp_core_binary.
destruct Zlt_bool ; try easy.
now destruct Pos.leb.
Qed.

Theorem Bfrexp_correct :
  forall f,
  is_finite_strict f = true ->
  let (z, e) := Bfrexp f in
  (B2R f = B2R z * bpow radix2 e)%R /\
  ( (2 < emax)%Z -> (/2 <= Rabs (B2R z) < 1)%R /\ e = mag radix2 (B2R f) ).
Proof.
intro f; case f; intro s; try discriminate; intros m e Hf _.
generalize (Bfrexp_correct_aux s m e Hf).
intros (_, (Hb, Heq)); simpl; rewrite B2R_SF2B.
split.
easy.
intros Hp.
specialize (Hb Hp).
split.
easy.
rewrite Heq, mag_mult_bpow.
- apply (Z.add_reg_l (- (snd (Ffrexp_core_binary s m e)))).
  now ring_simplify; symmetry; apply mag_unique.
- intro H; destruct Hb as (Hb, _); revert Hb; rewrite H, Rabs_R0; lra.
Qed.

(** Ulp *)

Lemma Bulp_correct_aux :
  bounded 1 emin = true.
Proof.
unfold bounded, canonical_mantissa.
rewrite Zeq_bool_true.
apply Zle_bool_true.
apply Z.max_l_iff, fexp_emax.
apply Z.max_r.
simpl digits2_pos.
generalize (prec_gt_0 prec).
lia.
Qed.

Definition Bulp x :=
  match x with
  | B754_zero _ => B754_finite false 1 emin Bulp_correct_aux
  | B754_infinity _ => B754_infinity false
  | B754_nan => B754_nan
  | B754_finite _ _ e _ => binary_normalize mode_ZR 1 e false
  end.

Theorem is_nan_Bulp :
  forall x,
  is_nan (Bulp x) = is_nan x.
Proof.
intros [sx|sx| |sx mx ex Bx] ; try easy.
unfold Bulp.
apply is_nan_binary_normalize.
Qed.

Theorem Bulp_correct :
  forall x,
  is_finite x = true ->
  B2R (Bulp x) = ulp radix2 fexp (B2R x) /\
  is_finite (Bulp x) = true /\
  Bsign (Bulp x) = false.
Proof.
intros [sx|sx| |sx mx ex Hx] Fx ; try easy ; simpl.
- repeat split.
  change fexp with (FLT_exp emin prec).
  rewrite ulp_FLT_0 by easy.
  apply F2R_bpow.
- destruct (binary_round_correct mode_ZR false 1 ex) as [H1 H2].
  revert H2.
  simpl.
  destruct (andb_prop _ _ Hx) as [H5 H6].
  replace (round _ _ _ _) with (bpow radix2 ex).
  rewrite Rlt_bool_true.
  intros [H2 [H3 H4]].
  split ; [|split].
  + rewrite B2R_SF2B.
    rewrite ulp_canonical.
    exact H2.
    now case sx.
    now apply canonical_canonical_mantissa.
  + now rewrite is_finite_SF2B.
  + now rewrite Bsign_SF2B.
  + rewrite Rabs_pos_eq by apply bpow_ge_0.
    apply bpow_lt.
    generalize (prec_gt_0 prec) (Zle_bool_imp_le _ _ H6).
    clear ; lia.
  + rewrite F2R_bpow.
    apply sym_eq, round_generic.
    typeclasses eauto.
    apply generic_format_FLT_bpow.
    easy.
    rewrite (canonical_canonical_mantissa false _ _ H5).
    apply Z.max_le_iff.
    now right.
Qed.

Theorem is_finite_strict_Bulp :
  forall x,
  is_finite_strict (Bulp x) = is_finite x.
Proof.
intros [sx|sx| |sx mx ex Bx] ; try easy.
generalize (Bulp_correct (B754_finite sx mx ex Bx) eq_refl).
destruct Bulp as [sy| | |] ; try easy.
intros [H _].
contradict H.
rewrite ulp_neq_0.
apply Rlt_not_eq.
apply bpow_gt_0.
apply F2R_neq_0.
now destruct sx.
Qed.

Definition Bulp' x := Bldexp mode_NE Bone (fexp (snd (Bfrexp x))).

Theorem Bulp'_correct :
  (2 < emax)%Z ->
  forall x,
  is_finite x = true ->
  Bulp' x = Bulp x.
Proof.
intros Hp x Fx.
assert (B2R (Bulp' x) = ulp radix2 fexp (B2R x) /\
        is_finite (Bulp' x) = true /\
        Bsign (Bulp' x) = false) as [H1 [H2 H3]].
{ destruct x as [sx|sx| |sx mx ex Hx] ; unfold Bulp'.
- replace (fexp _) with emin.
  + generalize (Bldexp_correct mode_NE Bone emin).
    rewrite Bone_correct, Rmult_1_l, round_generic;
      [|now apply valid_rnd_N|apply generic_format_bpow; unfold fexp, FLT_exp;
        rewrite Z.max_r; unfold Prec_gt_0 in prec_gt_0_; lia].
    rewrite Rlt_bool_true.
    * intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
      split; [|now split; [apply is_finite_Bone|apply Bsign_Bone]].
      simpl; unfold ulp; rewrite Req_bool_true; [|reflexivity].
      destruct (negligible_exp_FLT emin prec) as (n, (Hn, Hn')).
      change fexp with (FLT_exp emin prec); rewrite Hn.
      now unfold FLT_exp; rewrite Z.max_r;
        [|unfold Prec_gt_0 in prec_gt_0_; lia].
    * rewrite Rabs_pos_eq; [|now apply bpow_ge_0]; apply bpow_lt.
      apply emin_lt_emax.
  + simpl; change (fexp _) with (fexp (-2 * emax - prec)).
    unfold fexp, FLT_exp; rewrite Z.max_r; [reflexivity|].
    unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
- discriminate.
- discriminate.
- unfold ulp, cexp.
  set (f := B754_finite _ _ _ _).
  rewrite Req_bool_false.
  + destruct (Bfrexp_correct f (eq_refl _)) as (Hfr1, (Hfr2, Hfr3)).
    apply Hp.
    simpl.
    rewrite Hfr3.
    set (e' := fexp _).
    generalize (Bldexp_correct mode_NE Bone e').
    rewrite Bone_correct, Rmult_1_l, round_generic; [|now apply valid_rnd_N|].
    { rewrite Rlt_bool_true.
      - intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
        now split; [|split; [apply is_finite_Bone|apply Bsign_Bone]].
      - rewrite Rabs_pos_eq; [|now apply bpow_ge_0].
        unfold e', fexp, FLT_exp.
        apply bpow_lt.
        case (Z.max_spec (mag radix2 (B2R f) - prec) emin)
          as [(_, Hm)|(_, Hm)]; rewrite Hm.
        apply emin_lt_emax.
        apply (Zplus_lt_reg_r _ _ prec); ring_simplify.
        assert (mag radix2 (B2R f) <= emax)%Z;
          [|now unfold Prec_gt_0 in prec_gt_0_; lia].
        apply mag_le_bpow; [|now apply abs_B2R_lt_emax].
        now unfold f, B2R; apply F2R_neq_0; case sx. }
    apply generic_format_bpow, Z.max_lub.
    * unfold Prec_gt_0 in prec_gt_0_; lia.
    * apply Z.le_max_r.
  + now unfold f, B2R; apply F2R_neq_0; case sx. }
destruct (Bulp_correct x Fx) as [H4 [H5 H6]].
apply B2R_Bsign_inj ; try easy.
now rewrite H4.
now rewrite H3.
Qed.

(** Successor (and predecessor) *)

Definition Bsucc x :=
  match x with
  | B754_zero _ => B754_finite false 1 emin Bulp_correct_aux
  | B754_infinity false => x
  | B754_infinity true => Bopp Bmax_float
  | B754_nan => B754_nan
  | B754_finite false mx ex _ =>
    SF2B _ (proj1 (binary_round_correct mode_UP false (mx + 1) ex))
  | B754_finite true mx ex _ =>
    SF2B _ (proj1 (binary_round_correct mode_ZR true (xO mx - 1) (ex - 1)))
  end.

Theorem is_nan_Bsucc :
  forall x,
  is_nan (Bsucc x) = is_nan x.
Proof.
unfold Bsucc.
intros [sx|[|]| |[|] mx ex Bx] ; try easy.
rewrite is_nan_SF2B.
apply is_nan_binary_round.
rewrite is_nan_SF2B.
apply is_nan_binary_round.
Qed.

Theorem Bsucc_correct :
  forall x,
  is_finite x = true ->
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc x) = true /\
    (Bsign (Bsucc x) = Bsign x && is_finite_strict x)%bool
  else
    B2SF (Bsucc x) = S754_infinity false.
Proof.
intros [sx|sx| | [|] mx ex Bx] Hx ; try easy ; clear Hx.
- simpl.
  change fexp with (FLT_exp emin prec).
  rewrite succ_0, ulp_FLT_0 by easy.
  rewrite Rlt_bool_true.
  repeat split ; cycle 1.
  now case sx.
  apply F2R_bpow.
  apply bpow_lt.
  apply emin_lt_emax.
- change (B2R (B754_finite _ _ _ _)) with (F2R (Fopp (Float radix2 (Zpos mx) ex))).
  rewrite F2R_opp, succ_opp.
  rewrite Rlt_bool_true ; cycle 1.
  { apply Rle_lt_trans with 0%R.
    2: apply bpow_gt_0.
    rewrite <- Ropp_0.
    apply Ropp_le_contravar.
    apply pred_ge_0.
    now apply FLT_exp_valid.
    now apply F2R_gt_0.
    apply generic_format_canonical.
    now apply (canonical_bounded false). }
  simpl.
  rewrite B2R_SF2B, is_finite_SF2B, Bsign_SF2B.
  generalize (binary_round_correct mode_ZR true (xO mx - 1) (ex - 1)).
  set (z := binary_round _ _ _ _).
  rewrite F2R_cond_Zopp.
  simpl.
  rewrite round_ZR_opp.
  rewrite round_ZR_DN by now apply F2R_ge_0.
  assert (H: F2R (Float radix2 (Zpos (xO mx - 1)) (ex - 1)) = (F2R (Float radix2 (Zpos mx) ex) - F2R (Float radix2 1 (ex - 1)))%R).
  { rewrite (F2R_change_exp _ (ex - 1) _ ex) by apply Z.le_pred_l.
    rewrite <- F2R_minus, Fminus_same_exp.
    apply F2R_eq.
    replace (ex - (ex - 1))%Z with 1%Z by ring.
    now rewrite Zmult_comm. }
  rewrite Rlt_bool_true.
  + intros [_ [H1 [H2 H3]]].
    split.
    2: now split.
    rewrite H1, H.
    apply f_equal.
    apply round_DN_minus_eps_pos.
      now apply FLT_exp_valid.
      now apply F2R_gt_0.
      apply (generic_format_B2R (B754_finite false mx ex Bx)).
    split.
      now apply F2R_gt_0.
    rewrite F2R_bpow.
    change fexp with (FLT_exp emin prec).
    destruct (ulp_FLT_pred_pos radix2 emin prec (F2R (Float radix2 (Zpos mx) ex))) as [Hu|[Hu1 Hu2]].
    * apply (generic_format_B2R (B754_finite false mx ex Bx)).
    * now apply F2R_ge_0.
    * rewrite Hu.
      rewrite ulp_canonical.
      apply bpow_le.
      apply Z.le_pred_l.
      easy.
      now apply (canonical_bounded false).
    * rewrite Hu2.
      rewrite ulp_canonical.
      rewrite <- (Zmult_1_r radix2).
      change (_ / _)%R with (bpow radix2 ex * bpow radix2 (-1))%R.
      rewrite <- bpow_plus.
      apply Rle_refl.
      easy.
      now apply (canonical_bounded false).
  + rewrite Rabs_Ropp, Rabs_pos_eq.
    eapply Rle_lt_trans.
    2: apply bounded_lt_emax with (1 := Bx).
    apply Rle_trans with (F2R (Float radix2 (Zpos (xO mx - 1)) (ex - 1))).
    apply round_DN_pt.
    now apply FLT_exp_valid.
    rewrite H.
    rewrite <- (Rminus_0_r (F2R _)) at 2.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    now apply F2R_ge_0.
    apply round_DN_pt.
    now apply FLT_exp_valid.
    apply generic_format_0.
    now apply F2R_ge_0.
- assert (Cx := proj1 (andb_prop _ _ Bx)).
  apply (canonical_canonical_mantissa false) in Cx.
  replace (succ _ _ _) with (F2R (Float radix2 (Zpos mx + 1) ex)) ; cycle 1.
  { unfold succ, B2R.
    rewrite Rle_bool_true by now apply F2R_ge_0.
    rewrite ulp_canonical by easy.
    rewrite <- F2R_bpow.
    rewrite <- F2R_plus.
    now rewrite Fplus_same_exp. }
  simpl.
  rewrite B2R_SF2B, is_finite_SF2B, Bsign_SF2B.
  generalize (binary_round_correct mode_UP false (mx + 1) ex).
  simpl.
  rewrite round_generic.
  + rewrite Rabs_pos_eq by now apply F2R_ge_0.
    case Rlt_bool_spec ; intros Hs.
    now intros [_ H].
    intros H.
    rewrite B2SF_SF2B.
    now rewrite (proj2 H).
  + apply valid_rnd_UP.
  + destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as [e He].
    rewrite Rabs_pos_eq in He by now apply F2R_ge_0.
    refine (_ (He _)).
    2: now apply F2R_neq_0.
    clear He. intros He.
    destruct (F2R_p1_le_bpow _ (Zpos mx) _ _ eq_refl (proj2 He)) as [H|H].
    * apply generic_format_F2R.
      intros _.
      rewrite Cx at 2.
      apply cexp_ge_bpow.
      apply FLT_exp_monotone.
      rewrite Rabs_pos_eq by now apply F2R_ge_0.
      rewrite (mag_unique_pos _ _ e).
      apply He.
      split.
      apply Rle_trans with (1 := proj1 He).
      apply F2R_le.
      apply Z.le_succ_diag_r.
      exact H.
    * simpl in H.
      rewrite H.
      apply generic_format_FLT_bpow.
      easy.
      apply le_bpow with radix2.
      apply Rlt_le.
      apply Rle_lt_trans with (2 := proj2 He).
      apply generic_format_ge_bpow with fexp.
      intros e'.
      apply Z.le_max_r.
      now apply F2R_gt_0.
      now apply generic_format_canonical.
Qed.

Definition Bpred x := Bopp (Bsucc (Bopp x)).

Theorem is_nan_Bpred :
  forall x,
  is_nan (Bpred x) = is_nan x.
Proof.
intros x.
unfold Bpred.
rewrite is_nan_Bopp, is_nan_Bsucc.
apply is_nan_Bopp.
Qed.

Theorem Bpred_correct :
  forall x,
  is_finite x = true ->
  if Rlt_bool (- bpow radix2 emax) (pred radix2 fexp (B2R x)) then
    B2R (Bpred x) = pred radix2 fexp (B2R x) /\
    is_finite (Bpred x) = true /\
    (Bsign (Bpred x) = Bsign x || negb (is_finite_strict x))%bool
  else
    B2SF (Bpred x) = S754_infinity true.
Proof.
intros x Fx.
assert (Fox : is_finite (Bopp x) = true).
{ now rewrite is_finite_Bopp. }
rewrite <-(Ropp_involutive (B2R x)), <-B2R_Bopp.
rewrite pred_opp, Rlt_bool_opp.
generalize (Bsucc_correct _ Fox).
case (Rlt_bool _ _).
- intros (HR, (HF, HS)); unfold Bpred.
  rewrite B2R_Bopp, HR, is_finite_Bopp.
  rewrite <-(Bool.negb_involutive (Bsign x)), <-Bool.negb_andb.
  apply (conj eq_refl).
  apply (conj HF).
  rewrite Bsign_Bopp, <-(Bsign_Bopp x), HS.
  + now rewrite is_finite_strict_Bopp.
  + now revert Fx; case x.
  + now revert HF; case (Bsucc _).
- now unfold Bpred; case (Bsucc _); intro s; case s.
Qed.

Definition Bpred_pos' x :=
  match x with
  | B754_finite _ mx _ _ =>
    let d :=
      if (mx~0 =? shift_pos (Z.to_pos prec) 1)%positive then
        Bldexp mode_NE Bone (fexp (snd (Bfrexp x) - 1))
      else
        Bulp' x in
    Bminus mode_NE x d
  | _ => x
  end.

Theorem Bpred_pos'_correct :
  (2 < emax)%Z ->
  forall x,
  (0 < B2R x)%R ->
  Bpred_pos' x = Bpred x.
Proof.
intros Hp x Fx.
assert (B2R (Bpred_pos' x) = pred_pos radix2 fexp (B2R x) /\
        is_finite (Bpred_pos' x) = true /\
        Bsign (Bpred_pos' x) = false) as [H1 [H2 H3]].
{ generalize (Bfrexp_correct x).
  destruct x as [sx|sx| |sx mx ex Bx] ; try elim (Rlt_irrefl _ Fx).
  intros Hfrexpx.
  assert (Hsx : sx = false).
  { apply gt_0_F2R in Fx.
    revert Fx.
    now case sx. }
  clear Fx.
  rewrite Hsx in Hfrexpx |- *; clear Hsx sx.
  specialize (Hfrexpx (eq_refl _)).
  simpl in Hfrexpx; rewrite B2R_SF2B in Hfrexpx.
  destruct Hfrexpx as (Hfrexpx_bounds, (Hfrexpx_eq, Hfrexpx_exp)).
  apply Hp.
  unfold Bpred_pos', Bfrexp.
  simpl (snd (_, snd _)).
  rewrite Hfrexpx_exp.
  set (x' := B754_finite _ _ _ _).
  set (xr := F2R _).
  assert (Nzxr : xr <> 0%R).
  { now apply F2R_neq_0. }
  assert (Hulp := Bulp_correct x' (eq_refl _)).
  rewrite <- (Bulp'_correct Hp x') in Hulp by easy.
  assert (Hldexp := Bldexp_correct mode_NE Bone (fexp (mag radix2 xr - 1))).
  rewrite Bone_correct, Rmult_1_l in Hldexp.
  assert (Fbpowxr : generic_format radix2 fexp
                      (bpow radix2 (fexp (mag radix2 xr - 1)))).
  { apply generic_format_bpow, Z.max_lub.
    - unfold Prec_gt_0 in prec_gt_0_; lia.
    - apply Z.le_max_r. }
  assert (H : Rlt_bool (Rabs
               (round radix2 fexp (round_mode mode_NE)
                  (bpow radix2 (fexp (mag radix2 xr - 1)))))
              (bpow radix2 emax) = true); [|rewrite H in Hldexp; clear H].
  { apply Rlt_bool_true; rewrite round_generic;
      [|apply valid_rnd_round_mode|apply Fbpowxr].
    rewrite Rabs_pos_eq; [|apply bpow_ge_0]; apply bpow_lt.
    apply Z.max_lub_lt. 2: apply emin_lt_emax.
    apply (Zplus_lt_reg_r _ _ (prec + 1)); ring_simplify.
    rewrite Z.add_1_r; apply Zle_lt_succ, mag_le_bpow.
    - exact Nzxr.
    - apply (Rlt_le_trans _ (bpow radix2 emax)).
      + change xr with (B2R x'); apply abs_B2R_lt_emax.
      + apply bpow_le; unfold Prec_gt_0 in prec_gt_0_; lia. }
  set (d := if (mx~0 =? _)%positive then _ else _).
  assert (Hminus := Bminus_correct mode_NE x' d (eq_refl _)).
  assert (Fd : is_finite d = true).
  { unfold d; case (_ =? _)%positive.
    - now rewrite (proj1 (proj2 Hldexp)), is_finite_Bone.
    - now rewrite (proj1 (proj2 Hulp)). }
  specialize (Hminus Fd).
  assert (Px : (0 <= B2R x')%R).
  { unfold B2R, x', F2R; simpl.
    now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
  assert (Pd : (0 <= B2R d)%R).
  { unfold d; case (_ =? _)%positive.
    - rewrite (proj1 Hldexp).
      now rewrite round_generic; [apply bpow_ge_0|apply valid_rnd_N|].
    - rewrite (proj1 Hulp); apply ulp_ge_0. }
  assert (Hdlex : (B2R d <= B2R x')%R).
  { unfold d; case (_ =? _)%positive.
    - rewrite (proj1 Hldexp).
      rewrite round_generic; [|now apply valid_rnd_N|now simpl].
      apply (Rle_trans _ (bpow radix2 (mag radix2 xr - 1))).
      + apply bpow_le, Z.max_lub.
        * unfold Prec_gt_0 in prec_gt_0_; lia.
        * apply (Zplus_le_reg_r _ _ 1); ring_simplify.
          apply mag_ge_bpow.
          replace (_ - 1)%Z with emin by ring.
          now change xr with (B2R x'); apply abs_B2R_ge_emin.
      + rewrite <-(Rabs_pos_eq _ Px).
        now change xr with (B2R x'); apply bpow_mag_le.
    - rewrite (proj1 Hulp); apply ulp_le_id.
      + assert (B2R x' <> 0%R); [exact Nzxr|lra].
      + apply generic_format_B2R. }
  assert (H : Rlt_bool
            (Rabs
               (round radix2 fexp
                  (round_mode mode_NE) (B2R x' - B2R d)))
            (bpow radix2 emax) = true); [|rewrite H in Hminus; clear H].
  { apply Rlt_bool_true.
    rewrite <-round_NE_abs; [|now apply FLT_exp_valid].
    rewrite Rabs_pos_eq; [|lra].
    apply (Rle_lt_trans _ (B2R x')).
    - apply round_le_generic;
        [now apply FLT_exp_valid|now apply valid_rnd_N| |lra].
      apply generic_format_B2R.
    - apply (Rle_lt_trans _ _ _ (Rle_abs _)), abs_B2R_lt_emax. }
  rewrite (proj1 Hminus).
  rewrite (proj1 (proj2 Hminus)).
  rewrite (proj2 (proj2 Hminus)).
  split; [|split; [reflexivity|now case (Rcompare_spec _ _); [lra| |]]].
  unfold pred_pos, d.
  case (Pos.eqb_spec _ _); intro Hd; case (Req_bool_spec _ _); intro Hpred.
  + rewrite (proj1 Hldexp).
    rewrite (round_generic _ _ _ _ Fbpowxr).
    change xr with (B2R x').
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    * rewrite round_generic; [reflexivity|now apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid|apply generic_format_B2R|].
      change xr with (B2R x') in Nzxr; lra.
    * now unfold pred_pos; rewrite Req_bool_true.
  + exfalso; apply Hpred.
    assert (Hmx : IZR (Z.pos mx) = bpow radix2 (prec - 1)).
    { apply (Rmult_eq_reg_l 2); [|lra]; rewrite <-mult_IZR.
      change (2 * Z.pos mx)%Z with (Z.pos mx~0); rewrite Hd.
      rewrite shift_pos_correct, Z.mul_1_r.
      change (IZR (Z.pow_pos _ _)) with (bpow radix2 (Z.pos (Z.to_pos prec))).
      rewrite Z2Pos.id; [|exact prec_gt_0_].
      change 2%R with (bpow radix2 1); rewrite <-bpow_plus.
      f_equal; ring. }
    unfold x' at 1; unfold B2R at 1; unfold F2R; simpl.
    rewrite Hmx, <-bpow_plus; f_equal.
    apply (Z.add_reg_l 1); ring_simplify; symmetry; apply mag_unique_pos.
    unfold F2R; simpl; rewrite Hmx, <-bpow_plus; split.
    * right; f_equal; ring.
    * apply bpow_lt; lia.
  + rewrite (proj1 Hulp).
    assert (H : ulp radix2 fexp (B2R x')
                = bpow radix2 (fexp (mag radix2 (B2R x') - 1)));
      [|rewrite H; clear H].
    { unfold ulp; rewrite Req_bool_false; [|now simpl].
      unfold cexp; f_equal.
      assert (H : (mag radix2 (B2R x') <= emin + prec)%Z).
      { assert (Hcm : canonical_mantissa mx ex = true).
        { now generalize Bx; unfold bounded; rewrite Bool.andb_true_iff. }
        apply (canonical_canonical_mantissa false) in Hcm.
        revert Hcm; fold emin; unfold canonical, cexp; simpl.
        change (F2R _) with (B2R x'); intro Hex.
        apply Z.nlt_ge; intro H'; apply Hd.
        apply Pos2Z.inj_pos; rewrite shift_pos_correct, Z.mul_1_r.
        apply eq_IZR; change (IZR (Z.pow_pos _ _))
          with (bpow radix2 (Z.pos (Z.to_pos prec))).
        rewrite Z2Pos.id; [|exact prec_gt_0_].
        change (Z.pos mx~0) with (2 * Z.pos mx)%Z.
        rewrite Z.mul_comm, mult_IZR.
        apply (Rmult_eq_reg_r (bpow radix2 (ex - 1)));
          [|apply Rgt_not_eq, bpow_gt_0].
        change 2%R with (bpow radix2 1); rewrite Rmult_assoc, <-!bpow_plus.
        replace (1 + _)%Z with ex by ring.
        unfold B2R at 1, F2R in Hpred; simpl in Hpred; rewrite Hpred.
        change (F2R _) with (B2R x'); rewrite Hex.
        unfold fexp, FLT_exp; rewrite Z.max_l; [f_equal; ring|lia]. }
      now unfold fexp, FLT_exp; do 2 (rewrite Z.max_r; [|lia]). }
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    * rewrite round_generic; [reflexivity|apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid| |change xr with (B2R x') in Nzxr; lra].
      apply generic_format_B2R.
    * now unfold pred_pos; rewrite Req_bool_true.
  + rewrite (proj1 Hulp).
    replace (_ - _)%R with (pred_pos radix2 fexp (B2R x')).
    * rewrite round_generic; [reflexivity|now apply valid_rnd_N|].
      apply generic_format_pred_pos;
        [now apply FLT_exp_valid|apply generic_format_B2R|].
      change xr with (B2R x') in Nzxr; lra.
    * now unfold pred_pos; rewrite Req_bool_false. }
assert (is_finite x = true /\ Bsign x = false) as [H4 H5].
{ clear -Fx.
  destruct x as [| | |sx mx ex Hx] ; try elim Rlt_irrefl with (1 := Fx).
  repeat split.
  destruct sx.
  elim Rlt_not_le with (1 := Fx).
  now apply F2R_le_0.
  easy. }
generalize (Bpred_correct x H4).
rewrite Rlt_bool_true ; cycle 1.
{ apply Rlt_le_trans with 0%R.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  apply bpow_gt_0.
  apply pred_ge_0.
  now apply FLT_exp_valid.
  exact Fx.
  apply generic_format_B2R. }
intros [H7 [H8 H9]].
apply eq_sym.
apply B2R_Bsign_inj ; try easy.
rewrite H7, H1.
apply pred_eq_pos.
now apply Rlt_le.
rewrite H9, H3.
rewrite is_finite_strict_B2R by now apply Rgt_not_eq.
now rewrite H5.
Qed.

Definition Bsucc' x :=
  match x with
  | B754_zero _ => Bldexp mode_NE Bone emin
  | B754_infinity false => x
  | B754_infinity true => Bopp Bmax_float
  | B754_nan => B754_nan
  | B754_finite false _ _ _ => Bplus mode_NE x (Bulp x)
  | B754_finite true _ _ _ => Bopp (Bpred_pos' (Bopp x))
  end.

Theorem Bsucc'_correct :
  (2 < emax)%Z ->
  forall x,
  is_finite x = true ->
  Bsucc' x = Bsucc x.
Proof.
intros Hp x Fx.
destruct x as [sx|sx| |sx mx ex Bx] ; try easy.
{ generalize (Bldexp_correct mode_NE Bone emin).
  rewrite Bone_correct, Rmult_1_l.
  rewrite round_generic.
  rewrite Rlt_bool_true.
  simpl.
  intros [H1 [H2 H3]].
  apply B2R_inj.
  apply is_finite_strict_B2R.
  rewrite H1.
  apply Rgt_not_eq.
  apply bpow_gt_0.
  easy.
  rewrite H1.
  apply eq_sym, F2R_bpow.
  rewrite Rabs_pos_eq by now apply bpow_ge_0.
  apply bpow_lt, emin_lt_emax.
  apply valid_rnd_N.
  apply generic_format_bpow.
  unfold fexp.
  rewrite Z.max_r.
  apply Z.le_refl.
  generalize (prec_gt_0 prec).
  lia. }
set (x := B754_finite sx mx ex Bx).
assert (H:
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc' x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc' x) = true /\
    Bsign (Bsucc' x) = sx
  else
    B2SF (Bsucc' x) = S754_infinity false).
{
  assert (Hsucc : succ radix2 fexp 0 = bpow radix2 emin).
  { rewrite succ_0.
    now apply ulp_FLT_0. }
  unfold Bsucc', x; destruct sx.
  + case Rlt_bool_spec; intro Hover.
    * rewrite B2R_Bopp; simpl (Bopp (B754_finite _ _ _ _)).
      rewrite is_finite_Bopp.
      set (ox := B754_finite false mx ex Bx).
      assert (Hpred := Bpred_correct ox eq_refl).
      rewrite Bpred_pos'_correct ; cycle 1.
        exact Hp.
        now apply F2R_gt_0.
      rewrite Rlt_bool_true in Hpred.
      rewrite (proj1 Hpred), (proj1 (proj2 Hpred)).
      split.
      rewrite <- succ_opp.
      simpl.
      now rewrite <- F2R_opp.
      apply (conj eq_refl).
      rewrite Bsign_Bopp, (proj2 (proj2 Hpred)).
      easy.
      generalize (proj1 (proj2 Hpred)).
      now case Bpred.
      apply Rlt_le_trans with 0%R.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar, bpow_gt_0.
      apply pred_ge_0.
      now apply FLT_exp_valid.
      now apply F2R_gt_0.
      apply generic_format_B2R.
    * exfalso; revert Hover; apply Rlt_not_le.
      apply (Rle_lt_trans _ (succ radix2 fexp 0)).
      { apply succ_le; [now apply FLT_exp_valid|apply generic_format_B2R|
                        apply generic_format_0|].
        unfold B2R, F2R; simpl; change (Z.neg mx) with (- Z.pos mx)%Z.
        rewrite opp_IZR, <-Ropp_mult_distr_l, <-Ropp_0; apply Ropp_le_contravar.
        now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
      rewrite Hsucc; apply bpow_lt.
      apply emin_lt_emax.
  + fold x.
    assert (Hulp := Bulp_correct x (eq_refl _)).
    assert (Hplus := Bplus_correct mode_NE x (Bulp x) (eq_refl _)).
    rewrite (proj1 (proj2 Hulp)) in Hplus; specialize (Hplus (eq_refl _)).
    assert (Px : (0 <= B2R x)%R).
    { now apply F2R_ge_0. }
    assert (Hsucc' : (succ radix2 fexp (B2R x)
                      = B2R x + ulp radix2 fexp (B2R x))%R).
    { now unfold succ; rewrite (Rle_bool_true _ _ Px). }
    rewrite (proj1 Hulp), <- Hsucc' in Hplus.
    rewrite round_generic in Hplus;
      [|apply valid_rnd_N| now apply generic_format_succ;
                           [apply FLT_exp_valid|apply generic_format_B2R]].
    rewrite Rabs_pos_eq in Hplus; [|apply (Rle_trans _ _ _ Px), succ_ge_id].
    revert Hplus; case Rlt_bool_spec; intros Hover Hplus.
    * split; [now simpl|split; [now simpl|]].
      rewrite (proj2 (proj2 Hplus)); case Rcompare_spec.
      { intro H; exfalso; revert H.
        apply Rle_not_lt, (Rle_trans _ _ _ Px), succ_ge_id. }
      { intro H; exfalso; revert H; apply Rgt_not_eq, Rlt_gt.
        apply (Rlt_le_trans _ (B2R x)); [|apply succ_ge_id].
        now apply Rmult_lt_0_compat; [apply IZR_lt|apply bpow_gt_0]. }
      now simpl.
    * now rewrite (proj1 Hplus). }
generalize (Bsucc_correct x Fx).
revert H.
case Rlt_bool_spec ; intros H.
intros [H1 [H2 H3]] [H4 [H5 H6]].
apply B2R_Bsign_inj ; try easy.
now rewrite H4.
rewrite H3, H6.
simpl.
now case sx.
intros H1 H2.
apply B2SF_inj.
now rewrite H1, H2.
Qed.

End Binary.

Arguments B754_zero {prec} {emax}.
Arguments B754_infinity {prec} {emax}.
Arguments B754_nan {prec} {emax}.
Arguments B754_finite {prec} {emax}.

Arguments SF2B {prec} {emax}.
Arguments B2SF {prec} {emax}.
Arguments B2R {prec} {emax}.

Arguments is_finite_strict {prec} {emax}.
Arguments is_finite {prec} {emax}.
Arguments is_nan {prec} {emax}.

Arguments erase {prec} {emax}.
Arguments Bsign {prec} {emax}.
Arguments Bcompare {prec} {emax}.
Arguments Beqb {prec} {emax}.
Arguments Bltb {prec} {emax}.
Arguments Bleb {prec} {emax}.
Arguments Bopp {prec} {emax}.
Arguments Babs {prec} {emax}.
Arguments Bone {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bmax_float {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.

Arguments Bplus {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bminus {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bmult {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bfma {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bdiv {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bsqrt {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bnearbyint {prec} {emax} {prec_lt_emax_}.
Arguments Btrunc {prec} {emax}.

Arguments Bldexp {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bnormfr_mantissa {prec} {emax}.
Arguments Bfrexp {prec} {emax} {prec_gt_0_}.
Arguments Bulp {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bulp' {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bsucc {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bpred {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.
Arguments Bpred_pos' {prec} {emax} {prec_gt_0_} {prec_lt_emax_}.

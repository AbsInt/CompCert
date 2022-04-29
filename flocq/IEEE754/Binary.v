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

(** * IEEE-754 arithmetic *)

From Coq Require Import ZArith Reals Psatz SpecFloat.

Require Import Core Round Bracket Operations Div Sqrt Relative BinarySingleNaN.

Arguments BinarySingleNaN.B754_zero {prec emax}.
Arguments BinarySingleNaN.B754_infinity {prec emax}.
Arguments BinarySingleNaN.B754_nan {prec emax}.
Arguments BinarySingleNaN.B754_finite {prec emax}.

Section AnyRadix.

Inductive full_float :=
  | F754_zero (s : bool)
  | F754_infinity (s : bool)
  | F754_nan (s : bool) (m : positive)
  | F754_finite (s : bool) (m : positive) (e : Z).

Definition FF2SF x :=
  match x with
  | F754_zero s => S754_zero s
  | F754_infinity s => S754_infinity s
  | F754_nan _ _ => S754_nan
  | F754_finite s m e => S754_finite s m e
  end.

Definition FF2R beta x :=
  match x with
  | F754_finite s m e => F2R (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

Lemma SF2R_FF2SF :
  forall beta x,
  SF2R beta (FF2SF x) = FF2R beta x.
Proof.
now intros beta [s|s|s m|s m e].
Qed.

Definition SF2FF x :=
  match x with
  | S754_zero s => F754_zero s
  | S754_infinity s => F754_infinity s
  | S754_nan => F754_nan false xH
  | S754_finite s m e => F754_finite s m e
  end.

Lemma FF2SF_SF2FF :
  forall x,
  FF2SF (SF2FF x) = x.
Proof.
now intros [s|s| |s m e].
Qed.

Lemma FF2R_SF2FF :
  forall beta x,
  FF2R beta (SF2FF x) = SF2R beta x.
Proof.
now intros beta [s|s| |s m e].
Qed.

Definition is_nan_FF f :=
  match f with
  | F754_nan _ _ => true
  | _ => false
  end.

Lemma is_nan_SF2FF :
  forall x,
  is_nan_FF (SF2FF x) = is_nan_SF x.
Proof.
now intros [s|s| |s m e].
Qed.

Lemma is_nan_FF2SF :
  forall x,
  is_nan_SF (FF2SF x) = is_nan_FF x.
Proof.
now intros [s|s|s m|s m e].
Qed.

Lemma SF2FF_FF2SF :
  forall x,
  is_nan_FF x = false ->
  SF2FF (FF2SF x) = x.
Proof.
now intros [s|s|s m|s m e] H.
Qed.

Definition sign_FF x :=
  match x with
  | F754_nan s _ => s
  | F754_zero s => s
  | F754_infinity s => s
  | F754_finite s _ _ => s
  end.

Definition is_finite_FF f :=
  match f with
  | F754_finite _ _ _ => true
  | F754_zero _ => true
  | _ => false
  end.

Lemma is_finite_SF2FF :
  forall x,
  is_finite_FF (SF2FF x) = is_finite_SF x.
Proof.
now intros [| | |].
Qed.

Lemma sign_SF2FF :
  forall x,
  sign_FF (SF2FF x) = sign_SF x.
Proof.
now intros [| | |].
Qed.

End AnyRadix.

Section Binary.

Arguments exist {A} {P}.

(** [prec] is the number of bits of the mantissa including the implicit one;
    [emax] is the exponent of the infinities.
    For instance, binary32 is defined by [prec = 24] and [emax = 128]. *)
Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Context (prec_lt_emax_ : Prec_lt_emax prec emax).

Notation emin := (emin prec emax) (only parsing).
Notation fexp := (fexp prec emax) (only parsing).
Instance fexp_correct : Valid_exp fexp := FLT_exp_valid emin prec.
Instance fexp_monotone : Monotone_exp fexp := FLT_exp_monotone emin prec.

Notation canonical_mantissa := (canonical_mantissa prec emax).

Notation bounded := (SpecFloat.bounded prec emax).

Definition nan_pl pl :=
  Zlt_bool (Zpos (digits2_pos pl)) prec.

Notation valid_binary_SF := (valid_binary prec emax).

Definition valid_binary x :=
  match x with
  | F754_finite _ m e => bounded m e
  | F754_nan _ pl => nan_pl pl
  | _ => true
  end.

Lemma valid_binary_SF2FF :
  forall x,
  is_nan_SF x = false ->
  valid_binary (SF2FF x) = valid_binary_SF x.
Proof.
now intros [sx|sx| |sx mx ex] H.
Qed.

(** Basic type used for representing binary FP numbers.
    Note that there is exactly one such object per FP datum. *)

Inductive binary_float :=
  | B754_zero (s : bool)
  | B754_infinity (s : bool)
  | B754_nan (s : bool) (pl : positive) :
    nan_pl pl = true -> binary_float
  | B754_finite (s : bool) (m : positive) (e : Z) :
    bounded m e = true -> binary_float.

Definition B2BSN (x : binary_float) : BinarySingleNaN.binary_float prec emax :=
  match x with
  | B754_zero s => BinarySingleNaN.B754_zero s
  | B754_infinity s => BinarySingleNaN.B754_infinity s
  | B754_nan _ _ _ => BinarySingleNaN.B754_nan
  | B754_finite s m e H => BinarySingleNaN.B754_finite s m e H
  end.

Definition FF2B x :=
  match x as x return valid_binary x = true -> binary_float with
  | F754_finite s m e => B754_finite s m e
  | F754_infinity s => fun _ => B754_infinity s
  | F754_zero s => fun _ => B754_zero s
  | F754_nan b pl => fun H => B754_nan b pl H
  end.

Definition B2FF x :=
  match x with
  | B754_finite s m e _ => F754_finite s m e
  | B754_infinity s => F754_infinity s
  | B754_zero s => F754_zero s
  | B754_nan b pl _ => F754_nan b pl
  end.

Definition B2R f :=
  match f with
  | B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

Definition B2SF (x : binary_float) :=
  match x with
  | B754_finite s m e _ => S754_finite s m e
  | B754_infinity s => S754_infinity s
  | B754_zero s => S754_zero s
  | B754_nan _ _ _ => S754_nan
  end.

Lemma B2SF_B2BSN :
  forall x,
  BinarySingleNaN.B2SF (B2BSN x) = B2SF x.
Proof.
now intros [sx|sx|sx px Px|sx mx ex Bx].
Qed.

Lemma B2SF_FF2B :
  forall x Bx,
  B2SF (FF2B x Bx) = FF2SF x.
Proof.
now intros [sx|sx|sx px|sx mx ex] Bx.
Qed.

Lemma B2R_B2BSN :
  forall x, BinarySingleNaN.B2R (B2BSN x) = B2R x.
Proof.
intros x.
now destruct x.
Qed.

Lemma FF2SF_B2FF :
  forall x,
  FF2SF (B2FF x) = B2SF x.
Proof.
now intros [sx|sx|sx plx|sx mx ex].
Qed.

Theorem FF2R_B2FF :
  forall x,
  FF2R radix2 (B2FF x) = B2R x.
Proof.
now intros [sx|sx|sx plx Hplx|sx mx ex Hx].
Qed.

Theorem B2FF_FF2B :
  forall x Hx,
  B2FF (FF2B x Hx) = x.
Proof.
now intros [sx|sx|sx plx|sx mx ex] Hx.
Qed.

Theorem valid_binary_B2FF :
  forall x,
  valid_binary (B2FF x) = true.
Proof.
now intros [sx|sx|sx plx Hplx|sx mx ex Hx].
Qed.

Theorem FF2B_B2FF :
  forall x H,
  FF2B (B2FF x) H = x.
Proof.
intros [sx|sx|sx plx Hplx|sx mx ex Hx] H ; try easy.
apply f_equal, eqbool_irrelevance.
apply f_equal, eqbool_irrelevance.
Qed.

Theorem FF2B_B2FF_valid :
  forall x,
  FF2B (B2FF x) (valid_binary_B2FF x) = x.
Proof.
intros x.
apply FF2B_B2FF.
Qed.

Theorem B2R_FF2B :
  forall x Hx,
  B2R (FF2B x Hx) = FF2R radix2 x.
Proof.
now intros [sx|sx|sx plx|sx mx ex] Hx.
Qed.

Theorem match_FF2B :
  forall {T} fz fi fn ff x Hx,
  match FF2B x Hx return T with
  | B754_zero sx => fz sx
  | B754_infinity sx => fi sx
  | B754_nan b p _ => fn b p
  | B754_finite sx mx ex _ => ff sx mx ex
  end =
  match x with
  | F754_zero sx => fz sx
  | F754_infinity sx => fi sx
  | F754_nan b p => fn b p
  | F754_finite sx mx ex => ff sx mx ex
  end.
Proof.
now intros T fz fi fn ff [sx|sx|sx plx|sx mx ex] Hx.
Qed.

Theorem canonical_canonical_mantissa :
  forall (sx : bool) mx ex,
  canonical_mantissa mx ex = true ->
  canonical radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof.
intros sx mx ex H.
now apply canonical_canonical_mantissa.
Qed.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof.
intros [sx|sx|sx plx Hx |sx mx ex Hx] ; try apply generic_format_0.
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

Theorem B2FF_inj :
  forall x y : binary_float,
  B2FF x = B2FF y ->
  x = y.
Proof.
intros [sx|sx|sx plx Hplx|sx mx ex Hx] [sy|sy|sy ply Hply|sy my ey Hy] ; try easy.
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
revert Hplx.
rewrite H2.
intros Hx.
apply f_equal, eqbool_irrelevance.
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

Lemma is_finite_strict_B2BSN :
  forall x, BinarySingleNaN.is_finite_strict (B2BSN x) = is_finite_strict x.
Proof.
intros x.
now destruct x.
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
  | B754_nan s _ _ => s
  | B754_zero s => s
  | B754_infinity s => s
  | B754_finite s _ _ _ => s
  end.

Theorem Bsign_FF2B :
  forall x H,
  Bsign (FF2B x H) = sign_FF x.
Proof.
now intros [sx|sx|sx plx|sx mx ex] H.
Qed.

Definition is_finite f :=
  match f with
  | B754_finite _ _ _ _ => true
  | B754_zero _ => true
  | _ => false
  end.

Lemma is_finite_B2BSN :
  forall x, BinarySingleNaN.is_finite (B2BSN x) = is_finite x.
Proof.
intros x.
now destruct x.
Qed.

Theorem is_finite_FF2B :
  forall x Hx,
  is_finite (FF2B x Hx) = is_finite_FF x.
Proof.
now intros [| | |].
Qed.

Theorem is_finite_B2FF :
  forall x,
  is_finite_FF (B2FF x) = is_finite x.
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
  | B754_nan _ _ _ => true
  | _ => false
  end.

Lemma is_nan_B2BSN :
  forall x,
  BinarySingleNaN.is_nan (B2BSN x) =  is_nan x.
Proof.
now intros [s|s|s p H|s m e H].
Qed.

Theorem is_nan_FF2B :
  forall x Hx,
  is_nan (FF2B x Hx) = is_nan_FF x.
Proof.
now intros [| | |].
Qed.

Theorem is_nan_B2FF :
  forall x,
  is_nan_FF (B2FF x) = is_nan x.
Proof.
now intros [| |? []|].
Qed.

Definition get_nan_pl (x : binary_float) : positive :=
  match x with B754_nan _ pl _ => pl | _ => xH end.

Definition build_nan (x : { x | is_nan x = true }) : binary_float.
Proof.
apply (B754_nan (Bsign (proj1_sig x)) (get_nan_pl (proj1_sig x))).
destruct x as [x H].
assert (K: false = true -> nan_pl 1 = true) by (intros K ; now elim Bool.diff_false_true).
simpl.
revert H.
destruct x as [sx|sx|sx px Px|sx mx ex Bx]; try apply K.
intros _.
apply Px.
Defined.

Theorem build_nan_correct :
  forall x : { x | is_nan x = true },
  build_nan x = proj1_sig x.
Proof.
intros [x H].
now destruct x.
Qed.

Theorem B2R_build_nan :
  forall x, B2R (build_nan x) = 0%R.
Proof.
easy.
Qed.

Theorem is_finite_build_nan :
  forall x, is_finite (build_nan x) = false.
Proof.
easy.
Qed.

Theorem is_nan_build_nan :
  forall x, is_nan (build_nan x) = true.
Proof.
easy.
Qed.

Definition BSN2B (nan : {x : binary_float | is_nan x = true }) (x : BinarySingleNaN.binary_float prec emax) : binary_float :=
  match x with
  | BinarySingleNaN.B754_nan => build_nan nan
  | BinarySingleNaN.B754_zero s => B754_zero s
  | BinarySingleNaN.B754_infinity s => B754_infinity s
  | BinarySingleNaN.B754_finite s m e H => B754_finite s m e H
  end.

Lemma B2BSN_BSN2B :
  forall nan x,
  B2BSN (BSN2B nan x) = x.
Proof.
now intros nan [s|s| |s m e H].
Qed.

Lemma B2R_BSN2B :
  forall nan x, B2R (BSN2B nan x) = BinarySingleNaN.B2R x.
Proof.
now intros nan [s|s| |s m e H].
Qed.

Lemma is_finite_BSN2B :
  forall nan x, is_finite (BSN2B nan x) = BinarySingleNaN.is_finite x.
Proof.
now intros nan [s|s| |s m e H].
Qed.

Lemma is_nan_BSN2B :
  forall nan x, is_nan (BSN2B nan x) = BinarySingleNaN.is_nan x.
Proof.
now intros nan [s|s| |s m e H].
Qed.

Lemma Bsign_B2BSN :
  forall x, is_nan x = false -> BinarySingleNaN.Bsign (B2BSN x) = Bsign x.
Proof.
now intros [s|s| |s m e H].
Qed.

Lemma Bsign_BSN2B :
  forall nan x, BinarySingleNaN.is_nan x = false ->
  Bsign (BSN2B nan x) = BinarySingleNaN.Bsign x.
Proof.
now intros nan [s|s| |s m e H].
Qed.

Definition BSN2B' (x : BinarySingleNaN.binary_float prec emax) : BinarySingleNaN.is_nan x = false -> binary_float.
Proof.
destruct x as [sx|sx| |sx mx ex Bx] ; intros H.
exact (B754_zero sx).
exact (B754_infinity sx).
now elim Bool.diff_true_false.
exact (B754_finite sx mx ex Bx).
Defined.

Lemma B2BSN_BSN2B' :
  forall x Nx,
  B2BSN (BSN2B' x Nx) = x.
Proof.
now intros [s|s| |s m e H] Nx.
Qed.

Lemma B2R_BSN2B' :
  forall x Nx,
  B2R (BSN2B' x Nx) = BinarySingleNaN.B2R x.
Proof.
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Lemma B2FF_BSN2B' :
  forall x Nx,
  B2FF (BSN2B' x Nx) = SF2FF (BinarySingleNaN.B2SF x).
Proof.
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Lemma Bsign_BSN2B' :
  forall x Nx,
  Bsign (BSN2B' x Nx) = BinarySingleNaN.Bsign x.
Proof.
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Lemma is_finite_BSN2B' :
  forall x Nx,
  is_finite (BSN2B' x Nx) = BinarySingleNaN.is_finite x.
Proof.
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Lemma is_nan_BSN2B' :
  forall x Nx,
  is_nan (BSN2B' x Nx) = false.
Proof.
now intros [sx|sx| |sx mx ex Bx] Nx.
Qed.

Definition erase (x : binary_float) : binary_float.
Proof.
destruct x as [s|s|s pl H|s m e H].
- exact (B754_zero s).
- exact (B754_infinity s).
- apply (B754_nan s pl).
  destruct nan_pl.
  apply eq_refl.
  exact H.
- apply (B754_finite s m e).
  destruct bounded.
  apply eq_refl.
  exact H.
Defined.

Theorem erase_correct :
  forall x, erase x = x.
Proof.
destruct x as [s|s|s pl H|s m e H] ; try easy ; simpl.
- apply f_equal, eqbool_irrelevance.
- apply f_equal, eqbool_irrelevance.
Qed.

(** Opposite *)

Definition Bopp opp_nan x :=
  match x with
  | B754_nan _ _ _ => build_nan (opp_nan x)
  | B754_infinity sx => B754_infinity (negb sx)
  | B754_finite sx mx ex Hx => B754_finite (negb sx) mx ex Hx
  | B754_zero sx => B754_zero (negb sx)
  end.

Theorem Bopp_involutive :
  forall opp_nan x,
  is_nan x = false ->
  Bopp opp_nan (Bopp opp_nan x) = x.
Proof.
now intros opp_nan [sx|sx|sx plx|sx mx ex Hx] ; simpl ; try rewrite Bool.negb_involutive.
Qed.

Theorem B2R_Bopp :
  forall opp_nan x,
  B2R (Bopp opp_nan x) = (- B2R x)%R.
Proof.
intros opp_nan [sx|sx|sx plx Hplx|sx mx ex Hx]; apply sym_eq ; try apply Ropp_0.
simpl.
rewrite <- F2R_opp.
now case sx.
Qed.

Theorem is_finite_Bopp :
  forall opp_nan x,
  is_finite (Bopp opp_nan x) = is_finite x.
Proof.
now intros opp_nan [| | |].
Qed.

Lemma Bsign_Bopp :
  forall opp_nan x, is_nan x = false -> Bsign (Bopp opp_nan x) = negb (Bsign x).
Proof. now intros opp_nan [s|s|s pl H|s m e H]. Qed.

(** Absolute value *)

Definition Babs abs_nan (x : binary_float) : binary_float :=
  match x with
  | B754_nan _ _ _ => build_nan (abs_nan x)
  | B754_infinity sx => B754_infinity false
  | B754_finite sx mx ex Hx => B754_finite false mx ex Hx
  | B754_zero sx => B754_zero false
  end.

Theorem B2R_Babs :
  forall abs_nan x,
  B2R (Babs abs_nan x) = Rabs (B2R x).
Proof.
  intros abs_nan [sx|sx|sx plx Hx|sx mx ex Hx]; apply sym_eq ; try apply Rabs_R0.
  simpl. rewrite <- F2R_abs. now destruct sx.
Qed.

Theorem is_finite_Babs :
  forall abs_nan x,
  is_finite (Babs abs_nan x) = is_finite x.
Proof.
  now intros abs_nan [| | |].
Qed.

Theorem Bsign_Babs :
  forall abs_nan x,
  is_nan x = false ->
  Bsign (Babs abs_nan x) = false.
Proof.
  now intros abs_nan [| | |].
Qed.

Theorem Babs_idempotent :
  forall abs_nan (x: binary_float),
  is_nan x = false ->
  Babs abs_nan (Babs abs_nan x) = Babs abs_nan x.
Proof.
  now intros abs_nan [sx|sx|sx plx|sx mx ex Hx].
Qed.

Theorem Babs_Bopp :
  forall abs_nan opp_nan x,
  is_nan x = false ->
  Babs abs_nan (Bopp opp_nan x) = Babs abs_nan x.
Proof.
  now intros abs_nan opp_nan [| | |].
Qed.

(** Comparison

[Some c] means ordered as per [c]; [None] means unordered. *)

Definition Bcompare (f1 f2 : binary_float) : option comparison :=
  BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2).

Theorem Bcompare_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bcompare f1 f2 = Some (Rcompare (B2R f1) (B2R f2)).
Proof.
  intros f1 f2 H1 H2.
  unfold Bcompare.
  rewrite BinarySingleNaN.Bcompare_correct.
  now rewrite 2!B2R_B2BSN.
  now rewrite is_finite_B2BSN.
  now rewrite is_finite_B2BSN.
Qed.

Theorem Bcompare_swap :
  forall x y,
  Bcompare y x = match Bcompare x y with Some c => Some (CompOpp c) | None => None end.
Proof.
  intros.
  apply BinarySingleNaN.Bcompare_swap.
Qed.

Theorem bounded_le_emax_minus_prec :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex)
   <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof.
now apply BinarySingleNaN.bounded_le_emax_minus_prec.
Qed.

Theorem bounded_lt_emax :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R.
Proof.
now apply bounded_lt_emax.
Qed.

Theorem bounded_ge_emin :
  forall mx ex,
  bounded mx ex = true ->
  (bpow radix2 emin <= F2R (Float radix2 (Zpos mx) ex))%R.
Proof.
now apply bounded_ge_emin.
Qed.

Theorem abs_B2R_le_emax_minus_prec :
  forall x,
  (Rabs (B2R x) <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof.
intros x.
rewrite <- B2R_B2BSN.
now apply abs_B2R_le_emax_minus_prec.
Qed.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof.
intros x.
rewrite <- B2R_B2BSN.
now apply abs_B2R_lt_emax.
Qed.

Theorem abs_B2R_ge_emin :
  forall x,
  is_finite_strict x = true ->
  (bpow radix2 emin <= Rabs (B2R x))%R.
Proof.
intros x.
rewrite <- is_finite_strict_B2BSN.
rewrite <- B2R_B2BSN.
now apply abs_B2R_ge_emin.
Qed.

Theorem bounded_canonical_lt_emax :
  forall mx ex,
  canonical radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R ->
  bounded mx ex = true.
Proof.
intros mx ex.
now apply bounded_canonical_lt_emax.
Qed.

(** Truncation *)

Notation shr_fexp := (shr_fexp prec emax) (only parsing).

Theorem shr_fexp_truncate :
  forall m e l,
  (0 <= m)%Z ->
  shr_fexp m e l =
  let '(m', e', l') := truncate radix2 fexp (m, e, l) in (shr_record_of_loc m' l', e').
Proof.
intros m e l.
now apply shr_fexp_truncate.
Qed.

(** Rounding modes *)

Definition binary_overflow m s :=
  SF2FF (binary_overflow prec emax m s).

Lemma eq_binary_overflow_FF2SF :
  forall x m s,
  FF2SF x = BinarySingleNaN.binary_overflow prec emax m s ->
  x = binary_overflow m s.
Proof.
intros x m s H.
unfold binary_overflow.
rewrite <- H.
apply eq_sym, SF2FF_FF2SF.
rewrite <- is_nan_FF2SF, H.
apply is_nan_binary_overflow.
Qed.

Definition binary_round_aux mode sx mx ex lx :=
  SF2FF (binary_round_aux prec emax mode sx mx ex lx).

Theorem binary_round_aux_correct' :
  forall mode x mx ex lx,
  (x <> 0)%R ->
  inbetween_float radix2 mx ex (Rabs x) lx ->
  (ex <= cexp radix2 fexp x)%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) mx ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_FF z = true /\ sign_FF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof.
intros mode x mx ex lx Px Bx Ex.
generalize (binary_round_aux_correct' prec emax _ _ mode x mx ex lx Px Bx Ex).
unfold binary_round_aux.
destruct (Rlt_bool (Rabs _) _).
- now destruct BinarySingleNaN.binary_round_aux as [sz|sz| |sz mz ez].
- intros [_ ->].
  split.
  rewrite valid_binary_SF2FF by apply is_nan_binary_overflow.
  now apply binary_overflow_correct.
  easy.
Qed.

Theorem binary_round_aux_correct :
  forall mode x mx ex lx,
  inbetween_float radix2 (Zpos mx) ex (Rabs x) lx ->
  (ex <= fexp (Zdigits radix2 (Zpos mx) + ex))%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) (Zpos mx) ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_FF z = true /\ sign_FF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof.
intros mode x mx ex lx Bx Ex.
generalize (binary_round_aux_correct prec emax _ _ mode x mx ex lx Bx Ex).
unfold binary_round_aux.
destruct (Rlt_bool (Rabs _) _).
- now destruct BinarySingleNaN.binary_round_aux as [sz|sz| |sz mz ez].
- intros [_ ->].
  split.
  rewrite valid_binary_SF2FF by apply is_nan_binary_overflow.
  now apply binary_overflow_correct.
  easy.
Qed.

(** Multiplication *)

Definition Bmult mult_nan m x y :=
  BSN2B (mult_nan x y) (Bmult m (B2BSN x) (B2BSN y)).

Theorem Bmult_correct :
  forall mult_nan m x y,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x * B2R y))) (bpow radix2 emax) then
    B2R (Bmult mult_nan m x y) = round radix2 fexp (round_mode m) (B2R x * B2R y) /\
    is_finite (Bmult mult_nan m x y) = andb (is_finite x) (is_finite y) /\
    (is_nan (Bmult mult_nan m x y) = false ->
      Bsign (Bmult mult_nan m x y) = xorb (Bsign x) (Bsign y))
  else
    B2FF (Bmult mult_nan m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof.
intros mult_nan mode x y.
generalize (Bmult_correct prec emax _ _ mode (B2BSN x) (B2BSN y)).
replace (BinarySingleNaN.Bmult _ _ _) with (B2BSN (Bmult mult_nan mode x y)) by apply B2BSN_BSN2B.
intros H.
destruct x as [sx|sx|sx plx Hplx|sx mx ex Hx] ;
  destruct y as [sy|sy|sy ply Hply|sy my ey Hy] ;
  try ( rewrite ?Rmult_0_r, ?Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ try easy | apply bpow_gt_0 | now auto with typeclass_instances ]).
revert H.
rewrite 2!B2R_B2BSN.
destruct Rlt_bool.
- now destruct Bmult.
- intros H.
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

(** Normalization and rounding *)

Definition shl_align_fexp mx ex :=
  shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex)).

Lemma shl_align_fexp_correct :
  forall mx ex,
  let (mx', ex') := shl_align_fexp mx ex in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') /\
  (ex' <= fexp (Zdigits radix2 (Zpos mx') + ex'))%Z.
Proof.
intros mx ex.
apply shl_align_fexp_correct.
Qed.

Definition binary_round m sx mx ex :=
  SF2FF (binary_round prec emax m sx mx ex).

Theorem binary_round_correct :
  forall m sx mx ex,
  let z := binary_round m sx mx ex in
  valid_binary z = true /\
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) x)) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode m) x /\
    is_finite_FF z = true /\
    sign_FF z = sx
  else
    z = binary_overflow m sx.
Proof.
intros mode sx mx ex.
generalize (binary_round_correct prec emax _ _ mode sx mx ex).
simpl.
unfold binary_round.
destruct Rlt_bool.
- now destruct BinarySingleNaN.binary_round.
- intros [H1 ->].
  split.
  rewrite valid_binary_SF2FF by apply is_nan_binary_overflow.
  now apply binary_overflow_correct.
  easy.
Qed.

Definition binary_normalize mode m e szero :=
  BSN2B' _ (is_nan_binary_normalize prec emax _ _ mode m e szero).

Theorem binary_normalize_correct :
  forall m mx ex szero,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (F2R (Float radix2 mx ex)))) (bpow radix2 emax) then
    B2R (binary_normalize m mx ex szero) = round radix2 fexp (round_mode m) (F2R (Float radix2 mx ex)) /\
    is_finite (binary_normalize m mx ex szero) = true /\
    Bsign (binary_normalize m mx ex szero) =
      match Rcompare (F2R (Float radix2 mx ex)) 0 with
        | Eq => szero
        | Lt => true
        | Gt => false
      end
  else
    B2FF (binary_normalize m mx ex szero) = binary_overflow m (Rlt_bool (F2R (Float radix2 mx ex)) 0).
Proof.
intros mode mx ex szero.
generalize (binary_normalize_correct prec emax _ _ mode mx ex szero).
replace (BinarySingleNaN.binary_normalize _ _ _ _ _ _ _ _) with (B2BSN (binary_normalize mode mx ex szero)) by apply B2BSN_BSN2B'.
simpl.
destruct Rlt_bool.
- now destruct binary_normalize.
- intros H.
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

(** Addition *)

Definition Bplus plus_nan m x y :=
  BSN2B (plus_nan x y) (Bplus m (B2BSN x) (B2BSN y)).

Theorem Bplus_correct :
  forall plus_nan m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x + B2R y))) (bpow radix2 emax) then
    B2R (Bplus plus_nan m x y) = round radix2 fexp (round_mode m) (B2R x + B2R y) /\
    is_finite (Bplus plus_nan m x y) = true /\
    Bsign (Bplus plus_nan m x y) =
      match Rcompare (B2R x + B2R y) 0 with
        | Eq => match m with mode_DN => orb (Bsign x) (Bsign y)
                                 | _ => andb (Bsign x) (Bsign y) end
        | Lt => true
        | Gt => false
      end
  else
    (B2FF (Bplus plus_nan m x y) = binary_overflow m (Bsign x) /\ Bsign x = Bsign y).
Proof with auto with typeclass_instances.
intros plus_nan mode x y Fx Fy.
rewrite <- is_finite_B2BSN in Fx, Fy.
generalize (Bplus_correct prec emax _ _ mode _ _ Fx Fy).
replace (BinarySingleNaN.Bplus _ _ _) with (B2BSN (Bplus plus_nan mode x y)) by apply B2BSN_BSN2B.
rewrite 2!B2R_B2BSN.
rewrite (Bsign_B2BSN x) by (clear -Fx ; now destruct x).
rewrite (Bsign_B2BSN y) by (clear -Fy ; now destruct y).
destruct Rlt_bool.
- now destruct Bplus.
- intros [H1 H2].
  refine (conj _ H2).
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

(** Subtraction *)

Definition Bminus minus_nan m x y :=
  BSN2B (minus_nan x y) (Bminus m (B2BSN x) (B2BSN y)).

Theorem Bminus_correct :
  forall minus_nan m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x - B2R y))) (bpow radix2 emax) then
    B2R (Bminus minus_nan m x y) = round radix2 fexp (round_mode m) (B2R x - B2R y) /\
    is_finite (Bminus minus_nan m x y) = true /\
    Bsign (Bminus minus_nan m x y) =
      match Rcompare (B2R x - B2R y) 0 with
        | Eq => match m with mode_DN => orb (Bsign x) (negb (Bsign y))
                                 | _ => andb (Bsign x) (negb (Bsign y)) end
        | Lt => true
        | Gt => false
      end
  else
    (B2FF (Bminus minus_nan m x y) = binary_overflow m (Bsign x) /\ Bsign x = negb (Bsign y)).
Proof with auto with typeclass_instances.
intros minus_nan mode x y Fx Fy.
rewrite <- is_finite_B2BSN in Fx, Fy.
generalize (Bminus_correct prec emax _ _ mode _ _ Fx Fy).
replace (BinarySingleNaN.Bminus _ _ _) with (B2BSN (Bminus minus_nan mode x y)) by apply B2BSN_BSN2B.
rewrite 2!B2R_B2BSN.
rewrite (Bsign_B2BSN x) by (clear -Fx ; now destruct x).
rewrite (Bsign_B2BSN y) by (clear -Fy ; now destruct y).
destruct Rlt_bool.
- now destruct Bminus.
- intros [H1 H2].
  refine (conj _ H2).
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

(** Fused Multiply-Add *)

Definition Bfma_szero m (x y z : binary_float) :=
  Bfma_szero prec emax m (B2BSN x) (B2BSN y) (B2BSN z).

Definition Bfma fma_nan m (x y z: binary_float) :=
  BSN2B (fma_nan x y z) (Bfma m (B2BSN x) (B2BSN y) (B2BSN z)).

Theorem Bfma_correct:
  forall fma_nan m x y z,
  is_finite x = true ->
  is_finite y = true ->
  is_finite z = true ->
  let res := (B2R x * B2R y + B2R z)%R in
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) res)) (bpow radix2 emax) then
    B2R (Bfma fma_nan m x y z) = round radix2 fexp (round_mode m) res /\
    is_finite (Bfma fma_nan m x y z) = true /\
    Bsign (Bfma fma_nan m x y z) =
      match Rcompare res 0 with
        | Eq => Bfma_szero m x y z
        | Lt => true
        | Gt => false
      end
  else
    B2FF (Bfma fma_nan m x y z) = binary_overflow m (Rlt_bool res 0).
Proof.
intros fma_nan mode x y z Fx Fy Fz.
rewrite <- is_finite_B2BSN in Fx, Fy, Fz.
generalize (Bfma_correct prec emax _ _ mode _ _ _ Fx Fy Fz).
replace (BinarySingleNaN.Bfma _ _ _ _) with (B2BSN (Bfma fma_nan mode x y z)) by apply B2BSN_BSN2B.
rewrite 3!B2R_B2BSN.
cbv zeta.
destruct Rlt_bool.
- now destruct Bfma.
- intros H.
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

(** Division *)

Definition Bdiv div_nan m x y :=
  BSN2B (div_nan x y) (Bdiv m (B2BSN x) (B2BSN y)).

Theorem Bdiv_correct :
  forall div_nan m x y,
  B2R y <> 0%R ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x / B2R y))) (bpow radix2 emax) then
    B2R (Bdiv div_nan m x y) = round radix2 fexp (round_mode m) (B2R x / B2R y) /\
    is_finite (Bdiv div_nan m x y) = is_finite x /\
    (is_nan (Bdiv div_nan m x y) = false ->
      Bsign (Bdiv div_nan m x y) = xorb (Bsign x) (Bsign y))
  else
    B2FF (Bdiv div_nan m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof.
intros div_nan mode x y Zy.
rewrite <- B2R_B2BSN in Zy.
generalize (Bdiv_correct prec emax _ _ mode (B2BSN x) _ Zy).
replace (BinarySingleNaN.Bdiv _ _ _) with (B2BSN (Bdiv div_nan mode x y)) by apply B2BSN_BSN2B.
unfold Rdiv.
destruct y as [sy|sy|sy ply|sy my ey Hy] ; try now elim Zy.
destruct x as [sx|sx|sx plx Hx|sx mx ex Hx] ;
  try ( simpl ; rewrite Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ simpl ; try easy ; now rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan | apply bpow_gt_0 | auto with typeclass_instances ] ).
destruct Rlt_bool.
- now destruct Bdiv.
- intros H.
  apply eq_binary_overflow_FF2SF.
  now rewrite FF2SF_B2FF, <- B2SF_B2BSN.
Qed.

(** Square root *)

Definition Bsqrt sqrt_nan m x :=
  BSN2B (sqrt_nan x) (Bsqrt m (B2BSN x)).

Theorem Bsqrt_correct :
  forall sqrt_nan m x,
  B2R (Bsqrt sqrt_nan m x) = round radix2 fexp (round_mode m) (sqrt (B2R x)) /\
  is_finite (Bsqrt sqrt_nan m x) = match x with B754_zero _ => true | B754_finite false _ _ _ => true | _ => false end /\
  (is_nan (Bsqrt sqrt_nan m x) = false -> Bsign (Bsqrt sqrt_nan m x) = Bsign x).
Proof.
intros sqrt_nan mode x.
generalize (Bsqrt_correct prec emax _ _ mode (B2BSN x)).
replace (BinarySingleNaN.Bsqrt _ _) with (B2BSN (Bsqrt sqrt_nan mode x)) by apply B2BSN_BSN2B.
intros H.
destruct x as [sx|[|]|sx plx Hplx|sx mx ex Hx] ; try easy.
now destruct Bsqrt.
Qed.

(** NearbyInt and Trunc **)

Definition Bnearbyint nearbyint_nan m x :=
  BSN2B (nearbyint_nan x) (Bnearbyint m (B2BSN x)).

Theorem Bnearbyint_correct :
  forall nearbyint_nan md x,
  B2R (Bnearbyint nearbyint_nan md x) = round radix2 (FIX_exp 0) (round_mode md) (B2R x) /\
  is_finite (Bnearbyint nearbyint_nan md x) = is_finite x /\
  (is_nan (Bnearbyint nearbyint_nan md x) = false -> Bsign (Bnearbyint nearbyint_nan md x) = Bsign x).
Proof.
intros nearbyint_nan mode x.
generalize (Bnearbyint_correct prec emax _ mode (B2BSN x)).
replace (BinarySingleNaN.Bnearbyint _ _) with (B2BSN (Bnearbyint nearbyint_nan mode x)) by apply B2BSN_BSN2B.
intros H.
destruct x as [sx|[|]|sx plx Hplx|sx mx ex Hx] ; try easy.
now destruct Bnearbyint.
Qed.

Definition Btrunc x := Btrunc (B2BSN x).

Theorem Btrunc_correct :
  forall x,
  IZR (Btrunc x) = round radix2 (FIX_exp 0) Ztrunc (B2R x).
Proof.
  intros x.
  rewrite <-B2R_B2BSN.
  now apply Btrunc_correct.
Qed.

(** A few values *)

Definition Bone :=
  BSN2B' _ (@is_nan_Bone prec emax _ _).

Theorem Bone_correct : B2R Bone = 1%R.
Proof.
unfold Bone.
rewrite B2R_BSN2B'.
apply Bone_correct.
Qed.

Lemma is_finite_Bone : is_finite Bone = true.
Proof.
unfold Bone.
rewrite is_finite_BSN2B'.
apply is_finite_Bone.
Qed.

Lemma Bsign_Bone : Bsign Bone = false.
Proof.
unfold Bone.
rewrite Bsign_BSN2B'.
apply Bsign_Bone.
Qed.

Definition Bmax_float :=
  BSN2B' Bmax_float eq_refl.

(** Extraction/modification of mantissa/exponent *)

Definition Bnormfr_mantissa x :=
  Bnormfr_mantissa (B2BSN x).

Definition lift x y (Ny : @BinarySingleNaN.is_nan prec emax y = is_nan x) : binary_float.
Proof.
destruct (is_nan x).
exact x.
now apply (BSN2B' y).
Defined.

Lemma B2BSN_lift :
  forall x y Ny,
  B2BSN (lift x y Ny) = y.
Proof.
intros x y Ny.
unfold lift.
destruct x as [sx|sx|sx px Px|sx mx ex Bx] ; simpl ; try apply B2BSN_BSN2B'.
now destruct y.
Qed.

Definition Bldexp (mode : mode) (x : binary_float) (e : Z) : binary_float.
Proof.
apply (lift x (Bldexp mode (B2BSN x) e)).
rewrite <- is_nan_B2BSN.
apply is_nan_Bldexp.
Defined.

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
    B2FF (Bldexp m f e) = binary_overflow m (Bsign f).
Proof.
intros mode x e.
generalize (Bldexp_correct prec emax _ _ mode (B2BSN x) e).
replace (BinarySingleNaN.Bldexp _ _ _) with (B2BSN (Bldexp mode x e)) by apply B2BSN_lift.
rewrite B2R_B2BSN.
destruct Rlt_bool.
- destruct x as [sx|sx|sx px Px|sx mx ex Bx] ; try easy.
  now destruct Bldexp.
- intros H.
  apply eq_binary_overflow_FF2SF.
  rewrite B2SF_B2BSN in H.
  rewrite FF2SF_B2FF, H.
  destruct x as [sx|sx|sx px Px|sx mx ex Bx] ; simpl in H ; try easy.
  contradict H.
  unfold BinarySingleNaN.binary_overflow.
  now destruct overflow_to_inf.
Qed.

Section Bfrexp.

(** This hypothesis is needed to implement [Bfrexp]
    (otherwise, we have emin > - prec
     and [Bfrexp] cannot fit the mantissa in interval #[0.5, 1)#) *)
Hypothesis Hemax : (2 < emax)%Z.

Definition Bfrexp (x : binary_float) : binary_float * Z.
Proof.
set (y := Bfrexp (B2BSN x)).
refine (pair _ (snd y)).
apply (lift x (fst y)).
rewrite <- is_nan_B2BSN.
apply is_nan_Bfrexp.
Defined.

Theorem Bfrexp_correct :
  forall f,
  is_finite_strict f = true ->
  let x := B2R f in
  let z := fst (Bfrexp f) in
  let e := snd (Bfrexp f) in
  (/2 <= Rabs (B2R z) < 1)%R /\
  (x = B2R z * bpow radix2 e)%R /\
  e = mag radix2 x.
Proof.
intros x Fx.
rewrite <- is_finite_strict_B2BSN in Fx.
generalize (Bfrexp_correct prec emax _ (B2BSN x) Fx).
simpl.
rewrite <- B2R_B2BSN.
rewrite B2BSN_lift.
destruct BinarySingleNaN.Bfrexp as [z e].
rewrite B2R_B2BSN.
now intros [H1 [H2 H3]].
Qed.

End Bfrexp.

(** Ulp *)

Definition Bulp (x : binary_float) : binary_float.
Proof.
apply (lift x (Bulp (B2BSN x))).
rewrite <- is_nan_B2BSN.
apply is_nan_Bulp.
Defined.

Theorem Bulp_correct :
  forall x,
  is_finite x = true ->
  B2R (Bulp x) = ulp radix2 fexp (B2R x) /\
  is_finite (Bulp x) = true /\
  Bsign (Bulp x) = false.
Proof.
intros x Fx.
rewrite <- is_finite_B2BSN in Fx.
generalize (Bulp_correct prec emax _ _ _ Fx).
replace (BinarySingleNaN.Bulp (B2BSN x)) with (B2BSN (Bulp x)) by apply B2BSN_lift.
rewrite 2!B2R_B2BSN.
now destruct Bulp.
Qed.

(** Successor (and predecessor) *)

Definition Bsucc (x : binary_float) : binary_float.
Proof.
apply (lift x (Bsucc (B2BSN x))).
rewrite <- is_nan_B2BSN.
apply is_nan_Bsucc.
Defined.

Lemma Bsucc_correct :
  forall x,
  is_finite x = true ->
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc x) = true /\
    (Bsign (Bsucc x) = Bsign x && is_finite_strict x)%bool
  else
    B2FF (Bsucc x) = F754_infinity false.
Proof.
intros x Fx.
rewrite <- is_finite_B2BSN in Fx.
generalize (Bsucc_correct prec emax _ _ _ Fx).
replace (BinarySingleNaN.Bsucc (B2BSN x)) with (B2BSN (Bsucc x)) by apply B2BSN_lift.
rewrite 2!B2R_B2BSN.
destruct Rlt_bool.
- rewrite (Bsign_B2BSN x) by now destruct x.
  rewrite is_finite_strict_B2BSN.
  now destruct Bsucc.
- now destruct Bsucc as [|[|]| |].
Qed.

Definition Bpred (x : binary_float) : binary_float.
Proof.
apply (lift x (Bpred (B2BSN x))).
rewrite <- is_nan_B2BSN.
apply is_nan_Bpred.
Defined.

Lemma Bpred_correct :
  forall x,
  is_finite x = true ->
  if Rlt_bool (- bpow radix2 emax) (pred radix2 fexp (B2R x)) then
    B2R (Bpred x) = pred radix2 fexp (B2R x) /\
    is_finite (Bpred x) = true /\
    (Bsign (Bpred x) = Bsign x || negb (is_finite_strict x))%bool
  else
    B2FF (Bpred x) = F754_infinity true.
Proof.
intros x Fx.
rewrite <- is_finite_B2BSN in Fx.
generalize (Bpred_correct prec emax _ _ _ Fx).
replace (BinarySingleNaN.Bpred (B2BSN x)) with (B2BSN (Bpred x)) by apply B2BSN_lift.
rewrite 2!B2R_B2BSN.
destruct Rlt_bool.
- rewrite (Bsign_B2BSN x) by now destruct x.
  rewrite is_finite_strict_B2BSN.
  now destruct Bpred.
- now destruct Bpred as [|[|]| |].
Qed.

End Binary.

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
Require Import Core Digits Round Bracket Operations Div Sqrt Relative.
Require Import Psatz.

Section AnyRadix.

Inductive full_float :=
  | F754_zero (s : bool)
  | F754_infinity (s : bool)
  | F754_nan (s : bool) (m : positive)
  | F754_finite (s : bool) (m : positive) (e : Z).

Definition FF2R beta x :=
  match x with
  | F754_finite s m e => F2R (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

End AnyRadix.

Section Binary.

Arguments exist {A} {P}.

(** [prec] is the number of bits of the mantissa including the implicit one;
    [emax] is the exponent of the infinities.
    For instance, binary32 is defined by [prec = 24] and [emax = 128]. *)
Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Hypothesis Hmax : (prec < emax)%Z.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.
Instance fexp_correct : Valid_exp fexp := FLT_exp_valid emin prec.
Instance fexp_monotone : Monotone_exp fexp := FLT_exp_monotone emin prec.

Definition canonical_mantissa m e :=
  Zeq_bool (fexp (Zpos (digits2_pos m) + e)) e.

Definition bounded m e :=
  andb (canonical_mantissa m e) (Zle_bool e (emax - prec)).

Definition nan_pl pl :=
  Zlt_bool (Zpos (digits2_pos pl)) prec.

Definition valid_binary x :=
  match x with
  | F754_finite _ m e => bounded m e
  | F754_nan _ pl => nan_pl pl
  | _ => true
  end.

(** Basic type used for representing binary FP numbers.
    Note that there is exactly one such object per FP datum. *)

Inductive binary_float :=
  | B754_zero (s : bool)
  | B754_infinity (s : bool)
  | B754_nan (s : bool) (pl : positive) :
    nan_pl pl = true -> binary_float
  | B754_finite (s : bool) (m : positive) (e : Z) :
    bounded m e = true -> binary_float.

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

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof.
intros [sx|sx|sx plx Hx |sx mx ex Hx] ; try apply generic_format_0.
simpl.
apply generic_format_canonical.
apply canonical_canonical_mantissa.
now destruct (andb_prop _ _ Hx) as (H, _).
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
apply canonical_canonical_mantissa.
exact (proj1 (andb_prop _ _ Hx)).
apply canonical_canonical_mantissa.
exact (proj1 (andb_prop _ _ Hy)).
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

Definition sign_FF x :=
  match x with
  | F754_nan s _ => s
  | F754_zero s => s
  | F754_infinity s => s
  | F754_finite s _ _ => s
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

Definition is_finite_FF f :=
  match f with
  | F754_finite _ _ _ => true
  | F754_zero _ => true
  | _ => false
  end.

Theorem is_finite_FF2B :
  forall x Hx,
  is_finite (FF2B x Hx) = is_finite_FF x.
Proof.
now intros [| | |].
Qed.

Theorem is_finite_FF_B2FF :
  forall x,
  is_finite_FF (B2FF x) = is_finite x.
Proof.
now intros [| |? []|].
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

Definition is_nan_FF f :=
  match f with
  | F754_nan _ _ => true
  | _ => false
  end.

Theorem is_nan_FF2B :
  forall x Hx,
  is_nan (FF2B x Hx) = is_nan_FF x.
Proof.
now intros [| | |].
Qed.

Theorem is_nan_FF_B2FF :
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
simpl.
revert H.
assert (H: false = true -> nan_pl 1 = true) by now destruct (nan_pl 1).
destruct x; try apply H.
intros _.
apply e.
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
  match f1, f2 with
  | B754_nan _ _ _,_ | _,B754_nan _ _ _ => None
  | B754_infinity s1, B754_infinity s2 =>
    Some match s1, s2 with
    | true, true => Eq
    | false, false => Eq
    | true, false => Lt
    | false, true => Gt
    end
  | B754_infinity s, _ => Some (if s then Lt else Gt)
  | _, B754_infinity s => Some (if s then Gt else Lt)
  | B754_finite s _ _ _, B754_zero _ => Some (if s then Lt else Gt)
  | B754_zero _, B754_finite s _ _ _ => Some (if s then Gt else Lt)
  | B754_zero _, B754_zero _ => Some Eq
  | B754_finite s1 m1 e1 _, B754_finite s2 m2 e2 _ =>
    Some match s1, s2 with
    | true, false => Lt
    | false, true => Gt
    | false, false =>
      match Z.compare e1 e2 with
      | Lt => Lt
      | Gt => Gt
      | Eq => Pcompare m1 m2 Eq
      end
    | true, true =>
      match Z.compare e1 e2 with
      | Lt => Gt
      | Gt => Lt
      | Eq => CompOpp (Pcompare m1 m2 Eq)
      end
    end
  end.

Theorem Bcompare_correct :
  forall f1 f2,
  is_finite f1 = true -> is_finite f2 = true ->
  Bcompare f1 f2 = Some (Rcompare (B2R f1) (B2R f2)).
Proof.
  Ltac apply_Rcompare :=
    match goal with
      | [ |- Lt = Rcompare _ _ ] => symmetry; apply Rcompare_Lt
      | [ |- Eq = Rcompare _ _ ] => symmetry; apply Rcompare_Eq
      | [ |- Gt = Rcompare _ _ ] => symmetry; apply Rcompare_Gt
    end.
  unfold Bcompare; intros f1 f2 H1 H2.
  destruct f1, f2; try easy; apply f_equal; clear H1 H2.
  now rewrite Rcompare_Eq.
  destruct s0 ; apply_Rcompare.
  now apply F2R_lt_0.
  now apply F2R_gt_0.
  destruct s ; apply_Rcompare.
  now apply F2R_lt_0.
  now apply F2R_gt_0.
  simpl.
  apply andb_prop in e0; destruct e0; apply (canonical_canonical_mantissa false) in H.
  apply andb_prop in e2; destruct e2; apply (canonical_canonical_mantissa false) in H1.
  pose proof (Zcompare_spec e e1); unfold canonical, Fexp in H1, H.
  assert (forall m1 m2 e1 e2,
    let x := (IZR (Zpos m1) * bpow radix2 e1)%R in
    let y := (IZR (Zpos m2) * bpow radix2 e2)%R in
    (cexp radix2 fexp x < cexp radix2 fexp y)%Z -> (x < y)%R).
  {
  intros; apply Rnot_le_lt; intro; apply (mag_le radix2) in H5.
  apply Zlt_not_le with (1 := H4).
  now apply fexp_monotone.
  now apply (F2R_gt_0 _ (Float radix2 (Zpos m2) e2)).
  }
  assert (forall m1 m2 e1 e2, (IZR (- Zpos m1) * bpow radix2 e1 < IZR (Zpos m2) * bpow radix2 e2)%R).
  {
  intros; apply (Rlt_trans _ 0%R).
  now apply (F2R_lt_0 _ (Float radix2 (Zneg m1) e0)).
  now apply (F2R_gt_0 _ (Float radix2 (Zpos m2) e2)).
  }
  unfold F2R, Fnum, Fexp.
  destruct s, s0; try (now apply_Rcompare; apply H5); inversion H3;
    try (apply_Rcompare; apply H4; rewrite H, H1 in H7; assumption);
    try (apply_Rcompare; do 2 rewrite opp_IZR, Ropp_mult_distr_l_reverse;
      apply Ropp_lt_contravar; apply H4; rewrite H, H1 in H7; assumption);
    rewrite H7, Rcompare_mult_r, Rcompare_IZR by (apply bpow_gt_0); reflexivity.
Qed.

Theorem Bcompare_swap :
  forall x y,
  Bcompare y x = match Bcompare x y with Some c => Some (CompOpp c) | None => None end.
Proof.
  intros.
  destruct x as [ ? | [] | ? ? | [] mx ex Bx ];
  destruct y as [ ? | [] | ? ? | [] my ey By ]; simpl; try easy.
- rewrite <- (Zcompare_antisym ex ey). destruct (ex ?= ey)%Z; try easy.
  now rewrite (Pcompare_antisym mx my).
- rewrite <- (Zcompare_antisym ex ey). destruct (ex ?= ey)%Z; try easy.
  now rewrite Pcompare_antisym.
Qed.

Theorem bounded_le_emax_minus_prec :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex)
   <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof.
intros mx ex Hx.
destruct (andb_prop _ _ Hx) as (H1,H2).
generalize (Zeq_bool_eq _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
generalize (mag_F2R_Zdigits radix2 (Zpos mx) ex).
destruct (mag radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex).
unfold mag_val.
intros H.
elim Ex; [|now apply Rgt_not_eq, F2R_gt_0]; intros _.
rewrite <-F2R_Zabs; simpl; clear Ex; intros Ex.
generalize (Rmult_lt_compat_r (bpow radix2 (-ex)) _ _ (bpow_gt_0 _ _) Ex).
unfold F2R; simpl; rewrite Rmult_assoc, <-!bpow_plus.
rewrite H; [|intro H'; discriminate H'].
rewrite <-Z.add_assoc, Z.add_opp_diag_r, Z.add_0_r, Rmult_1_r.
rewrite <-(IZR_Zpower _ _ (Zdigits_ge_0 _ _)); clear Ex; intro Ex.
generalize (Zlt_le_succ _ _ (lt_IZR _ _ Ex)); clear Ex; intro Ex.
generalize (IZR_le _ _ Ex).
rewrite succ_IZR; clear Ex; intro Ex.
generalize (Rplus_le_compat_r (-1) _ _ Ex); clear Ex; intro Ex.
ring_simplify in Ex; revert Ex.
rewrite (IZR_Zpower _ _ (Zdigits_ge_0 _ _)); intro Ex.
generalize (Rmult_le_compat_r (bpow radix2 ex) _ _ (bpow_ge_0 _ _) Ex).
intro H'; apply (Rle_trans _ _ _ H').
rewrite Rmult_minus_distr_r, Rmult_1_l, <-bpow_plus.
revert H1; unfold fexp, FLT_exp; intro H1.
generalize (Z.le_max_l (Z.pos (digits2_pos mx) + ex - prec) emin).
rewrite H1; intro H1'.
generalize (proj1 (Z.le_sub_le_add_r _ _ _) H1').
rewrite Zpos_digits2_pos; clear H1'; intro H1'.
apply (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ (bpow_le _ _ _ H1'))).
replace emax with (emax - prec - ex + (ex + prec))%Z at 1 by ring.
replace (emax - prec)%Z with (emax - prec - ex + ex)%Z at 2 by ring.
do 2 rewrite (bpow_plus _ (emax - prec - ex)).
rewrite <-Rmult_minus_distr_l.
rewrite <-(Rmult_1_l (_ + _)).
apply Rmult_le_compat_r.
{ apply Rle_0_minus, bpow_le; unfold Prec_gt_0 in prec_gt_0_; lia. }
change 1%R with (bpow radix2 0); apply bpow_le; lia.
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
intros ; zify ; lia.
Qed.

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
clearbody emin.
intros ; zify ; lia.
Qed.

Theorem abs_B2R_le_emax_minus_prec :
  forall x,
  (Rabs (B2R x) <= bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof.
intros [sx|sx|sx plx Hx|sx mx ex Hx] ; simpl ;
  [rewrite Rabs_R0 ; apply Rle_0_minus, bpow_le ;
   revert prec_gt_0_; unfold Prec_gt_0; lia..|].
rewrite <- F2R_Zabs, abs_cond_Zopp.
now apply bounded_le_emax_minus_prec.
Qed.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof.
intros [sx|sx|sx plx Hx|sx mx ex Hx] ; simpl ; try ( rewrite Rabs_R0 ; apply bpow_gt_0 ).
rewrite <- F2R_Zabs, abs_cond_Zopp.
now apply bounded_lt_emax.
Qed.

Theorem abs_B2R_ge_emin :
  forall x,
  is_finite_strict x = true ->
  (bpow radix2 emin <= Rabs (B2R x))%R.
Proof.
intros [sx|sx|sx plx Hx|sx mx ex Hx] ; simpl ; try discriminate.
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
unfold emin.
generalize (prec_gt_0 prec).
clear -Hmax ; lia.
Qed.

(** Truncation *)

Record shr_record := { shr_m : Z ; shr_r : bool ; shr_s : bool }.

Definition shr_1 mrs :=
  let '(Build_shr_record m r s) := mrs in
  let s := orb r s in
  match m with
  | Z0 => Build_shr_record Z0 false s
  | Zpos xH => Build_shr_record Z0 true s
  | Zpos (xO p) => Build_shr_record (Zpos p) false s
  | Zpos (xI p) => Build_shr_record (Zpos p) true s
  | Zneg xH => Build_shr_record Z0 true s
  | Zneg (xO p) => Build_shr_record (Zneg p) false s
  | Zneg (xI p) => Build_shr_record (Zneg p) true s
  end.

Definition loc_of_shr_record mrs :=
  match mrs with
  | Build_shr_record _ false false => loc_Exact
  | Build_shr_record _ false true => loc_Inexact Lt
  | Build_shr_record _ true false => loc_Inexact Eq
  | Build_shr_record _ true true => loc_Inexact Gt
  end.

Definition shr_record_of_loc m l :=
  match l with
  | loc_Exact => Build_shr_record m false false
  | loc_Inexact Lt => Build_shr_record m false true
  | loc_Inexact Eq => Build_shr_record m true false
  | loc_Inexact Gt => Build_shr_record m true true
  end.

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

Definition shr mrs e n :=
  match n with
  | Zpos p => (iter_pos shr_1 p mrs, (e + n)%Z)
  | _ => (mrs, e)
  end.

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
replace (new_location_even 2 (if shr_r (shr_1 mrs) then 1%Z else 0%Z) (loc_of_shr_record mrs)) with (loc_of_shr_record (shr_1 mrs)).
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

Definition shr_fexp m e l :=
  shr (shr_record_of_loc m l) e (fexp (Zdigits2 m + e) - e).

Theorem shr_truncate :
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
clear -Hp ; zify ; lia.
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
  if overflow_to_inf m s then F754_infinity s
  else F754_finite s (match (Zpower 2 prec - 1)%Z with Zpos p => p | _ => xH end) (emax - prec).

Definition binary_round_aux mode sx mx ex lx :=
  let '(mrs', e') := shr_fexp mx ex lx in
  let '(mrs'', e'') := shr_fexp (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact in
  match shr_m mrs'' with
  | Z0 => F754_zero sx
  | Zpos m => if Zle_bool e'' (emax - prec) then F754_finite sx m e'' else binary_overflow mode sx
  | _ => F754_nan false xH (* dummy *)
  end.

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
Proof with auto with typeclass_instances.
intros m x mx ex lx Px Bx Ex z.
unfold binary_round_aux in z.
revert z.
rewrite shr_truncate.
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
replace (Z.abs m1') with (Z.abs (cond_Zopp (Rlt_bool x 0) m1')).
rewrite F2R_Zabs.
now apply f_equal.
apply abs_cond_Zopp.
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
rewrite shr_truncate. 2: apply Z.le_refl.
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
rewrite shr_truncate. 2: easy.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0.
rewrite F2R_cond_Zopp, H3, abs_cond_Ropp, <- F2R_abs.
simpl Z.abs.
case_eq (Zle_bool e2 (emax - prec)) ; intros He2.
assert (bounded m2 e2 = true).
apply andb_true_intro.
split.
unfold canonical_mantissa.
apply Zeq_bool_true.
rewrite Zpos_digits2_pos.
rewrite <- mag_F2R_Zdigits.
apply sym_eq.
now rewrite H3 in H4.
discriminate.
exact He2.
apply (conj H).
rewrite Rlt_bool_true.
repeat split.
apply F2R_cond_Zopp.
now apply bounded_lt_emax.
rewrite (Rlt_bool_false _ (bpow radix2 emax)).
refine (conj _ (refl_equal _)).
unfold binary_overflow.
case overflow_to_inf.
apply refl_equal.
unfold valid_binary, bounded.
rewrite Zle_bool_refl.
rewrite Bool.andb_true_r.
apply Zeq_bool_true.
rewrite Zpos_digits2_pos.
replace (Zdigits radix2 (Zpos (match (Zpower 2 prec - 1)%Z with Zpos p => p | _ => xH end))) with prec.
unfold fexp, FLT_exp, emin.
generalize (prec_gt_0 prec).
clear -Hmax ; zify ; lia.
change 2%Z with (radix_val radix2).
case_eq (Zpower radix2 prec - 1)%Z.
simpl Zdigits.
generalize (Zpower_gt_1 radix2 prec (prec_gt_0 prec)).
clear ; lia.
intros p Hp.
apply Zle_antisym.
cut (prec - 1 < Zdigits radix2 (Zpos p))%Z. clear ; lia.
apply Zdigits_gt_Zpower.
simpl Z.abs. rewrite <- Hp.
cut (Zpower radix2 (prec - 1) < Zpower radix2 prec)%Z. clear ; lia.
apply lt_IZR.
rewrite 2!IZR_Zpower. 2: now apply Zlt_le_weak.
apply bpow_lt.
apply Zlt_pred.
now apply Zlt_0_le_0_pred.
apply Zdigits_le_Zpower.
simpl Z.abs. rewrite <- Hp.
apply Zlt_pred.
intros p Hp.
generalize (Zpower_gt_1 radix2 _ (prec_gt_0 prec)).
clear -Hp ; zify ; lia.
apply Rnot_lt_le.
intros Hx.
generalize (refl_equal (bounded m2 e2)).
unfold bounded at 2.
rewrite He2.
rewrite Bool.andb_false_r.
rewrite bounded_canonical_lt_emax with (2 := Hx).
discriminate.
unfold canonical.
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
    FF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_FF z = true /\ sign_FF z = Rlt_bool x 0
  else
    z = binary_overflow mode (Rlt_bool x 0).
Proof with auto with typeclass_instances.
intros m x mx ex lx Bx Ex z.
unfold binary_round_aux in z.
revert z.
rewrite shr_truncate. 2: easy.
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
replace (Z.abs m1') with (Z.abs (cond_Zopp (Rlt_bool x 0) m1')).
rewrite F2R_Zabs.
now apply f_equal.
apply abs_cond_Zopp.
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
rewrite shr_truncate. 2: apply Z.le_refl.
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
rewrite shr_truncate. 2: easy.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0.
rewrite F2R_cond_Zopp, H3, abs_cond_Ropp, <- F2R_abs.
simpl Z.abs.
case_eq (Zle_bool e2 (emax - prec)) ; intros He2.
assert (bounded m2 e2 = true).
apply andb_true_intro.
split.
unfold canonical_mantissa.
apply Zeq_bool_true.
rewrite Zpos_digits2_pos.
rewrite <- mag_F2R_Zdigits.
apply sym_eq.
now rewrite H3 in H4.
discriminate.
exact He2.
apply (conj H).
rewrite Rlt_bool_true.
repeat split.
apply F2R_cond_Zopp.
now apply bounded_lt_emax.
rewrite (Rlt_bool_false _ (bpow radix2 emax)).
refine (conj _ (refl_equal _)).
unfold binary_overflow.
case overflow_to_inf.
apply refl_equal.
unfold valid_binary, bounded.
rewrite Zle_bool_refl.
rewrite Bool.andb_true_r.
apply Zeq_bool_true.
rewrite Zpos_digits2_pos.
replace (Zdigits radix2 (Zpos (match (Zpower 2 prec - 1)%Z with Zpos p => p | _ => xH end))) with prec.
unfold fexp, FLT_exp, emin.
generalize (prec_gt_0 prec).
clear -Hmax ; zify ; lia.
change 2%Z with (radix_val radix2).
case_eq (Zpower radix2 prec - 1)%Z.
simpl Zdigits.
generalize (Zpower_gt_1 radix2 prec (prec_gt_0 prec)).
clear ; lia.
intros p Hp.
apply Zle_antisym.
cut (prec - 1 < Zdigits radix2 (Zpos p))%Z. clear ; lia.
apply Zdigits_gt_Zpower.
simpl Z.abs. rewrite <- Hp.
cut (Zpower radix2 (prec - 1) < Zpower radix2 prec)%Z. clear ; lia.
apply lt_IZR.
rewrite 2!IZR_Zpower. 2: now apply Zlt_le_weak.
apply bpow_lt.
apply Zlt_pred.
now apply Zlt_0_le_0_pred.
apply Zdigits_le_Zpower.
simpl Z.abs. rewrite <- Hp.
apply Zlt_pred.
intros p Hp.
generalize (Zpower_gt_1 radix2 _ (prec_gt_0 prec)).
clear -Hp ; zify ; lia.
apply Rnot_lt_le.
intros Hx.
generalize (refl_equal (bounded m2 e2)).
unfold bounded at 2.
rewrite He2.
rewrite Bool.andb_false_r.
rewrite bounded_canonical_lt_emax with (2 := Hx).
discriminate.
unfold canonical.
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
    FF2R radix2 z = round radix2 fexp (round_mode m) (x * y) /\
    is_finite_FF z = true /\ sign_FF z = xorb sx sy
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
clear -Hmax.
unfold emin.
intros dx dy dxy Hx Hy Hxy.
zify ; intros ; subst.
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

Definition Bmult mult_nan m x y :=
  match x, y with
  | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan (mult_nan x y)
  | B754_infinity sx, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity _, B754_zero _ => build_nan (mult_nan x y)
  | B754_zero _, B754_infinity _ => build_nan (mult_nan x y)
  | B754_finite sx _ _ _, B754_zero sy => B754_zero (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_zero (xorb sx sy)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    FF2B _ (proj1 (Bmult_correct_aux m sx mx ex Hx sy my ey Hy))
  end.

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
intros mult_nan m [sx|sx|sx plx Hplx|sx mx ex Hx] [sy|sy|sy ply Hply|sy my ey Hy] ;
  try ( rewrite ?Rmult_0_r, ?Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ simpl ; try easy ; now rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan | apply bpow_gt_0 | now auto with typeclass_instances ] ).
simpl.
case Bmult_correct_aux.
intros H1.
case Rlt_bool.
intros (H2, (H3, H4)).
split.
now rewrite B2R_FF2B.
split.
now rewrite is_finite_FF2B.
rewrite Bsign_FF2B. auto.
intros H2.
now rewrite B2FF_FF2B.
Qed.

(** Normalization and rounding *)

Definition shl_align mx ex ex' :=
  match (ex' - ex)%Z with
  | Zneg d => (shift_pos d mx, ex')
  | _ => (mx, ex)
  end.

Theorem shl_align_correct :
  forall mx ex ex',
  let (mx', ex'') := shl_align mx ex ex' in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex'') /\
  (ex'' <= ex')%Z.
Proof.
intros mx ex ex'.
unfold shl_align.
case_eq (ex' - ex)%Z.
(* d = 0 *)
intros H.
repeat split.
rewrite Zminus_eq with (1 := H).
apply Z.le_refl.
(* d > 0 *)
intros d Hd.
repeat split.
replace ex' with (ex' - ex + ex)%Z by ring.
rewrite Hd.
pattern ex at 1 ; rewrite <- Zplus_0_l.
now apply Zplus_le_compat_r.
(* d < 0 *)
intros d Hd.
rewrite shift_pos_correct, Zmult_comm.
change (Zpower_pos 2 d) with (Zpower radix2 (Zpos d)).
change (Zpos d) with (Z.opp (Zneg d)).
rewrite <- Hd.
split.
replace (- (ex' - ex))%Z with (ex - ex')%Z by ring.
apply F2R_change_exp.
apply Zle_0_minus_le.
replace (ex - ex')%Z with (- (ex' - ex))%Z by ring.
now rewrite Hd.
apply Z.le_refl.
Qed.

Theorem snd_shl_align :
  forall mx ex ex',
  (ex' <= ex)%Z ->
  snd (shl_align mx ex ex') = ex'.
Proof.
intros mx ex ex' He.
unfold shl_align.
case_eq (ex' - ex)%Z ; simpl.
intros H.
now rewrite Zminus_eq with (1 := H).
intros p.
clear -He ; zify ; lia.
intros.
apply refl_equal.
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

Definition binary_round m sx mx ex :=
  let '(mz, ez) := shl_align_fexp mx ex in binary_round_aux m sx (Zpos mz) ez loc_Exact.

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

Definition binary_normalize mode m e szero :=
  match m with
  | Z0 => B754_zero szero
  | Zpos m => FF2B _ (proj1 (binary_round_correct mode false m e))
  | Zneg m => FF2B _ (proj1 (binary_round_correct mode true m e))
  end.

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
now rewrite B2R_FF2B.
split.
now rewrite is_finite_FF2B.
rewrite Bsign_FF2B, Rz''.
rewrite Rcompare_Gt...
apply F2R_gt_0.
simpl. zify; lia.
intros Hz' (Vz, Rz).
rewrite B2FF_FF2B, Rz.
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
now rewrite B2R_FF2B.
split.
now rewrite is_finite_FF2B.
rewrite Bsign_FF2B, Rz''.
rewrite Rcompare_Lt...
apply F2R_lt_0.
simpl. zify; lia.
intros Hz' (Vz, Rz).
rewrite B2FF_FF2B, Rz.
apply f_equal.
apply sym_eq.
apply Rlt_bool_true.
now apply F2R_lt_0.
Qed.

(** Addition *)

Definition Bplus plus_nan m x y :=
  match x, y with
  | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan (plus_nan x y)
  | B754_infinity sx, B754_infinity sy =>
    if Bool.eqb sx sy then x else build_nan (plus_nan x y)
  | B754_infinity _, _ => x
  | _, B754_infinity _ => y
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx sy then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, _ => y
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Z.min ex ey in
    binary_normalize m (Zplus (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez)))))
      ez (match m with mode_DN => true | _ => false end)
  end.

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
intros plus_nan m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] Fx Fy ; try easy.
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
set (mz := (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))) + cond_Zopp sy (Zpos (fst (shl_align my ey ez))))%Z).
assert (Hp: (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) +
  F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey))%R = F2R (Float radix2 mz ez)).
rewrite 2!F2R_cond_Zopp.
generalize (shl_align_correct mx ex ez).
generalize (shl_align_correct my ey ez).
generalize (snd_shl_align mx ex ez (Z.le_min_l ex ey)).
generalize (snd_shl_align my ey ez (Z.le_min_r ex ey)).
destruct (shl_align mx ex ez) as (mx', ex').
destruct (shl_align my ey ez) as (my', ey').
simpl.
intros H1 H2.
rewrite H1, H2.
clear H1 H2.
intros (H1, _) (H2, _).
rewrite H1, H2.
clear H1 H2.
rewrite <- 2!F2R_cond_Zopp.
unfold F2R. simpl.
now rewrite <- Rmult_plus_distr_r, <- plus_IZR.
rewrite Hp.
assert (Sz: (bpow radix2 emax <= Rabs (round radix2 fexp (round_mode m) (F2R (Float radix2 mz ez))))%R -> sx = Rlt_bool (F2R (Float radix2 mz ez)) 0 /\ sx = sy).
(* . *)
rewrite <- Hp.
intros Bz.
destruct (Bool.bool_dec sx sy) as [Hs|Hs].
(* .. *)
refine (conj _ Hs).
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
generalize (bounded_lt_emax _ _ Hx) (bounded_lt_emax _ _ Hy) (andb_prop _ _ Hx) (andb_prop _ _ Hy).
intros Bx By (Hx',_) (Hy',_).
generalize (canonical_canonical_mantissa sx _ _ Hx') (canonical_canonical_mantissa sy _ _ Hy').
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
(* . *)
generalize (binary_normalize_correct m mz ez szero).
case Rlt_bool_spec.
split; try easy. split; try easy.
destruct (Rcompare_spec (F2R (beta:=radix2) {| Fnum := mz; Fexp := ez |}) 0); try easy.
rewrite H1 in Hp.
apply Rplus_opp_r_uniq in Hp.
rewrite <- F2R_Zopp in Hp.
eapply canonical_unique in Hp.
inversion Hp. destruct sy, sx, m; try discriminate H3; easy.
apply canonical_canonical_mantissa.
apply Bool.andb_true_iff in Hy. easy.
replace (-cond_Zopp sx (Z.pos mx))%Z with (cond_Zopp (negb sx) (Z.pos mx))
  by (destruct sx; auto).
apply canonical_canonical_mantissa.
apply Bool.andb_true_iff in Hx. easy.
intros Hz' Vz.
specialize (Sz Hz').
split.
rewrite Vz.
now apply f_equal.
apply Sz.
Qed.

(** Subtraction *)

Definition Bminus minus_nan m x y :=
  match x, y with
  | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan (minus_nan x y)
  | B754_infinity sx, B754_infinity sy =>
    if Bool.eqb sx (negb sy) then x else build_nan (minus_nan x y)
  | B754_infinity _, _ => x
  | _, B754_infinity sy => B754_infinity (negb sy)
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx (negb sy) then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, B754_finite sy my ey Hy => B754_finite (negb sy) my ey Hy
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Z.min ex ey in
    binary_normalize m (Zminus (cond_Zopp sx (Zpos (fst (shl_align mx ex ez)))) (cond_Zopp sy (Zpos (fst (shl_align my ey ez)))))
      ez (match m with mode_DN => true | _ => false end)
  end.

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
intros minus_nan m x y Fx Fy.
generalize (Bplus_correct minus_nan m x (Bopp (fun n => minus_nan n (B754_zero false)) y) Fx).
rewrite is_finite_Bopp, B2R_Bopp.
intros H.
specialize (H Fy).
replace (negb (Bsign y)) with (Bsign (Bopp (fun n => minus_nan n (B754_zero false)) y)).
destruct x as [| | |sx mx ex Hx], y as [| | |sy my ey Hy] ; try easy.
unfold Bminus, Zminus.
now rewrite <- cond_Zopp_negb.
now destruct y as [ | | | ].
Qed.

(** Fused Multiply-Add *)

Definition Bfma_szero m (x y z: binary_float) : bool :=
  let s_xy := xorb (Bsign x) (Bsign y) in  (* sign of product x*y *)
  if Bool.eqb s_xy (Bsign z) then s_xy
  else match m with mode_DN => true | _ => false end.

Definition Bfma fma_nan m (x y z: binary_float) :=
  match x, y with
  | B754_nan _ _ _, _ | _, B754_nan _ _ _
  | B754_infinity _, B754_zero _
  | B754_zero _, B754_infinity _ =>
      (* Multiplication produces NaN *)
      build_nan (fma_nan x y z)
  | B754_infinity sx, B754_infinity sy
  | B754_infinity sx, B754_finite sy _ _ _
  | B754_finite sx _ _ _, B754_infinity sy =>
      let s := xorb sx sy in
      (* Multiplication produces infinity with sign [s] *)
      match z with
      | B754_nan _ _ _ => build_nan (fma_nan x y z)
      | B754_infinity sz =>
          if Bool.eqb s sz then z else build_nan (fma_nan x y z)
      | _ => B754_infinity s
      end
  | B754_finite sx _ _ _, B754_zero sy
  | B754_zero sx, B754_finite sy _ _ _
  | B754_zero sx, B754_zero sy =>
      (* Multiplication produces zero *)
      match z with
      | B754_nan _ _ _ => build_nan (fma_nan x y z)
      | B754_zero _ => B754_zero (Bfma_szero m x y z)
      | _ => z
      end
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>
      (* Multiplication produces a finite, non-zero result *)
      match z with
      | B754_nan _ _ _ => build_nan (fma_nan x y z)
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
  forall fma_nan m x y z,
  let res := (B2R x * B2R y + B2R z)%R in
  is_finite x = true ->
  is_finite y = true ->
  is_finite z = true ->
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
  intros. pattern (Bfma fma_nan m x y z).
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
    | B754_nan _ _ _ => build_nan (fma_nan x y z)
    | B754_zero sz => B754_zero szero
    | _ => z
    end).
  assert (ADDZERO: B2R x = 0%R \/ B2R y = 0%R -> PROP add_zero).
  {
    intros Z.
    assert (RES: res = B2R z).
    { unfold res. destruct Z as [E|E]; rewrite E, ?Rmult_0_l, ?Rmult_0_r, Rplus_0_l; auto. }
    unfold PROP, add_zero; destruct z as [ sz | sz | sz plz | sz mz ez Bz]; try discriminate.
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
  destruct x as [ sx | sx | sx plx | sx mx ex Bx];
  destruct y as [ sy | sy | sy ply | sy my ey By];
  try discriminate.
- apply ADDZERO; auto.
- apply ADDZERO; auto.
- apply ADDZERO; auto.
- destruct z as [ sz | sz | sz plz | sz mz ez Bz]; try discriminate; unfold Bfma.
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

Definition Fdiv_core_binary m1 e1 m2 e2 :=
  let d1 := Zdigits2 m1 in
  let d2 := Zdigits2 m2 in
  let e' := Z.min (fexp (d1 + e1 - (d2 + e2))) (e1 - e2) in
  let s := (e1 - e2 - e')%Z in
  let m' :=
    match s with
    | Zpos _  => Z.shiftl m1 s
    | Z0 => m1
    | Zneg _ => Z0
    end in
  let '(q, r) :=  Zfast_div_eucl m' m2 in
  (q, e', new_location m2 r loc_Exact).

Lemma Bdiv_correct_aux :
  forall m sx mx ex sy my ey,
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  let z :=
    let '(mz, ez, lz) := Fdiv_core_binary (Zpos mx) ex (Zpos my) ey in
    binary_round_aux m (xorb sx sy) mz ez lz in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (x / y))) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode m) (x / y) /\
    is_finite_FF z = true /\ sign_FF z = xorb sx sy
  else
    z = binary_overflow m (xorb sx sy).
Proof.
intros m sx mx ex sy my ey.
unfold Fdiv_core_binary.
rewrite 2!Zdigits2_Zdigits.
set (e' := Z.min _ _).
generalize (Fdiv_core_correct radix2 (Zpos mx) ex (Zpos my) ey e' eq_refl eq_refl).
unfold Fdiv_core.
rewrite Zle_bool_true by apply Z.le_min_r.
match goal with |- context [Zfast_div_eucl ?m _] => set (mx' := m) end.
assert (mx' = Zpos mx * Zpower radix2 (ex - ey - e'))%Z as <-.
{ unfold mx'.
  destruct (ex - ey - e')%Z as [|p|p].
  now rewrite Zmult_1_r.
  now rewrite Z.shiftl_mul_pow2.
  easy. }
clearbody mx'.
rewrite Zfast_div_eucl_correct.
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
  now rewrite <- 2!F2R_Zabs, 2!abs_cond_Zopp.
  now apply F2R_neq_0 ; case sy.
- rewrite <- cexp_abs, Rabs_mult, Rabs_Rinv.
  rewrite 2!F2R_cond_Zopp, 2!abs_cond_Ropp, <- Rabs_Rinv.
  rewrite <- Rabs_mult, cexp_abs.
  apply Z.le_trans with (1 := Z.le_min_l _ _).
  apply FLT_exp_monotone.
  now apply mag_div_F2R.
  now apply F2R_neq_0.
  now apply F2R_neq_0 ; case sy.
Qed.

Definition Bdiv div_nan m x y :=
  match x, y with
  | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan (div_nan x y)
  | B754_infinity sx, B754_infinity sy => build_nan (div_nan x y)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_infinity sx, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_finite sx _ _ _, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => build_nan (div_nan x y)
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>
    FF2B _ (proj1 (Bdiv_correct_aux m sx mx ex sy my ey))
  end.

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
intros div_nan m x [sy|sy|sy ply|sy my ey Hy] Zy ; try now elim Zy.
revert x.
unfold Rdiv.
intros [sx|sx|sx plx Hx|sx mx ex Hx] ;
  try ( rewrite Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ simpl ; try easy ; now rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan | apply bpow_gt_0 | auto with typeclass_instances ] ).
simpl.
case Bdiv_correct_aux.
intros H1.
unfold Rdiv.
case Rlt_bool.
intros (H2, (H3, H4)).
split.
now rewrite B2R_FF2B.
split.
now rewrite is_finite_FF2B.
rewrite Bsign_FF2B. congruence.
intros H2.
now rewrite B2FF_FF2B.
Qed.

(** Square root *)

Definition Fsqrt_core_binary m e :=
  let d := Zdigits2 m in
  let e' := Z.min (fexp (Z.div2 (d + e + 1))) (Z.div2 e) in
  let s := (e - 2 * e')%Z in
  let m' :=
    match s with
    | Zpos p => Z.shiftl m s
    | Z0 => m
    | Zneg _ => Z0
    end in
  let (q, r) := Z.sqrtrem m' in
  let l :=
    if Zeq_bool r 0 then loc_Exact
    else loc_Inexact (if Zle_bool r q then Lt else Gt) in
  (q, e', l).

Lemma Bsqrt_correct_aux :
  forall m mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (Zpos mx) ex) in
  let z :=
    let '(mz, ez, lz) := Fsqrt_core_binary (Zpos mx) ex in
    binary_round_aux m false mz ez lz in
  valid_binary z = true /\
  FF2R radix2 z = round radix2 fexp (round_mode m) (sqrt x) /\
  is_finite_FF z = true /\ sign_FF z = false.
Proof with auto with typeclass_instances.
intros m mx ex Hx.
unfold Fsqrt_core_binary.
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
generalize (prec_gt_0 prec).
clear -Hmax ; lia.
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
clear -Hmax ; lia.
apply generic_format_ge_bpow with fexp.
intros.
apply Z.le_max_r.
now apply F2R_gt_0.
apply generic_format_canonical.
apply (canonical_canonical_mantissa false).
apply (andb_prop _ _ Hx).
apply round_ge_generic...
apply generic_format_0.
apply sqrt_ge_0.
Qed.

Definition Bsqrt sqrt_nan m x :=
  match x with
  | B754_nan sx plx _ => build_nan (sqrt_nan x)
  | B754_infinity false => x
  | B754_infinity true => build_nan (sqrt_nan x)
  | B754_finite true _ _ _ => build_nan (sqrt_nan x)
  | B754_zero _ => x
  | B754_finite sx mx ex Hx =>
    FF2B _ (proj1 (Bsqrt_correct_aux m mx ex Hx))
  end.

Theorem Bsqrt_correct :
  forall sqrt_nan m x,
  B2R (Bsqrt sqrt_nan m x) = round radix2 fexp (round_mode m) (sqrt (B2R x)) /\
  is_finite (Bsqrt sqrt_nan m x) = match x with B754_zero _ => true | B754_finite false _ _ _ => true | _ => false end /\
  (is_nan (Bsqrt sqrt_nan m x) = false -> Bsign (Bsqrt sqrt_nan m x) = Bsign x).
Proof.
intros sqrt_nan m [sx|[|]|sx plx Hplx|sx mx ex Hx] ;
  try ( simpl ; rewrite sqrt_0, round_0, ?B2R_build_nan, ?is_finite_build_nan, ?is_nan_build_nan ; intuition auto with typeclass_instances ; easy).
simpl.
case Bsqrt_correct_aux.
intros H1 (H2, (H3, H4)).
case sx.
rewrite B2R_build_nan, is_finite_build_nan, is_nan_build_nan.
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
now rewrite B2R_FF2B.
split.
now rewrite is_finite_FF2B.
intros _.
now rewrite Bsign_FF2B.
Qed.

(** A few values *)

Definition Bone := FF2B _ (proj1 (binary_round_correct mode_NE false 1 0)).

Theorem Bone_correct : B2R Bone = 1%R.
Proof.
unfold Bone; simpl.
set (Hr := binary_round_correct _ _ _ _).
unfold Hr; rewrite B2R_FF2B.
destruct Hr as (Vz, Hr).
revert Hr.
fold emin; simpl.
rewrite round_generic; [|now apply valid_rnd_N|].
- unfold F2R; simpl; rewrite Rmult_1_r.
  rewrite Rlt_bool_true.
  + now intros (Hr, Hr'); rewrite Hr.
  + rewrite Rabs_pos_eq; [|lra].
    change 1%R with (bpow radix2 0); apply bpow_lt.
    unfold Prec_gt_0 in prec_gt_0_; lia.
- apply generic_format_F2R; intros _.
  unfold cexp, fexp, FLT_exp, F2R; simpl; rewrite Rmult_1_r, mag_1.
  unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
Qed.

Lemma is_finite_Bone : is_finite Bone = true.
Proof.
generalize Bone_correct; case Bone; simpl;
 try (intros; reflexivity); intros; exfalso; lra.
Qed.

Lemma Bsign_Bone : Bsign Bone = false.
Proof.
generalize Bone_correct; case Bone; simpl;
  try (intros; exfalso; lra); intros s' m e _.
case s'; [|now intro]; unfold F2R; simpl.
intro H; exfalso; revert H; apply Rlt_not_eq, (Rle_lt_trans _ 0); [|lra].
rewrite <-Ropp_0, <-(Ropp_involutive (_ * _)); apply Ropp_le_contravar.
rewrite Ropp_mult_distr_l; apply Rmult_le_pos; [|now apply bpow_ge_0].
unfold IZR; rewrite <-INR_IPR; generalize (INR_pos m); lra.
Qed.

Lemma Bmax_float_proof :
  valid_binary
    (F754_finite false (shift_pos (Z.to_pos prec) 1 - 1) (emax - prec))
  = true.
Proof.
unfold valid_binary, bounded; apply andb_true_intro; split.
- unfold canonical_mantissa; apply Zeq_bool_true.
  set (p := Z.pos (digits2_pos _)).
  assert (H : p = prec).
  { unfold p; rewrite Zpos_digits2_pos, Pos2Z.inj_sub.
    - rewrite shift_pos_correct, Z.mul_1_r.
      assert (P2pm1 : (0 <= 2 ^ prec - 1)%Z).
      { apply (Zplus_le_reg_r _ _ 1); ring_simplify.
        change 1%Z with (2 ^ 0)%Z; change 2%Z with (radix2 : Z).
        apply Zpower_le; unfold Prec_gt_0 in prec_gt_0_; lia. }
      apply Zdigits_unique;
        rewrite Z.pow_pos_fold, Z2Pos.id; [|exact prec_gt_0_]; simpl; split.
      + rewrite (Z.abs_eq _ P2pm1).
        replace prec with (prec - 1 + 1)%Z at 2 by ring.
        rewrite Zpower_plus; [| unfold Prec_gt_0 in prec_gt_0_; lia|lia].
        simpl; unfold Z.pow_pos; simpl.
        assert (1 <= 2 ^ (prec - 1))%Z; [|lia].
        change 1%Z with (2 ^ 0)%Z; change 2%Z with (radix2 : Z).
        apply Zpower_le; simpl; unfold Prec_gt_0 in prec_gt_0_; lia.
      + now rewrite Z.abs_eq; [lia|].
    - change (_ < _)%positive
        with (Z.pos 1 < Z.pos (shift_pos (Z.to_pos prec) 1))%Z.
      rewrite shift_pos_correct, Z.mul_1_r, Z.pow_pos_fold.
      rewrite Z2Pos.id; [|exact prec_gt_0_].
      change 1%Z with (2 ^ 0)%Z; change 2%Z with (radix2 : Z).
      apply Zpower_lt; unfold Prec_gt_0 in prec_gt_0_; lia. }
  unfold fexp, FLT_exp; rewrite H, Z.max_l; [ring|].
  unfold Prec_gt_0 in prec_gt_0_; unfold emin; lia.
- apply Zle_bool_true; unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
Qed.

Definition Bmax_float := FF2B _ Bmax_float_proof.

(** Extraction/modification of mantissa/exponent *)

Definition Bnormfr_mantissa x :=
  match x with
  | B754_finite _ mx ex _ =>
    if Z.eqb ex (-prec)%Z then Npos mx else 0%N
  | _ => 0%N
  end.

Definition Bldexp mode f e :=
  match f with
  | B754_finite sx mx ex _ =>
    FF2B _ (proj1 (binary_round_correct mode sx mx (ex+e)))
  | _ => f
  end.

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
intros m f e.
case f.
- intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- intro s; simpl; rewrite Rmult_0_l, round_0; [|apply valid_rnd_round_mode].
  now rewrite Rabs_R0, Rlt_bool_true; [|now apply bpow_gt_0].
- intros s mf ef Hmef.
  case (Rlt_bool_spec _ _); intro Hover.
  + unfold Bldexp; rewrite B2R_FF2B, is_finite_FF2B, Bsign_FF2B.
    simpl; unfold F2R; simpl; rewrite Rmult_assoc, <-bpow_plus.
    destruct (binary_round_correct m s mf (ef + e)) as (Hf, Hr).
    fold emin in Hr; simpl in Hr; rewrite Rlt_bool_true in Hr.
    * now destruct Hr as (Hr, (Hfr, Hsr)); rewrite Hr, Hfr, Hsr.
    * now revert Hover; unfold B2R, F2R; simpl; rewrite Rmult_assoc, bpow_plus.
  + unfold Bldexp; rewrite B2FF_FF2B; simpl.
    destruct (binary_round_correct m s mf (ef + e)) as (Hf, Hr).
    fold emin in Hr; simpl in Hr; rewrite Rlt_bool_false in Hr; [exact Hr|].
    now revert Hover; unfold B2R, F2R; simpl; rewrite Rmult_assoc, bpow_plus.
Qed.

(** This hypothesis is needed to implement [Bfrexp]
    (otherwise, we have emin > - prec
     and [Bfrexp] cannot fit the mantissa in interval #[0.5, 1)#) *)
Hypothesis Hemax : (3 <= emax)%Z.

Definition Ffrexp_core_binary s m e :=
  if (Z.to_pos prec <=? digits2_pos m)%positive then
    (F754_finite s m (-prec), (e + prec)%Z)
  else
    let d := (prec - Z.pos (digits2_pos m))%Z in
    (F754_finite s (shift_pos (Z.to_pos d) m) (-prec), (e + prec - d)%Z).

Lemma Bfrexp_correct_aux :
  forall sx mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (cond_Zopp sx (Z.pos mx)) ex) in
  let z := fst (Ffrexp_core_binary sx mx ex) in
  let e := snd (Ffrexp_core_binary sx mx ex) in
  valid_binary z = true /\
  (/2 <= Rabs (FF2R radix2 z) < 1)%R /\
  (x = FF2R radix2 z * bpow radix2 e)%R.
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
case (Pos.leb_spec _ _); simpl; intro Dmx.
- unfold bounded, F2R; simpl.
  assert (Dmx' : digits2_pos mx = Z.to_pos prec).
  { now apply Pos.le_antisym. }
  assert (Dmx'' : Z.pos (digits2_pos mx) = prec).
  { now rewrite Dmx', Z2Pos.id; [|apply prec_gt_0_]. }
  split; [|split].
  + apply andb_true_intro.
    split; [|apply Zle_bool_true; lia].
    apply Zeq_bool_true; unfold fexp, FLT_exp.
    rewrite Dmx', Z2Pos.id; [|now apply prec_gt_0_].
    rewrite Z.max_l; [ring|unfold emin; lia].
  + rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)); [|now apply bpow_ge_0].
    rewrite <-abs_IZR, abs_cond_Zopp; simpl; split.
    * apply (Rmult_le_reg_r (bpow radix2 prec)); [now apply bpow_gt_0|].
      rewrite Rmult_assoc, <-bpow_plus, Z.add_opp_diag_l; simpl.
      rewrite Rmult_1_r.
      change (/ 2)%R with (bpow radix2 (- 1)); rewrite <-bpow_plus.
      rewrite <-Dmx'', Z.add_comm, Zpos_digits2_pos, Zdigits_mag; [|lia].
      set (b := bpow _ _).
      rewrite <-(Rabs_pos_eq (IZR _)); [|apply IZR_le; lia].
      apply bpow_mag_le; apply IZR_neq; lia.
    * apply (Rmult_lt_reg_r (bpow radix2 prec)); [now apply bpow_gt_0|].
      rewrite Rmult_assoc, <-bpow_plus, Z.add_opp_diag_l; simpl.
      rewrite Rmult_1_l, Rmult_1_r.
      rewrite <-Dmx'', Zpos_digits2_pos, Zdigits_mag; [|lia].
      set (b := bpow _ _).
      rewrite <-(Rabs_pos_eq (IZR _)); [|apply IZR_le; lia].
      apply bpow_mag_gt; apply IZR_neq; lia.
  + unfold x, F2R; simpl; rewrite Rmult_assoc, <-bpow_plus.
    now replace (_ + _)%Z with ex by ring.
- unfold bounded, F2R; simpl.
  assert (Dmx' : (Z.pos (digits2_pos mx) < prec)%Z).
  { now rewrite <-(Z2Pos.id prec); [|now apply prec_gt_0_]. }
  split; [|split].
  + unfold bounded; apply andb_true_intro.
    split; [|apply Zle_bool_true; lia].
    apply Zeq_bool_true; unfold fexp, FLT_exp.
    rewrite Zpos_digits2_pos, shift_pos_correct, Z.pow_pos_fold.
    rewrite Z2Pos.id; [|lia].
    rewrite Z.mul_comm; change 2%Z with (radix2 : Z).
    rewrite Zdigits_mult_Zpower; [|lia|lia].
    rewrite Zpos_digits2_pos; replace (_ - _)%Z with (- prec)%Z by ring.
    now rewrite Z.max_l; [|unfold emin; lia].
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
      rewrite <-(Rabs_pos_eq (IZR _)); [|apply IZR_le; lia].
      unfold d; rewrite Zpos_digits2_pos, Zdigits_mag; [|lia].
      apply bpow_mag_le; apply IZR_neq; lia.
    * apply (Rmult_lt_reg_l (bpow radix2 d)); [now apply bpow_gt_0|].
      rewrite <-Rmult_assoc, <-bpow_plus, Z.add_opp_diag_r.
      rewrite Rmult_1_l, Rmult_1_r.
      rewrite <-(Rabs_pos_eq (IZR _)); [|apply IZR_le; lia].
      unfold d; rewrite Zpos_digits2_pos, Zdigits_mag; [|lia].
      apply bpow_mag_gt; apply IZR_neq; lia.
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
    (FF2B _ (proj1 (Bfrexp_correct_aux s m e H)), e')
  | _ => (f, (-2*emax-prec)%Z)
  end.

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
intro f; case f; intro s; try discriminate; intros m e Hf _.
generalize (Bfrexp_correct_aux s m e Hf).
intros (_, (Hb, Heq)); simpl; rewrite B2R_FF2B.
split; [now simpl|]; split; [now simpl|].
rewrite Heq, mag_mult_bpow.
- apply (Z.add_reg_l (- (snd (Ffrexp_core_binary s m e)))).
  now ring_simplify; symmetry; apply mag_unique.
- intro H; destruct Hb as (Hb, _); revert Hb; rewrite H, Rabs_R0; lra.
Qed.

(** Ulp *)

Definition Bulp x := Bldexp mode_NE Bone (fexp (snd (Bfrexp x))).

Theorem Bulp_correct :
  forall x,
  is_finite x = true ->
  B2R (Bulp x) = ulp radix2 fexp (B2R x) /\
  is_finite (Bulp x) = true /\
  Bsign (Bulp x) = false.
Proof.
intro x; case x.
- intros s _; unfold Bulp.
  replace (fexp _) with emin.
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
      unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
  + simpl; change (fexp _) with (fexp (-2 * emax - prec)).
    unfold fexp, FLT_exp; rewrite Z.max_r; [reflexivity|].
    unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
- intro; discriminate.
- intros s pl Hpl; discriminate.
- intros s m e Hme _; unfold Bulp, ulp, cexp.
  set (f := B754_finite _ _ _ _).
  rewrite Req_bool_false.
  + destruct (Bfrexp_correct f (eq_refl _)) as (Hfr1, (Hfr2, Hfr3)).
    rewrite Hfr3.
    set (e' := fexp _).
    generalize (Bldexp_correct mode_NE Bone e').
    rewrite Bone_correct, Rmult_1_l, round_generic; [|now apply valid_rnd_N|].
    { rewrite Rlt_bool_true.
      - intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
        now split; [|split; [apply is_finite_Bone|apply Bsign_Bone]].
      - rewrite Rabs_pos_eq; [|now apply bpow_ge_0].
        unfold e', fexp, FLT_exp.
        case (Z.max_spec (mag radix2 (B2R f) - prec) emin)
          as [(_, Hm)|(_, Hm)]; rewrite Hm; apply bpow_lt;
          [now unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia|].
        apply (Zplus_lt_reg_r _ _ prec); ring_simplify.
        assert (mag radix2 (B2R f) <= emax)%Z;
          [|now unfold Prec_gt_0 in prec_gt_0_; lia].
        apply mag_le_bpow; [|now apply abs_B2R_lt_emax].
        now unfold f, B2R; apply F2R_neq_0; case s. }
    apply generic_format_bpow, Z.max_lub.
    * unfold Prec_gt_0 in prec_gt_0_; lia.
    * apply Z.le_max_r.
  + now unfold f, B2R; apply F2R_neq_0; case s.
Qed.

(** Successor (and predecessor) *)

Definition Bpred_pos pred_pos_nan x :=
  match x with
  | B754_finite _ mx _ _ =>
    let d :=
      if (mx~0 =? shift_pos (Z.to_pos prec) 1)%positive then
        Bldexp mode_NE Bone (fexp (snd (Bfrexp x) - 1))
      else
        Bulp x in
    Bminus (fun _ => pred_pos_nan) mode_NE x d
  | _ => x
  end.

Theorem Bpred_pos_correct :
  forall pred_pos_nan x,
  (0 < B2R x)%R ->
  B2R (Bpred_pos pred_pos_nan x) = pred_pos radix2 fexp (B2R x) /\
  is_finite (Bpred_pos pred_pos_nan x) = true /\
  Bsign (Bpred_pos pred_pos_nan x) = false.
Proof.
intros pred_pos_nan x.
generalize (Bfrexp_correct x).
case x.
- simpl; intros s _ Bx; exfalso; apply (Rlt_irrefl _ Bx).
- simpl; intros s _ Bx; exfalso; apply (Rlt_irrefl _ Bx).
- simpl; intros s pl Hpl _ Bx; exfalso; apply (Rlt_irrefl _ Bx).
- intros sx mx ex Hmex Hfrexpx Px.
  assert (Hsx : sx = false).
  { revert Px; case sx; unfold B2R, F2R; simpl; [|now intro].
    intro Px; exfalso; revert Px; apply Rle_not_lt.
    rewrite <-(Rmult_0_l (bpow radix2 ex)).
    apply Rmult_le_compat_r; [apply bpow_ge_0|apply IZR_le; lia]. }
  clear Px; rewrite Hsx in Hfrexpx |- *; clear Hsx sx.
  specialize (Hfrexpx (eq_refl _)).
  simpl in Hfrexpx; rewrite B2R_FF2B in Hfrexpx.
  destruct Hfrexpx as (Hfrexpx_bounds, (Hfrexpx_eq, Hfrexpx_exp)).
  unfold Bpred_pos, Bfrexp.
  simpl (snd (_, snd _)).
  rewrite Hfrexpx_exp.
  set (x' := B754_finite _ _ _ _).
  set (xr := F2R _).
  assert (Nzxr : xr <> 0%R).
  { unfold xr, F2R; simpl.
    rewrite <-(Rmult_0_l (bpow radix2 ex)); intro H.
    apply Rmult_eq_reg_r in H; [|apply Rgt_not_eq, bpow_gt_0].
    apply eq_IZR in H; lia. }
  assert (Hulp := Bulp_correct x').
  specialize (Hulp (eq_refl _)).
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
    apply Z.max_lub_lt; [|unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia].
    apply (Zplus_lt_reg_r _ _ (prec + 1)); ring_simplify.
    rewrite Z.add_1_r; apply Zle_lt_succ, mag_le_bpow.
    - exact Nzxr.
    - apply (Rlt_le_trans _ (bpow radix2 emax)).
      + change xr with (B2R x'); apply abs_B2R_lt_emax.
      + apply bpow_le; unfold Prec_gt_0 in prec_gt_0_; lia. }
  set (d := if (mx~0 =? _)%positive then _ else _).
  set (minus_nan := fun _ => _).
  assert (Hminus := Bminus_correct minus_nan mode_NE x' d (eq_refl _)).
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
        { now generalize Hmex; unfold bounded; rewrite Bool.andb_true_iff. }
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
    * now unfold pred_pos; rewrite Req_bool_false.
Qed.

Definition Bsucc succ_nan x :=
  match x with
  | B754_zero _ => Bldexp mode_NE Bone emin
  | B754_infinity false => x
  | B754_infinity true => Bopp succ_nan Bmax_float
  | B754_nan _ _ _ => build_nan (succ_nan x)
  | B754_finite false _ _ _ =>
    Bplus (fun _ => succ_nan) mode_NE x (Bulp x)
  | B754_finite true _ _ _ =>
    Bopp succ_nan (Bpred_pos succ_nan (Bopp succ_nan x))
  end.

Lemma Bsucc_correct :
  forall succ_nan x,
  is_finite x = true ->
  if Rlt_bool (succ radix2 fexp (B2R x)) (bpow radix2 emax) then
    B2R (Bsucc succ_nan x) = succ radix2 fexp (B2R x) /\
    is_finite (Bsucc succ_nan x) = true /\
    (Bsign (Bsucc succ_nan x) = Bsign x && is_finite_strict x)%bool
  else
    B2FF (Bsucc succ_nan x) = F754_infinity false.
Proof.
assert (Hsucc : succ radix2 fexp 0 = bpow radix2 emin).
{ unfold succ; rewrite Rle_bool_true; [|now right]; rewrite Rplus_0_l.
  unfold ulp; rewrite Req_bool_true; [|now simpl].
  destruct (negligible_exp_FLT emin prec) as (n, (Hne, Hn)).
  now unfold fexp; rewrite Hne; unfold FLT_exp; rewrite Z.max_r;
    [|unfold Prec_gt_0 in prec_gt_0_; lia]. }
intros succ_nan [s|s|s pl Hpl|sx mx ex Hmex]; try discriminate; intros _.
- generalize (Bldexp_correct mode_NE Bone emin); unfold Bsucc; simpl.
  assert (Hbemin : round radix2 fexp ZnearestE (bpow radix2 emin)
                   = bpow radix2 emin).
  { rewrite round_generic; [reflexivity|apply valid_rnd_N|].
    apply generic_format_bpow.
    unfold fexp, FLT_exp; rewrite Z.max_r; [now simpl|].
    unfold Prec_gt_0 in prec_gt_0_; lia. }
  rewrite Hsucc, Rlt_bool_true.
  + intros (Hr, (Hf, Hs)); rewrite Hr, Hf, Hs.
    rewrite Bone_correct, Rmult_1_l, is_finite_Bone, Bsign_Bone.
    case Rlt_bool_spec; intro Hover.
    * now rewrite Bool.andb_false_r.
    * exfalso; revert Hover; apply Rlt_not_le, bpow_lt.
      unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
  + rewrite Bone_correct, Rmult_1_l, Hbemin, Rabs_pos_eq; [|apply bpow_ge_0].
    apply bpow_lt; unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
- unfold Bsucc; case sx.
  + case Rlt_bool_spec; intro Hover.
    * rewrite B2R_Bopp; simpl (Bopp _ (B754_finite _ _ _ _)).
      rewrite is_finite_Bopp.
      set (ox := B754_finite false mx ex Hmex).
      assert (Hpred := Bpred_pos_correct succ_nan ox).
      assert (Hox : (0 < B2R ox)%R); [|specialize (Hpred Hox); clear Hox].
      { now apply Rmult_lt_0_compat; [apply IZR_lt|apply bpow_gt_0]. }
      rewrite (proj1 Hpred), (proj1 (proj2 Hpred)).
      unfold succ; rewrite Rle_bool_false; [split; [|split]|].
      { now unfold B2R, F2R, ox; simpl; rewrite Ropp_mult_distr_l, <-opp_IZR. }
      { now simpl. }
      { simpl (Bsign (B754_finite _ _ _ _)); simpl (true && _)%bool.
        rewrite Bsign_Bopp, (proj2 (proj2 Hpred)); [now simpl|].
        now destruct Hpred as (_, (H, _)); revert H; case (Bpred_pos _ _). }
      unfold B2R, F2R; simpl; change (Z.neg mx) with (- Z.pos mx)%Z.
      rewrite opp_IZR, <-Ropp_mult_distr_l, <-Ropp_0; apply Ropp_lt_contravar.
      now apply Rmult_lt_0_compat; [apply IZR_lt|apply bpow_gt_0].
    * exfalso; revert Hover; apply Rlt_not_le.
      apply (Rle_lt_trans _ (succ radix2 fexp 0)).
      { apply succ_le; [now apply FLT_exp_valid|apply generic_format_B2R|
                        apply generic_format_0|].
        unfold B2R, F2R; simpl; change (Z.neg mx) with (- Z.pos mx)%Z.
        rewrite opp_IZR, <-Ropp_mult_distr_l, <-Ropp_0; apply Ropp_le_contravar.
        now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
      rewrite Hsucc; apply bpow_lt.
      unfold emin; unfold Prec_gt_0 in prec_gt_0_; lia.
  + set (x := B754_finite _ _ _ _).
    set (plus_nan := fun _ => succ_nan).
    assert (Hulp := Bulp_correct x (eq_refl _)).
    assert (Hplus := Bplus_correct plus_nan mode_NE x (Bulp x) (eq_refl _)).
    rewrite (proj1 (proj2 Hulp)) in Hplus; specialize (Hplus (eq_refl _)).
    assert (Px : (0 <= B2R x)%R).
    { now apply Rmult_le_pos; [apply IZR_le|apply bpow_ge_0]. }
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
    * now rewrite (proj1 Hplus).
Qed.

Definition Bpred pred_nan x :=
  Bopp pred_nan (Bsucc pred_nan (Bopp pred_nan x)).

Lemma Bpred_correct :
  forall pred_nan x,
  is_finite x = true ->
  if Rlt_bool (- bpow radix2 emax) (pred radix2 fexp (B2R x)) then
    B2R (Bpred pred_nan x) = pred radix2 fexp (B2R x) /\
    is_finite (Bpred pred_nan x) = true /\
    (Bsign (Bpred pred_nan x) = Bsign x || negb (is_finite_strict x))%bool
  else
    B2FF (Bpred pred_nan x) = F754_infinity true.
Proof.
intros pred_nan x Fx.
assert (Fox : is_finite (Bopp pred_nan x) = true).
{ now rewrite is_finite_Bopp. }
rewrite <-(Ropp_involutive (B2R x)), <-(B2R_Bopp pred_nan).
rewrite pred_opp, Rlt_bool_opp.
generalize (Bsucc_correct pred_nan _ Fox).
case (Rlt_bool _ _).
- intros (HR, (HF, HS)); unfold Bpred.
  rewrite B2R_Bopp, HR, is_finite_Bopp.
  rewrite <-(Bool.negb_involutive (Bsign x)), <-Bool.negb_andb.
  split; [reflexivity|split; [exact HF|]].
  replace (is_finite_strict x) with (is_finite_strict (Bopp pred_nan x));
    [|now case x; try easy; intros s pl Hpl; simpl;
        rewrite is_finite_strict_build_nan].
  rewrite Bsign_Bopp, <-(Bsign_Bopp pred_nan x), HS.
  + now simpl.
  + now revert Fx; case x.
  + now revert HF; case (Bsucc _ _).
- now unfold Bpred; case (Bsucc _ _); intro s; case s.
Qed.

End Binary.

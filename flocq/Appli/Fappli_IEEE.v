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

(** * IEEE-754 arithmetic *)
Require Import Fcore.
Require Import Fcore_digits.
Require Import Fcalc_digits.
Require Import Fcalc_round.
Require Import Fcalc_bracket.
Require Import Fcalc_ops.
Require Import Fcalc_div.
Require Import Fcalc_sqrt.
Require Import Fprop_relative.

Section AnyRadix.

Inductive full_float :=
  | F754_zero : bool -> full_float
  | F754_infinity : bool -> full_float
  | F754_nan : bool -> positive -> full_float
  | F754_finite : bool -> positive -> Z -> full_float.

Definition FF2R beta x :=
  match x with
  | F754_finite s m e => F2R (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => 0%R
  end.

End AnyRadix.

Section Binary.

Arguments exist {A P} x _.

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

Definition canonic_mantissa m e :=
  Zeq_bool (fexp (Zpos (digits2_pos m) + e)) e.

Definition bounded m e :=
  andb (canonic_mantissa m e) (Zle_bool e (emax - prec)).

Definition valid_binary x :=
  match x with
  | F754_finite _ m e => bounded m e
  | F754_nan _ pl => (Zpos (digits2_pos pl) <? prec)%Z
  | _ => true
  end.

(** Basic type used for representing binary FP numbers.
    Note that there is exactly one such object per FP datum. *)

Definition nan_pl := {pl | (Zpos (digits2_pos pl) <? prec)%Z  = true}.

Inductive binary_float :=
  | B754_zero : bool -> binary_float
  | B754_infinity : bool -> binary_float
  | B754_nan : bool -> nan_pl -> binary_float
  | B754_finite : bool ->
    forall (m : positive) (e : Z), bounded m e = true -> binary_float.

Definition FF2B x :=
  match x as x return valid_binary x = true -> binary_float with
  | F754_finite s m e => B754_finite s m e
  | F754_infinity s => fun _ => B754_infinity s
  | F754_zero s => fun _ => B754_zero s
  | F754_nan b pl => fun H => B754_nan b (exist pl H)
  end.

Definition B2FF x :=
  match x with
  | B754_finite s m e _ => F754_finite s m e
  | B754_infinity s => F754_infinity s
  | B754_zero s => F754_zero s
  | B754_nan b (exist pl _) => F754_nan b pl
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
now intros [sx|sx|sx [plx Hplx]|sx mx ex Hx].
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
now intros [sx|sx|sx [plx Hplx]|sx mx ex Hx].
Qed.

Theorem FF2B_B2FF :
  forall x H,
  FF2B (B2FF x) H = x.
Proof.
intros [sx|sx|sx [plx Hplx]|sx mx ex Hx] H ; try easy.
simpl. apply f_equal, f_equal, eqbool_irrelevance.
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
  | B754_nan b (exist p _) => fn b p
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

Theorem canonic_canonic_mantissa :
  forall (sx : bool) mx ex,
  canonic_mantissa mx ex = true ->
  canonic radix2 fexp (Float radix2 (cond_Zopp sx (Zpos mx)) ex).
Proof.
intros sx mx ex H.
assert (Hx := Zeq_bool_eq _ _ H). clear H.
apply sym_eq.
simpl.
pattern ex at 2 ; rewrite <- Hx.
apply (f_equal fexp).
rewrite ln_beta_F2R_Zdigits.
rewrite <- Zdigits_abs.
rewrite Zpos_digits2_pos.
now case sx.
now case sx.
Qed.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof.
intros [sx|sx|sx plx|sx mx ex Hx] ; try apply generic_format_0.
simpl.
apply generic_format_canonic.
apply canonic_canonic_mantissa.
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
intros [sx|sx|sx [plx Hplx]|sx mx ex Hx] [sy|sy|sy [ply Hply]|sy my ey Hy] ; try easy.
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
apply f_equal, f_equal, eqbool_irrelevance.
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
now apply F2R_lt_0_compat.
now apply F2R_gt_0_compat.
apply Rgt_not_eq.
apply Rgt_trans with R0.
now apply F2R_gt_0_compat.
now apply F2R_lt_0_compat.
assert (mx = my /\ ex = ey).
(* *)
refine (_ (canonic_unicity _ fexp _ _ _ _ Heq)).
rewrite Hs.
now case sy ; intro H ; injection H ; split.
apply canonic_canonic_mantissa.
exact (proj1 (andb_prop _ _ Hx)).
apply canonic_canonic_mantissa.
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
  | B754_nan s _ => s
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
  destruct H1. apply (eq_Z2R _ 0) in H1. destruct b0; discriminate H1.
  simpl in H1. pose proof (bpow_gt_0 radix2 e).
  rewrite H1 in H3. apply Rlt_irrefl in H3. destruct H3.
- apply Rmult_integral in H1.
  destruct H1. apply (eq_Z2R _ 0) in H1. destruct b; discriminate H1.
  simpl in H1. pose proof (bpow_gt_0 radix2 e).
  rewrite H1 in H3. apply Rlt_irrefl in H3. destruct H3.
Qed.

Definition is_nan f :=
  match f with
  | B754_nan _ _ => true
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

(** Opposite *)

Definition Bopp opp_nan x :=
  match x with
  | B754_nan sx plx =>
    let '(sres, plres) := opp_nan sx plx in B754_nan sres plres
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
intros opp_nan [sx|sx|sx plx|sx mx ex Hx]; apply sym_eq ; try apply Ropp_0.
simpl. destruct opp_nan. apply Ropp_0.
simpl.
rewrite <- F2R_opp.
now case sx.
Qed.

Theorem is_finite_Bopp :
  forall opp_nan x,
  is_finite (Bopp opp_nan x) = is_finite x.
Proof.
intros opp_nan [| |s pl|] ; try easy.
simpl.
now case opp_nan.
Qed.

(** Absolute value *)

Definition Babs abs_nan (x : binary_float) : binary_float :=
  match x with
  | B754_nan sx plx =>
      let '(sres, plres) := abs_nan sx plx in B754_nan sres plres
  | B754_infinity sx => B754_infinity false
  | B754_finite sx mx ex Hx => B754_finite false mx ex Hx
  | B754_zero sx => B754_zero false
  end.

Theorem B2R_Babs :
  forall abs_nan x,
  B2R (Babs abs_nan x) = Rabs (B2R x).
Proof.
  intros abs_nan [sx|sx|sx plx|sx mx ex Hx]; apply sym_eq ; try apply Rabs_R0.
  simpl. destruct abs_nan. simpl. apply Rabs_R0.
  simpl. rewrite <- F2R_abs. now destruct sx.
Qed.

Theorem is_finite_Babs :
  forall abs_nan x,
  is_finite (Babs abs_nan x) = is_finite x.
Proof.
  intros abs_nan [| |s pl|] ; try easy.
  simpl.
  now case abs_nan.
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
  | B754_nan _ _,_ | _,B754_nan _ _ => None
  | B754_infinity true, B754_infinity true
  | B754_infinity false, B754_infinity false => Some Eq
  | B754_infinity true, _ => Some Lt
  | B754_infinity false, _ => Some Gt
  | _, B754_infinity true => Some Gt
  | _, B754_infinity false => Some Lt
  | B754_finite true _ _ _, B754_zero _ => Some Lt
  | B754_finite false _ _ _, B754_zero _ => Some Gt
  | B754_zero _, B754_finite true _ _ _ => Some Gt
  | B754_zero _, B754_finite false _ _ _ => Some Lt
  | B754_zero _, B754_zero _ => Some Eq
  | B754_finite s1 m1 e1 _, B754_finite s2 m2 e2 _ =>
    match s1, s2 with
    | true, false => Some Lt
    | false, true => Some Gt
    | false, false =>
      match Zcompare e1 e2 with
      | Lt => Some Lt
      | Gt => Some Gt
      | Eq => Some (Pcompare m1 m2 Eq)
      end
    | true, true =>
      match Zcompare e1 e2 with
      | Lt => Some Gt
      | Gt => Some Lt
      | Eq => Some (CompOpp (Pcompare m1 m2 Eq))
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
      | [ |- Some Lt = Some (Rcompare _ _) ] => f_equal; symmetry; apply Rcompare_Lt
      | [ |- Some Eq = Some (Rcompare _ _) ] => f_equal; symmetry; apply Rcompare_Eq
      | [ |- Some Gt = Some (Rcompare _ _) ] => f_equal; symmetry; apply Rcompare_Gt
    end.
  unfold Bcompare; intros.
  destruct f1, f2 ; try easy.
  now rewrite Rcompare_Eq.
  destruct b0 ; apply_Rcompare.
  now apply F2R_lt_0_compat.
  now apply F2R_gt_0_compat.
  destruct b ; apply_Rcompare.
  now apply F2R_lt_0_compat.
  now apply F2R_gt_0_compat.
  simpl.
  clear H H0.
  apply andb_prop in e0; destruct e0; apply (canonic_canonic_mantissa false) in H.
  apply andb_prop in e2; destruct e2; apply (canonic_canonic_mantissa false) in H1.
  pose proof (Zcompare_spec e e1); unfold canonic, Fexp in H1, H.
  assert (forall m1 m2 e1 e2,
    let x := (Z2R (Zpos m1) * bpow radix2 e1)%R in
    let y := (Z2R (Zpos m2) * bpow radix2 e2)%R in
    (canonic_exp radix2 fexp x < canonic_exp radix2 fexp y)%Z -> (x < y)%R).
  {
  intros; apply Rnot_le_lt; intro; apply (ln_beta_le radix2) in H5.
  apply Zlt_not_le with (1 := H4).
  now apply fexp_monotone.
  now apply (F2R_gt_0_compat _ (Float radix2 (Zpos m2) e2)).
  }
  assert (forall m1 m2 e1 e2, (Z2R (- Zpos m1) * bpow radix2 e1 < Z2R (Zpos m2) * bpow radix2 e2)%R).
  {
  intros; apply (Rlt_trans _ 0%R).
  now apply (F2R_lt_0_compat _ (Float radix2 (Zneg m1) e0)).
  now apply (F2R_gt_0_compat _ (Float radix2 (Zpos m2) e2)).
  }
  unfold F2R, Fnum, Fexp.
  destruct b, b0; try (now apply_Rcompare; apply H5); inversion H3;
    try (apply_Rcompare; apply H4; rewrite H, H1 in H7; assumption);
    try (apply_Rcompare; do 2 rewrite Z2R_opp, Ropp_mult_distr_l_reverse;
      apply Ropp_lt_contravar; apply H4; rewrite H, H1 in H7; assumption);
    rewrite H7, Rcompare_mult_r, Rcompare_Z2R by (apply bpow_gt_0); reflexivity.
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

Theorem bounded_lt_emax :
  forall mx ex,
  bounded mx ex = true ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R.
Proof.
intros mx ex Hx.
destruct (andb_prop _ _ Hx) as (H1,H2).
generalize (Zeq_bool_eq _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
generalize (ln_beta_F2R_Zdigits radix2 (Zpos mx) ex).
destruct (ln_beta radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex).
unfold ln_beta_val.
intros H.
apply Rlt_le_trans with (bpow radix2 e').
change (Zpos mx) with (Zabs (Zpos mx)).
rewrite F2R_Zabs.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
apply bpow_le.
rewrite H. 2: discriminate.
revert H1. clear -H2.
rewrite Zpos_digits2_pos.
unfold fexp, FLT_exp.
generalize (Zdigits radix2 (Zpos mx)).
clearbody emin.
intros ; zify ; omega.
Qed.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof.
intros [sx|sx|sx plx|sx mx ex Hx] ; simpl ; try ( rewrite Rabs_R0 ; apply bpow_gt_0 ).
rewrite <- F2R_Zabs, abs_cond_Zopp.
now apply bounded_lt_emax.
Qed.

Theorem bounded_canonic_lt_emax :
  forall mx ex,
  canonic radix2 fexp (Float radix2 (Zpos mx) ex) ->
  (F2R (Float radix2 (Zpos mx) ex) < bpow radix2 emax)%R ->
  bounded mx ex = true.
Proof.
intros mx ex Cx Bx.
apply andb_true_intro.
split.
unfold canonic_mantissa.
unfold canonic, Fexp in Cx.
rewrite Cx at 2.
rewrite Zpos_digits2_pos.
unfold canonic_exp.
rewrite ln_beta_F2R_Zdigits. 2: discriminate.
now apply -> Zeq_is_eq_bool.
apply Zle_bool_true.
unfold canonic, Fexp in Cx.
rewrite Cx.
unfold canonic_exp, fexp, FLT_exp.
destruct (ln_beta radix2 (F2R (Float radix2 (Zpos mx) ex))) as (e',Ex). simpl.
apply Zmax_lub.
cut (e' - 1 < emax)%Z. clear ; omega.
apply lt_bpow with radix2.
apply Rle_lt_trans with (2 := Bx).
change (Zpos mx) with (Zabs (Zpos mx)).
rewrite F2R_Zabs.
apply Ex.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
unfold emin.
generalize (prec_gt_0 prec).
clear -Hmax ; omega.
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
change (Z2R 2) with (bpow radix2 1).
rewrite <- bpow_plus.
rewrite (Zplus_comm 1), <- (F2R_bpow radix2 (e + 1)).
unfold inbetween_float, F2R. simpl.
rewrite Z2R_plus, Rmult_plus_distr_r.
replace (new_location_even 2 (if shr_r (shr_1 mrs) then 1%Z else 0%Z) (loc_of_shr_record mrs)) with (loc_of_shr_record (shr_1 mrs)).
easy.
clear -Hm.
destruct mrs as (m, r, s).
now destruct m as [|[m|m|]|m] ; try (now elim Hm) ; destruct r as [|] ; destruct s as [|].
rewrite (F2R_change_exp radix2 e).
2: apply Zle_succ.
unfold F2R. simpl.
rewrite <- 2!Rmult_plus_distr_r, <- 2!Z2R_plus.
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
unfold Zsucc.
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
clear -Hp ; zify ; omega.
destruct (inbetween_float_ex radix2 m e l) as (x, Hx).
generalize (inbetween_shr x m e l (fexp (Zdigits radix2 m + e) - e) Hm Hx).
assert (Hx0 : (0 <= x)%R).
apply Rle_trans with (F2R (Float radix2 m e)).
now apply F2R_ge_0_compat.
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
  | mode_NE => cond_incr (round_N (negb (Zeven mx)) lx) mx
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
  let '(mrs', e') := shr_fexp (Zpos mx) ex lx in
  let '(mrs'', e'') := shr_fexp (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact in
  match shr_m mrs'' with
  | Z0 => F754_zero sx
  | Zpos m => if Zle_bool e'' (emax - prec) then F754_finite sx m e'' else binary_overflow mode sx
  | _ => F754_nan false xH (* dummy *)
  end.

Theorem binary_round_aux_correct :
  forall mode x mx ex lx,
  inbetween_float radix2 (Zpos mx) ex (Rabs x) lx ->
  (ex <= fexp (Zdigits radix2 (Zpos mx) + ex))%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) mx ex lx in
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
  try apply Zle_refl ;
  match goal with |- (m1 <= if ?b then _ else _)%Z =>
    case b ; [ apply Zle_succ | apply Zle_refl ] end.
assert (Hr: Rabs (round radix2 fexp (round_mode m) x) = F2R (Float radix2 m1' e1)).
(* . *)
rewrite <- (Zabs_eq m1').
replace (Zabs m1') with (Zabs (cond_Zopp (Rlt_bool x 0) m1')).
rewrite F2R_Zabs.
now apply f_equal.
apply abs_cond_Zopp.
apply Zle_trans with (2 := Hm).
apply Zlt_succ_le.
apply F2R_gt_0_reg with radix2 e1.
apply Rle_lt_trans with (1 := Rabs_pos x).
exact (proj2 (inbetween_float_bounds _ _ _ _ _ H1a)).
(* . *)
assert (Br: inbetween_float radix2 m1' e1 (Rabs (round radix2 fexp (round_mode m) x)) loc_Exact).
now apply inbetween_Exact.
destruct m1' as [|m1'|m1'].
(* . m1' = 0 *)
rewrite shr_truncate. 2: apply Zle_refl.
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
rewrite <- ln_beta_F2R_Zdigits, <- Hr, ln_beta_abs.
2: discriminate.
rewrite H1b.
rewrite canonic_exp_abs.
fold (canonic_exp radix2 fexp (round radix2 fexp (round_mode m) x)).
apply canonic_exp_round_ge...
rewrite H1c.
case (Rlt_bool x 0).
apply Rlt_not_eq.
now apply F2R_lt_0_compat.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
refine (_ (truncate_correct_partial _ _ _ _ _ _ _ Br He)).
2: now rewrite Hr ; apply F2R_gt_0_compat.
refine (_ (truncate_correct_format radix2 fexp (Zpos m1') e1 _ _ He)).
2: discriminate.
rewrite shr_truncate. 2: easy.
destruct (truncate radix2 fexp (Zpos m1', e1, loc_Exact)) as ((m2, e2), l2).
rewrite shr_m_shr_record_of_loc.
intros (H3,H4) (H2,_).
destruct m2 as [|m2|m2].
elim Rgt_not_eq with (2 := H3).
rewrite F2R_0.
now apply F2R_gt_0_compat.
rewrite F2R_cond_Zopp, H3, abs_cond_Ropp, <- F2R_abs.
simpl Zabs.
case_eq (Zle_bool e2 (emax - prec)) ; intros He2.
assert (bounded m2 e2 = true).
apply andb_true_intro.
split.
unfold canonic_mantissa.
apply Zeq_bool_true.
rewrite Zpos_digits2_pos.
rewrite <- ln_beta_F2R_Zdigits.
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
clear -Hmax ; zify ; omega.
change 2%Z with (radix_val radix2).
case_eq (Zpower radix2 prec - 1)%Z.
simpl Zdigits.
generalize (Zpower_gt_1 radix2 prec (prec_gt_0 prec)).
clear ; omega.
intros p Hp.
apply Zle_antisym.
cut (prec - 1 < Zdigits radix2 (Zpos p))%Z. clear ; omega.
apply Zdigits_gt_Zpower.
simpl Zabs. rewrite <- Hp.
cut (Zpower radix2 (prec - 1) < Zpower radix2 prec)%Z. clear ; omega.
apply lt_Z2R.
rewrite 2!Z2R_Zpower. 2: now apply Zlt_le_weak.
apply bpow_lt.
apply Zlt_pred.
now apply Zlt_0_le_0_pred.
apply Zdigits_le_Zpower.
simpl Zabs. rewrite <- Hp.
apply Zlt_pred.
intros p Hp.
generalize (Zpower_gt_1 radix2 _ (prec_gt_0 prec)).
clear -Hp ; zify ; omega.
apply Rnot_lt_le.
intros Hx.
generalize (refl_equal (bounded m2 e2)).
unfold bounded at 2.
rewrite He2.
rewrite Bool.andb_false_r.
rewrite bounded_canonic_lt_emax with (2 := Hx).
discriminate.
unfold canonic.
now rewrite <- H3.
elim Rgt_not_eq with (2 := H3).
apply Rlt_trans with R0.
now apply F2R_lt_0_compat.
now apply F2R_gt_0_compat.
rewrite <- Hr.
apply generic_format_abs...
apply generic_format_round...
(* . not m1' < 0 *)
elim Rgt_not_eq with (2 := Hr).
apply Rlt_le_trans with R0.
now apply F2R_lt_0_compat.
apply Rabs_pos.
(* *)
apply Rlt_le_trans with (2 := proj1 (inbetween_float_bounds _ _ _ _ _ Bx)).
now apply F2R_gt_0_compat.
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
  let z := binary_round_aux m (xorb sx sy) (mx * my) (ex + ey) loc_Exact in
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
apply F2R_eq_compat.
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
omega.
(* *)
case sx ; case sy.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
Qed.

Definition Bmult mult_nan m x y :=
  let f pl := B754_nan (fst pl) (snd pl) in
  match x, y with
  | B754_nan _ _, _ | _, B754_nan _ _ => f (mult_nan x y)
  | B754_infinity sx, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity _, B754_zero _ => f (mult_nan x y)
  | B754_zero _, B754_infinity _ => f (mult_nan x y)
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
intros mult_nan m [sx|sx|sx plx|sx mx ex Hx] [sy|sy|sy ply|sy my ey Hy] ;
  try ( rewrite ?Rmult_0_r, ?Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ now repeat constructor | apply bpow_gt_0 | now auto with typeclass_instances ] ).
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

Definition Bmult_FF mult_nan m x y :=
  let f pl := F754_nan (fst pl) (snd pl) in
  match x, y with
  | F754_nan _ _, _ | _, F754_nan _ _ => f (mult_nan x y)
  | F754_infinity sx, F754_infinity sy => F754_infinity (xorb sx sy)
  | F754_infinity sx, F754_finite sy _ _ => F754_infinity (xorb sx sy)
  | F754_finite sx _ _, F754_infinity sy => F754_infinity (xorb sx sy)
  | F754_infinity _, F754_zero _ => f (mult_nan x y)
  | F754_zero _, F754_infinity _ => f (mult_nan x y)
  | F754_finite sx _ _, F754_zero sy => F754_zero (xorb sx sy)
  | F754_zero sx, F754_finite sy _ _ => F754_zero (xorb sx sy)
  | F754_zero sx, F754_zero sy => F754_zero (xorb sx sy)
  | F754_finite sx mx ex, F754_finite sy my ey =>
    binary_round_aux m (xorb sx sy) (mx * my) (ex + ey) loc_Exact
  end.

Theorem B2FF_Bmult :
  forall mult_nan mult_nan_ff,
  forall m x y,
  mult_nan_ff (B2FF x) (B2FF y) = (let '(sr, exist plr _) := mult_nan x y in (sr, plr)) ->
  B2FF (Bmult mult_nan m x y) = Bmult_FF mult_nan_ff m (B2FF x) (B2FF y).
Proof.
intros mult_nan mult_nan_ff m x y Hmult_nan.
unfold Bmult_FF. rewrite Hmult_nan.
destruct x as [sx|sx|sx [plx Hplx]|sx mx ex Hx], y as [sy|sy|sy [ply Hply]|sy my ey Hy] ;
  simpl; try match goal with |- context [mult_nan ?x ?y] =>
               destruct (mult_nan x y) as [? []] end;
  try easy.
apply B2FF_FF2B.
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
apply Zle_refl.
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
change (Zpos d) with (Zopp (Zneg d)).
rewrite <- Hd.
split.
replace (- (ex' - ex))%Z with (ex - ex')%Z by ring.
apply F2R_change_exp.
apply Zle_0_minus_le.
replace (ex - ex')%Z with (- (ex' - ex))%Z by ring.
now rewrite Hd.
apply Zle_refl.
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
clear -He ; zify ; omega.
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
rewrite <- ln_beta_F2R_Zdigits. 2: easy.
rewrite <- H1.
now rewrite ln_beta_F2R_Zdigits.
Qed.

Definition binary_round m sx mx ex :=
  let '(mz, ez) := shl_align_fexp mx ex in binary_round_aux m sx mz ez loc_Exact.

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
now apply F2R_lt_0_compat.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
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
apply F2R_gt_0_compat.
simpl. zify; omega.
intros Hz' (Vz, Rz).
rewrite B2FF_FF2B, Rz.
apply f_equal.
apply sym_eq.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
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
apply F2R_lt_0_compat.
simpl. zify; omega.
intros Hz' (Vz, Rz).
rewrite B2FF_FF2B, Rz.
apply f_equal.
apply sym_eq.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
Qed.

(** Addition *)

Definition Bplus plus_nan m x y :=
  let f pl := B754_nan (fst pl) (snd pl) in
  match x, y with
  | B754_nan _ _, _ | _, B754_nan _ _ => f (plus_nan x y)
  | B754_infinity sx, B754_infinity sy =>
    if Bool.eqb sx sy then x else f (plus_nan x y)
  | B754_infinity _, _ => x
  | _, B754_infinity _ => y
  | B754_zero sx, B754_zero sy =>
    if Bool.eqb sx sy then x else
    match m with mode_DN => B754_zero true | _ => B754_zero false end
  | B754_zero _, _ => y
  | _, B754_zero _ => x
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    let ez := Zmin ex ey in
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
rewrite Rcompare_Z2R with (y:=0%Z).
destruct sy...
apply bpow_gt_0.
apply abs_B2R_lt_emax.
apply generic_format_B2R.
(* *)
rewrite Rplus_0_r, round_generic, Rlt_bool_true...
split... split...
simpl. unfold F2R.
erewrite <- Rmult_0_l, Rcompare_mult_r.
rewrite Rcompare_Z2R with (y:=0%Z).
destruct sx...
apply bpow_gt_0.
apply abs_B2R_lt_emax.
apply generic_format_B2R.
(* *)
clear Fx Fy.
simpl.
set (szero := match m with mode_DN => true | _ => false end).
set (ez := Zmin ex ey).
set (mz := (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))) + cond_Zopp sy (Zpos (fst (shl_align my ey ez))))%Z).
assert (Hp: (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) +
  F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey))%R = F2R (Float radix2 mz ez)).
rewrite 2!F2R_cond_Zopp.
generalize (shl_align_correct mx ex ez).
generalize (shl_align_correct my ey ez).
generalize (snd_shl_align mx ex ez (Zle_min_l ex ey)).
generalize (snd_shl_align my ey ez (Zle_min_r ex ey)).
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
now rewrite <- Rmult_plus_distr_r, <- Z2R_plus.
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
now apply F2R_lt_0_compat.
now apply F2R_lt_0_compat.
apply Rlt_bool_false.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
now apply F2R_ge_0_compat.
now apply F2R_ge_0_compat.
(* .. *)
elim Rle_not_lt with (1 := Bz).
generalize (bounded_lt_emax _ _ Hx) (bounded_lt_emax _ _ Hy) (andb_prop _ _ Hx) (andb_prop _ _ Hy).
intros Bx By (Hx',_) (Hy',_).
generalize (canonic_canonic_mantissa sx _ _ Hx') (canonic_canonic_mantissa sy _ _ Hy').
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
now apply generic_format_canonic.
pattern (F2R (Float radix2 (cond_Zopp true (Zpos mx)) ex)) at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
now apply F2R_ge_0_compat.
apply Rle_lt_trans with (2 := By).
apply round_le_generic...
now apply generic_format_canonic.
rewrite <- (Rplus_0_l (F2R (Float radix2 (Zpos my) ey))).
apply Rplus_le_compat_r.
now apply F2R_le_0_compat.
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
now apply generic_format_canonic.
pattern (F2R (Float radix2 (cond_Zopp true (Zpos my)) ey)) at 1 ; rewrite <- Rplus_0_l.
apply Rplus_le_compat_r.
now apply F2R_ge_0_compat.
apply Rle_lt_trans with (2 := Bx).
apply round_le_generic...
now apply generic_format_canonic.
rewrite <- (Rplus_0_r (F2R (Float radix2 (Zpos mx) ex))).
apply Rplus_le_compat_l.
now apply F2R_le_0_compat.
(* . *)
generalize (binary_normalize_correct m mz ez szero).
case Rlt_bool_spec.
split; try easy. split; try easy.
destruct (Rcompare_spec (F2R (beta:=radix2) {| Fnum := mz; Fexp := ez |}) 0); try easy.
rewrite H1 in Hp.
apply Rplus_opp_r_uniq in Hp.
rewrite <- F2R_Zopp in Hp.
eapply canonic_unicity in Hp.
inversion Hp. destruct sy, sx, m; try discriminate H3; easy.
apply canonic_canonic_mantissa.
apply Bool.andb_true_iff in Hy. easy.
replace (-cond_Zopp sx (Z.pos mx))%Z with  (cond_Zopp (negb sx) (Z.pos mx))
  by (destruct sx; auto).
apply canonic_canonic_mantissa.
apply Bool.andb_true_iff in Hx. easy.
intros Hz' Vz.
specialize (Sz Hz').
split.
rewrite Vz.
now apply f_equal.
apply Sz.
Qed.

(** Subtraction *)

Definition Bminus minus_nan m x y := Bplus minus_nan m x (Bopp pair y).

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
intros m minus_nan x y Fx Fy.
replace (negb (Bsign y)) with (Bsign (Bopp pair y)).
unfold Rminus.
erewrite <- B2R_Bopp.
apply Bplus_correct.
exact Fx.
rewrite is_finite_Bopp. auto. now destruct y as [ | | | ].
Qed.

(** Division *)

Definition Fdiv_core_binary m1 e1 m2 e2 :=
  let d1 := Zdigits2 m1 in
  let d2 := Zdigits2 m2 in
  let e := (e1 - e2)%Z in
  let (m, e') :=
    match (d2 + prec - d1)%Z with
    | Zpos p => (Z.shiftl m1 (Zpos p), e + Zneg p)%Z
    | _ => (m1, e)
    end in
  let '(q, r) :=  Zfast_div_eucl m m2 in
  (q, e', new_location m2 r loc_Exact).

Lemma Bdiv_correct_aux :
  forall m sx mx ex sy my ey,
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  let z :=
    let '(mz, ez, lz) := Fdiv_core_binary (Zpos mx) ex (Zpos my) ey in
    match mz with
    | Zpos mz => binary_round_aux m (xorb sx sy) mz ez lz
    | _ => F754_nan false xH (* dummy *)
    end in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (x / y))) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode m) (x / y) /\
    is_finite_FF z = true /\ sign_FF z = xorb sx sy
  else
    z = binary_overflow m (xorb sx sy).
Proof.
intros m sx mx ex sy my ey.
replace (Fdiv_core_binary (Zpos mx) ex (Zpos my) ey) with (Fdiv_core radix2 prec (Zpos mx) ex (Zpos my) ey).
refine (_ (Fdiv_core_correct radix2 prec (Zpos mx) ex (Zpos my) ey _ _ _)) ; try easy.
destruct (Fdiv_core radix2 prec (Zpos mx) ex (Zpos my) ey) as ((mz, ez), lz).
intros (Pz, Bz).
simpl.
replace (xorb sx sy) with (Rlt_bool (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) *
  / F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey)) 0).
unfold Rdiv.
destruct mz as [|mz|mz].
(* . mz = 0 *)
elim (Zlt_irrefl prec).
now apply Zle_lt_trans with Z0.
(* . mz > 0 *)
apply binary_round_aux_correct.
rewrite Rabs_mult, Rabs_Rinv.
now rewrite <- 2!F2R_Zabs, 2!abs_cond_Zopp.
case sy.
apply Rlt_not_eq.
now apply F2R_lt_0_compat.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
revert Pz.
generalize (Zdigits radix2 (Zpos mz)).
unfold fexp, FLT_exp.
clear.
intros ; zify ; subst.
omega.
(* . mz < 0 *)
elim Rlt_not_le with (1 := proj2 (inbetween_float_bounds _ _ _ _ _ Bz)).
apply Rle_trans with R0.
apply F2R_le_0_compat.
now case mz.
apply Rmult_le_pos.
now apply F2R_ge_0_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
(* *)
case sy ; simpl.
change (Zneg my) with (Zopp (Zpos my)).
rewrite F2R_Zopp.
rewrite <- Ropp_inv_permute.
rewrite Ropp_mult_distr_r_reverse.
case sx ; simpl.
apply Rlt_bool_false.
rewrite <- Ropp_mult_distr_l_reverse.
apply Rmult_le_pos.
rewrite <- F2R_opp.
now apply F2R_ge_0_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
apply Rlt_bool_true.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
now apply F2R_gt_0_compat.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
case sx.
apply Rlt_bool_true.
rewrite F2R_Zopp.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
now apply F2R_gt_0_compat.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
apply Rlt_bool_false.
apply Rmult_le_pos.
now apply F2R_ge_0_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply F2R_gt_0_compat.
(* *)
unfold Fdiv_core_binary, Fdiv_core.
rewrite 2!Zdigits2_Zdigits.
change 2%Z with (radix_val radix2).
destruct (Zdigits radix2 (Z.pos my) + prec - Zdigits radix2 (Z.pos mx))%Z as [|p|p].
now rewrite Zfast_div_eucl_correct.
rewrite Z.shiftl_mul_pow2 by easy.
now rewrite Zfast_div_eucl_correct.
now rewrite Zfast_div_eucl_correct.
Qed.

Definition Bdiv div_nan m x y :=
  let f pl := B754_nan (fst pl) (snd pl) in
  match x, y with
  | B754_nan _ _, _ | _, B754_nan _ _ => f (div_nan x y)
  | B754_infinity sx, B754_infinity sy => f (div_nan x y)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_infinity sx, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_finite sx _ _ _, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => f (div_nan x y)
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
intros [sx|sx|sx plx|sx mx ex Hx] ;
  try ( rewrite Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ now repeat constructor | apply bpow_gt_0 | auto with typeclass_instances ] ).
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
  let s := Zmax (2 * prec - d) 0 in
  let e' := (e - s)%Z in
  let (s', e'') := if Zeven e' then (s, e') else (s + 1, e' - 1)%Z in
  let m' :=
    match s' with
    | Zpos p => Z.shiftl m (Zpos p)
    | _ => m
    end in
  let (q, r) := Z.sqrtrem m' in
  let l :=
    if Zeq_bool r 0 then loc_Exact
    else loc_Inexact (if Zle_bool r q then Lt else Gt) in
  (q, Zdiv2 e'', l).

Lemma Bsqrt_correct_aux :
  forall m mx ex (Hx : bounded mx ex = true),
  let x := F2R (Float radix2 (Zpos mx) ex) in
  let z :=
    let '(mz, ez, lz) := Fsqrt_core_binary (Zpos mx) ex in
    match mz with
    | Zpos mz => binary_round_aux m false mz ez lz
    | _ => F754_nan false xH (* dummy *)
    end in
  valid_binary z = true /\
  FF2R radix2 z = round radix2 fexp (round_mode m) (sqrt x) /\
  is_finite_FF z = true /\ sign_FF z = false.
Proof with auto with typeclass_instances.
intros m mx ex Hx.
replace (Fsqrt_core_binary (Zpos mx) ex) with (Fsqrt_core radix2 prec (Zpos mx) ex).
simpl.
refine (_ (Fsqrt_core_correct radix2 prec (Zpos mx) ex _)) ; try easy.
destruct (Fsqrt_core radix2 prec (Zpos mx) ex) as ((mz, ez), lz).
intros (Pz, Bz).
destruct mz as [|mz|mz].
(* . mz = 0 *)
elim (Zlt_irrefl prec).
now apply Zle_lt_trans with Z0.
(* . mz > 0 *)
refine (_ (binary_round_aux_correct m (sqrt (F2R (Float radix2 (Zpos mx) ex))) mz ez lz _ _)).
rewrite Rlt_bool_false. 2: apply sqrt_ge_0.
rewrite Rlt_bool_true.
easy.
(* .. *)
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
clear ; omega.
apply Rsqr_incrst_0.
3: apply bpow_ge_0.
rewrite Rsqr_mult.
rewrite Rsqr_sqrt.
2: now apply F2R_ge_0_compat.
unfold Rsqr.
apply Rmult_ge_0_gt_0_lt_compat.
apply Rle_ge.
apply Rle_0_sqr.
apply bpow_gt_0.
now apply bounded_lt_emax.
apply Rlt_le_trans with 4%R.
apply Rsqr_incrst_1.
apply Rplus_lt_compat_l.
apply (Rabs_lt_inv _ _ Heps').
rewrite <- (Rplus_opp_r 1).
apply Rplus_le_compat_l.
apply Rlt_le.
apply (Rabs_lt_inv _ _ Heps').
now apply (Z2R_le 0 2).
change 4%R with (bpow radix2 2).
apply bpow_le.
generalize (prec_gt_0 prec).
clear -Hmax ; omega.
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
2: now apply F2R_ge_0_compat.
apply Rle_trans with (bpow radix2 emin).
unfold Rsqr.
rewrite <- bpow_plus.
apply bpow_le.
unfold emin.
clear -Hmax ; omega.
apply generic_format_ge_bpow with fexp.
intros.
apply Zle_max_r.
now apply F2R_gt_0_compat.
apply generic_format_canonic.
apply (canonic_canonic_mantissa false).
apply (andb_prop _ _ Hx).
(* .. *)
apply round_ge_generic...
apply generic_format_0.
apply sqrt_ge_0.
rewrite Rabs_pos_eq.
exact Bz.
apply sqrt_ge_0.
revert Pz.
generalize (Zdigits radix2 (Zpos mz)).
unfold fexp, FLT_exp.
clear.
intros ; zify ; subst.
omega.
(* . mz < 0 *)
elim Rlt_not_le  with (1 := proj2 (inbetween_float_bounds _ _ _ _ _ Bz)).
apply Rle_trans with R0.
apply F2R_le_0_compat.
now case mz.
apply sqrt_ge_0.
(* *)
unfold Fsqrt_core, Fsqrt_core_binary.
rewrite Zdigits2_Zdigits.
destruct (if Zeven _ then _ else _) as [[|s'|s'] e''] ; try easy.
now rewrite Z.shiftl_mul_pow2.
Qed.

Definition Bsqrt sqrt_nan m x :=
  let f pl := B754_nan (fst pl) (snd pl) in
  match x with
  | B754_nan sx plx => f (sqrt_nan x)
  | B754_infinity false => x
  | B754_infinity true => f (sqrt_nan x)
  | B754_finite true _ _ _ => f (sqrt_nan x)
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
intros sqrt_nan m [sx|[|]| |sx mx ex Hx] ; try ( now simpl ; rewrite sqrt_0, round_0 ; intuition auto with typeclass_instances ).
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
now apply F2R_lt_0_compat.
easy.
split.
now rewrite B2R_FF2B.
split.
now rewrite is_finite_FF2B.
intro. rewrite Bsign_FF2B. auto.
Qed.

End Binary.

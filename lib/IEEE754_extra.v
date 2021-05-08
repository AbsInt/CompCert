(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Additional operations and proofs about IEEE-754 binary
    floating-point numbers, on top of the Flocq library. *)

From Flocq Require Import Core Digits Operations Round Bracket Sterbenz
                          Binary Round_odd.
Require Import Psatz.
Require Import Bool.
Require Import Eqdep_dec.

Local Open Scope Z_scope.

Section Extra_ops.

(** [prec] is the number of bits of the mantissa including the implicit one.
    [emax] is the exponent of the infinities.
    Typically p=24 and emax = 128 in single precision. *)

Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.
Hypothesis Hmax : (prec < emax)%Z.
Let binary_float := binary_float prec emax.

(** Remarks on [is_finite] *)

Remark is_finite_not_is_nan:
  forall (f: binary_float), is_finite _ _ f = true -> is_nan _ _ f = false.
Proof.
  destruct f; reflexivity || discriminate.
Qed.

Remark is_finite_strict_finite:
  forall (f: binary_float), is_finite_strict _ _ f = true -> is_finite _ _ f = true.
Proof.
  destruct f; reflexivity || discriminate.
Qed.

(** Digression on FP numbers that cannot be [-0.0]. *)

Definition is_finite_pos0 (f: binary_float) : bool :=
  match f with
  | B754_zero _ _ s => negb s
  | B754_infinity _ _ _ => false
  | B754_nan _ _ _ _ _ => false
  | B754_finite _ _ _ _ _ _ => true
  end.

Lemma Bsign_pos0:
  forall x, is_finite_pos0 x = true -> Bsign _ _ x = Rlt_bool (B2R _ _ x) 0%R.
Proof.
  intros. destruct x as [ [] | | | [] ex mx Bx ]; try discriminate; simpl.
- rewrite Rlt_bool_false; auto. lra.
- rewrite Rlt_bool_true; auto. apply F2R_lt_0. compute; auto.
- rewrite Rlt_bool_false; auto.
  assert ((F2R (Float radix2 (Z.pos ex) mx) > 0)%R) by
    ( apply F2R_gt_0; compute; auto ).
  lra.
Qed.

Theorem B2R_inj_pos0:
  forall x y,
  is_finite_pos0 x = true -> is_finite_pos0 y = true ->
  B2R _ _ x = B2R _ _ y ->
  x = y.
Proof.
  intros. apply B2R_Bsign_inj.
  destruct x; reflexivity||discriminate.
  destruct y; reflexivity||discriminate.
  auto.
  rewrite ! Bsign_pos0 by auto. rewrite H1; auto.
Qed.

(** ** Decidable equality *)

Definition Beq_dec: forall (f1 f2: binary_float), {f1 = f2} + {f1 <> f2}.
Proof.
  assert (UIP_bool: forall (b1 b2: bool) (e e': b1 = b2), e = e').
  { intros. apply UIP_dec. decide equality. }
  Ltac try_not_eq := try solve [right; congruence].
  destruct f1 as [s1|s1|s1 p1 H1|s1 m1 e1 H1], f2 as [s2|s2|s2 p2 H2|s2 m2 e2 H2];
  try destruct s1; try destruct s2;
  try solve [left; auto]; try_not_eq.
  destruct (Pos.eq_dec p1 p2); try_not_eq;
    subst; left; f_equal; f_equal; apply UIP_bool.
  destruct (Pos.eq_dec p1 p2); try_not_eq;
    subst; left; f_equal; f_equal; apply UIP_bool.
  destruct (Pos.eq_dec m1 m2); try_not_eq;
  destruct (Z.eq_dec e1 e2); try solve [right; intro H; inversion H; congruence];
  subst; left; f_equal; apply UIP_bool.
  destruct (Pos.eq_dec m1 m2); try_not_eq;
  destruct (Z.eq_dec e1 e2); try solve [right; intro H; inversion H; congruence];
  subst; left; f_equal; apply UIP_bool.
Defined.

(** ** Conversion from an integer to a FP number *)

(** Integers that can be represented exactly as FP numbers. *)

Definition integer_representable (n: Z): Prop :=
  Z.abs n <= 2^emax - 2^(emax - prec) /\ generic_format radix2 fexp (IZR n).

Let int_upper_bound_eq: 2^emax - 2^(emax - prec) = (2^prec - 1) * 2^(emax - prec).
Proof.
  red in prec_gt_0_.
  ring_simplify. rewrite <- (Zpower_plus radix2) by lia. f_equal. f_equal. lia.
Qed.

Lemma integer_representable_n2p:
  forall n p,
  -2^prec < n < 2^prec -> 0 <= p -> p <= emax - prec ->
  integer_representable (n * 2^p).
Proof.
  intros; split.
- red in prec_gt_0_. replace (Z.abs (n * 2^p)) with (Z.abs n * 2^p).
  rewrite int_upper_bound_eq.
  apply Zmult_le_compat. zify; lia. apply (Zpower_le radix2); lia.
  zify; lia. apply (Zpower_ge_0 radix2).
  rewrite Z.abs_mul. f_equal. rewrite Z.abs_eq. auto. apply (Zpower_ge_0 radix2).
- apply generic_format_FLT. exists (Float radix2 n p).
  unfold F2R; simpl.
  rewrite <- IZR_Zpower by auto. apply mult_IZR.
  simpl; zify; lia.
  unfold emin, Fexp; red in prec_gt_0_; lia.
Qed.

Lemma integer_representable_2p:
  forall p,
  0 <= p <= emax - 1 ->
  integer_representable (2^p).
Proof.
  intros; split.
- red in prec_gt_0_.
  rewrite Z.abs_eq by (apply (Zpower_ge_0 radix2)).
  apply Z.le_trans with (2^(emax-1)).
  apply (Zpower_le radix2); lia.
  assert (2^emax = 2^(emax-1)*2).
  { change 2 with (2^1) at 3. rewrite <- (Zpower_plus radix2) by lia.
    f_equal. lia. }
  assert (2^(emax - prec) <= 2^(emax - 1)).
  { apply (Zpower_le radix2). lia. }
  lia.
- red in prec_gt_0_.
  apply generic_format_FLT. exists (Float radix2 1 p).
  unfold F2R; simpl.
  rewrite Rmult_1_l. rewrite <- IZR_Zpower. auto. lia.
  simpl Z.abs. change 1 with (2^0). apply (Zpower_lt radix2). lia. auto.
  unfold emin, Fexp; lia.
Qed.

Lemma integer_representable_opp:
  forall n, integer_representable n -> integer_representable (-n).
Proof.
  intros n (A & B); split. rewrite Z.abs_opp. auto.
  rewrite opp_IZR. apply generic_format_opp; auto.
Qed.

Lemma integer_representable_n2p_wide:
  forall n p,
  -2^prec <= n <= 2^prec -> 0 <= p -> p < emax - prec ->
  integer_representable (n * 2^p).
Proof.
  intros. red in prec_gt_0_.
  destruct (Z.eq_dec n (2^prec)); [idtac | destruct (Z.eq_dec n (-2^prec))].
- rewrite e. rewrite <- (Zpower_plus radix2) by lia.
  apply integer_representable_2p. lia.
- rewrite e. rewrite <- Zopp_mult_distr_l. apply integer_representable_opp.
  rewrite <- (Zpower_plus radix2) by lia.
  apply integer_representable_2p. lia.
- apply integer_representable_n2p; lia.
Qed.

Lemma integer_representable_n:
  forall n, -2^prec <= n <= 2^prec -> integer_representable n.
Proof.
  red in prec_gt_0_. intros.
  replace n with (n * 2^0) by (change (2^0) with 1; ring).
  apply integer_representable_n2p_wide. auto. lia. lia.
Qed.

Lemma round_int_no_overflow:
  forall n,
  Z.abs n <= 2^emax - 2^(emax-prec) ->
  (Rabs (round radix2 fexp (round_mode mode_NE) (IZR n)) < bpow radix2 emax)%R.
Proof.
  intros. red in prec_gt_0_.
  rewrite <- round_NE_abs.
  apply Rle_lt_trans with (IZR (2^emax - 2^(emax-prec))).
  apply round_le_generic. apply fexp_correct; auto. apply valid_rnd_N.
  apply generic_format_FLT. exists (Float radix2 (2^prec-1) (emax-prec)).
  rewrite int_upper_bound_eq. unfold F2R; simpl.
  rewrite <- IZR_Zpower by lia. rewrite <- mult_IZR. auto.
  assert (0 < 2^prec) by (apply (Zpower_gt_0 radix2); lia).
  unfold Fnum; simpl; zify; lia.
  unfold emin, Fexp; lia.
  rewrite <- abs_IZR. apply IZR_le. auto.
  rewrite <- IZR_Zpower by lia. apply IZR_lt. simpl.
  assert (0 < 2^(emax-prec)) by (apply (Zpower_gt_0 radix2); lia).
  lia.
  apply fexp_correct. auto.
Qed.

(** Conversion from an integer.  Round to nearest. *)

Definition BofZ (n: Z) : binary_float :=
  binary_normalize prec emax prec_gt_0_ Hmax mode_NE n 0 false.

Theorem BofZ_correct:
  forall n,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode_NE) (IZR n))) (bpow radix2 emax)
  then
    B2R prec emax (BofZ n) = round radix2 fexp (round_mode mode_NE) (IZR n) /\
    is_finite _ _ (BofZ n) = true /\
    Bsign prec emax (BofZ n) = Z.ltb n 0
  else
    B2FF prec emax (BofZ n) = binary_overflow prec emax mode_NE (Z.ltb n 0).
Proof.
  intros.
  generalize (binary_normalize_correct prec emax prec_gt_0_ Hmax mode_NE n 0 false).
  fold emin; fold fexp; fold (BofZ n).
  replace (F2R {| Fnum := n; Fexp := 0 |}) with (IZR n).
  destruct Rlt_bool.
- intros (A & B & C). split; [|split].
  + auto.
  + auto.
  + rewrite C. rewrite Rcompare_IZR.
    unfold Z.ltb. auto.
- intros A; rewrite A. f_equal.
  generalize (Z.ltb_spec n 0); intros SPEC; inversion SPEC.
  apply Rlt_bool_true; apply IZR_lt; auto.
  apply Rlt_bool_false; apply IZR_le; auto.
- unfold F2R; simpl. ring.
Qed.

Theorem BofZ_finite:
  forall n,
  Z.abs n <= 2^emax - 2^(emax-prec) ->
  B2R _ _ (BofZ n) = round radix2 fexp (round_mode mode_NE) (IZR n)
  /\ is_finite _ _ (BofZ n) = true
  /\ Bsign _ _ (BofZ n) = Z.ltb n 0%Z.
Proof.
  intros.
  generalize (BofZ_correct n). rewrite Rlt_bool_true. auto.
  apply round_int_no_overflow; auto.
Qed.

Theorem BofZ_representable:
  forall n,
  integer_representable n ->
  B2R _ _ (BofZ n) = IZR n
  /\ is_finite _ _ (BofZ n) = true
  /\ Bsign _ _ (BofZ n) = (n <? 0).
Proof.
  intros. destruct H as (P & Q). destruct (BofZ_finite n) as (A & B & C). auto.
  intuition. rewrite A. apply round_generic. apply valid_rnd_round_mode. auto.
Qed.

Theorem BofZ_exact:
  forall n,
  -2^prec <= n <= 2^prec ->
  B2R _ _ (BofZ n) = IZR n
  /\ is_finite _ _ (BofZ n) = true
  /\ Bsign _ _ (BofZ n) = Z.ltb n 0%Z.
Proof.
  intros. apply BofZ_representable. apply integer_representable_n; auto.
Qed.

Lemma BofZ_finite_pos0:
  forall n,
  Z.abs n <= 2^emax - 2^(emax-prec) -> is_finite_pos0 (BofZ n) = true.
Proof.
  intros.
  generalize (binary_normalize_correct prec emax prec_gt_0_ Hmax mode_NE n 0 false).
  fold emin; fold fexp; fold (BofZ n).
  replace (F2R {| Fnum := n; Fexp := 0 |}) with (IZR n) by
    (unfold F2R; simpl; ring).
  rewrite Rlt_bool_true by (apply round_int_no_overflow; auto).
  intros (A & B & C).
  destruct (BofZ n); auto; try discriminate.
  simpl in *. rewrite C. rewrite Rcompare_IZR.
  generalize (Zcompare_spec n 0); intros SPEC; inversion SPEC; auto.
  assert ((round radix2 fexp ZnearestE (IZR n) <= -1)%R).
  { apply round_le_generic. apply fexp_correct. auto. apply valid_rnd_N.
    apply (integer_representable_opp 1).
    apply (integer_representable_2p 0).
    red in prec_gt_0_; lia.
    apply IZR_le; lia.
  }
  lra.
Qed.

Lemma BofZ_finite_equal:
  forall x y,
  Z.abs x <= 2^emax - 2^(emax-prec) ->
  Z.abs y <= 2^emax - 2^(emax-prec) ->
  B2R _ _ (BofZ x) = B2R _ _ (BofZ y) ->
  BofZ x = BofZ y.
Proof.
  intros. apply B2R_inj_pos0; auto; apply BofZ_finite_pos0; auto.
Qed.

(** Commutation properties with addition, subtraction, multiplication. *)

Theorem BofZ_plus:
  forall nan p q,
  integer_representable p -> integer_representable q ->
  Bplus _ _ _ Hmax nan mode_NE (BofZ p) (BofZ q) = BofZ (p + q).
Proof.
  intros.
  destruct (BofZ_representable p) as (A & B & C); auto.
  destruct (BofZ_representable q) as (D & E & F); auto.
  generalize (Bplus_correct _ _ _ Hmax nan mode_NE (BofZ p) (BofZ q) B E).
  fold emin; fold fexp.
  rewrite A, D. rewrite <- plus_IZR.
  generalize (BofZ_correct (p + q)). destruct Rlt_bool.
- intros (P & Q & R) (U & V & W).
  apply B2R_Bsign_inj; auto.
  rewrite P, U; auto.
  rewrite R, W, C, F.
  rewrite Rcompare_IZR. unfold Z.ltb at 3.
  generalize (Zcompare_spec (p + q) 0); intros SPEC; inversion SPEC; auto.
  assert (EITHER: 0 <= p \/ 0 <= q) by lia.
  destruct EITHER; [apply andb_false_intro1 | apply andb_false_intro2];
  apply Zlt_bool_false; auto.
- intros P (U & V).
  apply B2FF_inj.
  rewrite P, U, C. f_equal. rewrite C, F in V.
  generalize (Zlt_bool_spec p 0) (Zlt_bool_spec q 0). rewrite <- V.
  intros SPEC1 SPEC2; inversion SPEC1; inversion SPEC2; try congruence; symmetry.
  apply Zlt_bool_true; lia.
  apply Zlt_bool_false; lia.
Qed.

Theorem BofZ_minus:
  forall nan p q,
  integer_representable p -> integer_representable q ->
  Bminus _ _ _ Hmax nan mode_NE (BofZ p) (BofZ q) = BofZ (p - q).
Proof.
  intros.
  destruct (BofZ_representable p) as (A & B & C); auto.
  destruct (BofZ_representable q) as (D & E & F); auto.
  generalize (Bminus_correct _ _ _ Hmax nan mode_NE (BofZ p) (BofZ q) B E).
  fold emin; fold fexp.
  rewrite A, D. rewrite <- minus_IZR.
  generalize (BofZ_correct (p - q)). destruct Rlt_bool.
- intros (P & Q & R) (U & V & W).
  apply B2R_Bsign_inj; auto.
  rewrite P, U; auto.
  rewrite R, W, C, F.
  rewrite Rcompare_IZR. unfold Z.ltb at 3.
  generalize (Zcompare_spec (p - q) 0); intros SPEC; inversion SPEC; auto.
  assert (EITHER: 0 <= p \/ q < 0) by lia.
  destruct EITHER; [apply andb_false_intro1 | apply andb_false_intro2].
  rewrite Zlt_bool_false; auto.
  rewrite Zlt_bool_true; auto.
- intros P (U & V).
  apply B2FF_inj.
  rewrite P, U, C. f_equal. rewrite C, F in V.
  generalize (Zlt_bool_spec p 0) (Zlt_bool_spec q 0). rewrite V.
  intros SPEC1 SPEC2; inversion SPEC1; inversion SPEC2; symmetry.
  rewrite <- H3 in H1; discriminate.
  apply Zlt_bool_true; lia.
  apply Zlt_bool_false; lia.
  rewrite <- H3 in H1; discriminate.
Qed.

Theorem BofZ_mult:
  forall nan p q,
  integer_representable p -> integer_representable q ->
  0 < q ->
  Bmult _ _ _ Hmax nan mode_NE (BofZ p) (BofZ q) = BofZ (p * q).
Proof.
  intros.
  assert (SIGN: xorb (p <? 0) (q <? 0) = (p * q <? 0)).
  {
    rewrite (Zlt_bool_false q) by lia.
    generalize (Zlt_bool_spec p 0); intros SPEC; inversion SPEC; simpl; symmetry.
    apply Zlt_bool_true. rewrite Z.mul_comm. apply Z.mul_pos_neg; lia.
    apply Zlt_bool_false. apply Zsame_sign_imp; lia.
  }
  destruct (BofZ_representable p) as (A & B & C); auto.
  destruct (BofZ_representable q) as (D & E & F); auto.
  generalize (Bmult_correct _ _ _ Hmax nan mode_NE (BofZ p) (BofZ q)).
  fold emin; fold fexp.
  rewrite A, B, C, D, E, F. rewrite <- mult_IZR.
  generalize (BofZ_correct (p * q)). destruct Rlt_bool.
- intros (P & Q & R) (U & V & W).
  apply B2R_Bsign_inj; auto.
  rewrite P, U; auto.
  rewrite R, W; auto.
  apply is_finite_not_is_nan; auto.
- intros P U.
  apply B2FF_inj. rewrite P, U. f_equal. auto.
Qed.

Theorem BofZ_mult_2p:
  forall nan x p,
  Z.abs x <= 2^emax - 2^(emax-prec) ->
  2^prec <= Z.abs x ->
  0 <= p <= emax - 1 ->
  Bmult _ _ _ Hmax nan mode_NE (BofZ x) (BofZ (2^p)) = BofZ (x * 2^p).
Proof.
  intros.
  destruct (Z.eq_dec x 0).
- subst x. apply BofZ_mult.
    apply integer_representable_n.
    generalize (Zpower_ge_0 radix2 prec). simpl; lia.
    apply integer_representable_2p. auto.
    apply (Zpower_gt_0 radix2).
    lia.
- assert (IZR x <> 0%R) by (apply (IZR_neq _ _ n)).
  destruct (BofZ_finite x H) as (A & B & C).
  destruct (BofZ_representable (2^p)) as (D & E & F).
    apply integer_representable_2p. auto.
  assert (cexp radix2 fexp (IZR (x * 2^p)) =
          cexp radix2 fexp (IZR x) + p).
  {
    unfold cexp, fexp. rewrite mult_IZR.
    change (2^p) with (radix2^p). rewrite IZR_Zpower by lia.
    rewrite mag_mult_bpow by auto.
    assert (prec + 1 <= mag radix2 (IZR x)).
    { rewrite <- (mag_abs radix2 (IZR x)).
      rewrite <- (mag_bpow radix2 prec).
      apply mag_le.
      apply bpow_gt_0. rewrite <- IZR_Zpower by (red in prec_gt_0_;lia).
      rewrite <- abs_IZR. apply IZR_le; auto. }
    unfold FLT_exp.
    unfold emin; red in prec_gt_0_; zify; lia.
  }
  assert (forall m, round radix2 fexp m (IZR x) * IZR (2^p) =
                    round radix2 fexp m (IZR (x * 2^p)))%R.
  {
    intros. unfold round, scaled_mantissa. rewrite H3.
    rewrite mult_IZR. rewrite Z.opp_add_distr. rewrite bpow_plus.
    set (a := IZR x); set (b := bpow radix2 (- cexp radix2 fexp a)).
    replace (a * IZR (2^p) * (b * bpow radix2 (-p)))%R with (a * b)%R.
    unfold F2R; simpl. rewrite Rmult_assoc. f_equal.
    rewrite bpow_plus.  f_equal. apply (IZR_Zpower radix2). lia.
    transitivity ((a * b) * (IZR (2^p) * bpow radix2 (-p)))%R.
    rewrite (IZR_Zpower radix2). rewrite <- bpow_plus.
    replace (p + -p) with 0 by lia. change (bpow radix2 0) with 1%R. ring.
    lia.
    ring.
  }
  assert (forall m x,
    round radix2 fexp (round_mode m) (round radix2 fexp (round_mode m) x) =
    round radix2 fexp (round_mode m) x).
  {
    intros. apply round_generic. apply valid_rnd_round_mode.
    apply generic_format_round.  apply fexp_correct; auto.
    apply valid_rnd_round_mode.
  }
  assert (xorb (x <? 0) (2^p <? 0) = (x * 2^p <? 0)).
  {
    assert (0 < 2^p) by (apply (Zpower_gt_0 radix2); lia).
    rewrite (Zlt_bool_false (2^p)) by lia. rewrite xorb_false_r.
    symmetry. generalize (Zlt_bool_spec x 0); intros SPEC; inversion SPEC.
    apply Zlt_bool_true. apply Z.mul_neg_pos; auto.
    apply Zlt_bool_false. apply Z.mul_nonneg_nonneg; lia.
  }
  generalize (Bmult_correct _ _ _ Hmax nan mode_NE (BofZ x) (BofZ (2^p)))
             (BofZ_correct (x * 2^p)).
  fold emin; fold fexp. rewrite A, B, C, D, E, F, H4, H5.
  destruct Rlt_bool.
+ intros (P & Q & R) (U & V & W).
  apply B2R_Bsign_inj; auto.
  rewrite P, U. auto.
  rewrite R, W. auto.
  apply is_finite_not_is_nan; auto.
+ intros P U.
  apply B2FF_inj. rewrite P, U. f_equal; auto.
Qed.

(** Rounding to odd the argument of [BofZ]. *)

Lemma round_odd_flt:
  forall prec' emin' x choice,
  prec > 1 -> prec' > 1 -> prec' >= prec + 2 -> emin' <= emin - 2 ->
  round radix2 fexp (Znearest choice) (round radix2 (FLT_exp emin' prec') Zrnd_odd x) =
  round radix2 fexp (Znearest choice) x.
Proof.
  intros. apply round_N_odd. auto. apply fexp_correct; auto.
  apply exists_NE_FLT. right; lia.
  apply FLT_exp_valid. red; lia.
  apply exists_NE_FLT. right; lia.
  unfold fexp, FLT_exp; intros. zify; lia.
Qed.

Corollary round_odd_fix:
  forall x p choice,
  prec > 1 ->
  0 <= p ->
  (bpow radix2 (prec + p + 1) <= Rabs x)%R ->
  round radix2 fexp (Znearest choice) (round radix2 (FIX_exp p) Zrnd_odd x) =
  round radix2 fexp (Znearest choice) x.
Proof.
  intros. destruct (Req_EM_T x 0%R).
- subst x. rewrite round_0. auto. apply valid_rnd_odd.
- set (prec' := mag radix2 x - p).
  set (emin' := emin - 2).
  assert (PREC: mag radix2 (bpow radix2 (prec + p + 1)) <= mag radix2 x).
  { rewrite <- (mag_abs radix2 x).
    apply mag_le; auto. apply bpow_gt_0. }
  rewrite mag_bpow in PREC.
  assert (CANON: cexp radix2 (FLT_exp emin' prec') x =
                 cexp radix2 (FIX_exp p) x).
  {
    unfold cexp, FLT_exp, FIX_exp.
    replace (mag radix2 x - prec') with p by (unfold prec'; lia).
    apply Z.max_l. unfold emin', emin. red in prec_gt_0_; lia.
  }
  assert (RND: round radix2 (FIX_exp p) Zrnd_odd x =
               round radix2 (FLT_exp emin' prec') Zrnd_odd x).
  {
    unfold round, scaled_mantissa. rewrite CANON. auto.
  }
  rewrite RND.
  apply round_odd_flt. auto.
  unfold prec'. red in prec_gt_0_; lia.
  unfold prec'. lia.
  unfold emin'. lia.
Qed.

Definition int_round_odd (x: Z) (p: Z) :=
  (if Z.eqb (x mod 2^p) 0 || Z.odd (x / 2^p) then x / 2^p else x / 2^p + 1) * 2^p.

Lemma Zrnd_odd_int:
  forall n p, 0 <= p ->
  Zrnd_odd (IZR n * bpow radix2 (-p)) * 2^p =
  int_round_odd n p.
Proof.
  clear. intros.
  assert (0 < 2^p) by (apply (Zpower_gt_0 radix2); lia).
  assert (n = (n / 2^p) * 2^p + n mod 2^p) by (rewrite Z.mul_comm; apply Z.div_mod; lia).
  assert (0 <= n mod 2^p < 2^p) by (apply Z_mod_lt; lia).
  unfold int_round_odd. set (q := n / 2^p) in *; set (r := n mod 2^p) in *.
  f_equal.
  pose proof (bpow_gt_0 radix2 (-p)).
  assert (bpow radix2 p * bpow radix2 (-p) = 1)%R.
  { rewrite <- bpow_plus. replace (p + -p) with 0 by lia. auto. }
  assert (IZR n * bpow radix2 (-p) = IZR q + IZR r * bpow radix2 (-p))%R.
  { rewrite H1. rewrite plus_IZR, mult_IZR.
    change (IZR (2^p)) with (IZR (radix2^p)).
    rewrite IZR_Zpower by lia. ring_simplify.
    rewrite Rmult_assoc. rewrite H4. ring. }
  assert (0 <= IZR r < bpow radix2 p)%R.
  { split. apply IZR_le; lia.
    rewrite <- IZR_Zpower by lia. apply IZR_lt; tauto. }
  assert (0 <= IZR r * bpow radix2 (-p) < 1)%R.
  { generalize (bpow_gt_0 radix2 (-p)). intros.
    split. apply Rmult_le_pos; lra.
    rewrite <- H4. apply Rmult_lt_compat_r. auto. tauto. }
  assert (Zfloor (IZR n * bpow radix2 (-p)) = q).
  { apply Zfloor_imp. rewrite H5. rewrite plus_IZR. lra. }
  unfold Zrnd_odd. destruct Req_EM_T.
- assert (IZR r * bpow radix2 (-p) = 0)%R.
  { rewrite H8 in e. rewrite e in H5. lra. }
  apply Rmult_integral in H9. destruct H9; [ | lra ].
  apply (eq_IZR r 0) in H9. apply <- Z.eqb_eq in H9. rewrite H9. assumption.
- assert (IZR r * bpow radix2 (-p) <> 0)%R.
  { rewrite H8 in n0. lra. }
  destruct (Z.eqb r 0) eqn:RZ.
  apply Z.eqb_eq in RZ. rewrite RZ in H9.
  rewrite Rmult_0_l in H9. congruence.
  rewrite Zceil_floor_neq by lra. rewrite H8.
  change Zeven with Z.even. rewrite Zodd_even_bool. destruct (Z.even q); auto.
Qed.

Lemma int_round_odd_le:
  forall p x y, 0 <= p ->
  x <= y -> int_round_odd x p <= int_round_odd y p.
Proof.
  clear. intros.
  assert (Zrnd_odd (IZR x * bpow radix2 (-p)) <= Zrnd_odd (IZR y * bpow radix2 (-p))).
  { apply Zrnd_le. apply valid_rnd_odd. apply Rmult_le_compat_r. apply bpow_ge_0.
    apply IZR_le; auto. }
  rewrite <- ! Zrnd_odd_int by auto.
  apply Zmult_le_compat_r. auto. apply (Zpower_ge_0 radix2).
Qed.

Lemma int_round_odd_exact:
  forall p x, 0 <= p ->
  (2^p | x) -> int_round_odd x p = x.
Proof.
  clear. intros. unfold int_round_odd. apply Znumtheory.Zdivide_mod in H0.
  rewrite H0. simpl. rewrite Z.mul_comm. symmetry. apply Z_div_exact_2.
  apply Z.lt_gt. apply (Zpower_gt_0 radix2). auto. auto.
Qed.

Theorem BofZ_round_odd:
  forall x p,
  prec > 1 ->
  Z.abs x <= 2^emax - 2^(emax-prec) ->
  0 <= p <= emax - prec ->
  2^(prec + p + 1) <= Z.abs x ->
  BofZ x = BofZ (int_round_odd x p).
Proof.
  intros x p PREC XRANGE PRANGE XGE.
  assert (DIV: (2^p | 2^emax - 2^(emax - prec))).
  { rewrite int_upper_bound_eq. apply Z.divide_mul_r.
    exists (2^(emax - prec - p)). red in prec_gt_0_.
    rewrite <- (Zpower_plus radix2) by lia. f_equal; lia. }
  assert (YRANGE: Z.abs (int_round_odd x p) <= 2^emax - 2^(emax-prec)).
  { apply Z.abs_le. split.
    replace (-(2^emax - 2^(emax-prec))) with (int_round_odd (-(2^emax - 2^(emax-prec))) p).
    apply int_round_odd_le; zify; lia.
    apply int_round_odd_exact. lia. apply Z.divide_opp_r. auto.
    replace (2^emax - 2^(emax-prec)) with (int_round_odd (2^emax - 2^(emax-prec)) p).
    apply int_round_odd_le; zify; lia.
    apply int_round_odd_exact. lia. auto. }
  destruct (BofZ_finite x XRANGE) as (X1 & X2 & X3).
  destruct (BofZ_finite (int_round_odd x p) YRANGE) as (Y1 & Y2 & Y3).
  apply BofZ_finite_equal; auto.
  rewrite X1, Y1.
  assert (IZR (int_round_odd x p) = round radix2 (FIX_exp p) Zrnd_odd (IZR x)).
  {
     unfold round, scaled_mantissa, cexp, FIX_exp.
     rewrite <- Zrnd_odd_int by lia.
     unfold F2R; simpl. rewrite mult_IZR. f_equal. apply (IZR_Zpower radix2). lia.
  }
  rewrite H. symmetry. apply round_odd_fix. auto. lia.
  rewrite <- IZR_Zpower. rewrite <- abs_IZR. apply IZR_le; auto.
  red in prec_gt_0_; lia.
Qed.

Lemma int_round_odd_shifts:
  forall x p, 0 <= p ->
  int_round_odd x p =
  Z.shiftl (if Z.eqb (x mod 2^p) 0 then Z.shiftr x p else Z.lor (Z.shiftr x p) 1) p.
Proof.
  clear. intros.
  unfold int_round_odd. rewrite Z.shiftl_mul_pow2 by auto. f_equal.
  rewrite Z.shiftr_div_pow2 by auto.
  destruct (x mod 2^p =? 0) eqn:E. auto.
  assert (forall n, (if Z.odd n then n else n + 1) = Z.lor n 1).
  { destruct n; simpl; auto.
    destruct p0; auto.
    destruct p0; auto. induction p0; auto. }
  simpl. apply H0.
Qed.

Lemma int_round_odd_bits:
  forall x y p, 0 <= p ->
  (forall i, 0 <= i < p -> Z.testbit y i = false) ->
  Z.testbit y p = (if Z.eqb (x mod 2^p) 0 then Z.testbit x p else true) ->
  (forall i, p < i -> Z.testbit y i = Z.testbit x i) ->
  int_round_odd x p = y.
Proof.
  clear. intros until p; intros PPOS BELOW AT ABOVE.
  rewrite int_round_odd_shifts by auto.
  apply Z.bits_inj'. intros.
  generalize (Zcompare_spec n p); intros SPEC; inversion SPEC.
- rewrite BELOW by auto. apply Z.shiftl_spec_low; auto.
- subst n. rewrite AT. rewrite Z.shiftl_spec_high by lia.
  replace (p - p) with 0 by lia.
  destruct (x mod 2^p =? 0).
  + rewrite Z.shiftr_spec by lia. f_equal; lia.
  + rewrite Z.lor_spec. apply orb_true_r.
- rewrite ABOVE by auto.  rewrite Z.shiftl_spec_high by lia.
  destruct (x mod 2^p =? 0).
  rewrite Z.shiftr_spec by lia. f_equal; lia.
  rewrite Z.lor_spec, Z.shiftr_spec by lia.
  change 1 with (Z.ones 1). rewrite Z.ones_spec_high by lia. rewrite orb_false_r.
  f_equal; lia.
Qed.

(** ** Conversion from a FP number to an integer *)

(** Always rounds toward zero. *)

Definition ZofB (f: binary_float): option Z :=
  match f with
    | B754_finite _ _ s m (Zpos e) _ => Some (cond_Zopp s (Zpos m) * Z.pow_pos radix2 e)%Z
    | B754_finite _ _ s m 0 _ => Some (cond_Zopp s (Zpos m))
    | B754_finite _ _ s m (Zneg e) _ => Some (cond_Zopp s (Zpos m / Z.pow_pos radix2 e))%Z
    | B754_zero _ _ _ => Some 0%Z
    | _ => None
  end.

Theorem ZofB_correct:
  forall f,
  ZofB f = if is_finite _ _ f then Some (Ztrunc (B2R _ _ f)) else None.
Proof.
  destruct f as [s|s|s p H|s m e H]; simpl; auto.
- f_equal. symmetry. apply (Ztrunc_IZR 0).
- destruct e; f_equal.
  + unfold F2R; simpl. rewrite Rmult_1_r. rewrite Ztrunc_IZR. auto.
  + unfold F2R; simpl. rewrite <- mult_IZR. rewrite Ztrunc_IZR. auto.
  + unfold F2R; simpl. rewrite IZR_cond_Zopp. rewrite <- cond_Ropp_mult_l.
    assert (EQ: forall x, Ztrunc (cond_Ropp s x) = cond_Zopp s (Ztrunc x)).
    {
      intros. destruct s; simpl; auto. apply Ztrunc_opp.
    }
    rewrite EQ. f_equal.
    generalize (Zpower_pos_gt_0 2 p (eq_refl _)); intros.
    rewrite Ztrunc_floor. symmetry. apply Zfloor_div. lia.
    apply Rmult_le_pos. apply IZR_le. compute; congruence.
    apply Rlt_le. apply Rinv_0_lt_compat. apply IZR_lt. auto.
Qed.

(** Interval properties. *)

Remark Ztrunc_range_pos:
  forall x, 0 < Ztrunc x -> (IZR (Ztrunc x) <= x < IZR (Ztrunc x + 1)%Z)%R.
Proof.
  intros.
  rewrite Ztrunc_floor. split. apply Zfloor_lb. rewrite plus_IZR. apply Zfloor_ub.
  generalize (Rle_bool_spec 0%R x). intros RLE; inversion RLE; subst; clear RLE.
  auto.
  rewrite Ztrunc_ceil in H by lra. unfold Zceil in H.
  assert (-x < 0)%R.
  { apply Rlt_le_trans with (IZR (Zfloor (-x)) + 1)%R. apply Zfloor_ub.
    rewrite <- plus_IZR.
    apply IZR_le. lia. }
  lra.
Qed.

Remark Ztrunc_range_zero:
  forall x, Ztrunc x = 0 -> (-1 < x < 1)%R.
Proof.
  intros; generalize (Rle_bool_spec 0%R x). intros RLE; inversion RLE; subst; clear RLE.
- rewrite Ztrunc_floor in H by auto. split.
  + apply Rlt_le_trans with 0%R; auto. rewrite <- Ropp_0. apply Ropp_lt_contravar. apply Rlt_0_1.
  + replace 1%R with (IZR (Zfloor x) + 1)%R. apply Zfloor_ub. rewrite H. simpl. apply Rplus_0_l.
- rewrite Ztrunc_ceil in H by (apply Rlt_le; auto). split.
  + apply (Ropp_lt_cancel (-(1))). rewrite Ropp_involutive.
    replace 1%R with (IZR (Zfloor (-x)) + 1)%R. apply Zfloor_ub.
    unfold Zceil in H. replace (Zfloor (-x)) with 0 by lia. simpl. apply Rplus_0_l.
  + apply Rlt_le_trans with 0%R; auto. apply Rle_0_1.
Qed.

Theorem ZofB_range_pos:
  forall f n, ZofB f = Some n -> 0 < n -> (IZR n <= B2R _ _ f < IZR (n + 1)%Z)%R.
Proof.
  intros. rewrite ZofB_correct in H. destruct (is_finite prec emax f) eqn:FIN; inversion H.
  apply Ztrunc_range_pos. congruence.
Qed.

Theorem ZofB_range_neg:
  forall f n, ZofB f = Some n -> n < 0 -> (IZR (n - 1)%Z < B2R _ _ f <= IZR n)%R.
Proof.
  intros. rewrite ZofB_correct in H. destruct (is_finite prec emax f) eqn:FIN; inversion H.
  set (x := B2R prec emax f) in *. set (y := (-x)%R).
  assert (A: (IZR (Ztrunc y) <= y < IZR (Ztrunc y + 1)%Z)%R).
  { apply Ztrunc_range_pos. unfold y. rewrite Ztrunc_opp. lia. }
  destruct A as [B C].
  unfold y in B, C. rewrite Ztrunc_opp in B, C.
  replace (- Ztrunc x + 1) with (- (Ztrunc x - 1)) in C by lia.
  rewrite opp_IZR in B, C. lra.
Qed.

Theorem ZofB_range_zero:
  forall f, ZofB f = Some 0 -> (-1 < B2R _ _ f < 1)%R.
Proof.
  intros. rewrite ZofB_correct in H. destruct (is_finite prec emax f) eqn:FIN; inversion H.
  apply Ztrunc_range_zero. auto.
Qed.

Theorem ZofB_range_nonneg:
  forall f n, ZofB f = Some n -> 0 <= n -> (-1 < B2R _ _ f < IZR (n + 1)%Z)%R.
Proof.
  intros. destruct (Z.eq_dec n 0).
- subst n. apply ZofB_range_zero. auto.
- destruct (ZofB_range_pos f n) as (A & B). auto. lia.
  split; auto. apply Rlt_le_trans with 0%R. simpl; lra.
  apply Rle_trans with (IZR n); auto. apply IZR_le; auto.
Qed.

(** For representable integers, [ZofB] is left inverse of [BofZ]. *)

Theorem ZofBofZ_exact:
  forall n, integer_representable n -> ZofB (BofZ n) = Some n.
Proof.
  intros. destruct (BofZ_representable n H) as (A & B & C).
  rewrite ZofB_correct. rewrite A, B. f_equal. apply Ztrunc_IZR.
Qed.

(** Compatibility with subtraction *)

Remark Zfloor_minus:
  forall x n, Zfloor (x - IZR n) = Zfloor x - n.
Proof.
  intros. apply Zfloor_imp. replace (Zfloor x - n + 1) with ((Zfloor x + 1) - n) by lia.
  rewrite ! minus_IZR. unfold Rminus. split.
  apply Rplus_le_compat_r. apply Zfloor_lb.
  apply Rplus_lt_compat_r. rewrite plus_IZR. apply Zfloor_ub.
Qed.

Theorem ZofB_minus:
  forall minus_nan m f p q,
  ZofB f = Some p -> 0 <= p < 2*q -> q <= 2^prec -> (IZR q <= B2R _ _ f)%R ->
  ZofB (Bminus _ _ _ Hmax minus_nan m f (BofZ q)) = Some (p - q).
Proof.
  intros.
  assert (Q: -2^prec <= q <= 2^prec).
  { split; auto.  generalize (Zpower_ge_0 radix2 prec); simpl; lia. }
  assert (RANGE: (-1 < B2R _ _ f < IZR (p + 1)%Z)%R) by (apply ZofB_range_nonneg; auto; lia).
  rewrite ZofB_correct in H. destruct (is_finite prec emax f) eqn:FIN; try discriminate.
  assert (PQ2: (IZR (p + 1) <= IZR q * 2)%R).
  { rewrite <- mult_IZR. apply IZR_le. lia. }
  assert (EXACT: round radix2 fexp (round_mode m) (B2R _ _ f - IZR q)%R = (B2R _ _ f - IZR q)%R).
  { apply round_generic. apply valid_rnd_round_mode.
    apply sterbenz_aux. now apply FLT_exp_valid. apply FLT_exp_monotone. apply generic_format_B2R.
    apply integer_representable_n. auto. lra. }
  destruct (BofZ_exact q Q) as (A & B & C).
  generalize (Bminus_correct _ _ _ Hmax minus_nan m f (BofZ q) FIN B).
  rewrite Rlt_bool_true.
- fold emin; fold fexp. intros (D & E & F).
  rewrite ZofB_correct. rewrite E. rewrite D. rewrite A. rewrite EXACT.
  inversion H. f_equal. rewrite ! Ztrunc_floor. apply Zfloor_minus.
  lra. lra.
- rewrite A. fold emin; fold fexp. rewrite EXACT.
  apply Rle_lt_trans with (bpow radix2 prec).
  apply Rle_trans with (IZR q). apply Rabs_le. lra.
  rewrite <- IZR_Zpower. apply IZR_le; auto. red in prec_gt_0_; lia.
  apply bpow_lt. auto.
Qed.

(** A variant of [ZofB] that bounds the range of representable integers. *)

Definition ZofB_range (f: binary_float) (zmin zmax: Z): option Z :=
  match ZofB f with
  | None => None
  | Some z => if Z.leb zmin z && Z.leb z zmax then Some z else None
  end.

Theorem ZofB_range_correct:
  forall f min max,
  let n := Ztrunc (B2R _ _ f) in
  ZofB_range f min max =
  if is_finite _ _ f && Z.leb min n && Z.leb n max then Some n else None.
Proof.
  intros. unfold ZofB_range. rewrite ZofB_correct. fold n.
  destruct (is_finite prec emax f); auto.
Qed.

Lemma ZofB_range_inversion:
  forall f min max n,
  ZofB_range f min max = Some n ->
  min <= n /\ n <= max /\ ZofB f = Some n.
Proof.
  intros. rewrite ZofB_range_correct in H. rewrite ZofB_correct.
  destruct (is_finite prec emax f); try discriminate.
  set (n1 := Ztrunc (B2R _ _ f)) in *.
  destruct (min <=? n1) eqn:MIN; try discriminate.
  destruct (n1 <=? max) eqn:MAX; try discriminate.
  simpl in H. inversion H. subst n.
  split. apply Zle_bool_imp_le; auto.
  split. apply Zle_bool_imp_le; auto.
  auto.
Qed.

Theorem ZofB_range_minus:
  forall minus_nan m f p q,
  ZofB_range f 0 (2 * q - 1) = Some p -> q <= 2^prec -> (IZR q <= B2R _ _ f)%R ->
  ZofB_range (Bminus _ _ _ Hmax minus_nan m f (BofZ q)) (-q) (q - 1) = Some (p - q).
Proof.
  intros. destruct (ZofB_range_inversion _ _ _ _ H) as (A & B & C).
  set (f' := Bminus prec emax prec_gt_0_ Hmax minus_nan m f (BofZ q)).
  assert (D: ZofB f' = Some (p - q)).
  { apply ZofB_minus. auto. lia. auto. auto. }
  unfold ZofB_range. rewrite D. rewrite Zle_bool_true by lia. rewrite Zle_bool_true by lia. auto.
Qed.

(** ** Algebraic identities *)

(** Commutativity of addition and multiplication *)

Theorem Bplus_commut:
  forall plus_nan mode (x y: binary_float),
  plus_nan x y = plus_nan y x ->
  Bplus _ _ _ Hmax plus_nan mode x y = Bplus _ _ _ Hmax plus_nan mode y x.
Proof.
  intros until y; intros NAN.
  pose proof (Bplus_correct _ _ _ Hmax plus_nan mode x y).
  pose proof (Bplus_correct _ _ _ Hmax plus_nan mode y x).
  unfold Bplus in *; destruct x as [sx|sx|sx px Hx|sx mx ex Hx]; destruct y as [sy|sy|sy py Hy|sy my ey Hy]; auto.
- rewrite (eqb_sym sy sx). destruct (eqb sx sy) eqn:EQB; auto.
  f_equal; apply eqb_prop; auto.
- rewrite NAN; auto.
- rewrite (eqb_sym sy sx). destruct (eqb sx sy) eqn:EQB.
  f_equal; apply eqb_prop; auto.
  rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- generalize (H (eq_refl _) (eq_refl _)); clear H.
  generalize (H0 (eq_refl _) (eq_refl _)); clear H0.
  fold emin. fold fexp.
  set (x := B754_finite prec emax sx mx ex Hx). set (rx := B2R _ _ x).
  set (y := B754_finite prec emax sy my ey Hy). set (ry := B2R _ _ y).
  rewrite (Rplus_comm ry rx). destruct Rlt_bool.
  + intros (A1 & A2 & A3) (B1 & B2 & B3).
    apply B2R_Bsign_inj; auto. rewrite <- B1 in A1. auto.
    rewrite Z.add_comm. rewrite Z.min_comm. auto.
  + intros (A1 & A2) (B1 & B2). apply B2FF_inj. rewrite B2 in B1. rewrite <- B1 in A1. auto.
Qed.

Theorem Bmult_commut:
  forall mult_nan mode (x y: binary_float),
  mult_nan x y = mult_nan y x ->
  Bmult _ _ _ Hmax mult_nan mode x y = Bmult _ _ _ Hmax mult_nan mode y x.
Proof.
  intros until y; intros NAN.
  pose proof (Bmult_correct _ _ _ Hmax mult_nan mode x y).
  pose proof (Bmult_correct _ _ _ Hmax mult_nan mode y x).
  unfold Bmult in *; destruct x as [sx|sx|sx px Hx|sx mx ex Hx]; destruct y as [sy|sy|sy py Hy|sy my ey Hy]; auto.
- rewrite (xorb_comm sx sy); auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite (xorb_comm sx sy); auto.
- rewrite NAN; auto.
- rewrite (xorb_comm sx sy); auto.
- rewrite NAN; auto.
- rewrite (xorb_comm sx sy); auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite NAN; auto.
- rewrite (xorb_comm sx sy); auto.
- rewrite (xorb_comm sx sy); auto.
- rewrite NAN; auto.
- revert H H0. fold emin. fold fexp.
  set (x := B754_finite prec emax sx mx ex Hx). set (rx := B2R _ _ x).
  set (y := B754_finite prec emax sy my ey Hy). set (ry := B2R _ _ y).
  rewrite (Rmult_comm ry rx).
  destruct (Rlt_bool (Rabs (round radix2 fexp (round_mode mode) (rx * ry)))
                     (bpow radix2 emax)).
  + intros (A1 & A2 & A3) (B1 & B2 & B3).
    apply B2R_Bsign_inj; auto. rewrite <- B1 in A1. auto.
    rewrite ! Bsign_FF2B. f_equal. f_equal. apply xorb_comm. now rewrite Pos.mul_comm. apply Z.add_comm.
  + intros A B. apply B2FF_inj. etransitivity. eapply A. rewrite xorb_comm. auto.
Qed.

(** Multiplication by 2 is diagonal addition. *)

Theorem Bmult2_Bplus:
  forall plus_nan mult_nan mode (f: binary_float),
  (forall (x y: binary_float),
   is_nan _ _ x = true -> is_finite _ _ y = true -> plus_nan x x = mult_nan x y) ->
  Bplus _ _ _ Hmax plus_nan mode f f = Bmult _ _ _ Hmax mult_nan mode f (BofZ 2%Z).
Proof.
  intros until f; intros NAN.
  destruct (BofZ_representable 2) as (A & B & C).
  apply (integer_representable_2p 1). red in prec_gt_0_; lia.
  pose proof (Bmult_correct _ _ _ Hmax mult_nan mode f (BofZ 2%Z)). fold emin in H.
  rewrite A, B, C in H. rewrite xorb_false_r in H.
  destruct (is_finite _ _ f) eqn:FIN.
- pose proof (Bplus_correct _ _ _ Hmax plus_nan mode f f FIN FIN). fold emin in H0.
  assert (EQ: (B2R prec emax f * IZR 2%Z = B2R prec emax f + B2R prec emax f)%R).
  { ring. }
  rewrite <- EQ in H0. destruct Rlt_bool.
  + destruct H0 as (P & Q & R). destruct H as (S & T & U).
    apply B2R_Bsign_inj; auto.
    rewrite P, S. auto.
    rewrite R, U.
    replace 0%R with (0 * 2)%R by ring. rewrite Rcompare_mult_r.
    rewrite andb_diag, orb_diag. destruct f as [s|s|s p H|s m e H]; try discriminate; simpl.
    rewrite Rcompare_Eq by auto. destruct mode; auto.
    replace 0%R with (@F2R radix2 {| Fnum := 0%Z; Fexp := e |}).
    rewrite Rcompare_F2R. destruct s; auto.
    unfold F2R. simpl. ring.
    apply IZR_lt. lia.
    destruct (Bmult prec emax prec_gt_0_ Hmax mult_nan mode f (BofZ 2)); reflexivity || discriminate.
  + destruct H0 as (P & Q). apply B2FF_inj. rewrite P, H. auto.
- destruct f as [sf|sf|sf pf Hf|sf mf ef Hf]; try discriminate.
  + simpl Bplus. rewrite eqb_true. destruct (BofZ 2) as [| | |s2 m2 e2 H2] eqn:B2; try discriminate; simpl in *.
    assert ((0 = 2)%Z) by (apply eq_IZR; auto). discriminate.
    subst s2. rewrite xorb_false_r. auto.
    auto.
  + unfold Bplus, Bmult. rewrite <- NAN by auto. auto.
Qed.

(** Divisions that can be turned into multiplications by an inverse *)

Definition Bexact_inverse_mantissa := Z.iter (prec - 1) xO xH.

Remark Bexact_inverse_mantissa_value:
  Zpos Bexact_inverse_mantissa = 2 ^ (prec - 1).
Proof.
  assert (REC: forall n, Z.pos (nat_rect _ xH (fun _ => xO) n) = 2 ^ (Z.of_nat n)).
  { induction n. reflexivity.
    simpl nat_rect. transitivity (2 * Z.pos (nat_rect _ xH (fun _ => xO) n)). reflexivity.
    rewrite Nat2Z.inj_succ. rewrite IHn. unfold Z.succ. rewrite Zpower_plus by lia.
    change (2 ^ 1) with 2. ring. }
  red in prec_gt_0_.
  unfold Bexact_inverse_mantissa. rewrite iter_nat_of_Z by lia. rewrite REC.
  rewrite Zabs2Nat.id_abs. rewrite Z.abs_eq by lia. auto.
Qed.

Remark Bexact_inverse_mantissa_digits2_pos:
  Z.pos (digits2_pos Bexact_inverse_mantissa) = prec.
Proof.
  assert (DIGITS: forall n, digits2_pos (nat_rect _ xH (fun _ => xO) n) = Pos.of_nat (n+1)).
  { induction n; simpl. auto. rewrite IHn. destruct n; auto. }
  red in prec_gt_0_.
  unfold Bexact_inverse_mantissa. rewrite iter_nat_of_Z by lia. rewrite DIGITS.
  rewrite Zabs2Nat.abs_nat_nonneg, Z2Nat.inj_sub by lia.
  destruct prec; try  discriminate. rewrite Nat.sub_add.
  simpl. rewrite Pos2Nat.id. auto.
  simpl. zify; lia.
Qed.

Remark bounded_Bexact_inverse:
  forall e,
  emin <= e <= emax - prec <-> bounded prec emax Bexact_inverse_mantissa e = true.
Proof.
  intros. unfold bounded, canonical_mantissa. rewrite andb_true_iff.
  rewrite <- Zeq_is_eq_bool. rewrite <- Zle_is_le_bool.
  rewrite Bexact_inverse_mantissa_digits2_pos.
  split.
- intros; split. unfold FLT_exp. unfold emin in H. zify; lia. lia.
- intros [A B]. unfold FLT_exp in A. unfold emin. zify; lia.
Qed.

Program Definition Bexact_inverse (f: binary_float) : option binary_float :=
  match f with
  | B754_finite _ _ s m e B =>
      if Pos.eq_dec m Bexact_inverse_mantissa then
      let e' := -e - (prec - 1) * 2 in
      if Z_le_dec emin e' then
      if Z_le_dec e' emax then
        Some(B754_finite _ _ s m e' _)
      else None else None else None
  | _ => None
  end.
Next Obligation.
  rewrite <- bounded_Bexact_inverse in B. rewrite <- bounded_Bexact_inverse.
  unfold emin in *. lia.
Qed.

Lemma Bexact_inverse_correct:
  forall f f', Bexact_inverse f = Some f' ->
  is_finite_strict _ _ f = true
  /\ is_finite_strict _ _ f' = true
  /\ B2R _ _ f' = (/ B2R _ _ f)%R
  /\ B2R _ _ f <> 0%R
  /\ Bsign _ _ f' = Bsign _ _ f.
Proof with (try discriminate).
  intros f f' EI. unfold Bexact_inverse in EI. destruct f as [s|s|s p H|s m e H]...
  destruct (Pos.eq_dec m Bexact_inverse_mantissa)...
  set (e' := -e - (prec - 1) * 2) in *.
  destruct (Z_le_dec emin e')...
  destruct (Z_le_dec e' emax)...
  inversion EI; clear EI; subst f' m.
  split. auto. split. auto. split. unfold B2R. rewrite Bexact_inverse_mantissa_value.
  unfold F2R; simpl. rewrite IZR_cond_Zopp.
  rewrite <- ! cond_Ropp_mult_l.
  red in prec_gt_0_.
  replace (IZR (2 ^ (prec - 1))) with (bpow radix2 (prec - 1))
  by (symmetry; apply (IZR_Zpower radix2); lia).
  rewrite <- ! bpow_plus.
  replace (prec - 1 + e') with (- (prec - 1 + e)) by (unfold e'; lia).
  rewrite bpow_opp. unfold cond_Ropp; destruct s; auto.
  rewrite Ropp_inv_permute. auto. apply Rgt_not_eq. apply bpow_gt_0.
  split. simpl. apply F2R_neq_0. destruct s; simpl in H; discriminate.
  auto.
Qed.

Theorem Bdiv_mult_inverse:
  forall div_nan mult_nan mode x y z,
  (forall (x y z: binary_float),
   is_nan _ _ x = true -> is_finite _ _ y = true -> is_finite _ _ z = true ->
   div_nan x y = mult_nan x z) ->
  Bexact_inverse y = Some z ->
  Bdiv _ _ _ Hmax div_nan mode x y = Bmult _ _ _ Hmax mult_nan mode x z.
Proof.
  intros until z; intros NAN; intros. destruct (Bexact_inverse_correct _ _ H) as (A & B & C & D & E).
  pose proof (Bmult_correct _ _ _ Hmax mult_nan mode x z).
  fold emin in H0. fold fexp in H0.
  pose proof (Bdiv_correct _ _ _ Hmax div_nan mode x y D).
  fold emin in H1. fold fexp in H1.
  unfold Rdiv in H1. rewrite <- C in H1.
  destruct (is_finite _ _ x) eqn:FINX.
- destruct Rlt_bool.
  + destruct H0 as (P & Q & R). destruct H1 as (S & T & U).
    apply B2R_Bsign_inj; auto.
    rewrite Q. simpl. apply is_finite_strict_finite; auto.
    rewrite P, S. auto.
    rewrite R, U, E. auto.
    apply is_finite_not_is_nan; auto.
    apply is_finite_not_is_nan. rewrite Q. simpl. apply is_finite_strict_finite; auto.  + apply B2FF_inj. rewrite H0, H1. rewrite E. auto.
- destruct y; try discriminate. destruct z; try discriminate.
  destruct x; try discriminate; simpl.
  + simpl in E; congruence.
  + erewrite NAN; eauto.
Qed.

(** ** Conversion from scientific notation *)

(** Russian peasant exponentiation *)

Fixpoint pos_pow (x y: positive) : positive :=
  match y with
  | xH => x
  | xO y => Pos.square (pos_pow x y)
  | xI y => Pos.mul x (Pos.square (pos_pow x y))
  end.

Lemma pos_pow_spec:
  forall x y, Z.pos (pos_pow x y) = Z.pos x ^ Z.pos y.
Proof.
  intros x.
  assert (REC: forall y a, Pos.iter (Pos.mul x) a y = Pos.mul (pos_pow x y) a).
  { induction y; simpl; intros.
  - rewrite ! IHy, Pos.square_spec, ! Pos.mul_assoc. auto.
  - rewrite ! IHy, Pos.square_spec, ! Pos.mul_assoc. auto.
  - auto.
  }
  intros. simpl. rewrite <- Pos2Z.inj_pow_pos. unfold Pos.pow. rewrite REC. rewrite Pos.mul_1_r. auto.
Qed.

(** Given a base [base], a mantissa [m] and an exponent [e], the following function
  computes the FP number closest to [m * base ^ e], using round to odd, ties break to even.
  The algorithm is naive, computing [base ^ |e|] exactly before doing a multiplication or
  division with [m].  However, we treat specially very large or very small values of [e],
  when the result is known to be [+infinity] or [0.0] respectively. *)

Definition Bparse (base: positive) (m: positive) (e: Z): binary_float :=
  match e with
  | Z0 =>
     BofZ (Zpos m)
  | Zpos p =>
     if e * Z.log2 (Zpos base) <? emax
     then BofZ (Zpos m * Zpos (pos_pow base p))
     else B754_infinity _ _ false
  | Zneg p =>
     if e * Z.log2 (Zpos base) + Z.log2_up (Zpos m) <? emin
     then B754_zero _ _ false
     else FF2B prec emax _ (proj1 (Bdiv_correct_aux prec emax prec_gt_0_ Hmax mode_NE
                                     false m Z0 false (pos_pow base p) Z0))
  end.

(** Properties of [Z.log2] and [Z.log2_up]. *)

Lemma Zpower_log:
  forall (base: radix) n,
  0 < n ->
  2 ^ (n * Z.log2 base) <= base ^ n <= 2 ^ (n * Z.log2_up base).
Proof.
  intros.
  assert (A: 0 < base) by apply radix_gt_0.
  assert (B: 0 <= Z.log2 base) by apply Z.log2_nonneg.
  assert (C: 0 <= Z.log2_up base) by apply Z.log2_up_nonneg.
  destruct (Z.log2_spec base) as [D E]; auto.
  destruct (Z.log2_up_spec base) as [F G]. apply radix_gt_1.
  assert (K: 0 <= 2 ^ Z.log2 base) by (apply Z.pow_nonneg; lia).
  rewrite ! (Z.mul_comm n). rewrite ! Z.pow_mul_r by lia.
  split; apply Z.pow_le_mono_l; lia.
Qed.

Lemma bpow_log_pos:
  forall (base: radix) n,
  0 < n ->
  (bpow radix2 (n * Z.log2 base)%Z <= bpow base n)%R.
Proof.
  intros. rewrite <- ! IZR_Zpower. apply IZR_le; apply Zpower_log; auto.
  lia.
  rewrite Z.mul_comm; apply Zmult_gt_0_le_0_compat. lia. apply Z.log2_nonneg.
Qed.

Lemma bpow_log_neg:
  forall (base: radix) n,
  n < 0 ->
  (bpow base n <= bpow radix2 (n * Z.log2 base)%Z)%R.
Proof.
  intros. set (m := -n). replace n with (-m) by (unfold m; lia).
  rewrite ! Z.mul_opp_l, ! bpow_opp. apply Rinv_le.
  apply bpow_gt_0.
  apply bpow_log_pos. unfold m; lia.
Qed.

(** Overflow and underflow conditions. *)

Lemma round_integer_overflow:
  forall (base: radix) e m,
  0 < e ->
  emax <= e * Z.log2 base ->
  (bpow radix2 emax <= round radix2 fexp (round_mode mode_NE) (IZR (Zpos m) * bpow base e))%R.
Proof.
  intros.
  rewrite <- (round_generic radix2 fexp (round_mode mode_NE) (bpow radix2 emax)); auto.
  apply round_le; auto. apply fexp_correct; auto. apply valid_rnd_round_mode.
  rewrite <- (Rmult_1_l (bpow radix2 emax)). apply Rmult_le_compat.
  apply Rle_0_1.
  apply bpow_ge_0.
  apply IZR_le. zify; lia.
  eapply Rle_trans. eapply bpow_le. eassumption. apply bpow_log_pos; auto.
  apply generic_format_FLT. exists (Float radix2 1 emax).
  unfold F2R; simpl. ring.
  simpl. apply (Zpower_gt_1 radix2); auto.
  simpl. unfold emin; red in prec_gt_0_; lia.
Qed.

Lemma round_NE_underflows:
  forall x,
  (0 <= x <= bpow radix2 (emin - 1))%R ->
  round radix2 fexp (round_mode mode_NE) x = 0%R.
Proof.
  intros.
  set (eps := bpow radix2 (emin - 1)) in *.
  assert (A: round radix2 fexp (round_mode mode_NE) eps = 0%R).
  { unfold round. simpl.
    assert (E: cexp radix2 fexp eps = emin).
    { unfold cexp, eps. rewrite mag_bpow. unfold fexp, FLT_exp. zify; red in prec_gt_0_; lia. }
    unfold scaled_mantissa; rewrite E.
    assert (P: (eps * bpow radix2 (-emin) = / 2)%R).
    { unfold eps. rewrite <- bpow_plus. replace (emin - 1 + -emin) with (-1) by lia. auto. }
    rewrite P. unfold Znearest.
    assert (F: Zfloor (/ 2)%R = 0).
    { apply Zfloor_imp. simpl. lra. }
    rewrite F. rewrite Rminus_0_r. rewrite Rcompare_Eq by auto.
    simpl. unfold F2R; simpl. apply Rmult_0_l.
  }
  apply Rle_antisym.
- rewrite <- A. apply round_le. apply fexp_correct; auto. apply valid_rnd_round_mode. tauto.
- rewrite <- (round_0 radix2 fexp (round_mode mode_NE)).
  apply round_le. apply fexp_correct; auto. apply valid_rnd_round_mode. tauto.
Qed.

Lemma round_integer_underflow:
  forall (base: radix) e m,
  e < 0 ->
  e * Z.log2 base + Z.log2_up (Zpos m) < emin ->
  round radix2 fexp (round_mode mode_NE) (IZR (Zpos m) * bpow base e) = 0%R.
Proof.
  intros. apply round_NE_underflows. split.
- apply Rmult_le_pos. apply IZR_le. zify; lia. apply bpow_ge_0.
- apply Rle_trans with (bpow radix2 (Z.log2_up (Z.pos m) + e * Z.log2 base)).
+ rewrite bpow_plus. apply Rmult_le_compat.
  apply IZR_le; zify; lia.
  apply bpow_ge_0.
  rewrite <- IZR_Zpower. apply IZR_le.
  destruct (Z.eq_dec (Z.pos m) 1).
  rewrite e0. simpl. lia.
  apply Z.log2_up_spec. zify; lia.
  apply Z.log2_up_nonneg.
  apply bpow_log_neg. auto.
+ apply bpow_le. lia.
Qed.

(** Correctness of Bparse *)

Theorem Bparse_correct:
  forall b m e (BASE: 2 <= Zpos b),
  let base := {| radix_val := Zpos b; radix_prop := Zle_imp_le_bool _ _ BASE |} in
  let r := round radix2 fexp (round_mode mode_NE) (IZR (Zpos m) * bpow base e) in
  if Rlt_bool (Rabs r) (bpow radix2 emax) then
     B2R _ _ (Bparse b m e) = r
  /\ is_finite _ _ (Bparse b m e) = true
  /\ Bsign _ _ (Bparse b m e) = false
  else
    B2FF _ _ (Bparse b m e) = F754_infinity false.
Proof.
  intros.
  assert (A: forall x, @F2R radix2 {| Fnum := x; Fexp := 0 |} = IZR x).
  { intros. unfold F2R, Fnum; simpl. ring. }
  unfold Bparse, r. destruct e as [ | e | e].
- (* e = Z0 *)
  change (bpow base 0) with 1%R. rewrite Rmult_1_r.
  exact (BofZ_correct (Z.pos m)).
- (* e = Zpos e *)
  destruct (Z.ltb_spec (Z.pos e * Z.log2 (Z.pos b)) emax).
+ (* no overflow *)
  rewrite pos_pow_spec. rewrite <- IZR_Zpower by (zify; lia). rewrite <- mult_IZR.
  replace false with (Z.pos m * Z.pos b ^ Z.pos e <? 0).
  exact (BofZ_correct (Z.pos m * Z.pos b ^ Z.pos e)).
  rewrite Z.ltb_ge. rewrite Z.mul_comm. apply Zmult_gt_0_le_0_compat. zify; lia.  apply (Zpower_ge_0 base).
+ (* overflow *)
  rewrite Rlt_bool_false. auto. eapply Rle_trans; [idtac|apply Rle_abs].
  apply (round_integer_overflow base). zify; lia. auto.
- (* e = Zneg e *)
  destruct (Z.ltb_spec (Z.neg e * Z.log2 (Z.pos b) + Z.log2_up (Z.pos m)) emin).
+ (* undeflow *)
  rewrite round_integer_underflow; auto.
  rewrite Rlt_bool_true. auto.
  replace (Rabs 0)%R with 0%R. apply bpow_gt_0. apply (abs_IZR 0).
  zify; lia.
+ (* no underflow *)
  generalize (Bdiv_correct_aux prec emax prec_gt_0_ Hmax mode_NE false m 0 false (pos_pow b e) 0).
  set (f := let '(mz, ez, lz) := Fdiv_core_binary prec emax (Z.pos m) 0 (Z.pos (pos_pow b e)) 0
         in binary_round_aux prec emax mode_NE (xorb false false) mz ez lz).
  fold emin; fold fexp. rewrite ! A. unfold cond_Zopp. rewrite pos_pow_spec.
  assert (B: (IZR (Z.pos m) / IZR (Z.pos b ^ Z.pos e) =
              IZR (Z.pos m) * bpow base (Z.neg e))%R).
  { change (Z.neg e) with (- (Z.pos e)). rewrite bpow_opp. auto. }
  rewrite B. intros [P Q].
  destruct (Rlt_bool
     (Rabs
        (round radix2 fexp (round_mode mode_NE)
           (IZR (Z.pos m) * bpow base (Z.neg e))))
    (bpow radix2 emax)).
* destruct Q as (Q1 & Q2 & Q3).
  split. rewrite B2R_FF2B, Q1. auto.
  split. rewrite is_finite_FF2B. auto.
  rewrite Bsign_FF2B. auto.
* rewrite B2FF_FF2B. auto.
Qed.

End Extra_ops.

(** ** Conversions between two FP formats *)

Section Conversions.

Variable prec1 emax1 prec2 emax2 : Z.
Context (prec1_gt_0_ : Prec_gt_0 prec1) (prec2_gt_0_ : Prec_gt_0 prec2).
Let emin1 := (3 - emax1 - prec1)%Z.
Let fexp1 := FLT_exp emin1 prec1.
Let emin2 := (3 - emax2 - prec2)%Z.
Let fexp2 := FLT_exp emin2 prec2.
Hypothesis Hmax1 : (prec1 < emax1)%Z.
Hypothesis Hmax2 : (prec2 < emax2)%Z.
Let binary_float1 := binary_float prec1 emax1.
Let binary_float2 := binary_float prec2 emax2.

Definition Bconv (conv_nan: binary_float1 -> {x | is_nan prec2 emax2 x = true}) (md: mode) (f: binary_float1) : binary_float2 :=
  match f with
    | B754_nan _ _ _ _ _ => build_nan prec2 emax2 (conv_nan f)
    | B754_infinity _ _ s => B754_infinity _ _ s
    | B754_zero _ _ s => B754_zero _ _ s
    | B754_finite _ _ s m e _ => binary_normalize _ _ _ Hmax2 md (cond_Zopp s (Zpos m)) e s
  end.

Theorem Bconv_correct:
  forall conv_nan m f,
  is_finite _ _ f = true ->
  if Rlt_bool (Rabs (round radix2 fexp2 (round_mode m) (B2R _ _ f))) (bpow radix2 emax2)
  then
     B2R _ _ (Bconv conv_nan m f) = round radix2 fexp2 (round_mode m) (B2R _ _ f)
  /\ is_finite _ _ (Bconv conv_nan m f) = true
  /\ Bsign _ _ (Bconv conv_nan m f) = Bsign _ _ f
  else
     B2FF _ _ (Bconv conv_nan m f) = binary_overflow prec2 emax2 m (Bsign _ _ f).
Proof.
  intros. destruct f as [sf|sf|sf pf Hf|sf mf ef Hf]; try discriminate.
- simpl. rewrite round_0. rewrite Rabs_R0. rewrite Rlt_bool_true. auto.
  apply bpow_gt_0. apply valid_rnd_round_mode.
- generalize (binary_normalize_correct _ _ _ Hmax2 m (cond_Zopp sf (Zpos mf)) ef sf).
  fold emin2; fold fexp2. simpl. destruct Rlt_bool.
  + intros (A & B & C). split. auto. split. auto. rewrite C.
    destruct sf; simpl.
    rewrite Rcompare_Lt. auto. apply F2R_lt_0. simpl. compute; auto.
    rewrite Rcompare_Gt. auto. apply F2R_gt_0. simpl. compute; auto.
  + intros A. rewrite A. f_equal. destruct sf.
    apply Rlt_bool_true. apply F2R_lt_0. simpl. compute; auto.
    apply Rlt_bool_false. apply Rlt_le. apply Rgt_lt. apply F2R_gt_0. simpl. compute; auto.
Qed.

(** Converting a finite FP number to higher or equal precision preserves its value. *)

Theorem Bconv_widen_exact:
  (prec2 >= prec1)%Z -> (emax2 >= emax1)%Z ->
  forall conv_nan m f,
  is_finite _ _ f = true ->
     B2R _ _ (Bconv conv_nan m f) = B2R _ _ f
  /\ is_finite _ _ (Bconv conv_nan m f) = true
  /\ Bsign _ _ (Bconv conv_nan m f) = Bsign _ _ f.
Proof.
  intros PREC EMAX; intros. generalize (Bconv_correct conv_nan m f H).
  assert (LT: (Rabs (B2R _ _ f) < bpow radix2 emax2)%R).
  {
    destruct f; try discriminate; simpl.
    rewrite Rabs_R0. apply bpow_gt_0.
    apply Rlt_le_trans with (bpow radix2 emax1).
    rewrite F2R_cond_Zopp. rewrite abs_cond_Ropp. rewrite <- F2R_Zabs. simpl Z.abs.
    eapply bounded_lt_emax; eauto.
    apply bpow_le. lia.
  }
  assert (EQ: round radix2 fexp2 (round_mode m) (B2R prec1 emax1 f) = B2R prec1 emax1 f).
  {
    apply round_generic. apply valid_rnd_round_mode. eapply generic_inclusion_le.
    5: apply generic_format_B2R. apply fexp_correct; auto. apply fexp_correct; auto.
    instantiate (1 := emax2). intros. unfold fexp2, FLT_exp. unfold emin2. zify; lia.
    apply Rlt_le; auto.
  }
  rewrite EQ. rewrite Rlt_bool_true by auto. auto.
Qed.

(** Conversion from integers and change of format *)

Theorem Bconv_BofZ:
  forall conv_nan n,
  integer_representable prec1 emax1 n ->
  Bconv conv_nan mode_NE (BofZ prec1 emax1 _ Hmax1 n) = BofZ prec2 emax2 _ Hmax2 n.
Proof.
  intros.
  destruct (BofZ_representable _ _ _ Hmax1 n H) as (A & B & C).
  set (f := BofZ prec1 emax1 prec1_gt_0_ Hmax1 n) in *.
  generalize (Bconv_correct conv_nan mode_NE f B).
  unfold BofZ.
  generalize (binary_normalize_correct _ _ _ Hmax2 mode_NE n 0 false).
  fold emin2; fold fexp2. rewrite A.
  replace (F2R {| Fnum := n; Fexp := 0 |}) with (IZR n).
  destruct Rlt_bool.
- intros (P & Q & R) (D & E & F). apply B2R_Bsign_inj; auto.
  congruence. rewrite F, C, R. rewrite Rcompare_IZR.
  unfold Z.ltb. auto.
- intros P Q. apply B2FF_inj. rewrite P, Q. rewrite C. f_equal.
  generalize (Zlt_bool_spec n 0); intros LT; inversion LT.
  rewrite Rlt_bool_true; auto. apply IZR_lt; auto.
  rewrite Rlt_bool_false; auto. apply IZR_le; auto.
- unfold F2R; simpl. rewrite Rmult_1_r. auto.
Qed.

(** Change of format (to higher precision) and conversion to integer. *)

Theorem ZofB_Bconv:
  prec2 >= prec1 -> emax2 >= emax1 ->
  forall conv_nan m f n,
  ZofB _ _ f = Some n -> ZofB _ _ (Bconv conv_nan m f) = Some n.
Proof.
  intros. rewrite ZofB_correct in H1. destruct (is_finite _ _ f) eqn:FIN; inversion H1.
  destruct (Bconv_widen_exact H H0 conv_nan m f) as (A & B & C). auto.
  rewrite ZofB_correct. rewrite B. rewrite A. auto.
Qed.

Theorem ZofB_range_Bconv:
  forall min1 max1 min2 max2,
  prec2 >= prec1 -> emax2 >= emax1 -> min2 <= min1 -> max1 <= max2 ->
  forall conv_nan m f n,
  ZofB_range _ _ f min1 max1 = Some n ->
  ZofB_range _ _ (Bconv conv_nan m f) min2 max2 = Some n.
Proof.
  intros.
  destruct (ZofB_range_inversion _ _ _ _ _ _ H3) as (A & B & C).
  unfold ZofB_range. erewrite ZofB_Bconv by eauto.
  rewrite ! Zle_bool_true by lia. auto.
Qed.

(** Change of format (to higher precision) and comparison. *)

Theorem Bcompare_Bconv_widen:
  prec2 >= prec1 -> emax2 >= emax1 ->
  forall conv_nan m x y,
  Bcompare _ _ (Bconv conv_nan m x) (Bconv conv_nan m y) = Bcompare _ _ x y.
Proof.
  intros. destruct (is_finite _ _ x && is_finite _ _ y) eqn:FIN.
- apply andb_true_iff in FIN. destruct FIN.
  destruct (Bconv_widen_exact H H0 conv_nan m x H1) as (A & B & C).
  destruct (Bconv_widen_exact H H0 conv_nan m y H2) as (D & E & F).
  rewrite ! Bcompare_correct by auto. rewrite A, D. auto.
- generalize (Bconv_widen_exact H H0 conv_nan m x)
             (Bconv_widen_exact H H0 conv_nan m y); intros P Q.
  destruct x as [sx|sx|sx px Hx|sx mx ex Hx], y as [sy|sy|sy py Hy|sy my ey Hy]; try discriminate; simpl in P, Q; simpl;
  repeat (match goal with |- context [conv_nan ?b ?pl] => destruct (conv_nan b pl) end);
  auto.
  destruct Q as (D & E & F); auto.
  now destruct binary_normalize.
  destruct P as (A & B & C); auto.
  now destruct binary_normalize.
  destruct P as (A & B & C); auto.
  now destruct binary_normalize.
Qed.

End Conversions.

Section Compose_Conversions.

Variable prec1 emax1 prec2 emax2 : Z.
Context (prec1_gt_0_ : Prec_gt_0 prec1) (prec2_gt_0_ : Prec_gt_0 prec2).
Let emin1 := (3 - emax1 - prec1)%Z.
Let fexp1 := FLT_exp emin1 prec1.
Let emin2 := (3 - emax2 - prec2)%Z.
Let fexp2 := FLT_exp emin2 prec2.
Hypothesis Hmax1 : (prec1 < emax1)%Z.
Hypothesis Hmax2 : (prec2 < emax2)%Z.
Let binary_float1 := binary_float prec1 emax1.
Let binary_float2 := binary_float prec2 emax2.

(** Converting to a higher precision then down to the original format
    is the identity. *)
Theorem Bconv_narrow_widen:
  prec2 >= prec1 -> emax2 >= emax1 ->
  forall narrow_nan widen_nan m f,
  is_nan _ _ f = false ->
  Bconv prec2 emax2 prec1 emax1 _ Hmax1 narrow_nan m (Bconv prec1 emax1 prec2 emax2 _ Hmax2 widen_nan m f) = f.
Proof.
  intros. destruct (is_finite _ _ f) eqn:FIN.
- assert (EQ: round radix2 fexp1 (round_mode m) (B2R prec1 emax1 f) = B2R prec1 emax1 f).
  { apply round_generic. apply valid_rnd_round_mode. apply generic_format_B2R. }
  generalize (Bconv_widen_exact _ _ _ _ _ _ Hmax2 H H0 widen_nan m f FIN).
  set (f' := Bconv prec1 emax1 prec2 emax2 _ Hmax2 widen_nan m f).
  intros (A & B & C).
  generalize (Bconv_correct _ _ _ _ _ Hmax1 narrow_nan m f' B).
  fold emin1. fold fexp1. rewrite A, C, EQ. rewrite Rlt_bool_true.
  intros (D & E & F).
  apply B2R_Bsign_inj; auto.
  destruct f; try discriminate; simpl.
  rewrite Rabs_R0. apply bpow_gt_0.
  rewrite F2R_cond_Zopp. rewrite abs_cond_Ropp. rewrite <- F2R_Zabs. simpl Z.abs.
  eapply bounded_lt_emax; eauto.
- destruct f; try discriminate. simpl. auto.
Qed.

End Compose_Conversions.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection for integer division *)

Require Import Zquot Coqlib.
Require Import AST Integers Floats Values Memory Globalenvs Events.
Require Import Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong SplitLongproof SelectLong SelectLongproof SelectDiv.

Local Open Scope cminorsel_scope.

(** * Main approximation theorems *)

Section Z_DIV_MUL.

Variable N: Z.      (**r number of relevant bits *)
Hypothesis N_pos: N >= 0.
Variable d: Z.      (**r divisor *)
Hypothesis d_pos: d > 0.

(** This is theorem 4.2 from Granlund and Montgomery, PLDI 1994. *)

Lemma Zdiv_mul_pos:
  forall m l,
  l >= 0 ->
  two_p (N+l) <= m * d <= two_p (N+l) + two_p l ->
  forall n,
  0 <= n < two_p N ->
  Z.div n d = Z.div (m * n) (two_p (N + l)).
Proof.
  intros m l l_pos [LO HI] n RANGE.
  exploit (Z_div_mod_eq n d). auto.
  set (q := n / d).
  set (r := n mod d).
  intro EUCL.
  assert (0 <= r <= d - 1).
    unfold r. generalize (Z_mod_lt n d d_pos). omega.
  assert (0 <= m).
    apply Zmult_le_0_reg_r with d. auto.
    exploit (two_p_gt_ZERO (N + l)). omega. omega.
  set (k := m * d - two_p (N + l)).
  assert (0 <= k <= two_p l).
    unfold k; omega.
  assert ((m * n - two_p (N + l) * q) * d = k * n + two_p (N + l) * r).
    unfold k. rewrite EUCL. ring.
  assert (0 <= k * n).
    apply Z.mul_nonneg_nonneg; omega.
  assert (k * n <= two_p (N + l) - two_p l).
    apply Z.le_trans with (two_p l * n).
    apply Zmult_le_compat_r. omega. omega.
    replace (N + l) with (l + N) by omega.
    rewrite two_p_is_exp.
    replace (two_p l * two_p N - two_p l)
       with (two_p l * (two_p N - 1))
         by ring.
    apply Zmult_le_compat_l. omega. exploit (two_p_gt_ZERO l). omega. omega.
    omega. omega.
  assert (0 <= two_p (N + l) * r).
    apply Z.mul_nonneg_nonneg.
    exploit (two_p_gt_ZERO (N + l)). omega. omega.
    omega.
  assert (two_p (N + l) * r <= two_p (N + l) * d - two_p (N + l)).
    replace (two_p (N + l) * d - two_p (N + l))
       with (two_p (N + l) * (d - 1)) by ring.
    apply Zmult_le_compat_l.
    omega.
    exploit (two_p_gt_ZERO (N + l)). omega. omega.
  assert (0 <= m * n - two_p (N + l) * q).
    apply Zmult_le_reg_r with d. auto.
    replace (0 * d) with 0 by ring.  rewrite H2. omega.
  assert (m * n - two_p (N + l) * q < two_p (N + l)).
    apply Zmult_lt_reg_r with d. omega.
    rewrite H2.
    apply Z.le_lt_trans with (two_p (N + l) * d - two_p l).
    omega.
    exploit (two_p_gt_ZERO l). omega. omega.
  symmetry. apply Zdiv_unique with (m * n - two_p (N + l) * q).
  ring. omega.
Qed.

Lemma Zdiv_unique_2:
  forall x y q, y > 0 -> 0 < y * q - x <= y -> Z.div x y = q - 1.
Proof.
  intros. apply Zdiv_unique with (x - (q - 1) * y). ring.
  replace ((q - 1) * y) with (y * q - y) by ring. omega.
Qed.

Lemma Zdiv_mul_opp:
  forall m l,
  l >= 0 ->
  two_p (N+l) < m * d <= two_p (N+l) + two_p l ->
  forall n,
  0 < n <= two_p N ->
  Z.div n d = - Z.div (m * (-n)) (two_p (N + l)) - 1.
Proof.
  intros m l l_pos [LO HI] n RANGE.
  replace (m * (-n)) with (- (m * n)) by ring.
  exploit (Z_div_mod_eq n d). auto.
  set (q := n / d).
  set (r := n mod d).
  intro EUCL.
  assert (0 <= r <= d - 1).
    unfold r. generalize (Z_mod_lt n d d_pos). omega.
  assert (0 <= m).
    apply Zmult_le_0_reg_r with d. auto.
    exploit (two_p_gt_ZERO (N + l)). omega. omega.
  cut (Z.div (- (m * n)) (two_p (N + l)) = -q - 1).
    omega.
  apply Zdiv_unique_2.
  apply two_p_gt_ZERO. omega.
  replace (two_p (N + l) * - q - - (m * n))
     with (m * n - two_p (N + l) * q)
       by ring.
  set (k := m * d - two_p (N + l)).
  assert (0 < k <= two_p l).
    unfold k; omega.
  assert ((m * n - two_p (N + l) * q) * d = k * n + two_p (N + l) * r).
    unfold k. rewrite EUCL. ring.
  split.
  apply Zmult_lt_reg_r with d. omega.
  replace (0 * d) with 0 by omega.
  rewrite H2.
  assert (0 < k * n). apply Z.mul_pos_pos; omega.
  assert (0 <= two_p (N + l) * r).
    apply Z.mul_nonneg_nonneg. exploit (two_p_gt_ZERO (N + l)); omega. omega.
  omega.
  apply Zmult_le_reg_r with d. omega.
  rewrite H2.
  assert (k * n <= two_p (N + l)).
    rewrite Z.add_comm. rewrite two_p_is_exp; try omega.
    apply Z.le_trans with (two_p l * n). apply Zmult_le_compat_r. omega. omega.
    apply Zmult_le_compat_l. omega. exploit (two_p_gt_ZERO l). omega. omega.
  assert (two_p (N + l) * r <= two_p (N + l) * d - two_p (N + l)).
    replace (two_p (N + l) * d - two_p (N + l))
       with (two_p (N + l) * (d - 1))
         by ring.
    apply Zmult_le_compat_l. omega. exploit (two_p_gt_ZERO (N + l)). omega. omega.
  omega.
Qed.

(** This is theorem 5.1 from Granlund and Montgomery, PLDI 1994. *)

Lemma Zquot_mul:
  forall m l,
  l >= 0 ->
  two_p (N+l) < m * d <= two_p (N+l) + two_p l ->
  forall n,
  - two_p N <= n < two_p N ->
  Z.quot n d = Z.div (m * n) (two_p (N + l)) + (if zlt n 0 then 1 else 0).
Proof.
  intros. destruct (zlt n 0).
  exploit (Zdiv_mul_opp m l H H0 (-n)). omega.
  replace (- - n) with n by ring.
  replace (Z.quot n d) with (- Z.quot (-n) d).
  rewrite Zquot_Zdiv_pos by omega. omega.
  rewrite Z.quot_opp_l by omega. ring.
  rewrite Z.add_0_r. rewrite Zquot_Zdiv_pos by omega.
  apply Zdiv_mul_pos; omega.
Qed.

End Z_DIV_MUL.

(** * Correctness of the division parameters *)

Lemma divs_mul_params_sound:
  forall d m p,
  divs_mul_params d = Some(p, m) ->
  0 <= m < Int.modulus /\ 0 <= p < 32 /\
  forall n,
  Int.min_signed <= n <= Int.max_signed ->
  Z.quot n d = Z.div (m * n) (two_p (32 + p)) + (if zlt n 0 then 1 else 0).
Proof with (try discriminate).
  unfold divs_mul_params; intros d m' p'.
  destruct (find_div_mul_params Int.wordsize
               (Int.half_modulus - Int.half_modulus mod d - 1) d 32)
  as [[p m] | ]...
  generalize (p - 32). intro p1.
  destruct (zlt 0 d)...
  destruct (zlt (two_p (32 + p1)) (m * d))...
  destruct (zle (m * d) (two_p (32 + p1) + two_p (p1 + 1)))...
  destruct (zle 0 m)...
  destruct (zlt m Int.modulus)...
  destruct (zle 0 p1)...
  destruct (zlt p1 32)...
  intros EQ; inv EQ.
  split. auto. split. auto. intros.
  replace (32 + p') with (31 + (p' + 1)) by omega.
  apply Zquot_mul; try omega.
  replace (31 + (p' + 1)) with (32 + p') by omega. omega.
  change (Int.min_signed <= n < Int.half_modulus).
  unfold Int.max_signed in H. omega.
Qed.

Lemma divu_mul_params_sound:
  forall d m p,
  divu_mul_params d = Some(p, m) ->
  0 <= m < Int.modulus /\ 0 <= p < 32 /\
  forall n,
  0 <= n < Int.modulus ->
  Z.div n d = Z.div (m * n) (two_p (32 + p)).
Proof with (try discriminate).
  unfold divu_mul_params; intros d m' p'.
  destruct (find_div_mul_params Int.wordsize
               (Int.modulus - Int.modulus mod d - 1) d 32)
  as [[p m] | ]...
  generalize (p - 32); intro p1.
  destruct (zlt 0 d)...
  destruct (zle (two_p (32 + p1)) (m * d))...
  destruct (zle (m * d) (two_p (32 + p1) + two_p p1))...
  destruct (zle 0 m)...
  destruct (zlt m Int.modulus)...
  destruct (zle 0 p1)...
  destruct (zlt p1 32)...
  intros EQ; inv EQ.
  split. auto. split. auto. intros.
  apply Zdiv_mul_pos; try omega. assumption.
Qed.

Lemma divs_mul_shift_gen:
  forall x y m p,
  divs_mul_params (Int.signed y) = Some(p, m) ->
  0 <= m < Int.modulus /\ 0 <= p < 32 /\
  Int.divs x y = Int.add (Int.shr (Int.repr ((Int.signed x * m) / Int.modulus)) (Int.repr p))
                         (Int.shru x (Int.repr 31)).
Proof.
  intros. set (n := Int.signed x). set (d := Int.signed y) in *.
  exploit divs_mul_params_sound; eauto. intros (A & B & C).
  split. auto. split. auto.
  unfold Int.divs. fold n; fold d. rewrite C by (apply Int.signed_range).
  rewrite two_p_is_exp by omega. rewrite <- Zdiv_Zdiv.
  rewrite Int.shru_lt_zero. unfold Int.add. apply Int.eqm_samerepr. apply Int.eqm_add.
  rewrite Int.shr_div_two_p. apply Int.eqm_unsigned_repr_r. apply Int.eqm_refl2.
  rewrite Int.unsigned_repr. f_equal.
  rewrite Int.signed_repr. rewrite Int.modulus_power. f_equal. ring.
  cut (Int.min_signed <= n * m / Int.modulus < Int.half_modulus).
  unfold Int.max_signed; omega.
  apply Zdiv_interval_1. generalize Int.min_signed_neg; omega. apply Int.half_modulus_pos.
  apply Int.modulus_pos.
  split. apply Z.le_trans with (Int.min_signed * m). apply Zmult_le_compat_l_neg. omega. generalize Int.min_signed_neg; omega.
  apply Zmult_le_compat_r. unfold n; generalize (Int.signed_range x); tauto. tauto.
  apply Z.le_lt_trans with (Int.half_modulus * m).
  apply Zmult_le_compat_r. generalize (Int.signed_range x); unfold n, Int.max_signed; omega. tauto.
  apply Zmult_lt_compat_l. generalize Int.half_modulus_pos; omega. tauto.
  assert (32 < Int.max_unsigned) by (compute; auto). omega.
  unfold Int.lt; fold n. rewrite Int.signed_zero. destruct (zlt n 0); apply Int.eqm_unsigned_repr.
  apply two_p_gt_ZERO. omega.
  apply two_p_gt_ZERO. omega.
Qed.

Theorem divs_mul_shift_1:
  forall x y m p,
  divs_mul_params (Int.signed y) = Some(p, m) ->
  m < Int.half_modulus ->
  0 <= p < 32 /\
  Int.divs x y = Int.add (Int.shr (Int.mulhs x (Int.repr m)) (Int.repr p))
                         (Int.shru x (Int.repr 31)).
Proof.
  intros. exploit divs_mul_shift_gen; eauto. instantiate (1 := x).
  intros (A & B & C). split. auto. rewrite C.
  unfold Int.mulhs. rewrite Int.signed_repr. auto.
  generalize Int.min_signed_neg; unfold Int.max_signed; omega.
Qed.

Theorem divs_mul_shift_2:
  forall x y m p,
  divs_mul_params (Int.signed y) = Some(p, m) ->
  m >= Int.half_modulus ->
  0 <= p < 32 /\
  Int.divs x y = Int.add (Int.shr (Int.add (Int.mulhs x (Int.repr m)) x) (Int.repr p))
                         (Int.shru x (Int.repr 31)).
Proof.
  intros. exploit divs_mul_shift_gen; eauto. instantiate (1 := x).
  intros (A & B & C). split. auto. rewrite C. f_equal. f_equal.
  rewrite Int.add_signed. unfold Int.mulhs. set (n := Int.signed x).
  transitivity (Int.repr (n * (m - Int.modulus) / Int.modulus + n)).
  apply f_equal.
  replace (n * (m - Int.modulus)) with (n * m +  (-n) * Int.modulus) by ring.
  rewrite Z_div_plus. ring. apply Int.modulus_pos.
  apply Int.eqm_samerepr. apply Int.eqm_add; auto with ints.
  apply Int.eqm_sym. eapply Int.eqm_trans. apply Int.eqm_signed_unsigned.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl2.
  apply (f_equal (fun x => n * x / Int.modulus)).
  rewrite Int.signed_repr_eq. rewrite Zmod_small by assumption.
  apply zlt_false. assumption.
Qed.

Theorem divu_mul_shift:
  forall x y m p,
  divu_mul_params (Int.unsigned y) = Some(p, m) ->
  0 <= p < 32 /\
  Int.divu x y = Int.shru (Int.mulhu x (Int.repr m)) (Int.repr p).
Proof.
  intros. exploit divu_mul_params_sound; eauto. intros (A & B & C).
  split. auto.
  rewrite Int.shru_div_two_p. rewrite Int.unsigned_repr.
  unfold Int.divu, Int.mulhu. f_equal. rewrite C by apply Int.unsigned_range.
  rewrite two_p_is_exp by omega. rewrite <- Zdiv_Zdiv by (apply two_p_gt_ZERO; omega).
  f_equal. rewrite (Int.unsigned_repr m).
  rewrite Int.unsigned_repr. f_equal. ring.
  cut (0 <= Int.unsigned x * m / Int.modulus < Int.modulus).
  unfold Int.max_unsigned; omega.
  apply Zdiv_interval_1. omega. compute; auto. compute; auto.
  split. simpl. apply Z.mul_nonneg_nonneg. generalize (Int.unsigned_range x); omega. omega.
  apply Z.le_lt_trans with (Int.modulus * m).
  apply Zmult_le_compat_r. generalize (Int.unsigned_range x); omega. omega.
  apply Zmult_lt_compat_l. compute; auto. omega.
  unfold Int.max_unsigned; omega.
  assert (32 < Int.max_unsigned) by (compute; auto). omega.
Qed.

(** Same, for 64-bit integers *)

Lemma divls_mul_params_sound:
  forall d m p,
  divls_mul_params d = Some(p, m) ->
  0 <= m < Int64.modulus /\ 0 <= p < 64 /\
  forall n,
  Int64.min_signed <= n <= Int64.max_signed ->
  Z.quot n d = Z.div (m * n) (two_p (64 + p)) + (if zlt n 0 then 1 else 0).
Proof with (try discriminate).
  unfold divls_mul_params; intros d m' p'.
  destruct (find_div_mul_params Int64.wordsize
               (Int64.half_modulus - Int64.half_modulus mod d - 1) d 64)
  as [[p m] | ]...
  generalize (p - 64). intro p1.
  destruct (zlt 0 d)...
  destruct (zlt (two_p (64 + p1)) (m * d))...
  destruct (zle (m * d) (two_p (64 + p1) + two_p (p1 + 1)))...
  destruct (zle 0 m)...
  destruct (zlt m Int64.modulus)...
  destruct (zle 0 p1)...
  destruct (zlt p1 64)...
  intros EQ; inv EQ.
  split. auto. split. auto. intros.
  replace (64 + p') with (63 + (p' + 1)) by omega.
  apply Zquot_mul; try omega.
  replace (63 + (p' + 1)) with (64 + p') by omega. omega.
  change (Int64.min_signed <= n < Int64.half_modulus).
  unfold Int64.max_signed in H. omega.
Qed.

Lemma divlu_mul_params_sound:
  forall d m p,
  divlu_mul_params d = Some(p, m) ->
  0 <= m < Int64.modulus /\ 0 <= p < 64 /\
  forall n,
  0 <= n < Int64.modulus ->
  Z.div n d = Z.div (m * n) (two_p (64 + p)).
Proof with (try discriminate).
  unfold divlu_mul_params; intros d m' p'.
  destruct (find_div_mul_params Int64.wordsize
               (Int64.modulus - Int64.modulus mod d - 1) d 64)
  as [[p m] | ]...
  generalize (p - 64); intro p1.
  destruct (zlt 0 d)...
  destruct (zle (two_p (64 + p1)) (m * d))...
  destruct (zle (m * d) (two_p (64 + p1) + two_p p1))...
  destruct (zle 0 m)...
  destruct (zlt m Int64.modulus)...
  destruct (zle 0 p1)...
  destruct (zlt p1 64)...
  intros EQ; inv EQ.
  split. auto. split. auto. intros.
  apply Zdiv_mul_pos; try omega. assumption.
Qed.

Remark int64_shr'_div_two_p:
  forall x y, Int64.shr' x y = Int64.repr (Int64.signed x / two_p (Int.unsigned y)).
Proof.
  intros; unfold Int64.shr'. rewrite Int64.Zshiftr_div_two_p; auto. generalize (Int.unsigned_range y); omega.
Qed.

Lemma divls_mul_shift_gen:
  forall x y m p,
  divls_mul_params (Int64.signed y) = Some(p, m) ->
  0 <= m < Int64.modulus /\ 0 <= p < 64 /\
  Int64.divs x y = Int64.add (Int64.shr' (Int64.repr ((Int64.signed x * m) / Int64.modulus)) (Int.repr p))
                             (Int64.shru x (Int64.repr 63)).
Proof.
  intros. set (n := Int64.signed x). set (d := Int64.signed y) in *.
  exploit divls_mul_params_sound; eauto. intros (A & B & C).
  split. auto. split. auto.
  unfold Int64.divs. fold n; fold d. rewrite C by (apply Int64.signed_range).
  rewrite two_p_is_exp by omega. rewrite <- Zdiv_Zdiv.
  rewrite Int64.shru_lt_zero. unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add.
  rewrite int64_shr'_div_two_p. apply Int64.eqm_unsigned_repr_r. apply Int64.eqm_refl2.
  rewrite Int.unsigned_repr. f_equal.
  rewrite Int64.signed_repr. rewrite Int64.modulus_power. f_equal. ring.
  cut (Int64.min_signed <= n * m / Int64.modulus < Int64.half_modulus).
  unfold Int64.max_signed; omega.
  apply Zdiv_interval_1. generalize Int64.min_signed_neg; omega. apply Int64.half_modulus_pos.
  apply Int64.modulus_pos.
  split. apply Z.le_trans with (Int64.min_signed * m). apply Zmult_le_compat_l_neg. omega. generalize Int64.min_signed_neg; omega.
  apply Zmult_le_compat_r. unfold n; generalize (Int64.signed_range x); tauto. tauto.
  apply Z.le_lt_trans with (Int64.half_modulus * m).
  apply Zmult_le_compat_r. generalize (Int64.signed_range x); unfold n, Int64.max_signed; omega. tauto.
  apply Zmult_lt_compat_l. generalize Int64.half_modulus_pos; omega. tauto.
  assert (64 < Int.max_unsigned) by (compute; auto). omega.
  unfold Int64.lt; fold n. rewrite Int64.signed_zero. destruct (zlt n 0); apply Int64.eqm_unsigned_repr.
  apply two_p_gt_ZERO. omega.
  apply two_p_gt_ZERO. omega.
Qed.

Theorem divls_mul_shift_1:
  forall x y m p,
  divls_mul_params (Int64.signed y) = Some(p, m) ->
  m < Int64.half_modulus ->
  0 <= p < 64 /\
  Int64.divs x y = Int64.add (Int64.shr' (Int64.mulhs x (Int64.repr m)) (Int.repr p))
                             (Int64.shru' x (Int.repr 63)).
Proof.
  intros. exploit divls_mul_shift_gen; eauto. instantiate (1 := x).
  intros (A & B & C). split. auto. rewrite C.
  unfold Int64.mulhs. rewrite Int64.signed_repr. auto.
  generalize Int64.min_signed_neg; unfold Int64.max_signed; omega.
Qed.

Theorem divls_mul_shift_2:
  forall x y m p,
  divls_mul_params (Int64.signed y) = Some(p, m) ->
  m >= Int64.half_modulus ->
  0 <= p < 64 /\
  Int64.divs x y = Int64.add (Int64.shr' (Int64.add (Int64.mulhs x (Int64.repr m)) x) (Int.repr p))
                             (Int64.shru' x (Int.repr 63)).
Proof.
  intros. exploit divls_mul_shift_gen; eauto. instantiate (1 := x).
  intros (A & B & C). split. auto. rewrite C. f_equal. f_equal.
  rewrite Int64.add_signed. unfold Int64.mulhs. set (n := Int64.signed x).
  transitivity (Int64.repr (n * (m - Int64.modulus) / Int64.modulus + n)).
  apply f_equal.
  replace (n * (m - Int64.modulus)) with (n * m +  (-n) * Int64.modulus) by ring.
  rewrite Z_div_plus. ring. apply Int64.modulus_pos.
  apply Int64.eqm_samerepr. apply Int64.eqm_add; auto with ints.
  apply Int64.eqm_sym. eapply Int64.eqm_trans. apply Int64.eqm_signed_unsigned.
  apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl2.
  apply (f_equal (fun x => n * x / Int64.modulus)).
  rewrite Int64.signed_repr_eq. rewrite Zmod_small by assumption.
  apply zlt_false. assumption.
Qed.

Remark int64_shru'_div_two_p:
  forall x y, Int64.shru' x y = Int64.repr (Int64.unsigned x / two_p (Int.unsigned y)).
Proof.
  intros; unfold Int64.shru'. rewrite Int64.Zshiftr_div_two_p; auto. generalize (Int.unsigned_range y); omega.
Qed.

Theorem divlu_mul_shift:
  forall x y m p,
  divlu_mul_params (Int64.unsigned y) = Some(p, m) ->
  0 <= p < 64 /\
  Int64.divu x y = Int64.shru' (Int64.mulhu x (Int64.repr m)) (Int.repr p).
Proof.
  intros. exploit divlu_mul_params_sound; eauto. intros (A & B & C).
  split. auto.
  rewrite int64_shru'_div_two_p. rewrite Int.unsigned_repr.
  unfold Int64.divu, Int64.mulhu. f_equal. rewrite C by apply Int64.unsigned_range.
  rewrite two_p_is_exp by omega. rewrite <- Zdiv_Zdiv by (apply two_p_gt_ZERO; omega).
  f_equal. rewrite (Int64.unsigned_repr m).
  rewrite Int64.unsigned_repr. f_equal. ring.
  cut (0 <= Int64.unsigned x * m / Int64.modulus < Int64.modulus).
  unfold Int64.max_unsigned; omega.
  apply Zdiv_interval_1. omega. compute; auto. compute; auto.
  split. simpl. apply Z.mul_nonneg_nonneg. generalize (Int64.unsigned_range x); omega. omega.
  apply Z.le_lt_trans with (Int64.modulus * m).
  apply Zmult_le_compat_r. generalize (Int64.unsigned_range x); omega. omega.
  apply Zmult_lt_compat_l. compute; auto. omega.
  unfold Int64.max_unsigned; omega.
  assert (64 < Int.max_unsigned) by (compute; auto). omega.
Qed.

(** * Correctness of the smart constructors for division and modulus *)

Section CMCONSTRS.

Variable prog: program.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared prog hf.
Let ge := Genv.globalenv prog.
Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma is_intconst_sound:
  forall v a n le,
  is_intconst a = Some n -> eval_expr ge sp e m le a v -> v = Vint n.
Proof with (try discriminate).
  intros. unfold is_intconst in *.
  destruct a... destruct o... inv H. inv H0. destruct vl; inv H5. auto.
Qed.

Lemma eval_divu_mul:
  forall le x y p M,
  divu_mul_params (Int.unsigned y) = Some(p, M) ->
  nth_error le O = Some (Vint x) ->
  eval_expr ge sp e m le (divu_mul p M) (Vint (Int.divu x y)).
Proof.
  intros. unfold divu_mul. exploit (divu_mul_shift x); eauto. intros [A B].
  assert (C: eval_expr ge sp e m le (Eletvar 0) (Vint x)) by (apply eval_Eletvar; eauto).
  assert (D: eval_expr ge sp e m le (Eop (Ointconst (Int.repr M)) Enil) (Vint (Int.repr M))) by EvalOp.
  exploit eval_mulhu. eexact C. eexact D. intros (v & E & F). simpl in F. inv F. 
  exploit eval_shruimm. eexact E. instantiate (1 := Int.repr p).
  intros [v [P Q]]. simpl in Q.
  replace (Int.ltu (Int.repr p) Int.iwordsize) with true in Q.
  inv Q. rewrite B. auto.
  unfold Int.ltu. rewrite Int.unsigned_repr. rewrite zlt_true; auto. tauto.
  assert (32 < Int.max_unsigned) by (compute; auto). omega.
Qed.

Theorem eval_divuimm:
  forall le e1 x n2 z,
  eval_expr ge sp e m le e1 x ->
  Val.divu x (Vint n2) = Some z ->
  exists v, eval_expr ge sp e m le (divuimm e1 n2) v /\ Val.lessdef z v.
Proof.
  unfold divuimm; intros. generalize H0; intros DIV.
  destruct x; simpl in DIV; try discriminate.
  destruct (Int.eq n2 Int.zero) eqn:Z2; inv DIV.
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
- erewrite Int.divu_pow2 by eauto.
  replace (Vint (Int.shru i l)) with (Val.shru (Vint i) (Vint l)).
  apply eval_shruimm; auto.
  simpl. erewrite Int.is_power2_range; eauto.
- destruct (Compopts.optim_for_size tt).
  + eapply eval_divu_base; eauto. EvalOp.
  + destruct (divu_mul_params (Int.unsigned n2)) as [[p M] | ] eqn:PARAMS.
    * exists (Vint (Int.divu i n2)); split; auto.
      econstructor; eauto. eapply eval_divu_mul; eauto.
    * eapply eval_divu_base; eauto. EvalOp.
Qed.

Theorem eval_divu:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divu x y = Some z ->
  exists v, eval_expr ge sp e m le (divu a b) v /\ Val.lessdef z v.
Proof.
  unfold divu; intros.
  destruct (is_intconst b) as [n2|] eqn:B.
- exploit is_intconst_sound; eauto. intros EB; clear B.
  destruct (is_intconst a) as [n1|] eqn:A.
+ exploit is_intconst_sound; eauto. intros EA; clear A.
  destruct (Int.eq n2 Int.zero) eqn:Z. eapply eval_divu_base; eauto. 
  subst. simpl in H1. rewrite Z in H1; inv H1.
  TrivialExists.
+ subst. eapply eval_divuimm; eauto.
- eapply eval_divu_base; eauto.
Qed.

Lemma eval_mod_from_div:
  forall le a n x y,
  eval_expr ge sp e m le a (Vint y) ->
  nth_error le O = Some (Vint x) ->
  eval_expr ge sp e m le (mod_from_div a n) (Vint (Int.sub x (Int.mul y n))).
Proof.
  unfold mod_from_div; intros.
  exploit eval_mulimm; eauto. instantiate (1 := n). intros [v [A B]].
  simpl in B. inv B. EvalOp.
Qed.

Theorem eval_moduimm:
  forall le e1 x n2 z,
  eval_expr ge sp e m le e1 x ->
  Val.modu x (Vint n2) = Some z ->
  exists v, eval_expr ge sp e m le (moduimm e1 n2) v /\ Val.lessdef z v.
Proof.
  unfold moduimm; intros. generalize H0; intros MOD.
  destruct x; simpl in MOD; try discriminate.
  destruct (Int.eq n2 Int.zero) eqn:Z2; inv MOD.
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
- erewrite Int.modu_and by eauto.
  change (Vint (Int.and i (Int.sub n2 Int.one)))
    with (Val.and (Vint i) (Vint (Int.sub n2 Int.one))).
  apply eval_andimm. auto.
- destruct (Compopts.optim_for_size tt).
  + eapply eval_modu_base; eauto. EvalOp.
  + destruct (divu_mul_params (Int.unsigned n2)) as [[p M] | ] eqn:PARAMS.
    * econstructor; split.
      econstructor; eauto. eapply eval_mod_from_div.
      eapply eval_divu_mul; eauto. simpl; eauto. simpl; eauto.
      rewrite Int.modu_divu. auto.
      red; intros; subst n2; discriminate.
    * eapply eval_modu_base; eauto. EvalOp.
Qed.

Theorem eval_modu:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modu x y = Some z ->
  exists v, eval_expr ge sp e m le (modu a b) v /\ Val.lessdef z v.
Proof.
  unfold modu; intros.
  destruct (is_intconst b) as [n2|] eqn:B.
- exploit is_intconst_sound; eauto. intros EB; clear B.
  destruct (is_intconst a) as [n1|] eqn:A.
+ exploit is_intconst_sound; eauto. intros EA; clear A.
  destruct (Int.eq n2 Int.zero) eqn:Z. eapply eval_modu_base; eauto. 
  subst. simpl in H1. rewrite Z in H1; inv H1.
  TrivialExists.
+ subst. eapply eval_moduimm; eauto.
- eapply eval_modu_base; eauto.
Qed.

Lemma eval_divs_mul:
  forall le x y p M,
  divs_mul_params (Int.signed y) = Some(p, M) ->
  nth_error le O = Some (Vint x) ->
  eval_expr ge sp e m le (divs_mul p M) (Vint (Int.divs x y)).
Proof.
  intros. unfold divs_mul.
  assert (C: eval_expr ge sp e m le (Eletvar 0) (Vint x)) by (apply eval_Eletvar; eauto).
  assert (D: eval_expr ge sp e m le (Eop (Ointconst (Int.repr M)) Enil) (Vint (Int.repr M))) by EvalOp.
  exploit eval_mulhs. eexact C. eexact D. intros (v & X & F). simpl in F; inv F.
  exploit eval_shruimm. eexact C. instantiate (1 := Int.repr (Int.zwordsize - 1)).
  intros [v1 [Y LD]]. simpl in LD.
  change (Int.ltu (Int.repr 31) Int.iwordsize) with true in LD.
  simpl in LD. inv LD.
  assert (RANGE: 0 <= p < 32 -> Int.ltu (Int.repr p) Int.iwordsize = true).
  { intros. unfold Int.ltu. rewrite Int.unsigned_repr. rewrite zlt_true by tauto. auto.
    assert (32 < Int.max_unsigned) by (compute; auto). omega. }
  destruct (zlt M Int.half_modulus).
- exploit (divs_mul_shift_1 x); eauto. intros [A B].
  exploit eval_shrimm. eexact X. instantiate (1 := Int.repr p). intros [v1 [Z LD]].
  simpl in LD. rewrite RANGE in LD by auto. inv LD.
  exploit eval_add. eexact Z. eexact Y. intros [v1 [W LD]].
  simpl in LD. inv LD.
  rewrite B. exact W.
- exploit (divs_mul_shift_2 x); eauto. intros [A B].
  exploit eval_add. eexact X. eexact C. intros [v1 [Z LD]].
  simpl in LD. inv LD.
  exploit eval_shrimm. eexact Z. instantiate (1 := Int.repr p). intros [v1 [U LD]].
  simpl in LD. rewrite RANGE in LD by auto. inv LD.
  exploit eval_add. eexact U. eexact Y. intros [v1 [W LD]].
  simpl in LD. inv LD.
  rewrite B. exact W.
Qed.

Theorem eval_divsimm:
  forall le e1 x n2 z,
  eval_expr ge sp e m le e1 x ->
  Val.divs x (Vint n2) = Some z ->
  exists v, eval_expr ge sp e m le (divsimm e1 n2) v /\ Val.lessdef z v.
Proof.
  unfold divsimm; intros. generalize H0; intros DIV.
  destruct x; simpl in DIV; try discriminate.
  destruct (Int.eq n2 Int.zero
            || Int.eq i (Int.repr Int.min_signed) && Int.eq n2 Int.mone) eqn:Z2; inv DIV.
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
- destruct (Int.ltu l (Int.repr 31)) eqn:LT31.
  + eapply eval_shrximm; eauto. eapply Val.divs_pow2; eauto.
  + eapply eval_divs_base; eauto. EvalOp.
- destruct (Compopts.optim_for_size tt).
  + eapply eval_divs_base; eauto. EvalOp.
  + destruct (divs_mul_params (Int.signed n2)) as [[p M] | ] eqn:PARAMS.
    * exists (Vint (Int.divs i n2)); split; auto.
      econstructor; eauto. eapply eval_divs_mul; eauto.
    * eapply eval_divs_base; eauto. EvalOp.
Qed.

Theorem eval_divs:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divs x y = Some z ->
  exists v, eval_expr ge sp e m le (divs a b) v /\ Val.lessdef z v.
Proof.
  unfold divs; intros.
  destruct (is_intconst b) as [n2|] eqn:B.
- exploit is_intconst_sound; eauto. intros EB; clear B.
  destruct (is_intconst a) as [n1|] eqn:A.
+ exploit is_intconst_sound; eauto. intros EA; clear A.
  destruct (Int.eq n2 Int.zero) eqn:Z. eapply eval_divs_base; eauto.
  subst. simpl in H1. 
  destruct (Int.eq n2 Int.zero || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); inv H1.
  TrivialExists.
+ subst. eapply eval_divsimm; eauto.
- eapply eval_divs_base; eauto.
Qed.

Theorem eval_modsimm:
  forall le e1 x n2 z,
  eval_expr ge sp e m le e1 x ->
  Val.mods x (Vint n2) = Some z ->
  exists v, eval_expr ge sp e m le (modsimm e1 n2) v /\ Val.lessdef z v.
Proof.
  unfold modsimm; intros.
  exploit Val.mods_divs; eauto. intros [y [A B]].
  generalize A; intros DIV.
  destruct x; simpl in DIV; try discriminate.
  destruct (Int.eq n2 Int.zero
            || Int.eq i (Int.repr Int.min_signed) && Int.eq n2 Int.mone) eqn:Z2; inv DIV.
  destruct (Int.is_power2 n2) as [l | ] eqn:P2.
- destruct (Int.ltu l (Int.repr 31)) eqn:LT31.
  + exploit (eval_shrximm ge sp e m (Vint i :: le) (Eletvar O)).
    constructor. simpl; eauto. eapply Val.divs_pow2; eauto.
    intros [v1 [X LD]]. inv LD.
    econstructor; split. econstructor. eauto.
    apply eval_mod_from_div. eexact X. simpl; eauto.
    simpl. auto.
  + eapply eval_mods_base; eauto. EvalOp.
- destruct (Compopts.optim_for_size tt).
  + eapply eval_mods_base; eauto. EvalOp.
  + destruct (divs_mul_params (Int.signed n2)) as [[p M] | ] eqn:PARAMS.
    * econstructor; split.
      econstructor. eauto. apply eval_mod_from_div with (x := i); auto.
      eapply eval_divs_mul with (x := i); eauto.
      simpl. auto.
    * eapply eval_mods_base; eauto. EvalOp.
Qed.

Theorem eval_mods:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.mods x y = Some z ->
  exists v, eval_expr ge sp e m le (mods a b) v /\ Val.lessdef z v.
Proof.
  unfold mods; intros.
  destruct (is_intconst b) as [n2|] eqn:B.
- exploit is_intconst_sound; eauto. intros EB; clear B.
  destruct (is_intconst a) as [n1|] eqn:A.
+ exploit is_intconst_sound; eauto. intros EA; clear A.
  destruct (Int.eq n2 Int.zero) eqn:Z. eapply eval_mods_base; eauto.
  subst. simpl in H1. 
  destruct (Int.eq n2 Int.zero || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); inv H1.
  TrivialExists.
+ subst. eapply eval_modsimm; eauto.
- eapply eval_mods_base; eauto.
Qed.

Lemma eval_modl_from_divl:
  forall le a n x y,
  eval_expr ge sp e m le a (Vlong y) ->
  nth_error le O = Some (Vlong x) ->
  eval_expr ge sp e m le (modl_from_divl a n) (Vlong (Int64.sub x (Int64.mul y n))).
Proof.
  unfold modl_from_divl; intros.
  exploit eval_mullimm; eauto. instantiate (1 := n). intros (v1 & A1 & B1).
  assert (A0: eval_expr ge sp e m le (Eletvar O) (Vlong x)) by (constructor; auto).
  exploit eval_subl ; auto ; try apply HELPERS. exact A0. exact A1.
  intros (v2 & A2 & B2).
  simpl in B1; inv B1. simpl in B2; inv B2. exact A2.
Qed.

Lemma eval_divlu_mull:
  forall le x y p M,
  divlu_mul_params (Int64.unsigned y) = Some(p, M) ->
  nth_error le O = Some (Vlong x) ->
  eval_expr ge sp e m le (divlu_mull p M) (Vlong (Int64.divu x y)).
Proof.
  intros. unfold divlu_mull. exploit (divlu_mul_shift x); eauto. intros [A B].
  assert (A0: eval_expr ge sp e m le (Eletvar O) (Vlong x)) by (constructor; auto).
  exploit eval_mullhu. eauto. eexact A0. instantiate (1 := Int64.repr M). intros (v1 & A1 & B1).
  exploit eval_shrluimm. eauto. eexact A1. instantiate (1 := Int.repr p). intros (v2 & A2 & B2).
  simpl in B1; inv B1. simpl in B2. replace (Int.ltu (Int.repr p) Int64.iwordsize') with true in B2. inv B2.
  rewrite B. assumption.
  unfold Int.ltu. rewrite Int.unsigned_repr. rewrite zlt_true; auto. tauto.
  assert (64 < Int.max_unsigned) by (compute; auto). omega.
Qed.

Theorem eval_divlu:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divlu x y = Some z ->
  exists v, eval_expr ge sp e m le (divlu a b) v /\ Val.lessdef z v.
Proof.
  unfold divlu; intros.
  destruct (is_longconst b) as [n2|] eqn:N2.
- assert (y = Vlong n2) by (eapply is_longconst_sound; eauto). subst y.
  destruct (is_longconst a) as [n1|] eqn:N1.
+ assert (x = Vlong n1) by (eapply is_longconst_sound; eauto). subst x.
  simpl in H1. destruct (Int64.eq n2 Int64.zero); inv H1.
  econstructor; split. apply eval_longconst. constructor.
+ destruct (Int64.is_power2' n2) as [l|] eqn:POW.
* exploit Val.divlu_pow2; eauto. intros EQ; subst z. apply eval_shrluimm; auto.
* destruct (Compopts.optim_for_size tt). eapply eval_divlu_base; eauto.
  destruct (divlu_mul_params (Int64.unsigned n2)) as [[p M]|] eqn:PARAMS.
** destruct x; simpl in H1; try discriminate.
   destruct (Int64.eq n2 Int64.zero); inv H1.
   econstructor; split; eauto. econstructor. eauto. eapply eval_divlu_mull; eauto.
** eapply eval_divlu_base; eauto.
- eapply eval_divlu_base; eauto.
Qed.

Theorem eval_modlu:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modlu x y = Some z ->
  exists v, eval_expr ge sp e m le (modlu a b) v /\ Val.lessdef z v.
Proof.
  unfold modlu; intros.
  destruct (is_longconst b) as [n2|] eqn:N2.
- assert (y = Vlong n2) by (eapply is_longconst_sound; eauto). subst y.
  destruct (is_longconst a) as [n1|] eqn:N1.
+ assert (x = Vlong n1) by (eapply is_longconst_sound; eauto). subst x.
  simpl in H1. destruct (Int64.eq n2 Int64.zero); inv H1.
  econstructor; split. apply eval_longconst. constructor.
+ destruct (Int64.is_power2 n2) as [l|] eqn:POW.
* exploit Val.modlu_pow2; eauto. intros EQ; subst z. eapply eval_andl; eauto. apply eval_longconst.
* destruct (Compopts.optim_for_size tt). eapply eval_modlu_base; eauto.
  destruct (divlu_mul_params (Int64.unsigned n2)) as [[p M]|] eqn:PARAMS.
** destruct x; simpl in H1; try discriminate.
   destruct (Int64.eq n2 Int64.zero) eqn:Z; inv H1.
   rewrite Int64.modu_divu.
    econstructor; split; eauto. econstructor. eauto.
    eapply eval_modl_from_divl; eauto.
    eapply eval_divlu_mull; eauto.
    red; intros; subst n2; discriminate Z.
** eapply eval_modlu_base; eauto.
- eapply eval_modlu_base; eauto.
Qed.

Lemma eval_divls_mull:
  forall le x y p M,
  divls_mul_params (Int64.signed y) = Some(p, M) ->
  nth_error le O = Some (Vlong x) ->
  eval_expr ge sp e m le (divls_mull p M) (Vlong (Int64.divs x y)).
Proof.
  intros. unfold divls_mull.
  assert (A0: eval_expr ge sp e m le (Eletvar O) (Vlong x)).
  { constructor; auto. }
  exploit eval_mullhs. eauto. eexact A0. instantiate (1 := Int64.repr M).  intros (v1 & A1 & B1).
  exploit eval_addl; auto; try apply HELPERS. eexact A1. eexact A0. intros (v2 & A2 & B2).
  exploit eval_shrluimm. eauto. eexact A0. instantiate (1 := Int.repr 63). intros (v3 & A3 & B3).
  set (a4 := if zlt M Int64.half_modulus
             then mullhs (Eletvar 0) (Int64.repr M)
             else addl (mullhs (Eletvar 0) (Int64.repr M)) (Eletvar 0)).
  set (v4 := if zlt M Int64.half_modulus then v1 else v2).
  assert (A4: eval_expr ge sp e m le a4 v4).
  { unfold a4, v4; destruct (zlt M Int64.half_modulus); auto. }
  exploit eval_shrlimm. eauto. eexact A4. instantiate (1 := Int.repr p). intros (v5 & A5 & B5).
  exploit eval_addl; auto; try apply HELPERS. eexact A5. eexact A3. intros (v6 & A6 & B6).
  assert (RANGE: forall x, 0 <= x < 64 -> Int.ltu (Int.repr x) Int64.iwordsize' = true).
  { intros. unfold Int.ltu. rewrite Int.unsigned_repr. rewrite zlt_true by tauto. auto.
    assert (64 < Int.max_unsigned) by (compute; auto). omega. }
  simpl in B1; inv B1.
  simpl in B2; inv B2.
  simpl in B3; rewrite RANGE in B3 by omega; inv B3.
  destruct (zlt M Int64.half_modulus).
- exploit (divls_mul_shift_1 x); eauto. intros [A B].
  simpl in B5; rewrite RANGE in B5 by auto; inv B5.
  simpl in B6; inv B6.
  rewrite B; exact A6.
- exploit (divls_mul_shift_2 x); eauto. intros [A B].
  simpl in B5; rewrite RANGE in B5 by auto; inv B5.
  simpl in B6; inv B6.
  rewrite B; exact A6.
Qed.

Theorem eval_divls:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divls x y = Some z ->
  exists v, eval_expr ge sp e m le (divls a b) v /\ Val.lessdef z v.
Proof.
  unfold divls; intros.
  destruct (is_longconst b) as [n2|] eqn:N2.
- assert (y = Vlong n2) by (eapply is_longconst_sound; eauto). subst y.
  destruct (is_longconst a) as [n1|] eqn:N1.
+ assert (x = Vlong n1) by (eapply is_longconst_sound; eauto). subst x.
  simpl in H1.
  destruct (Int64.eq n2 Int64.zero
         || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); inv H1.
  econstructor; split. apply eval_longconst. constructor.
+ destruct (Int64.is_power2' n2) as [l|] eqn:POW.
* destruct (Int.ltu l (Int.repr 63)) eqn:LT.
** exploit Val.divls_pow2; eauto. intros EQ. eapply eval_shrxlimm; eauto.
** eapply eval_divls_base; eauto.
* destruct (Compopts.optim_for_size tt). eapply eval_divls_base; eauto.
  destruct (divls_mul_params (Int64.signed n2)) as [[p M]|] eqn:PARAMS.
** destruct x; simpl in H1; try discriminate.
   destruct (Int64.eq n2 Int64.zero
             || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); inv H1.
   econstructor; split; eauto. econstructor. eauto.
   eapply eval_divls_mull; eauto.
** eapply eval_divls_base; eauto.
- eapply eval_divls_base; eauto.
Qed.

Theorem eval_modls:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modls x y = Some z ->
  exists v, eval_expr ge sp e m le (modls a b) v /\ Val.lessdef z v.
Proof.
  unfold modls; intros.
  destruct (is_longconst b) as [n2|] eqn:N2.
- assert (y = Vlong n2) by (eapply is_longconst_sound; eauto). subst y.
  destruct (is_longconst a) as [n1|] eqn:N1.
+ assert (x = Vlong n1) by (eapply is_longconst_sound; eauto). subst x.
  simpl in H1.
  destruct (Int64.eq n2 Int64.zero
         || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); inv H1.
  econstructor; split. apply eval_longconst. constructor.
+ destruct (Int64.is_power2' n2) as [l|] eqn:POW.
* destruct (Int.ltu l (Int.repr 63)) eqn:LT.
**destruct x; simpl in H1; try discriminate.
  destruct (Int64.eq n2 Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone) eqn:D; inv H1.
  assert (Val.divls (Vlong i) (Vlong n2) = Some (Vlong (Int64.divs i n2))).
  { simpl; rewrite D; auto. }
  exploit Val.divls_pow2; eauto. intros EQ.
  set (le' := Vlong i :: le).
  assert (A: eval_expr ge sp e m le' (Eletvar O) (Vlong i)) by (constructor; auto).
  exploit eval_shrxlimm; eauto. intros (v1 & A1 & B1). inv B1.
  econstructor; split.
  econstructor. eauto. eapply eval_modl_from_divl. eexact A1. reflexivity.
  rewrite Int64.mods_divs. auto.
**eapply eval_modls_base; eauto.
* destruct (Compopts.optim_for_size tt). eapply eval_modls_base; eauto.
  destruct (divls_mul_params (Int64.signed n2)) as [[p M]|] eqn:PARAMS.
** destruct x; simpl in H1; try discriminate.
   destruct (Int64.eq n2 Int64.zero
             || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); inv H1.
   econstructor; split; eauto. econstructor. eauto.
   rewrite Int64.mods_divs.
   eapply eval_modl_from_divl; auto.
   eapply eval_divls_mull; eauto.
** eapply eval_modls_base; eauto.
- eapply eval_modls_base; eauto.
Qed.

(** * Floating-point division *)

Theorem eval_divf:
  forall le a b x y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (divf a b) v /\ Val.lessdef (Val.divf x y) v.
Proof.
  intros until y. unfold divf. destruct (divf_match b); intros.
- unfold divfimm. destruct (Float.exact_inverse n2) as [n2' | ] eqn:EINV.
  + inv H0. inv H4. simpl in H6. inv H6. econstructor; split.
    EvalOp. constructor. eauto. constructor. EvalOp. simpl; eauto. constructor.
    simpl; eauto.
    destruct x; simpl; auto. erewrite Float.div_mul_inverse; eauto.
  + TrivialExists.
- TrivialExists.
Qed.

Theorem eval_divfs:
  forall le a b x y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (divfs a b) v /\ Val.lessdef (Val.divfs x y) v.
Proof.
  intros until y. unfold divfs. destruct (divfs_match b); intros.
- unfold divfsimm. destruct (Float32.exact_inverse n2) as [n2' | ] eqn:EINV.
  + inv H0. inv H4. simpl in H6. inv H6. econstructor; split.
    EvalOp. constructor. eauto. constructor. EvalOp. simpl; eauto. constructor.
    simpl; eauto.
    destruct x; simpl; auto. erewrite Float32.div_mul_inverse; eauto.
  + TrivialExists.
- TrivialExists.
Qed.

End CMCONSTRS.

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

Require Import Coqlib.
Require Import Zquot.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectOpproof.
Require Import SelectDiv.

Open Local Scope cminorsel_scope.

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
  Zdiv n d = Zdiv (m * n) (two_p (N + l)).
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
    apply Zmult_le_0_compat; omega.
  assert (k * n <= two_p (N + l) - two_p l).
    apply Zle_trans with (two_p l * n).
    apply Zmult_le_compat_r. omega. omega.
    replace (N + l) with (l + N) by omega.
    rewrite two_p_is_exp. 
    replace (two_p l * two_p N - two_p l)
       with (two_p l * (two_p N - 1))
         by ring.
    apply Zmult_le_compat_l. omega. exploit (two_p_gt_ZERO l). omega. omega.
    omega. omega.
  assert (0 <= two_p (N + l) * r).
    apply Zmult_le_0_compat. 
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
    apply Zle_lt_trans with (two_p (N + l) * d - two_p l).
    omega. 
    exploit (two_p_gt_ZERO l). omega. omega.
  symmetry. apply Zdiv_unique with (m * n - two_p (N + l) * q). 
  ring. omega.
Qed.

Lemma Zdiv_unique_2:
  forall x y q, y > 0 -> 0 < y * q - x <= y -> Zdiv x y = q - 1.
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
  Zdiv n d = - Zdiv (m * (-n)) (two_p (N + l)) - 1.
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
  cut (Zdiv (- (m * n)) (two_p (N + l)) = -q - 1).
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
  assert (0 < k * n). apply Zmult_lt_0_compat; omega.
  assert (0 <= two_p (N + l) * r).
    apply Zmult_le_0_compat. exploit (two_p_gt_ZERO (N + l)); omega. omega.
  omega.
  apply Zmult_le_reg_r with d. omega.
  rewrite H2. 
  assert (k * n <= two_p (N + l)).
    rewrite Zplus_comm. rewrite two_p_is_exp; try omega. 
    apply Zle_trans with (two_p l * n). apply Zmult_le_compat_r. omega. omega. 
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
  Z.quot n d = Zdiv (m * n) (two_p (N + l)) + (if zlt n 0 then 1 else 0).
Proof.
  intros. destruct (zlt n 0).
  exploit (Zdiv_mul_opp m l H H0 (-n)). omega. 
  replace (- - n) with n by ring.
  replace (Z.quot n d) with (- Z.quot (-n) d).
  rewrite Zquot_Zdiv_pos by omega. omega.
  rewrite Z.quot_opp_l by omega. ring.
  rewrite Zplus_0_r. rewrite Zquot_Zdiv_pos by omega. 
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
  Z.quot n d = Zdiv (m * n) (two_p (32 + p)) + (if zlt n 0 then 1 else 0).
Proof with (try discriminate).
  unfold divs_mul_params; intros d m' p' EQ.
  destruct (find_div_mul_params Int.wordsize
               (Int.half_modulus - Int.half_modulus mod d - 1) d 32)
  as [[p m] | ]...
  destruct (zlt 0 d)...
  destruct (zlt (two_p (32 + p)) (m * d))...
  destruct (zle (m * d) (two_p (32 + p) + two_p (p + 1)))...
  destruct (zle 0 m)...
  destruct (zlt m Int.modulus)...
  destruct (zle 0 p)...
  destruct (zlt p 32)...
  simpl in EQ. inv EQ. 
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
  Zdiv n d = Zdiv (m * n) (two_p (32 + p)).
Proof with (try discriminate).
  unfold divu_mul_params; intros d m' p' EQ.
  destruct (find_div_mul_params Int.wordsize
               (Int.modulus - Int.modulus mod d - 1) d 32)
  as [[p m] | ]...
  destruct (zlt 0 d)...
  destruct (zle (two_p (32 + p)) (m * d))...
  destruct (zle (m * d) (two_p (32 + p) + two_p p))...
  destruct (zle 0 m)...
  destruct (zlt m Int.modulus)...
  destruct (zle 0 p)...
  destruct (zlt p 32)...
  simpl in EQ. inv EQ. 
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
  split. apply Zle_trans with (Int.min_signed * m). apply Zmult_le_compat_l_neg. omega. generalize Int.min_signed_neg; omega.
  apply Zmult_le_compat_r. unfold n; generalize (Int.signed_range x); tauto. tauto.
  apply Zle_lt_trans with (Int.half_modulus * m). 
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
  f_equal. 
  replace (n * (m - Int.modulus)) with (n * m +  (-n) * Int.modulus) by ring.
  rewrite Z_div_plus. ring. apply Int.modulus_pos. 
  apply Int.eqm_samerepr. apply Int.eqm_add; auto with ints. 
  apply Int.eqm_sym. eapply Int.eqm_trans. apply Int.eqm_signed_unsigned. 
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl2. f_equal. f_equal. 
  rewrite Int.signed_repr_eq. rewrite Zmod_small by assumption. 
  apply zlt_false. omega.
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
  apply Zle_lt_trans with (Int.modulus * m).
  apply Zmult_le_compat_r. generalize (Int.unsigned_range x); omega. omega. 
  apply Zmult_lt_compat_l. compute; auto. omega. 
  unfold Int.max_unsigned; omega.
  assert (32 < Int.max_unsigned) by (compute; auto). omega.
Qed.

(** * Correctness of the smart constructors for division and modulus *)

Section CMCONSTRS.

Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma eval_divu_mul:
  forall le x y p M,
  divu_mul_params (Int.unsigned y) = Some(p, M) ->
  nth_error le O = Some (Vint x) ->
  eval_expr ge sp e m le (divu_mul p M) (Vint (Int.divu x y)).
Proof.
  intros. unfold divu_mul. exploit (divu_mul_shift x); eauto. intros [A B].
  assert (eval_expr ge sp e m le
           (Eop Omulhu (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil))
           (Vint (Int.mulhu x (Int.repr M)))).
  { EvalOp. econstructor. econstructor; eauto. econstructor. EvalOp. simpl; reflexivity. constructor.
    auto. }
  exploit eval_shruimm. eexact H1. instantiate (1 := Int.repr p). 
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
- destruct (divu_mul_params (Int.unsigned n2)) as [[p M] | ] eqn:PARAMS.
  + exists (Vint (Int.divu i n2)); split; auto.
    econstructor; eauto. eapply eval_divu_mul; eauto. 
  + eapply eval_divu_base; eauto. EvalOp.
Qed.

Theorem eval_divu:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divu x y = Some z ->
  exists v, eval_expr ge sp e m le (divu a b) v /\ Val.lessdef z v.
Proof.
  unfold divu; intros until b. destruct (divu_match b); intros.
- inv H0. inv H5. simpl in H7. inv H7. eapply eval_divuimm; eauto.
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
- destruct (divu_mul_params (Int.unsigned n2)) as [[p M] | ] eqn:PARAMS.
  + econstructor; split. 
    econstructor; eauto. eapply eval_mod_from_div. 
    eapply eval_divu_mul; eauto. simpl; eauto. simpl; eauto. 
    rewrite Int.modu_divu. auto. 
    red; intros; subst n2; discriminate.
  + eapply eval_modu_base; eauto. EvalOp.
Qed.

Theorem eval_modu:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modu x y = Some z ->
  exists v, eval_expr ge sp e m le (modu a b) v /\ Val.lessdef z v.
Proof.
  unfold modu; intros until b. destruct (modu_match b); intros.
- inv H0. inv H5. simpl in H7. inv H7. eapply eval_moduimm; eauto.
- eapply eval_modu_base; eauto. 
Qed.

Lemma eval_divs_mul:
  forall le x y p M,
  divs_mul_params (Int.signed y) = Some(p, M) ->
  nth_error le O = Some (Vint x) ->
  eval_expr ge sp e m le (divs_mul p M) (Vint (Int.divs x y)).
Proof.
  intros. unfold divs_mul.
  assert (V: eval_expr ge sp e m le (Eletvar O) (Vint x)).
  { constructor; auto. }
  assert (X: eval_expr ge sp e m le
           (Eop Omulhs (Eletvar 0 ::: Eop (Ointconst (Int.repr M)) Enil ::: Enil))
           (Vint (Int.mulhs x (Int.repr M)))).
  { EvalOp. econstructor. eauto. econstructor. EvalOp. simpl; reflexivity. constructor.
    auto. }
  exploit eval_shruimm. eexact V. instantiate (1 := Int.repr (Int.zwordsize - 1)). 
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
  exploit eval_add. eexact X. eexact V. intros [v1 [Z LD]]. 
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
- destruct (divs_mul_params (Int.signed n2)) as [[p M] | ] eqn:PARAMS.
  + exists (Vint (Int.divs i n2)); split; auto.
    econstructor; eauto. eapply eval_divs_mul; eauto. 
  + eapply eval_divs_base; eauto. EvalOp.
Qed.

Theorem eval_divs:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divs x y = Some z ->
  exists v, eval_expr ge sp e m le (divs a b) v /\ Val.lessdef z v.
Proof.
  unfold divs; intros until b. destruct (divs_match b); intros.
- inv H0. inv H5. simpl in H7. inv H7. eapply eval_divsimm; eauto.
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
- destruct (divs_mul_params (Int.signed n2)) as [[p M] | ] eqn:PARAMS.
  + econstructor; split. 
    econstructor. eauto. apply eval_mod_from_div with (x := i); auto.
    eapply eval_divs_mul with (x := i); eauto.
    simpl. auto.
  + eapply eval_mods_base; eauto. EvalOp.
Qed.

Theorem eval_mods:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.mods x y = Some z ->
  exists v, eval_expr ge sp e m le (mods a b) v /\ Val.lessdef z v.
Proof.
  unfold mods; intros until b. destruct (mods_match b); intros.
- inv H0. inv H5. simpl in H7. inv H7. eapply eval_modsimm; eauto.
- eapply eval_mods_base; eauto. 
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

End CMCONSTRS.

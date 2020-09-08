(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2011-2018 Sylvie Boldo
#<br />#
Copyright (C) 2011-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * IEEE-754 encoding of binary floating-point data *)

From Coq Require Import ZArith Reals Lia SpecFloat.

Require Import Core BinarySingleNaN Binary.

Section Binary_Bits.

Arguments exist {A} {P}.
Arguments B754_zero {prec} {emax}.
Arguments B754_infinity {prec} {emax}.
Arguments B754_nan {prec} {emax}.
Arguments B754_finite {prec} {emax}.

(** Number of bits for the fraction and exponent *)
Variable mw ew : Z.

Definition join_bits (s : bool) m e :=
  (Z.shiftl ((if s then Zpower 2 ew else 0) + e) mw + m)%Z.

Lemma join_bits_range :
  forall s m e,
  (0 <= m < 2^mw)%Z ->
  (0 <= e < 2^ew)%Z ->
  (0 <= join_bits s m e < 2 ^ (mw + ew + 1))%Z.
Proof.
intros s m e Hm He.
assert (0 <= mw)%Z as Hmw.
  destruct mw as [|mw'|mw'] ; try easy.
  clear -Hm ; simpl in Hm ; lia.
assert (0 <= ew)%Z as Hew.
  destruct ew as [|ew'|ew'] ; try easy.
  clear -He ; simpl in He ; lia.
unfold join_bits.
rewrite Z.shiftl_mul_pow2 by easy.
split.
- apply (Zplus_le_compat 0 _ 0) with (2 := proj1 Hm).
  rewrite <- (Zmult_0_l (2^mw)).
  apply Zmult_le_compat_r.
  case s.
  clear -He ; lia.
  now rewrite Zmult_0_l.
  clear -Hm ; lia.
- apply Z.lt_le_trans with (((if s then 2 ^ ew else 0) + e + 1) * 2 ^ mw)%Z.
  rewrite (Zmult_plus_distr_l _ 1).
  apply Zplus_lt_compat_l.
  now rewrite Zmult_1_l.
  rewrite <- (Zplus_assoc mw), (Zplus_comm mw), Zpower_plus.
  apply Zmult_le_compat_r.
  rewrite Zpower_plus by easy.
  change (2^1)%Z with 2%Z.
  case s ; clear -He ; lia.
  clear -Hm ; lia.
  clear -Hew ; lia.
  easy.
Qed.

Definition split_bits x :=
  let mm := Zpower 2 mw in
  let em := Zpower 2 ew in
  (Zle_bool (mm * em) x, Zmod x mm, Zmod (Z.div x mm) em)%Z.

Theorem split_join_bits :
  forall s m e,
  (0 <= m < Zpower 2 mw)%Z ->
  (0 <= e < Zpower 2 ew)%Z ->
  split_bits (join_bits s m e) = (s, m, e).
Proof.
intros s m e Hm He.
assert (0 <= mw)%Z as Hmw.
  destruct mw as [|mw'|mw'] ; try easy.
  clear -Hm ; simpl in Hm ; lia.
assert (0 <= ew)%Z as Hew.
  destruct ew as [|ew'|ew'] ; try easy.
  clear -He ; simpl in He ; lia.
unfold split_bits, join_bits.
rewrite Z.shiftl_mul_pow2 by easy.
apply f_equal2 ; [apply f_equal2|].
- case s.
  + apply Zle_bool_true.
    apply Zle_0_minus_le.
    ring_simplify.
    apply Zplus_le_0_compat.
    apply Zmult_le_0_compat.
    apply He.
    clear -Hm ; lia.
    apply Hm.
  + apply Zle_bool_false.
    apply Zplus_lt_reg_l with (2^mw * (-e))%Z.
    replace (2 ^ mw * - e + ((0 + e) * 2 ^ mw + m))%Z with (m * 1)%Z by ring.
    rewrite <- Zmult_plus_distr_r.
    apply Z.lt_le_trans with (2^mw * 1)%Z.
    now apply Zmult_lt_compat_r.
    apply Zmult_le_compat_l.
    clear -He ; lia.
    clear -Hm ; lia.
- rewrite Zplus_comm.
  rewrite Z_mod_plus_full.
  now apply Zmod_small.
- rewrite Z_div_plus_full_l by (clear -Hm ; lia).
  rewrite Zdiv_small with (1 := Hm).
  rewrite Zplus_0_r.
  case s.
  + replace (2^ew + e)%Z with (e + 1 * 2^ew)%Z by ring.
    rewrite Z_mod_plus_full.
    now apply Zmod_small.
  + now apply Zmod_small.
Qed.

Hypothesis Hmw : (0 < mw)%Z.
Hypothesis Hew : (0 < ew)%Z.

Let prec := (mw + 1)%Z.
Let emax := Zpower 2 (ew - 1).
Notation emin := (emin prec emax) (only parsing).
Notation fexp := (fexp prec emax) (only parsing).
Notation binary_float := (binary_float prec emax) (only parsing).

Let Hprec : (0 < prec)%Z.
Proof.
unfold prec.
apply Zle_lt_succ.
now apply Zlt_le_weak.
Qed.

Let Hm_gt_0 : (0 < 2^mw)%Z.
Proof.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
Qed.

Let He_gt_0 : (0 < 2^ew)%Z.
Proof.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
Qed.

Hypothesis Hmax : (prec < emax)%Z.

Theorem join_split_bits :
  forall x,
  (0 <= x < Zpower 2 (mw + ew + 1))%Z ->
  let '(s, m, e) := split_bits x in
  join_bits s m e = x.
Proof.
intros x Hx.
unfold split_bits, join_bits.
rewrite Z.shiftl_mul_pow2 by now apply Zlt_le_weak.
pattern x at 4 ; rewrite Z.div_mod with x (2^mw)%Z.
apply (f_equal (fun v => (v + _)%Z)).
rewrite Zmult_comm.
apply f_equal.
pattern (x / (2^mw))%Z at 2 ; rewrite Z.div_mod with (x / (2^mw))%Z (2^ew)%Z.
apply (f_equal (fun v => (v + _)%Z)).
replace (x / 2 ^ mw / 2 ^ ew)%Z with (if Zle_bool (2 ^ mw * 2 ^ ew) x then 1 else 0)%Z.
case Zle_bool.
now rewrite Zmult_1_r.
now rewrite Zmult_0_r.
rewrite Zdiv_Zdiv.
apply sym_eq.
case Zle_bool_spec ; intros Hs.
apply Zle_antisym.
cut (x / (2^mw * 2^ew) < 2)%Z. clear ; lia.
apply Zdiv_lt_upper_bound.
now apply Zmult_lt_0_compat.
rewrite <- Zpower_exp ; try ( apply Z.le_ge ; apply Zlt_le_weak ; assumption ).
change 2%Z with (Zpower 2 1) at 1.
rewrite <- Zpower_exp.
now rewrite Zplus_comm.
discriminate.
apply Z.le_ge.
now apply Zplus_le_0_compat ; apply Zlt_le_weak.
apply Zdiv_le_lower_bound.
now apply Zmult_lt_0_compat.
now rewrite Zmult_1_l.
apply Zdiv_small.
now split.
now apply Zlt_le_weak.
now apply Zlt_le_weak.
now apply Zgt_not_eq.
now apply Zgt_not_eq.
Qed.

Theorem split_bits_inj :
  forall x y,
  (0 <= x < Zpower 2 (mw + ew + 1))%Z ->
  (0 <= y < Zpower 2 (mw + ew + 1))%Z ->
  split_bits x = split_bits y ->
  x = y.
Proof.
intros x y Hx Hy.
generalize (join_split_bits x Hx) (join_split_bits y Hy).
destruct (split_bits x) as ((sx, mx), ex).
destruct (split_bits y) as ((sy, my), ey).
intros Jx Jy H. revert Jx Jy.
inversion_clear H.
intros Jx Jy.
now rewrite <- Jx.
Qed.

Definition bits_of_binary_float (x : binary_float) :=
  match x with
  | B754_zero sx => join_bits sx 0 0
  | B754_infinity sx => join_bits sx 0 (Zpower 2 ew - 1)
  | B754_nan sx plx _ => join_bits sx (Zpos plx) (Zpower 2 ew - 1)
  | B754_finite sx mx ex _ =>
    let m := (Zpos mx - Zpower 2 mw)%Z in
    if Zle_bool 0 m then
      join_bits sx m (ex - emin + 1)
    else
      join_bits sx (Zpos mx) 0
  end.

Definition split_bits_of_binary_float (x : binary_float) :=
  match x with
  | B754_zero sx => (sx, 0, 0)%Z
  | B754_infinity sx => (sx, 0, Zpower 2 ew - 1)%Z
  | B754_nan sx plx _ => (sx, Zpos plx, Zpower 2 ew - 1)%Z
  | B754_finite sx mx ex _ =>
    let m := (Zpos mx - Zpower 2 mw)%Z in
    if Zle_bool 0 m then
      (sx, m, ex - emin + 1)%Z
    else
      (sx, Zpos mx, 0)%Z
  end.

Theorem split_bits_of_binary_float_correct :
  forall x,
  split_bits (bits_of_binary_float x) = split_bits_of_binary_float x.
Proof.
intros [sx|sx|sx plx Hplx|sx mx ex Hx] ;
  try ( simpl ; apply split_join_bits ; split ; try apply Z.le_refl ; try apply Zlt_pred ; trivial ; lia ).
simpl. apply split_join_bits; split; try lia.
destruct (digits2_Pnat_correct plx).
unfold nan_pl in Hplx.
rewrite Zpos_digits2_pos, <- Z_of_nat_S_digits2_Pnat in Hplx.
rewrite Zpower_nat_Z in H0.
eapply Z.lt_le_trans. apply H0.
change 2%Z with (radix_val radix2). apply Zpower_le.
rewrite Z.ltb_lt in Hplx.
unfold prec in *. lia.
(* *)
unfold bits_of_binary_float, split_bits_of_binary_float.
assert (Hf: (emin <= ex /\ Zdigits radix2 (Zpos mx) <= prec)%Z).
destruct (andb_prop _ _ Hx) as (Hx', _).
unfold canonical_mantissa in Hx'.
rewrite Zpos_digits2_pos in Hx'.
generalize (Zeq_bool_eq _ _ Hx').
unfold fexp, FLT_exp, emin.
clear ; lia.
case Zle_bool_spec ; intros H ;
  [ apply -> Z.le_0_sub in H | apply -> Z.lt_sub_0 in H ] ;
  apply split_join_bits ; try now split.
(* *)
split.
clear -He_gt_0 H ; lia.
cut (Zpos mx < 2 * 2^mw)%Z. clear ; lia.
replace (2 * 2^mw)%Z with (2^prec)%Z.
apply (Zpower_gt_Zdigits radix2 _ (Zpos mx)).
apply Hf.
unfold prec.
rewrite Zplus_comm.
apply Zpower_exp ; apply Z.le_ge.
discriminate.
now apply Zlt_le_weak.
(* *)
split.
generalize (proj1 Hf).
clear ; lia.
destruct (andb_prop _ _ Hx) as (_, Hx').
unfold emin.
replace (2^ew)%Z with (2 * emax)%Z.
generalize (Zle_bool_imp_le _ _ Hx').
clear ; lia.
apply sym_eq.
rewrite (Zsucc_pred ew).
unfold Z.succ.
rewrite Zplus_comm.
apply Zpower_exp ; apply Z.le_ge.
discriminate.
now apply Zlt_0_le_0_pred.
Qed.

Theorem bits_of_binary_float_range:
  forall x, (0 <= bits_of_binary_float x < 2^(mw+ew+1))%Z.
Proof.
unfold bits_of_binary_float.
intros [sx|sx|sx pl pl_range|sx mx ex H].
- apply join_bits_range ; now split.
- apply join_bits_range.
  now split.
  clear -He_gt_0 ; lia.
- apply Z.ltb_lt in pl_range.
  apply join_bits_range.
  split.
  easy.
  apply (Zpower_gt_Zdigits radix2 _ (Zpos pl)).
  apply Z.lt_succ_r.
  now rewrite <- Zdigits2_Zdigits.
  clear -He_gt_0 ; lia.
- unfold bounded in H.
  apply Bool.andb_true_iff in H ; destruct H as [A B].
  apply Z.leb_le in B.
  unfold canonical_mantissa, fexp, FLT_exp in A. apply Zeq_bool_eq in A.
  case Zle_bool_spec ; intros H.
  + apply join_bits_range.
    * split.
      clear -H ; lia.
      rewrite Zpos_digits2_pos in A.
      cut (Zpos mx < 2 ^ prec)%Z.
      unfold prec.
      rewrite Zpower_plus by (clear -Hmw ; lia).
      change (2^1)%Z with 2%Z.
      clear ; lia.
      apply (Zpower_gt_Zdigits radix2 _ (Zpos mx)).
      unfold emin in A.
      clear -A ; lia.
    * split.
      unfold emin in A |- * ; clear -A ; lia.
      replace ew with ((ew - 1) + 1)%Z by ring.
      rewrite Zpower_plus by (clear - Hew ; lia).
      unfold emin, emax in *.
      change (2^1)%Z with 2%Z.
      clear -B ; lia.
  + apply -> Z.lt_sub_0 in H.
    apply join_bits_range ; now split.
Qed.

Definition binary_float_of_bits_aux x :=
  let '(sx, mx, ex) := split_bits x in
  if Zeq_bool ex 0 then
    match mx with
    | Z0 => F754_zero sx
    | Zpos px => F754_finite sx px emin
    | Zneg _ => F754_nan false xH (* dummy *)
    end
  else if Zeq_bool ex (Zpower 2 ew - 1) then
    match mx with
      | Z0 => F754_infinity sx
      | Zpos plx => F754_nan sx plx
      | Zneg _ => F754_nan false xH (* dummy *)
    end
  else
    match (mx + Zpower 2 mw)%Z with
    | Zpos px => F754_finite sx px (ex + emin - 1)
    | _ => F754_nan false xH (* dummy *)
    end.

Lemma binary_float_of_bits_aux_correct :
  forall x,
  valid_binary prec emax (binary_float_of_bits_aux x) = true.
Proof.
intros x.
unfold binary_float_of_bits_aux, split_bits.
assert (Hnan: nan_pl prec 1 = true).
  apply Z.ltb_lt.
  simpl. unfold prec.
  clear -Hmw ; lia.
case Zeq_bool_spec ; intros He1.
case_eq (x mod 2^mw)%Z ; try easy.
(* subnormal *)
intros px Hm.
assert (Zdigits radix2 (Zpos px) <= mw)%Z.
apply Zdigits_le_Zpower.
simpl.
rewrite <- Hm.
eapply Z_mod_lt.
now apply Z.lt_gt.
apply bounded_canonical_lt_emax ; try assumption.
unfold canonical, cexp.
fold emin.
rewrite mag_F2R_Zdigits. 2: discriminate.
unfold Fexp, FLT_exp.
apply sym_eq.
apply Zmax_right.
clear -H Hprec.
unfold prec ; lia.
apply Rnot_le_lt.
intros H0.
refine (_ (mag_le radix2 _ _ _ H0)).
rewrite mag_bpow.
rewrite mag_F2R_Zdigits. 2: discriminate.
unfold emin, prec.
apply Zlt_not_le.
cut (0 < emax)%Z. clear -H Hew ; lia.
apply (Zpower_gt_0 radix2).
clear -Hew ; lia.
apply bpow_gt_0.
case Zeq_bool_spec ; intros He2.
case_eq (x mod 2 ^ mw)%Z; try easy.
(* nan *)
intros plx Eqplx. apply Z.ltb_lt.
rewrite Zpos_digits2_pos.
assert (forall a b, a <= b -> a < b+1)%Z by (intros; lia). apply H. clear H.
apply Zdigits_le_Zpower. simpl.
rewrite <- Eqplx. edestruct Z_mod_lt; eauto.
change 2%Z with (radix_val radix2).
apply Z.lt_gt, Zpower_gt_0. lia.
case_eq (x mod 2^mw + 2^mw)%Z ; try easy.
(* normal *)
intros px Hm.
assert (prec = Zdigits radix2 (Zpos px)).
(* . *)
rewrite Zdigits_mag. 2: discriminate.
apply sym_eq.
apply mag_unique.
rewrite <- abs_IZR.
unfold Z.abs.
replace (prec - 1)%Z with mw by ( unfold prec ; ring ).
rewrite <- IZR_Zpower with (1 := Zlt_le_weak _ _ Hmw).
rewrite <- IZR_Zpower. 2: now apply Zlt_le_weak.
rewrite <- Hm.
split.
apply IZR_le.
change (radix2^mw)%Z with (0 + 2^mw)%Z.
apply Zplus_le_compat_r.
eapply Z_mod_lt.
now apply Z.lt_gt.
apply IZR_lt.
unfold prec.
rewrite Zpower_exp. 2: now apply Z.le_ge ; apply Zlt_le_weak. 2: discriminate.
rewrite <- Zplus_diag_eq_mult_2.
apply Zplus_lt_compat_r.
eapply Z_mod_lt.
now apply Z.lt_gt.
(* . *)
apply bounded_canonical_lt_emax ; try assumption.
unfold canonical, cexp.
rewrite mag_F2R_Zdigits. 2: discriminate.
unfold Fexp, fexp, FLT_exp.
rewrite <- H.
set (ex := ((x / 2^mw) mod 2^ew)%Z).
replace (prec + (ex + emin - 1) - prec)%Z with (ex + emin - 1)%Z by ring.
apply sym_eq.
apply Zmax_left.
revert He1.
fold ex.
cut (0 <= ex)%Z.
unfold emin.
clear ; intros H1 H2 ; lia.
eapply Z_mod_lt.
apply Z.lt_gt.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
apply Rnot_le_lt.
intros H0.
refine (_ (mag_le radix2 _ _ _ H0)).
rewrite mag_bpow.
rewrite mag_F2R_Zdigits. 2: discriminate.
rewrite <- H.
apply Zlt_not_le.
unfold emin.
apply Zplus_lt_reg_r with (emax - 1)%Z.
ring_simplify.
revert He2.
set (ex := ((x / 2^mw) mod 2^ew)%Z).
cut (ex < 2^ew)%Z.
replace (2^ew)%Z with (2 * emax)%Z.
clear ; intros H1 H2 ; lia.
replace ew with (1 + (ew - 1))%Z by ring.
rewrite Zpower_exp.
apply refl_equal.
discriminate.
clear -Hew ; lia.
eapply Z_mod_lt.
apply Z.lt_gt.
apply (Zpower_gt_0 radix2).
now apply Zlt_le_weak.
apply bpow_gt_0.
Qed.

Definition binary_float_of_bits x :=
  FF2B prec emax _ (binary_float_of_bits_aux_correct x).

Theorem binary_float_of_bits_of_binary_float :
  forall x,
  binary_float_of_bits (bits_of_binary_float x) = x.
Proof.
intros x.
apply B2FF_inj.
unfold binary_float_of_bits.
rewrite B2FF_FF2B.
unfold binary_float_of_bits_aux.
rewrite split_bits_of_binary_float_correct.
destruct x as [sx|sx|sx plx Hplx|sx mx ex Bx].
apply refl_equal.
(* *)
simpl.
rewrite Zeq_bool_false.
now rewrite Zeq_bool_true.
cut (1 < 2^ew)%Z. clear ; lia.
now apply (Zpower_gt_1 radix2).
(* *)
simpl.
rewrite Zeq_bool_false.
rewrite Zeq_bool_true; auto.
cut (1 < 2^ew)%Z. clear ; lia.
now apply (Zpower_gt_1 radix2).
(* *)
unfold split_bits_of_binary_float.
case Zle_bool_spec ; intros Hm.
(* . *)
rewrite Zeq_bool_false.
rewrite Zeq_bool_false.
now ring_simplify (Zpos mx - 2 ^ mw + 2 ^ mw)%Z (ex - emin + 1 + emin - 1)%Z.
destruct (andb_prop _ _ Bx) as (_, H1).
generalize (Zle_bool_imp_le _ _ H1).
unfold emin.
replace (2^ew)%Z with (2 * emax)%Z.
clear ; lia.
replace ew with (1 + (ew - 1))%Z by ring.
rewrite Zpower_exp.
apply refl_equal.
discriminate.
clear -Hew ; lia.
destruct (andb_prop _ _ Bx) as (H1, _).
generalize (Zeq_bool_eq _ _ H1).
rewrite Zpos_digits2_pos.
unfold FLT_exp, emin.
generalize (Zdigits radix2 (Zpos mx)).
clear.
unfold fexp, emin.
intros ; lia.
(* . *)
rewrite Zeq_bool_true. 2: apply refl_equal.
simpl.
apply f_equal.
destruct (andb_prop _ _ Bx) as (H1, _).
generalize (Zeq_bool_eq _ _ H1).
rewrite Zpos_digits2_pos.
unfold FLT_exp, emin, prec.
apply -> Z.lt_sub_0 in Hm.
generalize (Zdigits_le_Zpower radix2 _ (Zpos mx) Hm).
generalize (Zdigits radix2 (Zpos mx)).
clear.
unfold fexp, emin.
intros ; lia.
Qed.

Theorem bits_of_binary_float_of_bits :
  forall x,
  (0 <= x < 2^(mw+ew+1))%Z ->
  bits_of_binary_float (binary_float_of_bits x) = x.
Proof.
intros x Hx.
unfold binary_float_of_bits, bits_of_binary_float.
set (Cx := binary_float_of_bits_aux_correct x).
clearbody Cx.
rewrite match_FF2B.
revert Cx.
generalize (join_split_bits x Hx).
unfold binary_float_of_bits_aux.
case_eq (split_bits x).
intros (sx, mx) ex Sx.
assert (Bm: (0 <= mx < 2^mw)%Z).
inversion_clear Sx.
apply Z_mod_lt.
now apply Z.lt_gt.
case Zeq_bool_spec ; intros He1.
(* subnormal *)
case_eq mx.
intros Hm Jx _.
now rewrite He1 in Jx.
intros px Hm Jx _.
rewrite Zle_bool_false.
now rewrite <- He1.
apply <- Z.lt_sub_0.
now rewrite <- Hm.
intros px Hm _ _.
apply False_ind.
apply Zle_not_lt with (1 := proj1 Bm).
now rewrite Hm.
case Zeq_bool_spec ; intros He2.
(* infinity/nan *)
case_eq mx; intros Hm.
now rewrite He2.
now rewrite He2.
intros ; lia.
(* normal *)
case_eq (mx + 2 ^ mw)%Z.
intros Hm.
apply False_ind.
clear -Bm Hm ; lia.
intros p Hm Jx Cx.
rewrite <- Hm.
rewrite Zle_bool_true.
now ring_simplify (mx + 2^mw - 2^mw)%Z (ex + emin - 1 - emin + 1)%Z.
now ring_simplify.
intros p Hm.
apply False_ind.
clear -Bm Hm ; lia.
Qed.

End Binary_Bits.

(** Specialization for IEEE single precision operations *)
Section B32_Bits.

Arguments B754_nan {prec} {emax}.

Definition binary32 := binary_float 24 128.

Let Hprec : (0 < 24)%Z.
Proof.
apply refl_equal.
Qed.

Let Hprec_emax : (24 < 128)%Z.
Proof.
apply refl_equal.
Qed.

Let Hemax : (3 <= 128)%Z.
Proof.
intros H.
discriminate H.
Qed.

Definition default_nan_pl32 : { nan : binary32 | is_nan 24 128 nan = true } :=
  exist _ (@B754_nan 24 128 false (iter_nat xO 22 xH) (refl_equal true)) (refl_equal true).

Definition unop_nan_pl32 (f : binary32) : { nan : binary32 | is_nan 24 128 nan = true } :=
  match f as f with
  | B754_nan s pl Hpl => exist _ (B754_nan s pl Hpl) (refl_equal true)
  | _ => default_nan_pl32
  end.

Definition binop_nan_pl32 (f1 f2 : binary32) : { nan : binary32 | is_nan 24 128 nan = true } :=
  match f1, f2 with
  | B754_nan s1 pl1 Hpl1, _ => exist _ (B754_nan s1 pl1 Hpl1) (refl_equal true)
  | _, B754_nan s2 pl2 Hpl2 => exist _ (B754_nan s2 pl2 Hpl2) (refl_equal true)
  | _, _ => default_nan_pl32
  end.

Definition ternop_nan_pl32 (f1 f2 f3 : binary32) : { nan : binary32 | is_nan 24 128 nan = true } :=
  match f1, f2, f3 with
  | B754_nan s1 pl1 Hpl1, _, _ => exist _ (B754_nan s1 pl1 Hpl1) (refl_equal true)
  | _, B754_nan s2 pl2 Hpl2, _ => exist _ (B754_nan s2 pl2 Hpl2) (refl_equal true)
  | _, _, B754_nan s3 pl3 Hpl3 => exist _ (B754_nan s3 pl3 Hpl3) (refl_equal true)
  | _, _, _ => default_nan_pl32
  end.

Definition b32_erase : binary32 -> binary32 := erase 24 128.
Definition b32_opp : binary32 -> binary32 := Bopp 24 128 unop_nan_pl32.
Definition b32_abs : binary32 -> binary32 := Babs 24 128 unop_nan_pl32.
Definition b32_pred : binary32 -> binary32 := Bpred _ _ Hprec Hprec_emax.
Definition b32_succ : binary32 -> binary32 := Bsucc _ _ Hprec Hprec_emax.
Definition b32_sqrt : mode -> binary32 -> binary32 := Bsqrt  _ _ Hprec Hprec_emax unop_nan_pl32.

Definition b32_plus :  mode -> binary32 -> binary32 -> binary32 := Bplus  _ _ Hprec Hprec_emax binop_nan_pl32.
Definition b32_minus : mode -> binary32 -> binary32 -> binary32 := Bminus _ _ Hprec Hprec_emax binop_nan_pl32.
Definition b32_mult :  mode -> binary32 -> binary32 -> binary32 := Bmult  _ _ Hprec Hprec_emax binop_nan_pl32.
Definition b32_div :   mode -> binary32 -> binary32 -> binary32 := Bdiv   _ _ Hprec Hprec_emax binop_nan_pl32.

Definition b32_fma :   mode -> binary32 -> binary32 -> binary32 -> binary32 := Bfma _ _ Hprec Hprec_emax ternop_nan_pl32.

Definition b32_compare : binary32 -> binary32 -> option comparison := Bcompare 24 128.
Definition b32_of_bits : Z -> binary32 := binary_float_of_bits 23 8 (refl_equal _) (refl_equal _) (refl_equal _).
Definition bits_of_b32 : binary32 -> Z := bits_of_binary_float 23 8.

End B32_Bits.

(** Specialization for IEEE double precision operations *)
Section B64_Bits.

Arguments B754_nan {prec} {emax}.

Definition binary64 := binary_float 53 1024.

Let Hprec : (0 < 53)%Z.
Proof.
apply refl_equal.
Qed.

Let Hprec_emax : (53 < 1024)%Z.
Proof.
apply refl_equal.
Qed.

Let Hemax : (3 <= 1024)%Z.
Proof.
intros H.
discriminate H.
Qed.

Definition default_nan_pl64 : { nan : binary64 | is_nan 53 1024 nan = true } :=
  exist _ (@B754_nan 53 1024 false (iter_nat xO 51 xH) (refl_equal true)) (refl_equal true).

Definition unop_nan_pl64 (f : binary64) : { nan : binary64 | is_nan 53 1024 nan = true } :=
  match f as f with
  | B754_nan s pl Hpl => exist _ (B754_nan s pl Hpl) (refl_equal true)
  | _ => default_nan_pl64
  end.

Definition binop_nan_pl64 (f1 f2 : binary64) : { nan : binary64 | is_nan 53 1024 nan = true } :=
  match f1, f2 with
  | B754_nan s1 pl1 Hpl1, _ => exist _ (B754_nan s1 pl1 Hpl1) (refl_equal true)
  | _, B754_nan s2 pl2 Hpl2 => exist _ (B754_nan s2 pl2 Hpl2) (refl_equal true)
  | _, _ => default_nan_pl64
  end.

Definition ternop_nan_pl64 (f1 f2 f3 : binary64) : { nan : binary64 | is_nan 53 1024 nan = true } :=
  match f1, f2, f3 with
  | B754_nan s1 pl1 Hpl1, _, _ => exist _ (B754_nan s1 pl1 Hpl1) (refl_equal true)
  | _, B754_nan s2 pl2 Hpl2, _ => exist _ (B754_nan s2 pl2 Hpl2) (refl_equal true)
  | _, _, B754_nan s3 pl3 Hpl3 => exist _ (B754_nan s3 pl3 Hpl3) (refl_equal true)
  | _, _, _ => default_nan_pl64
  end.

Definition b64_erase : binary64 -> binary64 := erase 53 1024.
Definition b64_opp : binary64 -> binary64 := Bopp 53 1024 unop_nan_pl64.
Definition b64_abs : binary64 -> binary64 := Babs 53 1024 unop_nan_pl64.
Definition b64_pred : binary64 -> binary64 := Bpred _ _ Hprec Hprec_emax.
Definition b64_succ : binary64 -> binary64 := Bsucc _ _ Hprec Hprec_emax.
Definition b64_sqrt : mode -> binary64 -> binary64 := Bsqrt _ _ Hprec Hprec_emax unop_nan_pl64.

Definition b64_plus  : mode -> binary64 -> binary64 -> binary64 := Bplus  _ _ Hprec Hprec_emax binop_nan_pl64.
Definition b64_minus : mode -> binary64 -> binary64 -> binary64 := Bminus _ _ Hprec Hprec_emax binop_nan_pl64.
Definition b64_mult  : mode -> binary64 -> binary64 -> binary64 := Bmult  _ _ Hprec Hprec_emax binop_nan_pl64.
Definition b64_div   : mode -> binary64 -> binary64 -> binary64 := Bdiv   _ _ Hprec Hprec_emax binop_nan_pl64.

Definition b64_fma :   mode -> binary64 -> binary64 -> binary64 -> binary64 := Bfma _ _ Hprec Hprec_emax ternop_nan_pl64.

Definition b64_compare : binary64 -> binary64 -> option comparison := Bcompare 53 1024.
Definition b64_of_bits : Z -> binary64 := binary_float_of_bits 52 11 (refl_equal _) (refl_equal _) (refl_equal _).
Definition bits_of_b64 : binary64 -> Z := bits_of_binary_float 52 11.

End B64_Bits.

(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010-2011 Sylvie Boldo
#<br />#
Copyright (C) 2010-2011 Guillaume Melquiond

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
  | F754_nan : full_float
  | F754_finite : bool -> positive -> Z -> full_float.

Definition FF2R beta x :=
  match x with
  | F754_finite s m e => F2R (Float beta (cond_Zopp s (Zpos m)) e)
  | _ => R0
  end.

End AnyRadix.

Section Binary.

(** prec is the number of bits of the mantissa including the implicit one
    emax is the exponent of the infinities
    Typically p=24 and emax = 128 in single precision *)
Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Hypothesis Hmax : (prec < emax)%Z.

Let emin := (3 - emax - prec)%Z.
Let fexp := FLT_exp emin prec.
Instance fexp_correct : Valid_exp fexp := FLT_exp_valid emin prec.
Instance fexp_monotone : Monotone_exp fexp := FLT_exp_monotone emin prec.

Definition canonic_mantissa m e :=
  Zeq_bool (fexp (Z_of_nat (S (digits2_Pnat m)) + e)) e.

Definition bounded m e :=
  andb (canonic_mantissa m e) (Zle_bool e (emax - prec)).

Definition valid_binary x :=
  match x with
  | F754_finite _ m e => bounded m e
  | _ => true
  end.

(** Basic type used for representing binary FP numbers.
    Note that there is exactly one such object per FP datum.
    NaNs do not have any payload. They cannot be distinguished. *)
Inductive binary_float :=
  | B754_zero : bool -> binary_float
  | B754_infinity : bool -> binary_float
  | B754_nan : binary_float
  | B754_finite : bool ->
    forall (m : positive) (e : Z), bounded m e = true -> binary_float.

Definition FF2B x :=
  match x as x return valid_binary x = true -> binary_float with
  | F754_finite s m e => B754_finite s m e
  | F754_infinity s => fun _ => B754_infinity s
  | F754_zero s => fun _ => B754_zero s
  | F754_nan => fun _ => B754_nan
  end.

Definition B2FF x :=
  match x with
  | B754_finite s m e _ => F754_finite s m e
  | B754_infinity s => F754_infinity s
  | B754_zero s => F754_zero s
  | B754_nan => F754_nan
  end.

Definition radix2 := Build_radix 2 (refl_equal true).

Definition B2R f :=
  match f with
  | B754_finite s m e _ => F2R (Float radix2 (cond_Zopp s (Zpos m)) e)
  | _ => R0
  end.

Theorem FF2R_B2FF :
  forall x,
  FF2R radix2 (B2FF x) = B2R x.
Proof.
now intros [sx|sx| |sx mx ex Hx].
Qed.

Theorem B2FF_FF2B :
  forall x Hx,
  B2FF (FF2B x Hx) = x.
Proof.
now intros [sx|sx| |sx mx ex] Hx.
Qed.

Theorem valid_binary_B2FF :
  forall x,
  valid_binary (B2FF x) = true.
Proof.
now intros [sx|sx| |sx mx ex Hx].
Qed.

Theorem FF2B_B2FF :
  forall x H,
  FF2B (B2FF x) H = x.
Proof.
intros [sx|sx| |sx mx ex Hx] H ; try easy.
apply f_equal.
apply eqbool_irrelevance.
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
now intros [sx|sx| |sx mx ex] Hx.
Qed.

Theorem match_FF2B :
  forall {T} fz fi fn ff x Hx,
  match FF2B x Hx return T with
  | B754_zero sx => fz sx
  | B754_infinity sx => fi sx
  | B754_nan => fn
  | B754_finite sx mx ex _ => ff sx mx ex
  end =
  match x with
  | F754_zero sx => fz sx
  | F754_infinity sx => fi sx
  | F754_nan => fn
  | F754_finite sx mx ex => ff sx mx ex
  end.
Proof.
now intros T fz fi fn ff [sx|sx| |sx mx ex] Hx.
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
rewrite Z_of_nat_S_digits2_Pnat.
now case sx.
now case sx.
Qed.

Theorem generic_format_B2R :
  forall x,
  generic_format radix2 fexp (B2R x).
Proof.
intros [sx|sx| |sx mx ex Hx] ; try apply generic_format_0.
simpl.
apply generic_format_canonic.
apply canonic_canonic_mantissa.
now destruct (andb_prop _ _ Hx) as (H, _).
Qed.

Theorem B2FF_inj :
  forall x y : binary_float,
  B2FF x = B2FF y ->
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
apply f_equal.
apply eqbool_irrelevance.
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
now intros [| | |].
Qed.

Definition Bopp x :=
  match x with
  | B754_nan => x
  | B754_infinity sx => B754_infinity (negb sx)
  | B754_finite sx mx ex Hx => B754_finite (negb sx) mx ex Hx
  | B754_zero sx => B754_zero (negb sx)
  end.

Theorem Bopp_involutive :
  forall x, Bopp (Bopp x) = x.
Proof.
now intros [sx|sx| |sx mx ex Hx] ; simpl ; try rewrite Bool.negb_involutive.
Qed.

Theorem B2R_Bopp :
  forall x,
  B2R (Bopp x) = (- B2R x)%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; apply sym_eq ; try apply Ropp_0.
simpl.
rewrite <- F2R_opp.
now case sx.
Qed.


Theorem is_finite_Bopp: forall x,
  is_finite (Bopp x) = is_finite x.
Proof.
now intros [| | |].
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
rewrite Z_of_nat_S_digits2_Pnat.
change Fcalc_digits.radix2 with radix2.
unfold fexp, FLT_exp.
generalize (Zdigits radix2 (Zpos mx)).
intros ; zify ; subst.
clear -H H2. clearbody emin.
omega.
Qed.

Theorem abs_B2R_lt_emax :
  forall x,
  (Rabs (B2R x) < bpow radix2 emax)%R.
Proof.
intros [sx|sx| |sx mx ex Hx] ; simpl ; try ( rewrite Rabs_R0 ; apply bpow_gt_0 ).
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
rewrite Z_of_nat_S_digits2_Pnat.
change Fcalc_digits.radix2 with radix2.
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

(** mantissa, round and sticky bits *)
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
  | Zpos p => (iter_pos p _ shr_1 mrs, (e + n)%Z)
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
rewrite iter_nat_of_P.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
induction (nat_of_P n).
simpl.
rewrite Zplus_0_r.
now destruct l as [|[| |]].
simpl iter_nat.
rewrite inj_S.
unfold Zsucc.
rewrite  Zplus_assoc.
revert IHn0.
apply inbetween_shr_1.
clear -Hm.
induction n0.
now destruct l as [|[| |]].
simpl.
revert IHn0.
generalize (iter_nat n0 shr_record shr_1 (shr_record_of_loc m l)).
clear.
intros (m, r, s) Hm.
now destruct m as [|[m|m|]|m] ; try (now elim Hm) ; destruct r as [|] ; destruct s as [|].
Qed.

Definition Zdigits2 m :=
  match m with Z0 => m | Zpos p => Z_of_nat (S (digits2_Pnat p)) | Zneg p => Z_of_nat (S (digits2_Pnat p)) end.

Theorem Zdigits2_Zdigits :
  forall m,
  Zdigits2 m = Zdigits radix2 m.
Proof.
unfold Zdigits2.
intros [|m|m] ; try apply Z_of_nat_S_digits2_Pnat.
easy.
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
  | _ => F754_nan (* dummy *)
  end.

Theorem binary_round_aux_correct :
  forall mode x mx ex lx,
  inbetween_float radix2 (Zpos mx) ex (Rabs x) lx ->
  (ex <= fexp (Zdigits radix2 (Zpos mx) + ex))%Z ->
  let z := binary_round_aux mode (Rlt_bool x 0) mx ex lx in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode) x)) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode mode) x /\
    is_finite_FF z = true
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
intros z.
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
rewrite Z_of_nat_S_digits2_Pnat.
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
rewrite Z_of_nat_S_digits2_Pnat.
change Fcalc_digits.radix2 with radix2.
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

Definition Bsign x :=
  match x with
  | B754_nan => false
  | B754_zero s => s
  | B754_infinity s => s
  | B754_finite s _ _ _ => s
  end.

Definition sign_FF x :=
  match x with
  | F754_nan => false
  | F754_zero s => s
  | F754_infinity s => s
  | F754_finite s _ _ => s
  end.

Theorem Bsign_FF2B :
  forall x H,
  Bsign (FF2B x H) = sign_FF x.
Proof.
now intros [sx|sx| |sx mx ex] H.
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
    is_finite_FF z = true
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
now rewrite <- Z_of_nat_S_digits2_Pnat.
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

Definition Bmult m x y :=
  match x, y with
  | B754_nan, _ => x
  | _, B754_nan => y
  | B754_infinity sx, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xorb sx sy)
  | B754_infinity _, B754_zero _ => B754_nan
  | B754_zero _, B754_infinity _ => B754_nan
  | B754_finite sx _ _ _, B754_zero sy => B754_zero (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_zero (xorb sx sy)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    FF2B _ (proj1 (Bmult_correct_aux m sx mx ex Hx sy my ey Hy))
  end.

Theorem Bmult_correct :
  forall m x y,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x * B2R y))) (bpow radix2 emax) then
    B2R (Bmult m x y) = round radix2 fexp (round_mode m) (B2R x * B2R y) /\
    is_finite (Bmult m x y) = andb (is_finite x) (is_finite y)
  else
    B2FF (Bmult m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ;
  try ( rewrite ?Rmult_0_r, ?Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ split ; apply refl_equal | apply bpow_gt_0 | auto with typeclass_instances ] ).
simpl.
case Bmult_correct_aux.
intros H1.
case Rlt_bool.
intros (H2, H3).
split.
now rewrite B2R_FF2B.
now rewrite is_finite_FF2B.
intros H2.
now rewrite B2FF_FF2B.
Qed.

Definition Bmult_FF m x y :=
  match x, y with
  | F754_nan, _ => x
  | _, F754_nan => y
  | F754_infinity sx, F754_infinity sy => F754_infinity (xorb sx sy)
  | F754_infinity sx, F754_finite sy _ _ => F754_infinity (xorb sx sy)
  | F754_finite sx _ _, F754_infinity sy => F754_infinity (xorb sx sy)
  | F754_infinity _, F754_zero _ => F754_nan
  | F754_zero _, F754_infinity _ => F754_nan
  | F754_finite sx _ _, F754_zero sy => F754_zero (xorb sx sy)
  | F754_zero sx, F754_finite sy _ _ => F754_zero (xorb sx sy)
  | F754_zero sx, F754_zero sy => F754_zero (xorb sx sy)
  | F754_finite sx mx ex, F754_finite sy my ey =>
    binary_round_aux m (xorb sx sy) (mx * my) (ex + ey) loc_Exact
  end.

Theorem B2FF_Bmult :
  forall m x y,
  B2FF (Bmult m x y) = Bmult_FF m (B2FF x) (B2FF y).
Proof.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] ; try easy.
apply B2FF_FF2B.
Qed.


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
  shl_align mx ex (fexp (Z_of_nat (S (digits2_Pnat mx)) + ex)).

Theorem shl_align_fexp_correct :
  forall mx ex,
  let (mx', ex') := shl_align_fexp mx ex in
  F2R (Float radix2 (Zpos mx) ex) = F2R (Float radix2 (Zpos mx') ex') /\
  (ex' <= fexp (Zdigits radix2 (Zpos mx') + ex'))%Z.
Proof.
intros mx ex.
unfold shl_align_fexp.
generalize (shl_align_correct mx ex (fexp (Z_of_nat (S (digits2_Pnat mx)) + ex))).
rewrite Z_of_nat_S_digits2_Pnat.
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
    is_finite_FF z = true
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
    is_finite (binary_normalize m mx ex szero) = true
  else
    B2FF (binary_normalize m mx ex szero) = binary_overflow m (Rlt_bool (F2R (Float radix2 mx ex)) 0).
Proof with auto with typeclass_instances.
intros m mx ez szero.
destruct mx as [|mz|mz] ; simpl.
rewrite F2R_0, round_0, Rabs_R0, Rlt_bool_true...
apply bpow_gt_0.
(* . mz > 0 *)
generalize (binary_round_correct m false mz ez).
simpl.
case Rlt_bool_spec.
intros _ (Vz, (Rz, Rz')).
split.
now rewrite B2R_FF2B.
now rewrite is_finite_FF2B.
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
intros _ (Vz, (Rz, Rz')).
split.
now rewrite B2R_FF2B.
now rewrite is_finite_FF2B.
intros Hz' (Vz, Rz).
rewrite B2FF_FF2B, Rz.
apply f_equal.
apply sym_eq.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
Qed.

(** Addition *)
Definition Bplus m x y :=
  match x, y with
  | B754_nan, _ => x
  | _, B754_nan => y
  | B754_infinity sx, B754_infinity sy =>
    if Bool.eqb sx sy then x else B754_nan
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
  forall m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x + B2R y))) (bpow radix2 emax) then
    B2R (Bplus m x y) = round radix2 fexp (round_mode m) (B2R x + B2R y) /\
    is_finite (Bplus m x y) = true
  else
    (B2FF (Bplus m x y) = binary_overflow m (Bsign x) /\ Bsign x = Bsign y).
Proof with auto with typeclass_instances.
intros m [sx|sx| |sx mx ex Hx] [sy|sy| |sy my ey Hy] Fx Fy ; try easy.
(* *)
rewrite Rplus_0_r, round_0, Rabs_R0, Rlt_bool_true...
simpl.
case (Bool.eqb sx sy) ; try easy.
now case m.
apply bpow_gt_0.
(* *)
rewrite Rplus_0_l, round_generic, Rlt_bool_true...
apply abs_B2R_lt_emax.
apply generic_format_B2R.
(* *)
rewrite Rplus_0_r, round_generic, Rlt_bool_true...
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
clear -Bx By Hs.
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
easy.
intros Hz' Vz.
specialize (Sz Hz').
split.
rewrite Vz.
now apply f_equal.
apply Sz.
Qed.

Definition Bminus m x y := Bplus m x (Bopp y).

Theorem Bminus_correct :
  forall m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x - B2R y))) (bpow radix2 emax) then
    B2R (Bminus m x y) = round radix2 fexp (round_mode m) (B2R x - B2R y) /\
    is_finite (Bminus m x y) = true
  else
    (B2FF (Bminus m x y) = binary_overflow m (Bsign x) /\ Bsign x = negb (Bsign y)).
Proof with auto with typeclass_instances.
intros m x y Fx Fy.
replace (negb (Bsign y)) with (Bsign (Bopp y)).
unfold Rminus.
rewrite <- B2R_Bopp.
apply Bplus_correct.
exact Fx.
now rewrite is_finite_Bopp.
now destruct y as [ | | | ].
Qed.

(** Division *)
Definition Fdiv_core_binary m1 e1 m2 e2 :=
  let d1 := Zdigits2 m1 in
  let d2 := Zdigits2 m2 in
  let e := (e1 - e2)%Z in
  let (m, e') :=
    match (d2 + prec - d1)%Z with
    | Zpos p => (m1 * Zpower_pos 2 p, e + Zneg p)%Z
    | _ => (m1, e)
    end in
  let '(q, r) :=  Zdiv_eucl m m2 in
  (q, e', new_location m2 r loc_Exact).

Lemma Bdiv_correct_aux :
  forall m sx mx ex sy my ey,
  let x := F2R (Float radix2 (cond_Zopp sx (Zpos mx)) ex) in
  let y := F2R (Float radix2 (cond_Zopp sy (Zpos my)) ey) in
  let z :=
    let '(mz, ez, lz) := Fdiv_core_binary (Zpos mx) ex (Zpos my) ey in
    match mz with
    | Zpos mz => binary_round_aux m (xorb sx sy) mz ez lz
    | _ => F754_nan (* dummy *)
    end in
  valid_binary z = true /\
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (x / y))) (bpow radix2 emax) then
    FF2R radix2 z = round radix2 fexp (round_mode m) (x / y) /\
    is_finite_FF z = true
  else
    z = binary_overflow m (xorb sx sy).
Proof.
intros m sx mx ex sy my ey.
replace (Fdiv_core_binary (Zpos mx) ex (Zpos my) ey) with (Fdiv_core radix2 prec (Zpos mx) ex (Zpos my) ey).
2: now unfold Fdiv_core_binary ; rewrite 2!Zdigits2_Zdigits.
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
Qed.

Definition Bdiv m x y :=
  match x, y with
  | B754_nan, _ => x
  | _, B754_nan => y
  | B754_infinity sx, B754_infinity sy => B754_nan
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xorb sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_infinity sx, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_infinity sy => B754_zero (xorb sx sy)
  | B754_finite sx _ _ _, B754_zero sy => B754_infinity (xorb sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xorb sx sy)
  | B754_zero sx, B754_zero sy => B754_nan
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>
    FF2B _ (proj1 (Bdiv_correct_aux m sx mx ex sy my ey))
  end.

Theorem Bdiv_correct :
  forall m x y,
  B2R y <> R0 ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x / B2R y))) (bpow radix2 emax) then
    B2R (Bdiv m x y) = round radix2 fexp (round_mode m) (B2R x / B2R y) /\
    is_finite (Bdiv m x y) = is_finite x
  else
    B2FF (Bdiv m x y) = binary_overflow m (xorb (Bsign x) (Bsign y)).
Proof.
intros m x [sy|sy| |sy my ey Hy] Zy ; try now elim Zy.
revert x.
unfold Rdiv.
intros [sx|sx| |sx mx ex Hx] ;
  try ( rewrite Rmult_0_l, round_0, Rabs_R0, Rlt_bool_true ; [ split ; apply refl_equal | apply bpow_gt_0 | auto with typeclass_instances ] ).
simpl.
case Bdiv_correct_aux.
intros H1.
unfold Rdiv.
case Rlt_bool.
intros (H2, H3).
split.
now rewrite B2R_FF2B.
now rewrite is_finite_FF2B.
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
    | Zpos p => (m * Zpower_pos 2 p)%Z
    | _ => m
    end in
  let (q, r) := Zsqrt m' in
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
    | _ => F754_nan (* dummy *)
    end in
  valid_binary z = true /\
  FF2R radix2 z = round radix2 fexp (round_mode m) (sqrt x) /\
  is_finite_FF z = true.
Proof with auto with typeclass_instances.
intros m mx ex Hx.
replace (Fsqrt_core_binary (Zpos mx) ex) with (Fsqrt_core radix2 prec (Zpos mx) ex).
2: now unfold Fsqrt_core_binary ; rewrite Zdigits2_Zdigits.
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
Qed.

Definition Bsqrt m x :=
  match x with
  | B754_nan => x
  | B754_infinity false => x
  | B754_infinity true => B754_nan
  | B754_finite true _ _ _ => B754_nan
  | B754_zero _ => x
  | B754_finite sx mx ex Hx =>
    FF2B _ (proj1 (Bsqrt_correct_aux m mx ex Hx))
  end.

Theorem Bsqrt_correct :
  forall m x,
  B2R (Bsqrt m x) = round radix2 fexp (round_mode m) (sqrt (B2R x)) /\
  is_finite (Bsqrt m x) = match x with B754_zero _ => true | B754_finite false _ _ _ => true | _ => false end.
Proof.
intros m [sx|[|]| |sx mx ex Hx] ; try ( now simpl ; rewrite sqrt_0, round_0 ; auto with typeclass_instances ).
simpl.
case Bsqrt_correct_aux.
intros H1 (H2, H3).
case sx.
refine (conj _ (refl_equal false)).
apply sym_eq.
unfold sqrt.
case Rcase_abs.
intros _.
apply round_0.
auto with typeclass_instances.
intros H.
elim Rge_not_lt with (1 := H).
now apply F2R_lt_0_compat.
split.
now rewrite B2R_FF2B.
now rewrite is_finite_FF2B.
Qed.

End Binary.

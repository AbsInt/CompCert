(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2011 Sylvie Boldo
#<br />#
Copyright (C) 2011 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import ZArith.
Require Import ZOdiv.

Section Zmissing.

(** About Z *)
Theorem Zopp_le_cancel :
  forall x y : Z,
  (-y <= -x)%Z -> Zle x y.
Proof.
intros x y Hxy.
apply Zplus_le_reg_r with (-x - y)%Z.
now ring_simplify.
Qed.

Theorem Zgt_not_eq :
  forall x y : Z,
  (y < x)%Z -> (x <> y)%Z.
Proof.
intros x y H Hn.
apply Zlt_irrefl with x.
now rewrite Hn at 1.
Qed.

End Zmissing.

Section Proof_Irrelevance.

Scheme eq_dep_elim := Induction for eq Sort Type.

Definition eqbool_dep P (h1 : P true) b :=
  match b return P b -> Prop with
  | true => fun (h2 : P true) => h1 = h2
  | false => fun (h2 : P false) => False
  end.

Lemma eqbool_irrelevance : forall (b : bool) (h1 h2 : b = true), h1 = h2.
Proof.
assert (forall (h : true = true), refl_equal true = h).
apply (eq_dep_elim bool true (eqbool_dep _ _) (refl_equal _)).
intros b.
case b.
intros h1 h2.
now rewrite <- (H h1).
intros h.
discriminate h.
Qed.

End Proof_Irrelevance.

Section Even_Odd.

(** Zeven, used for rounding to nearest, ties to even *)
Definition Zeven (n : Z) :=
  match n with
  | Zpos (xO _) => true
  | Zneg (xO _) => true
  | Z0 => true
  | _ => false
  end.

Theorem Zeven_mult :
  forall x y, Zeven (x * y) = orb (Zeven x) (Zeven y).
Proof.
now intros [|[xp|xp|]|[xp|xp|]] [|[yp|yp|]|[yp|yp|]].
Qed.

Theorem Zeven_opp :
  forall x, Zeven (- x) = Zeven x.
Proof.
now intros [|[n|n|]|[n|n|]].
Qed.

Theorem Zeven_ex :
  forall x, exists p, x = (2 * p + if Zeven x then 0 else 1)%Z.
Proof.
intros [|[n|n|]|[n|n|]].
now exists Z0.
now exists (Zpos n).
now exists (Zpos n).
now exists Z0.
exists (Zneg n - 1)%Z.
change (2 * Zneg n - 1 = 2 * (Zneg n - 1) + 1)%Z.
ring.
now exists (Zneg n).
now exists (-1)%Z.
Qed.

Theorem Zeven_2xp1 :
  forall n, Zeven (2 * n + 1) = false.
Proof.
intros n.
destruct (Zeven_ex (2 * n + 1)) as (p, Hp).
revert Hp.
case (Zeven (2 * n + 1)) ; try easy.
intros H.
apply False_ind.
omega.
Qed.

Theorem Zeven_plus :
  forall x y, Zeven (x + y) = Bool.eqb (Zeven x) (Zeven y).
Proof.
intros x y.
destruct (Zeven_ex x) as (px, Hx).
rewrite Hx at 1.
destruct (Zeven_ex y) as (py, Hy).
rewrite Hy at 1.
replace (2 * px + (if Zeven x then 0 else 1) + (2 * py + (if Zeven y then 0 else 1)))%Z
  with (2 * (px + py) + ((if Zeven x then 0 else 1) + (if Zeven y then 0 else 1)))%Z by ring.
case (Zeven x) ; case (Zeven y).
rewrite Zplus_0_r.
now rewrite Zeven_mult.
apply Zeven_2xp1.
apply Zeven_2xp1.
replace (2 * (px + py) + (1 + 1))%Z with (2 * (px + py + 1))%Z by ring.
now rewrite Zeven_mult.
Qed.

End Even_Odd.

Section Zpower.

Theorem Zpower_plus :
  forall n k1 k2, (0 <= k1)%Z -> (0 <= k2)%Z ->
  Zpower n (k1 + k2) = (Zpower n k1 * Zpower n k2)%Z.
Proof.
intros n k1 k2 H1 H2.
now apply Zpower_exp ; apply Zle_ge.
Qed.

Theorem Zpower_Zpower_nat :
  forall b e, (0 <= e)%Z ->
  Zpower b e = Zpower_nat b (Zabs_nat e).
Proof.
intros b [|e|e] He.
apply refl_equal.
apply Zpower_pos_nat.
elim He.
apply refl_equal.
Qed.

Theorem Zpower_nat_S :
  forall b e,
  Zpower_nat b (S e) = (b * Zpower_nat b e)%Z.
Proof.
intros b e.
rewrite (Zpower_nat_is_exp 1 e).
apply (f_equal (fun x => x * _)%Z).
apply Zmult_1_r.
Qed.

Theorem Zpower_pos_gt_0 :
  forall b p, (0 < b)%Z ->
  (0 < Zpower_pos b p)%Z.
Proof.
intros b p Hb.
rewrite Zpower_pos_nat.
induction (nat_of_P p).
easy.
rewrite Zpower_nat_S.
now apply Zmult_lt_0_compat.
Qed.

Theorem Zeven_Zpower :
  forall b e, (0 < e)%Z ->
  Zeven (Zpower b e) = Zeven b.
Proof.
intros b e He.
case_eq (Zeven b) ; intros Hb.
(* b even *)
replace e with (e - 1 + 1)%Z by ring.
rewrite Zpower_exp.
rewrite Zeven_mult.
replace (Zeven (b ^ 1)) with true.
apply Bool.orb_true_r.
unfold Zpower, Zpower_pos. simpl.
now rewrite Zmult_1_r.
omega.
discriminate.
(* b odd *)
rewrite Zpower_Zpower_nat.
induction (Zabs_nat e).
easy.
unfold Zpower_nat. simpl.
rewrite Zeven_mult.
now rewrite Hb.
now apply Zlt_le_weak.
Qed.

Theorem Zeven_Zpower_odd :
  forall b e, (0 <= e)%Z -> Zeven b = false ->
  Zeven (Zpower b e) = false.
Proof.
intros b e He Hb.
destruct (Z_le_lt_eq_dec _ _ He) as [He'|He'].
rewrite <- Hb.
now apply Zeven_Zpower.
now rewrite <- He'.
Qed.

(** The radix must be greater than 1 *)
Record radix := { radix_val :> Z ; radix_prop : Zle_bool 2 radix_val = true }.

Theorem radix_val_inj :
  forall r1 r2, radix_val r1 = radix_val r2 -> r1 = r2.
Proof.
intros (r1, H1) (r2, H2) H.
simpl in H.
revert H1.
rewrite H.
intros H1.
apply f_equal.
apply eqbool_irrelevance.
Qed.

Variable r : radix.

Theorem radix_gt_0 : (0 < r)%Z.
Proof.
apply Zlt_le_trans with 2%Z.
easy.
apply Zle_bool_imp_le.
apply r.
Qed.

Theorem radix_gt_1 : (1 < r)%Z.
Proof.
destruct r as (v, Hr). simpl.
apply Zlt_le_trans with 2%Z.
easy.
now apply Zle_bool_imp_le.
Qed.

Theorem Zpower_gt_1 :
  forall p,
  (0 < p)%Z ->
  (1 < Zpower r p)%Z.
Proof.
intros [|p|p] Hp ; try easy.
simpl.
rewrite Zpower_pos_nat.
generalize (lt_O_nat_of_P p).
induction (nat_of_P p).
easy.
intros _.
rewrite Zpower_nat_S.
assert (0 < Zpower_nat r n)%Z.
clear.
induction n.
easy.
rewrite Zpower_nat_S.
apply Zmult_lt_0_compat with (2 := IHn).
apply radix_gt_0.
apply Zle_lt_trans with (1 * Zpower_nat r n)%Z.
rewrite Zmult_1_l.
now apply (Zlt_le_succ 0).
apply Zmult_lt_compat_r with (1 := H).
apply radix_gt_1.
Qed.

Theorem Zpower_gt_0 :
  forall p,
  (0 <= p)%Z ->
  (0 < Zpower r p)%Z.
Proof.
intros p Hp.
rewrite Zpower_Zpower_nat with (1 := Hp).
induction (Zabs_nat p).
easy.
rewrite Zpower_nat_S.
apply Zmult_lt_0_compat with (2 := IHn).
apply radix_gt_0.
Qed.

Theorem Zpower_ge_0 :
  forall e,
  (0 <= Zpower r e)%Z.
Proof.
intros [|e|e] ; try easy.
apply Zlt_le_weak.
now apply Zpower_gt_0.
Qed.

Theorem Zpower_le :
  forall e1 e2, (e1 <= e2)%Z ->
  (Zpower r e1 <= Zpower r e2)%Z.
Proof.
intros e1 e2 He.
destruct (Zle_or_lt 0 e1)%Z as [H1|H1].
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite Zpower_plus with (2 := H1).
rewrite <- (Zmult_1_l (r ^ e1)) at 1.
apply Zmult_le_compat_r.
apply (Zlt_le_succ 0).
apply Zpower_gt_0.
now apply Zle_minus_le_0.
apply Zpower_ge_0.
now apply Zle_minus_le_0.
clear He.
destruct e1 as [|e1|e1] ; try easy.
apply Zpower_ge_0.
Qed.

Theorem Zpower_lt :
  forall e1 e2, (0 <= e2)%Z -> (e1 < e2)%Z ->
  (Zpower r e1 < Zpower r e2)%Z.
Proof.
intros e1 e2 He2 He.
destruct (Zle_or_lt 0 e1)%Z as [H1|H1].
replace e2 with (e2 - e1 + e1)%Z by ring.
rewrite Zpower_plus with (2 := H1).
rewrite Zmult_comm.
rewrite <- (Zmult_1_r (r ^ e1)) at 1.
apply Zmult_lt_compat2.
split.
now apply Zpower_gt_0.
apply Zle_refl.
split.
easy.
apply Zpower_gt_1.
clear -He ; omega.
apply Zle_minus_le_0.
now apply Zlt_le_weak.
revert H1.
clear -He2.
destruct e1 ; try easy.
intros _.
now apply Zpower_gt_0.
Qed.

Theorem Zpower_lt_Zpower :
  forall e1 e2,
  (Zpower r (e1 - 1) < Zpower r e2)%Z ->
  (e1 <= e2)%Z.
Proof.
intros e1 e2 He.
apply Znot_gt_le.
intros H.
apply Zlt_not_le with (1 := He).
apply Zpower_le.
clear -H ; omega.
Qed.

End Zpower.

Section Div_Mod.

Theorem Zmod_mod_mult :
  forall n a b, (0 < a)%Z -> (0 <= b)%Z ->
  Zmod (Zmod n (a * b)) b = Zmod n b.
Proof.
intros n a [|b|b] Ha Hb.
now rewrite 2!Zmod_0_r.
rewrite (Zmod_eq n (a * Zpos b)).
rewrite Zmult_assoc.
unfold Zminus.
rewrite Zopp_mult_distr_l.
apply Z_mod_plus.
easy.
apply Zmult_gt_0_compat.
now apply Zlt_gt.
easy.
now elim Hb.
Qed.

Theorem ZOmod_eq :
  forall a b,
  ZOmod a b = (a - ZOdiv a b * b)%Z.
Proof.
intros a b.
rewrite (ZO_div_mod_eq a b) at 2.
ring.
Qed.

Theorem ZOmod_mod_mult :
  forall n a b,
  ZOmod (ZOmod n (a * b)) b = ZOmod n b.
Proof.
intros n a b.
assert (ZOmod n (a * b) = n + - (ZOdiv n (a * b) * a) * b)%Z.
rewrite <- Zopp_mult_distr_l.
rewrite <- Zmult_assoc.
apply ZOmod_eq.
rewrite H.
apply ZO_mod_plus.
rewrite <- H.
apply ZOmod_sgn2.
Qed.

Theorem Zdiv_mod_mult :
  forall n a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (Zdiv (Zmod n (a * b)) a) = Zmod (Zdiv n a) b.
Proof.
intros n a b Ha Hb.
destruct (Zle_lt_or_eq _ _ Ha) as [Ha'|Ha'].
destruct (Zle_lt_or_eq _ _ Hb) as [Hb'|Hb'].
rewrite (Zmod_eq n (a * b)).
rewrite (Zmult_comm a b) at 2.
rewrite Zmult_assoc.
unfold Zminus.
rewrite Zopp_mult_distr_l.
rewrite Z_div_plus by now apply Zlt_gt.
rewrite <- Zdiv_Zdiv by easy.
apply sym_eq.
apply Zmod_eq.
now apply Zlt_gt.
now apply Zmult_gt_0_compat ; apply Zlt_gt.
rewrite <- Hb'.
rewrite Zmult_0_r, 2!Zmod_0_r.
apply Zdiv_0_l.
rewrite <- Ha'.
now rewrite 2!Zdiv_0_r, Zmod_0_l.
Qed.

Theorem ZOdiv_mod_mult :
  forall n a b,
  (ZOdiv (ZOmod n (a * b)) a) = ZOmod (ZOdiv n a) b.
Proof.
intros n a b.
destruct (Z_eq_dec a 0) as [Za|Za].
rewrite Za.
now rewrite 2!ZOdiv_0_r, ZOmod_0_l.
assert (ZOmod n (a * b) = n + - (ZOdiv (ZOdiv n a) b * b) * a)%Z.
rewrite (ZOmod_eq n (a * b)) at 1.
rewrite ZOdiv_ZOdiv.
ring.
rewrite H.
rewrite ZO_div_plus with (2 := Za).
apply sym_eq.
apply ZOmod_eq.
rewrite <- H.
apply ZOmod_sgn2.
Qed.

Theorem ZOdiv_small_abs :
  forall a b,
  (Zabs a < b)%Z -> ZOdiv a b = Z0.
Proof.
intros a b Ha.
destruct (Zle_or_lt 0 a) as [H|H].
apply ZOdiv_small.
split.
exact H.
now rewrite Zabs_eq in Ha.
apply Zopp_inj.
rewrite <- ZOdiv_opp_l, Zopp_0.
apply ZOdiv_small.
generalize (Zabs_non_eq a).
omega.
Qed.

Theorem ZOmod_small_abs :
  forall a b,
  (Zabs a < b)%Z -> ZOmod a b = a.
Proof.
intros a b Ha.
destruct (Zle_or_lt 0 a) as [H|H].
apply ZOmod_small.
split.
exact H.
now rewrite Zabs_eq in Ha.
apply Zopp_inj.
rewrite <- ZOmod_opp_l.
apply ZOmod_small.
generalize (Zabs_non_eq a).
omega.
Qed.

Theorem ZOdiv_plus :
  forall a b c, (0 <= a * b)%Z ->
  (ZOdiv (a + b) c = ZOdiv a c + ZOdiv b c + ZOdiv (ZOmod a c + ZOmod b c) c)%Z.
Proof.
intros a b c Hab.
destruct (Z_eq_dec c 0) as [Zc|Zc].
now rewrite Zc, 4!ZOdiv_0_r.
apply Zmult_reg_r with (1 := Zc).
rewrite 2!Zmult_plus_distr_l.
assert (forall d, ZOdiv d c * c = d - ZOmod d c)%Z.
intros d.
rewrite ZOmod_eq.
ring.
rewrite 4!H.
rewrite <- ZOplus_mod with (1 := Hab).
ring.
Qed.

End Div_Mod.

Section Same_sign.

Theorem Zsame_sign_trans :
  forall v u w, v <> Z0 ->
  (0 <= u * v)%Z -> (0 <= v * w)%Z -> (0 <= u * w)%Z.
Proof.
intros [|v|v] [|u|u] [|w|w] Zv Huv Hvw ; try easy ; now elim Zv.
Qed.

Theorem Zsame_sign_trans_weak :
  forall v u w, (v = Z0 -> w = Z0) ->
  (0 <= u * v)%Z -> (0 <= v * w)%Z -> (0 <= u * w)%Z.
Proof.
intros [|v|v] [|u|u] [|w|w] Zv Huv Hvw ; try easy ; now discriminate Zv.
Qed.

Theorem Zsame_sign_imp :
  forall u v,
  (0 < u -> 0 <= v)%Z ->
  (0 < -u -> 0 <= -v)%Z ->
  (0 <= u * v)%Z.
Proof.
intros [|u|u] v Hp Hn.
easy.
apply Zmult_le_0_compat.
easy.
now apply Hp.
replace (Zneg u * v)%Z with (Zpos u * (-v))%Z.
apply Zmult_le_0_compat.
easy.
now apply Hn.
rewrite <- Zopp_mult_distr_r.
apply Zopp_mult_distr_l.
Qed.

Theorem Zsame_sign_odiv :
  forall u v, (0 <= v)%Z ->
  (0 <= u * ZOdiv u v)%Z.
Proof.
intros u v Hv.
apply Zsame_sign_imp ; intros Hu.
apply ZO_div_pos with (2 := Hv).
now apply Zlt_le_weak.
rewrite <- ZOdiv_opp_l.
apply ZO_div_pos with (2 := Hv).
now apply Zlt_le_weak.
Qed.

End Same_sign.

(** Boolean comparisons *)

Section Zeq_bool.

Inductive Zeq_bool_prop (x y : Z) : bool -> Prop :=
  | Zeq_bool_true_ : x = y -> Zeq_bool_prop x y true
  | Zeq_bool_false_ : x <> y -> Zeq_bool_prop x y false.

Theorem Zeq_bool_spec :
  forall x y, Zeq_bool_prop x y (Zeq_bool x y).
Proof.
intros x y.
generalize (Zeq_is_eq_bool x y).
case (Zeq_bool x y) ; intros (H1, H2) ; constructor.
now apply H2.
intros H.
specialize (H1 H).
discriminate H1.
Qed.

Theorem Zeq_bool_true :
  forall x y, x = y -> Zeq_bool x y = true.
Proof.
intros x y.
apply -> Zeq_is_eq_bool.
Qed.

Theorem Zeq_bool_false :
  forall x y, x <> y -> Zeq_bool x y = false.
Proof.
intros x y.
generalize (proj2 (Zeq_is_eq_bool x y)).
case Zeq_bool.
intros He Hn.
elim Hn.
now apply He.
now intros _ _.
Qed.

End Zeq_bool.

Section Zle_bool.

Inductive Zle_bool_prop (x y : Z) : bool -> Prop :=
  | Zle_bool_true_ : (x <= y)%Z -> Zle_bool_prop x y true
  | Zle_bool_false_ : (y < x)%Z -> Zle_bool_prop x y false.

Theorem Zle_bool_spec :
  forall x y, Zle_bool_prop x y (Zle_bool x y).
Proof.
intros x y.
generalize (Zle_is_le_bool x y).
case Zle_bool ; intros (H1, H2) ; constructor.
now apply H2.
destruct (Zle_or_lt x y) as [H|H].
now specialize (H1 H).
exact H.
Qed.

Theorem Zle_bool_true :
  forall x y : Z,
  (x <= y)%Z -> Zle_bool x y = true.
Proof.
intros x y.
apply (proj1 (Zle_is_le_bool x y)).
Qed.

Theorem Zle_bool_false :
  forall x y : Z,
  (y < x)%Z -> Zle_bool x y = false.
Proof.
intros x y Hxy.
generalize (Zle_cases x y).
case Zle_bool ; intros H.
elim (Zlt_irrefl x).
now apply Zle_lt_trans with y.
apply refl_equal.
Qed.

End Zle_bool.

Section Zlt_bool.

Inductive Zlt_bool_prop (x y : Z) : bool -> Prop :=
  | Zlt_bool_true_ : (x < y)%Z -> Zlt_bool_prop x y true
  | Zlt_bool_false_ : (y <= x)%Z -> Zlt_bool_prop x y false.

Theorem Zlt_bool_spec :
  forall x y, Zlt_bool_prop x y (Zlt_bool x y).
Proof.
intros x y.
generalize (Zlt_is_lt_bool x y).
case Zlt_bool ; intros (H1, H2) ; constructor.
now apply H2.
destruct (Zle_or_lt y x) as [H|H].
exact H.
now specialize (H1 H).
Qed.

Theorem Zlt_bool_true :
  forall x y : Z,
  (x < y)%Z -> Zlt_bool x y = true.
Proof.
intros x y.
apply (proj1 (Zlt_is_lt_bool x y)).
Qed.

Theorem Zlt_bool_false :
  forall x y : Z,
  (y <= x)%Z -> Zlt_bool x y = false.
Proof.
intros x y Hxy.
generalize (Zlt_cases x y).
case Zlt_bool ; intros H.
elim (Zlt_irrefl x).
now apply Zlt_le_trans with y.
apply refl_equal.
Qed.

Theorem negb_Zle_bool :
  forall x y : Z,
  negb (Zle_bool x y) = Zlt_bool y x.
Proof.
intros x y.
case Zle_bool_spec ; intros H.
now rewrite Zlt_bool_false.
now rewrite Zlt_bool_true.
Qed.

Theorem negb_Zlt_bool :
  forall x y : Z,
  negb (Zlt_bool x y) = Zle_bool y x.
Proof.
intros x y.
case Zlt_bool_spec ; intros H.
now rewrite Zle_bool_false.
now rewrite Zle_bool_true.
Qed.

End Zlt_bool.

Section Zcompare.

Inductive Zcompare_prop (x y : Z) : comparison -> Prop :=
  | Zcompare_Lt_ : (x < y)%Z -> Zcompare_prop x y Lt
  | Zcompare_Eq_ : x = y -> Zcompare_prop x y Eq
  | Zcompare_Gt_ : (y < x)%Z -> Zcompare_prop x y Gt.

Theorem Zcompare_spec :
  forall x y, Zcompare_prop x y (Zcompare x y).
Proof.
intros x y.
destruct (Z_dec x y) as [[H|H]|H].
generalize (Zlt_compare _ _ H).
case (Zcompare x y) ; try easy.
now constructor.
generalize (Zgt_compare _ _ H).
case (Zcompare x y) ; try easy.
constructor.
now apply Zgt_lt.
generalize (proj2 (Zcompare_Eq_iff_eq _ _) H).
case (Zcompare x y) ; try easy.
now constructor.
Qed.

Theorem Zcompare_Lt :
  forall x y,
  (x < y)%Z -> Zcompare x y = Lt.
Proof.
easy.
Qed.

Theorem Zcompare_Eq :
  forall x y,
  (x = y)%Z -> Zcompare x y = Eq.
Proof.
intros x y.
apply <- Zcompare_Eq_iff_eq.
Qed.

Theorem Zcompare_Gt :
  forall x y,
  (y < x)%Z -> Zcompare x y = Gt.
Proof.
intros x y.
apply Zlt_gt.
Qed.

End Zcompare.

Section cond_Zopp.

Definition cond_Zopp (b : bool) m := if b then Zopp m else m.

Theorem abs_cond_Zopp :
  forall b m,
  Zabs (cond_Zopp b m) = Zabs m.
Proof.
intros [|] m.
apply Zabs_Zopp.
apply refl_equal.
Qed.

Theorem cond_Zopp_Zlt_bool :
  forall m,
  cond_Zopp (Zlt_bool m 0) m = Zabs m.
Proof.
intros m.
apply sym_eq.
case Zlt_bool_spec ; intros Hm.
apply Zabs_non_eq.
now apply Zlt_le_weak.
now apply Zabs_eq.
Qed.

End cond_Zopp.

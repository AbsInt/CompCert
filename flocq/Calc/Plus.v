(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2010-2021 Sylvie Boldo
#<br />#
Copyright (C) 2010-2021 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** * Helper function and theorem for computing the rounded sum of two floating-point numbers. *)

From Coq Require Import ZArith Reals Lia.

Require Import Core Bracket Operations Round.

Section Plus.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.

Context { monotone_exp : Monotone_exp fexp }.

Definition Fplus_core m1 e1 m2 e2 e :=
  let k := (e - e2)%Z in
  let '(m2', _, l) :=
    if Zlt_bool 0 k then truncate_aux beta (m2, e2, loc_Exact) k
    else (m2 * Zpower beta (-k), e, loc_Exact)%Z in
  let m1' := (m1 * Zpower beta (e1 - e))%Z in
  (m1' + m2', l)%Z.

Theorem Fplus_core_correct :
  forall m1 e1 m2 e2 e,
  (e <= e1)%Z ->
  let '(m, l) := Fplus_core m1 e1 m2 e2 e in
  inbetween_float beta m e (F2R (Float beta m1 e1) + F2R (Float beta m2 e2)) l.
Proof.
intros m1 e1 m2 e2 e He1.
unfold Fplus_core.
case Zlt_bool_spec ; intros He2.
- unfold truncate_aux.
  unfold inbetween_float, F2R. simpl.
  rewrite 3!plus_IZR.
  rewrite Rplus_assoc.
  rewrite 2!Rmult_plus_distr_r.
  replace (IZR (m1 * Zpower beta (e1 - e)) * bpow e)%R with (IZR m1 * bpow e1)%R.
  2: {
    rewrite mult_IZR, IZR_Zpower by lia.
    rewrite Rmult_assoc, <- bpow_plus.
    apply (f_equal (fun v => IZR m1 * bpow v)%R).
    ring.
  }
  rewrite <- 3!(Rplus_comm _ (IZR m1 * bpow e1)).
  apply inbetween_plus_compat.
  set (k := (e - e2)%Z).
  rewrite <- (plus_IZR _ 1).
  replace e with (e2 + k)%Z by (unfold k ; ring).
  apply inbetween_float_new_location.
  exact He2.
  now constructor 1.
- constructor 1.
  unfold F2R. simpl.
  rewrite plus_IZR, Rmult_plus_distr_r.
  rewrite 2!mult_IZR, 2!IZR_Zpower by lia.
  rewrite 2!Rmult_assoc, <- 2!bpow_plus.
  apply (f_equal2 (fun v w => IZR m1 * bpow v + IZR m2 * bpow w)%R) ; ring.
Qed.

Definition Fplus (f1 f2 : float beta) :=
  let (m1, e1) := f1 in
  let (m2, e2) := f2 in
  if Zeq_bool m1 0 then
    (m2, e2, loc_Exact)
  else if Zeq_bool m2 0 then
    (m1, e1, loc_Exact)
  else
  let p1 := (Zdigits beta m1 + e1)%Z in
  let p2 := (Zdigits beta m2 + e2)%Z in
  if Zle_bool 2 (Z.abs (p1 - p2)) then
    let e := Z.min (Z.max e1 e2) (fexp (Z.max p1 p2 - 1)) in
    let (m, l) :=
      if Zlt_bool e1 e then
        Fplus_core m2 e2 m1 e1 e
      else
        Fplus_core m1 e1 m2 e2 e in
    (m, e, l)
  else
    let (m, e) := Fplus f1 f2 in
    (m, e, loc_Exact).

Theorem Fplus_correct :
  forall x y,
  let '(m, e, l) := Fplus x y in
  (l = loc_Exact \/ e <= cexp beta fexp (F2R x + F2R y))%Z /\
  inbetween_float beta m e (F2R x + F2R y) l.
Proof.
intros [m1 e1] [m2 e2].
unfold Fplus.
case Zeq_bool_spec ; intros Hm1.
{ rewrite Hm1.
  split.
  now left.
  rewrite F2R_0, Rplus_0_l.
  now constructor 1. }
case Zeq_bool_spec ; intros Hm2.
{ rewrite Hm2.
  split.
  now left.
  rewrite F2R_0, Rplus_0_r.
  now constructor 1. }
set (p1 := (Zdigits beta m1 + e1)%Z).
set (p2 := (Zdigits beta m2 + e2)%Z).
set (e := Z.min (Z.max e1 e2) (fexp (Z.max p1 p2 - 1))).
case Zle_bool_spec ; intros Hp ; cycle 1.
{ rewrite <- F2R_plus.
  destruct Operations.Fplus as [m' e'].
  split.
  now left.
  now constructor 1. }
set (z := (F2R _ + F2R _)%R).
assert (Hz: (e <= cexp beta fexp z)%Z).
{ apply Z.le_trans with (fexp (Z.max p1 p2 - 1)).
  apply Z.le_min_r.
  unfold cexp.
  apply monotone_exp.
  unfold z.
  revert Hp.
  unfold p1, p2.
  rewrite <- 2!mag_F2R_Zdigits by easy.
  clear -Hm1 Hm2.
  destruct (Zle_or_lt (mag beta (F2R (Float beta m1 e1))) (mag beta (F2R (Float beta m2 e2)))) as [Hp'|Hp'].
  - rewrite Z.max_r by easy.
    rewrite Z.abs_neq by (clear -Hp'; lia).
    rewrite Rplus_comm.
    intros H.
    apply mag_plus_ge.
    now apply F2R_neq_0.
    clear -H ; lia.
  - rewrite Z.max_l, Z.abs_eq by (clear -Hp'; lia).
    intros H.
    apply mag_plus_ge.
    now apply F2R_neq_0.
    clear -H ; lia. }
case Zlt_bool_spec ; intros He.
- assert (He': (e <= e2)%Z) by (clear -He ; lia).
  generalize (Fplus_core_correct m2 e2 m1 e1 e He').
  rewrite Rplus_comm.
  fold z.
  destruct Fplus_core as [m' l].
  refine (fun H => conj _ H).
  now right.
- assert (He': (e <= e1)%Z) by (clear -He ; lia).
  generalize (Fplus_core_correct m1 e1 m2 e2 e He').
  fold z.
  destruct Fplus_core as [m' l].
  refine (fun H => conj _ H).
  now right.
Qed.

End Plus.

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

(** Basic operations on floats: alignment, addition, multiplication *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.

Section Float_ops.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Arguments Float {beta} Fnum Fexp.

Definition Falign (f1 f2 : float beta) :=
  let '(Float m1 e1) := f1 in
  let '(Float m2 e2) := f2 in
  if Zle_bool e1 e2
  then (m1, (m2 * Zpower beta (e2 - e1))%Z, e1)
  else ((m1 * Zpower beta (e1 - e2))%Z, m2, e2).

Theorem Falign_spec :
  forall f1 f2 : float beta,
  let '(m1, m2, e) := Falign f1 f2 in
  F2R f1 = @F2R beta (Float m1 e) /\ F2R f2 = @F2R beta (Float m2 e).
Proof.
unfold Falign.
intros (m1, e1) (m2, e2).
generalize (Zle_cases e1 e2).
case (Zle_bool e1 e2) ; intros He ; split ; trivial.
now rewrite <- F2R_change_exp.
rewrite <- F2R_change_exp.
apply refl_equal.
omega.
Qed.

Theorem Falign_spec_exp:
  forall f1 f2 : float beta,
  snd (Falign f1 f2) = Zmin (Fexp f1) (Fexp f2).
Proof.
intros (m1,e1) (m2,e2).
unfold Falign; simpl.
generalize (Zle_cases e1 e2);case (Zle_bool e1 e2); intros He.
case (Zmin_spec e1 e2); intros (H1,H2); easy.
case (Zmin_spec e1 e2); intros (H1,H2); easy.
Qed.

Definition Fopp (f1 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  Float (-m1)%Z e1.

Theorem F2R_opp :
  forall f1 : float beta,
  (F2R (Fopp f1) = -F2R f1)%R.
intros (m1,e1).
apply F2R_Zopp.
Qed.

Definition Fabs (f1 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  Float (Zabs m1)%Z e1.

Theorem F2R_abs :
  forall f1 : float beta,
  (F2R (Fabs f1) = Rabs (F2R f1))%R.
intros (m1,e1).
apply F2R_Zabs.
Qed.

Definition Fplus (f1 f2 : float beta) : float beta :=
  let '(m1, m2 ,e) := Falign f1 f2 in
  Float (m1 + m2) e.

Theorem F2R_plus :
  forall f1 f2 : float beta,
  F2R (Fplus f1 f2) = (F2R f1 + F2R f2)%R.
Proof.
intros f1 f2.
unfold Fplus.
generalize (Falign_spec f1 f2).
destruct (Falign f1 f2) as ((m1, m2), e).
intros (H1, H2).
rewrite H1, H2.
unfold F2R. simpl.
rewrite Z2R_plus.
apply Rmult_plus_distr_r.
Qed.

Theorem Fplus_same_exp :
  forall m1 m2 e,
  Fplus (Float m1 e) (Float m2 e) = Float (m1 + m2) e.
Proof.
intros m1 m2 e.
unfold Fplus.
simpl.
now rewrite Zle_bool_refl, Zminus_diag, Zmult_1_r.
Qed.

Theorem Fexp_Fplus :
  forall f1 f2 : float beta,
  Fexp (Fplus f1 f2) = Zmin (Fexp f1) (Fexp f2).
Proof.
intros f1 f2.
unfold Fplus.
rewrite <- Falign_spec_exp.
now destruct (Falign f1 f2) as ((p,q),e).
Qed.

Definition Fminus (f1 f2 : float beta) :=
  Fplus f1 (Fopp f2).

Theorem F2R_minus :
  forall f1 f2 : float beta,
  F2R (Fminus f1 f2) = (F2R f1 - F2R f2)%R.
Proof.
intros f1 f2; unfold Fminus.
rewrite F2R_plus, F2R_opp.
ring.
Qed.

Theorem Fminus_same_exp :
  forall m1 m2 e,
  Fminus (Float m1 e) (Float m2 e) = Float (m1 - m2) e.
Proof.
intros m1 m2 e.
unfold Fminus.
apply Fplus_same_exp.
Qed.

Definition Fmult (f1 f2 : float beta) : float beta :=
  let '(Float m1 e1) := f1 in
  let '(Float m2 e2) := f2 in
  Float (m1 * m2) (e1 + e2).

Theorem F2R_mult :
  forall f1 f2 : float beta,
  F2R (Fmult f1 f2) = (F2R f1 * F2R f2)%R.
Proof.
intros (m1, e1) (m2, e2).
unfold Fmult, F2R. simpl.
rewrite Z2R_mult, bpow_plus.
ring.
Qed.

End Float_ops.

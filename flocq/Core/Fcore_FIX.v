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

(** * Fixed-point format *)
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_rnd.
Require Import Fcore_generic_fmt.
Require Import Fcore_ulp.
Require Import Fcore_rnd_ne.

Section RND_FIX.

Variable beta : radix.

Notation bpow := (bpow beta).

Variable emin : Z.

(* fixed-point format with exponent emin *)
Definition FIX_format (x : R) :=
  exists f : float beta,
  x = F2R f /\ (Fexp f = emin)%Z.

Definition FIX_exp (e : Z) := emin.

(** Properties of the FIX format *)

Global Instance FIX_exp_valid : Valid_exp FIX_exp.
Proof.
intros k.
unfold FIX_exp.
split ; intros H.
now apply Zlt_le_weak.
split.
apply Zle_refl.
now intros _ _.
Qed.

Theorem generic_format_FIX :
  forall x, FIX_format x -> generic_format beta FIX_exp x.
Proof.
intros x ((xm, xe), (Hx1, Hx2)).
rewrite Hx1.
now apply generic_format_canonic.
Qed.

Theorem FIX_format_generic :
  forall x, generic_format beta FIX_exp x -> FIX_format x.
Proof.
intros x H.
rewrite H.
eexists ; repeat split.
Qed.

Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
Proof.
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FIX_exp)).
intros x.
split.
apply FIX_format_generic.
apply generic_format_FIX.
Qed.

Global Instance FIX_exp_monotone : Monotone_exp FIX_exp.
Proof.
intros ex ey H.
apply Zle_refl.
Qed.

Theorem ulp_FIX: forall x, ulp beta FIX_exp x = bpow emin.
Proof.
intros x; unfold ulp.
case Req_bool_spec; intros Zx.
case (negligible_exp_spec FIX_exp).
intros T; specialize (T (emin-1)%Z); contradict T.
unfold FIX_exp; omega.
intros n _; reflexivity.
reflexivity.
Qed.


End RND_FIX.

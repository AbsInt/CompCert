(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2009-2018 Sylvie Boldo
#<br />#
Copyright (C) 2009-2018 Guillaume Melquiond

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

From Coq Require Import ZArith Reals Lia.

Require Import Zaux Raux Defs Round_pred Generic_fmt Ulp Round_NE.

Section RND_FIX.

Variable beta : radix.

Notation bpow := (bpow beta).

Variable emin : Z.

Inductive FIX_format (x : R) : Prop :=
  FIX_spec (f : float beta) :
    x = F2R f -> (Fexp f = emin)%Z -> FIX_format x.

Definition FIX_exp (e : Z) := emin.

(** Properties of the FIX format *)

Global Instance FIX_exp_valid : Valid_exp FIX_exp.
Proof.
intros k.
unfold FIX_exp.
split ; intros H.
now apply Zlt_le_weak.
split.
apply Z.le_refl.
now intros _ _.
Qed.

Theorem generic_format_FIX :
  forall x, FIX_format x -> generic_format beta FIX_exp x.
Proof.
intros x [[xm xe] Hx1 Hx2].
rewrite Hx1.
now apply generic_format_canonical.
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
apply Z.le_refl.
Qed.

Theorem ulp_FIX :
  forall x, ulp beta FIX_exp x = bpow emin.
Proof.
intros x; unfold ulp.
case Req_bool_spec; intros Zx.
case (negligible_exp_spec FIX_exp).
intros T; specialize (T (emin-1)%Z); contradict T.
unfold FIX_exp; lia.
intros n _; reflexivity.
reflexivity.
Qed.

Global Instance exists_NE_FIX :
      Exists_NE beta FIX_exp.
Proof.
unfold Exists_NE, FIX_exp; simpl.
right; split; auto.
Qed.

End RND_FIX.

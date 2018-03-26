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

(** * Basic definitions: float and rounding property *)
Require Import Fcore_Raux.

Section Def.

(** Definition of a floating-point number *)
Record float (beta : radix) := Float { Fnum : Z ; Fexp : Z }.

Arguments Fnum {beta} f.
Arguments Fexp {beta} f.

Variable beta : radix.

Definition F2R (f : float beta) :=
  (Z2R (Fnum f) * bpow beta (Fexp f))%R.

(** Requirements on a rounding mode *)
Definition round_pred_total (P : R -> R -> Prop) :=
  forall x, exists f, P x f.

Definition round_pred_monotone (P : R -> R -> Prop) :=
  forall x y f g, P x f -> P y g -> (x <= y)%R -> (f <= g)%R.

Definition round_pred (P : R -> R -> Prop) :=
  round_pred_total P /\
  round_pred_monotone P.

End Def.

Arguments Fnum {beta} f.
Arguments Fexp {beta} f.
Arguments F2R {beta} f.

Section RND.

(** property of being a round toward -inf *)
Definition Rnd_DN_pt (F : R -> Prop) (x f : R) :=
  F f /\ (f <= x)%R /\
  forall g : R, F g -> (g <= x)%R -> (g <= f)%R.

Definition Rnd_DN (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_DN_pt F x (rnd x).

(** property of being a round toward +inf *)
Definition Rnd_UP_pt (F : R -> Prop) (x f : R) :=
  F f /\ (x <= f)%R /\
  forall g : R, F g -> (x <= g)%R -> (f <= g)%R.

Definition Rnd_UP (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_UP_pt F x (rnd x).

(** property of being a round toward zero *)
Definition Rnd_ZR_pt (F : R -> Prop) (x f : R) :=
  ( (0 <= x)%R -> Rnd_DN_pt F x f ) /\
  ( (x <= 0)%R -> Rnd_UP_pt F x f ).

Definition Rnd_ZR (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_ZR_pt F x (rnd x).

(** property of being a round to nearest *)
Definition Rnd_N_pt (F : R -> Prop) (x f : R) :=
  F f /\
  forall g : R, F g -> (Rabs (f - x) <= Rabs (g - x))%R.

Definition Rnd_N (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_N_pt F x (rnd x).

Definition Rnd_NG_pt (F : R -> Prop) (P : R -> R -> Prop) (x f : R) :=
  Rnd_N_pt F x f /\
  ( P x f \/ forall f2 : R, Rnd_N_pt F x f2 -> f2 = f ).

Definition Rnd_NG (F : R -> Prop) (P : R -> R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_NG_pt F P x (rnd x).

Definition Rnd_NA_pt (F : R -> Prop) (x f : R) :=
  Rnd_N_pt F x f /\
  forall f2 : R, Rnd_N_pt F x f2 -> (Rabs f2 <= Rabs f)%R.

Definition Rnd_NA (F : R -> Prop) (rnd : R -> R) :=
  forall x : R, Rnd_NA_pt F x (rnd x).

End RND.

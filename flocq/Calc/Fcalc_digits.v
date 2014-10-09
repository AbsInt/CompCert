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

(** * Functions for computing the number of digits of integers and related theorems. *)

Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.
Require Import Fcore_digits.

Section Fcalc_digits.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Theorem Zdigits_ln_beta :
  forall n,
  n <> Z0 ->
  Zdigits beta n = ln_beta beta (Z2R n).
Proof.
intros n Hn.
destruct (ln_beta beta (Z2R n)) as (e, He) ; simpl.
specialize (He (Z2R_neq _ _ Hn)).
rewrite <- Z2R_abs in He.
assert (Hd := Zdigits_correct beta n).
assert (Hd' := Zdigits_gt_0 beta n).
apply Zle_antisym ; apply (bpow_lt_bpow beta).
apply Rle_lt_trans with (2 := proj2 He).
rewrite <- Z2R_Zpower by omega.
now apply Z2R_le.
apply Rle_lt_trans with (1 := proj1 He).
rewrite <- Z2R_Zpower by omega.
now apply Z2R_lt.
Qed.

Theorem ln_beta_F2R_Zdigits :
  forall m e, m <> Z0 ->
  (ln_beta beta (F2R (Float beta m e)) = Zdigits beta m + e :> Z)%Z.
Proof.
intros m e Hm.
rewrite ln_beta_F2R with (1 := Hm).
apply (f_equal (fun v => Zplus v e)).
apply sym_eq.
now apply Zdigits_ln_beta.
Qed.

End Fcalc_digits.

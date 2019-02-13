(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for PowerPC *)

Require Import ZArith.
(*From Flocq*)
Require Import Binary Bits.

Definition ptr64 := false.

Definition big_endian := true.

Definition align_int64 := 8%Z.
Definition align_float64 := 8%Z.

(** Can we use the 64-bit extensions to the PowerPC architecture? *)
Parameter ppc64 : bool.

Definition splitlong := negb ppc64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  reflexivity.
Qed.

Definition default_nan_64 : { x : binary64 | is_nan _ _ x = true } :=
  exist _ (B754_nan 53 1024 false (iter_nat 51 _ xO xH) (eq_refl true)) (eq_refl true).

Definition choose_binop_pl_64 (pl1 pl2 : positive) :=
  false.                        (**r always choose first NaN *)

Definition default_nan_32 : { x : binary32 | is_nan _ _ x = true } :=
  exist _ (B754_nan 24 128 false (iter_nat 22 _ xO xH) (eq_refl true)) (eq_refl true).

Definition choose_binop_pl_32 (pl1 pl2 : positive) :=
  false.                        (**r always choose first NaN *)

Definition fpu_returns_default_qNaN := false.

Definition float_of_single_preserves_sNaN := true.

Global Opaque ptr64 big_endian splitlong
              default_nan_64 choose_binop_pl_64
              default_nan_32 choose_binop_pl_32
              fpu_returns_default_qNaN
              float_of_single_preserves_sNaN.

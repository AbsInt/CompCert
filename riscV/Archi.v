(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                Xavier Leroy, INRIA Paris                            *)
(*                Jacques-Henri Jourdan, INRIA Paris                   *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for RISC-V *)

Require Import ZArith.
(*From Flocq*)
Require Import Binary Bits.

Parameter ptr64 : bool.

Definition big_endian := false.

Definition align_int64 := 8%Z.
Definition align_float64 := 8%Z.

Definition splitlong := negb ptr64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  unfold splitlong. destruct ptr64; simpl; congruence. 
Qed.

(** Section 7.3: "Except when otherwise stated, if the result of a
   floating-point operation is NaN, it is the canonical NaN. The
   canonical NaN has a positive sign and all significand bits clear
   except the MSB, a.k.a. the quiet bit."
   Exceptions are operations manipulating signs. *)

Definition default_nan_64 : { x : binary64 | is_nan _ _ x = true } :=
  exist _ (B754_nan 53 1024 false (iter_nat 51 _ xO xH) (eq_refl true)) (eq_refl true).

Definition choose_binop_pl_64 (pl1 pl2 : positive) :=
  false.                        (**r irrelevant *)

Definition default_nan_32 : { x : binary32 | is_nan _ _ x = true } :=
  exist _ (B754_nan 24 128 false (iter_nat 22 _ xO xH) (eq_refl true)) (eq_refl true).

Definition choose_binop_pl_32 (pl1 pl2 : positive) :=
  false.                        (**r irrelevant *)

Definition fpu_returns_default_qNaN := true.

Definition float_of_single_preserves_sNaN := false.

Global Opaque ptr64 big_endian splitlong
              default_nan_64 choose_binop_pl_64
              default_nan_32 choose_binop_pl_32
              fpu_returns_default_qNaN
              float_of_single_preserves_sNaN.

(** Whether to generate position-independent code or not *)

Parameter pic_code: unit -> bool.

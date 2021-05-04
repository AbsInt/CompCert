(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                Xavier Leroy, INRIA Paris                            *)
(*                Jacques-Henri Jourdan, INRIA Paris                   *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for x86 in 64-bit mode *)

From Flocq Require Import Binary Bits.
Require Import ZArith List.

Definition ptr64 := true.

Definition big_endian := false.

Definition align_int64 := 8%Z.
Definition align_float64 := 8%Z.

Definition splitlong := negb ptr64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  unfold splitlong. destruct ptr64; simpl; congruence.
Qed.

Definition default_nan_64 := (true, iter_nat 51 _ xO xH).
Definition default_nan_32 := (true, iter_nat 22 _ xO xH).

(* Always choose the first NaN argument, if any *)

Definition choose_nan_64 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_64 | n :: _ => n end.

Definition choose_nan_32 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_32 | n :: _ => n end.

Lemma choose_nan_64_idem: forall n,
  choose_nan_64 (n :: n :: nil) = choose_nan_64 (n :: nil).
Proof. auto. Qed.

Lemma choose_nan_32_idem: forall n,
  choose_nan_32 (n :: n :: nil) = choose_nan_32 (n :: nil).
Proof. auto. Qed.

Definition fma_order {A: Type} (x y z: A) := (x, y, z).

Definition fma_invalid_mul_is_nan := false.

Definition float_of_single_preserves_sNaN := false.

(** Which ABI to use. *)
Parameter win64: bool.

Global Opaque ptr64 big_endian splitlong
              default_nan_64 choose_nan_64
              default_nan_32 choose_nan_32
              fma_order fma_invalid_mul_is_nan
              float_of_single_preserves_sNaN.

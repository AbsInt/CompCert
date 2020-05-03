(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for AArch64 *)

Require Import ZArith List.
(*From Flocq*)
Require Import Binary Bits.

Definition ptr64 := true.

Definition big_endian := false.

Definition align_int64 := 8%Z.
Definition align_float64 := 8%Z.

Definition splitlong := false.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  unfold splitlong, ptr64; congruence.
Qed.

Definition default_nan_64 := (false, iter_nat 51 _ xO xH).
Definition default_nan_32 := (false, iter_nat 22 _ xO xH).

(** Choose the first signaling NaN, if any;
    otherwise choose the first NaN;
    otherwise use default. *)

Definition choose_nan (is_signaling: positive -> bool) 
                      (default: bool * positive)
                      (l0: list (bool * positive)) : bool * positive :=
  let fix choose_snan (l1: list (bool * positive)) :=
    match l1 with
    | nil =>
        match l0 with nil => default | n :: _ => n end
    | ((s, p) as n) :: l1 =>
        if is_signaling p then n else choose_snan l1
    end
  in choose_snan l0.

Lemma choose_nan_idem: forall is_signaling default n,
  choose_nan is_signaling default (n :: n :: nil) =
  choose_nan is_signaling default (n :: nil).
Proof.
  intros. destruct n as [s p]; unfold choose_nan; simpl.
  destruct (is_signaling p); auto. 
Qed.

Definition choose_nan_64 :=
  choose_nan (fun p => negb (Pos.testbit p 51)) default_nan_64.

Definition choose_nan_32 :=
  choose_nan (fun p => negb (Pos.testbit p 22)) default_nan_32.

Lemma choose_nan_64_idem: forall n,
  choose_nan_64 (n :: n :: nil) = choose_nan_64 (n :: nil).
Proof. intros; apply choose_nan_idem. Qed.

Lemma choose_nan_32_idem: forall n,
  choose_nan_32 (n :: n :: nil) = choose_nan_32 (n :: nil).
Proof. intros; apply choose_nan_idem. Qed.

Definition fma_order {A: Type} (x y z: A) := (z, x, y).

Definition fma_invalid_mul_is_nan := true.

Definition float_of_single_preserves_sNaN := false.

Global Opaque ptr64 big_endian splitlong
              default_nan_64 choose_nan_64
              default_nan_32 choose_nan_32
              fma_order fma_invalid_mul_is_nan
              float_of_single_preserves_sNaN.

(** Whether to generate position-independent code or not *)

Parameter pic_code: unit -> bool.

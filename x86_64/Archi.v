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

(** Architecture-dependent parameters for x86 in 64-bit mode *)

Require Import ZArith.
Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.

Definition ptr64 := true.

Definition big_endian := false.

Definition align_int64 := 8%Z.
Definition align_float64 := 8%Z.

Definition splitlong := negb ptr64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  unfold splitlong. destruct ptr64; simpl; congruence.
Qed.

Program Definition default_pl_64 : bool * nan_pl 53 :=
  (true, iter_nat 51 _ xO xH).

Definition choose_binop_pl_64 (s1: bool) (pl1: nan_pl 53) (s2: bool) (pl2: nan_pl 53) :=
  false.                        (**r always choose first NaN *)

Program Definition default_pl_32 : bool * nan_pl 24 :=
  (true, iter_nat 22 _ xO xH).

Definition choose_binop_pl_32 (s1: bool) (pl1: nan_pl 24) (s2: bool) (pl2: nan_pl 24) :=
  false.                        (**r always choose first NaN *)

Definition float_of_single_preserves_sNaN := false.

Global Opaque ptr64 big_endian splitlong
              default_pl_64 choose_binop_pl_64
              default_pl_32 choose_binop_pl_32
              float_of_single_preserves_sNaN.

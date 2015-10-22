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

(** Architecture-dependent parameters for IA32 *)

Require Import ZArith.
Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.

Definition big_endian := false.

Notation align_int64 := 4%Z (only parsing).
Notation align_float64 := 4%Z (only parsing).

Program Definition default_pl_64 : bool * nan_pl 53 :=
  (true, iter_nat 51 _ xO xH).

Definition choose_binop_pl_64 (s1: bool) (pl1: nan_pl 53) (s2: bool) (pl2: nan_pl 53) :=
  false.                        (**r always choose first NaN *)

Program Definition default_pl_32 : bool * nan_pl 24 :=
  (true, iter_nat 22 _ xO xH).

Definition choose_binop_pl_32 (s1: bool) (pl1: nan_pl 24) (s2: bool) (pl2: nan_pl 24) :=
  false.                        (**r always choose first NaN *)

Definition float_of_single_preserves_sNaN := false.

Global Opaque big_endian
              default_pl_64 choose_binop_pl_64
              default_pl_32 choose_binop_pl_32
              float_of_single_preserves_sNaN.

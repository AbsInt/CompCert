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

Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.
Require Import Floats.
Require Import ZArith.
Require Import Integers.

Program Definition default_pl : bool * nan_pl 53 := (true, nat_iter 51 xO xH).

Definition choose_binop_pl (s1: bool) (pl1: nan_pl 53) (s2: bool) (pl2: nan_pl 53) :=
  false.                        (** always choose first NaN *)

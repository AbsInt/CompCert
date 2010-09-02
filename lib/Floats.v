(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Axiomatization of floating-point numbers. *)

(** In contrast with what we do with machine integers, we do not bother
  to formalize precisely IEEE floating-point arithmetic.  Instead, we
  simply axiomatize a type [float] for IEEE double-precision floats
  and the associated operations.  *)

Require Import Coqlib.
Require Import Integers.

Parameter float: Type.                  (**r the type of IEE754 doubles *)

Module Float.

Parameter zero: float.                  (**r the float [+0.0] *)

Axiom eq_dec: forall (f1 f2: float), {f1 = f2} + {f1 <> f2}.

(** Arithmetic operations *)

Parameter neg: float -> float.          (**r opposite (change sign) *)
Parameter abs: float -> float.          (**r absolute value (set sign to [+]) *)
Parameter singleoffloat: float -> float. (**r conversion to single precision *)
Parameter intoffloat: float -> int.     (**r conversion to signed 32-bit int *)
Parameter intuoffloat: float -> int.    (**r conversion to unsigned 32-bit int *)
Parameter floatofint: int -> float.     (**r conversion from signed 32-bit int *)
Parameter floatofintu: int -> float.    (**r conversion from unsigned 32-bit int *)

Parameter add: float -> float -> float. (**r addition *)
Parameter sub: float -> float -> float. (**r subtraction *)
Parameter mul: float -> float -> float. (**r multiplication *)
Parameter div: float -> float -> float. (**r division *)

Parameter cmp: comparison -> float -> float -> bool.  (**r comparison *)

(** Conversions between floats and their concrete in-memory representation
    as a sequence of 64 bits (double precision) or 32 bits (single precision). *)

Parameter bits_of_double: float -> int64.
Parameter double_of_bits: int64 -> float.

Parameter bits_of_single: float -> int.
Parameter single_of_bits: int -> float.

Definition from_words (hi lo: int) : float :=
  double_of_bits
    (Int64.or (Int64.shl (Int64.repr (Int.unsigned hi)) (Int64.repr 32))
              (Int64.repr (Int.unsigned lo))).

(** Below are the only properties of floating-point arithmetic that we
  rely on in the compiler proof. *)

Axiom addf_commut: forall f1 f2, add f1 f2 = add f2 f1.

Axiom subf_addf_opp: forall f1 f2, sub f1 f2 = add f1 (neg f2).

Axiom singleoffloat_idem:
  forall f, singleoffloat (singleoffloat f) = singleoffloat f.

(** Properties of comparisons. *)

Axiom cmp_swap:
  forall c x y, Float.cmp (swap_comparison c) x y = Float.cmp c y x.
Axiom cmp_ne_eq:
  forall f1 f2, cmp Cne f1 f2 = negb (cmp Ceq f1 f2).
Axiom cmp_lt_eq_false:
  forall x y, cmp Clt x y = true -> cmp Ceq x y = true -> False.
Axiom cmp_le_lt_eq:
  forall f1 f2, cmp Cle f1 f2 = cmp Clt f1 f2 || cmp Ceq f1 f2.

Corollary cmp_gt_eq_false:
  forall x y, cmp Cgt x y = true -> cmp Ceq x y = true -> False.
Proof.
  intros. rewrite <- cmp_swap in H. rewrite <- cmp_swap in H0. 
  eapply cmp_lt_eq_false; eauto.
Qed.

Corollary cmp_ge_gt_eq:
  forall f1 f2, cmp Cge f1 f2 = cmp Cgt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros.
  change Cge with (swap_comparison Cle).
  change Cgt with (swap_comparison Clt).
  change Ceq with (swap_comparison Ceq).
  repeat rewrite cmp_swap. 
  apply cmp_le_lt_eq.
Qed.

(** Properties of conversions to/from in-memory representation.
  The double-precision conversions are bijective (one-to-one).
  The single-precision conversions lose precision exactly
  as described by [singleoffloat] rounding. *)

Axiom double_of_bits_of_double:
  forall f, double_of_bits (bits_of_double f) = f.
Axiom single_of_bits_of_single:
  forall f, single_of_bits (bits_of_single f) = singleoffloat f.

Axiom bits_of_singleoffloat:
  forall f, bits_of_single (singleoffloat f) = bits_of_single f.
Axiom singleoffloat_of_bits:
  forall b, singleoffloat (single_of_bits b) = single_of_bits b.

(** Conversions between floats and unsigned ints can be defined
  in terms of conversions between floats and signed ints.
  (Most processors provide only the latter, forcing the compiler
  to emulate the former.)   *)

Definition ox8000_0000 := Int.repr Int.half_modulus.  (**r [0x8000_0000] *)

Axiom floatofintu_floatofint_1:
  forall x,
  Int.ltu x ox8000_0000 = true ->
  floatofintu x = floatofint x.

Axiom floatofintu_floatofint_2:
  forall x,
  Int.ltu x ox8000_0000 = false ->
  floatofintu x = add (floatofint (Int.sub x ox8000_0000))
                      (floatofintu ox8000_0000).

Axiom intuoffloat_intoffloat_1:
  forall x,
  cmp Clt x (floatofintu ox8000_0000) = true ->
  intuoffloat x = intoffloat x.

Axiom intuoffloat_intoffloat_2:
  forall x,
  cmp Clt x (floatofintu ox8000_0000) = false ->
  intuoffloat x =
  Int.add (intoffloat (sub x (floatofintu ox8000_0000)))
          ox8000_0000.

(** Conversions from ints to floats can be defined as bitwise manipulations
  over the in-memory representation.  This is what the PowerPC port does.
  The trick is that [from_words 0x4330_0000 x] is the float
  [2^52 + floatofintu x]. *)

Definition ox4330_0000 := Int.repr 1127219200.        (**r [0x4330_0000] *)

Axiom floatofintu_from_words:
  forall x,
  floatofintu x =
    sub (from_words ox4330_0000 x) (from_words ox4330_0000 Int.zero).

Axiom floatofint_from_words:
  forall x,
  floatofint x =
    sub (from_words ox4330_0000 (Int.add x ox8000_0000))
        (from_words ox4330_0000 ox8000_0000).

End Float.

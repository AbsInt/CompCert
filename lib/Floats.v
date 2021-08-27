(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
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

(** Formalization of floating-point numbers, using the Flocq library. *)

Require Import Coqlib Zbits Integers.
From Flocq Require Import Binary Bits Core.
Require Import IEEE754_extra.
Require Import Program.
Require Archi.
Import ListNotations.

Close Scope R_scope.
Open Scope Z_scope.
Set Asymmetric Patterns.

Definition float := binary64. (**r the type of IEE754 double-precision FP numbers *)
Definition float32 := binary32. (**r the type of IEE754 single-precision FP numbers *)

(** Boolean-valued comparisons *)

Definition cmp_of_comparison (c: comparison) (x: option Datatypes.comparison) : bool :=
  match c with
  | Ceq =>
      match x with Some Eq => true | _ => false end
  | Cne =>
      match x with Some Eq => false | _ => true end
  | Clt =>
      match x with Some Lt => true | _ => false end
  | Cle =>
      match x with Some(Lt|Eq) => true | _ => false end
  | Cgt =>
      match x with Some Gt => true | _ => false end
  | Cge =>
      match x with Some(Gt|Eq) => true | _ => false end
  end.

Definition ordered_of_comparison (x: option Datatypes.comparison) : bool :=
  match x with None => false | Some _ => true end.

Lemma cmp_of_comparison_swap:
  forall c x,
  cmp_of_comparison (swap_comparison c) x =
  cmp_of_comparison c (match x with None => None | Some x => Some (CompOpp x) end).
Proof.
  intros. destruct c; destruct x as [[]|]; reflexivity.
Qed.

Lemma cmp_of_comparison_ne_eq:
  forall x, cmp_of_comparison Cne x = negb (cmp_of_comparison Ceq x).
Proof.
  intros. destruct x as [[]|]; reflexivity.
Qed.

Lemma cmp_of_comparison_lt_eq_false:
  forall x, cmp_of_comparison Clt x = true -> cmp_of_comparison Ceq x = true -> False.
Proof.
  destruct x as [[]|]; simpl; intros; discriminate.
Qed.

Lemma cmp_of_comparison_le_lt_eq:
  forall x, cmp_of_comparison Cle x = cmp_of_comparison Clt x || cmp_of_comparison Ceq x.
Proof.
  destruct x as [[]|]; reflexivity.
Qed.

Lemma cmp_of_comparison_gt_eq_false:
  forall x, cmp_of_comparison Cgt x = true -> cmp_of_comparison Ceq x = true -> False.
Proof.
  destruct x as [[]|]; simpl; intros; discriminate.
Qed.

Lemma cmp_of_comparison_ge_gt_eq:
  forall x, cmp_of_comparison Cge x = cmp_of_comparison Cgt x || cmp_of_comparison Ceq x.
Proof.
  destruct x as [[]|]; reflexivity.
Qed.

Lemma cmp_of_comparison_lt_gt_false:
  forall x, cmp_of_comparison Clt x = true -> cmp_of_comparison Cgt x = true -> False.
Proof.
  destruct x as [[]|]; simpl; intros; discriminate.
Qed.

(** Normalization of NaN payloads *)

Lemma normalized_nan: forall prec n p,
  Z.of_nat n = prec - 1 -> 1 < prec ->
  nan_pl prec (Z.to_pos (P_mod_two_p p n)) = true.
Proof.
  intros. unfold nan_pl. apply Z.ltb_lt. rewrite Digits.Zpos_digits2_pos.
  set (p' := P_mod_two_p p n).
  assert (A: 0 <= p' < 2 ^ Z.of_nat n).
  { rewrite <- two_power_nat_equiv; apply P_mod_two_p_range. }
  assert (B: Digits.Zdigits radix2 p' <= prec - 1).
  { apply Digits.Zdigits_le_Zpower. rewrite <- H. rewrite Z.abs_eq; tauto. }
  destruct (zeq p' 0).
- rewrite e. simpl; auto.
- rewrite Z2Pos.id by lia. lia.
Qed.

(** Transform a Nan payload to a quiet Nan payload. *)

Definition quiet_nan_64_payload (p: positive) :=
  Z.to_pos (P_mod_two_p (Pos.lor p ((iter_nat xO 51 1%positive))) 52%nat).

Lemma quiet_nan_64_proof: forall p, nan_pl 53 (quiet_nan_64_payload p) = true.
Proof. intros; apply normalized_nan; auto; lia. Qed.

Definition quiet_nan_64 (sp: bool * positive) : {x :float | is_nan _ _ x = true} :=
  let (s, p) := sp in
  exist _ (B754_nan 53 1024 s (quiet_nan_64_payload p) (quiet_nan_64_proof p)) (eq_refl true).

Definition default_nan_64 := quiet_nan_64 Archi.default_nan_64.

Definition quiet_nan_32_payload (p: positive) :=
  Z.to_pos (P_mod_two_p (Pos.lor p ((iter_nat xO 22 1%positive))) 23%nat).

Lemma quiet_nan_32_proof: forall p, nan_pl 24 (quiet_nan_32_payload p) = true.
Proof. intros; apply normalized_nan; auto; lia. Qed.

Definition quiet_nan_32 (sp: bool * positive) : {x :float32 | is_nan _ _ x = true} :=
  let (s, p) := sp in
  exist _ (B754_nan 24 128 s (quiet_nan_32_payload p) (quiet_nan_32_proof p)) (eq_refl true).

Definition default_nan_32 := quiet_nan_32 Archi.default_nan_32.

Local Notation __ := (eq_refl Datatypes.Lt).

Local Hint Extern 1 (Prec_gt_0 _) => exact (eq_refl Datatypes.Lt) : core.
Local Hint Extern 1 (_ < _) => exact (eq_refl Datatypes.Lt) : core.

(** * Double-precision FP numbers *)

Module Float.

(** ** NaN payload manipulations *)

(** The following definitions are not part of the IEEE754 standard but
    apply to all architectures supported by CompCert. *)

(** Nan payload operations for single <-> double conversions. *)

Definition expand_nan_payload (p: positive) := Pos.shiftl_nat p 29.

Lemma expand_nan_proof (p : positive) :
  nan_pl 24 p = true ->
  nan_pl 53 (expand_nan_payload p) = true.
Proof.
  unfold nan_pl, expand_nan_payload. intros K.
  rewrite Z.ltb_lt in *.
  unfold Pos.shiftl_nat, nat_rect, Digits.digits2_pos.
  fold (Digits.digits2_pos p).
  zify; lia.
Qed.

Definition expand_nan s p H : {x | is_nan _ _ x = true} :=
  exist _ (B754_nan 53 1024 s (expand_nan_payload p) (expand_nan_proof p H)) (eq_refl true).

Definition of_single_nan (f : float32) : { x : float | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H =>
    if Archi.float_of_single_preserves_sNaN
    then expand_nan s p H
    else quiet_nan_64 (s, expand_nan_payload p)
  | _ => default_nan_64
  end.

Definition reduce_nan_payload (p: positive) :=
  (* The [quiet_nan_64_payload p] before the right shift is redundant with
     the [quiet_nan_32_payload p] performed after, in [to_single_nan].
     However the former ensures that the result of the right shift is
     not 0 and therefore representable as a positive. *)
  Pos.shiftr_nat (quiet_nan_64_payload p) 29.

Definition to_single_nan (f : float) : { x : float32 | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => quiet_nan_32 (s, reduce_nan_payload p)
  | _ => default_nan_32
  end.

(** NaN payload operations for opposite and absolute value. *)

Definition neg_nan (f : float) : { x : float | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => exist _ (B754_nan 53 1024 (negb s) p H) (eq_refl true)
  | _ => default_nan_64
  end.

Definition abs_nan (f : float) : { x : float | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => exist _ (B754_nan 53 1024 false p H) (eq_refl true)
  | _ => default_nan_64
  end.

(** When an arithmetic operation returns a NaN, the sign and payload
  of this NaN are not fully specified by the IEEE standard, and vary
  among the architectures supported by CompCert.  However, the following
  behavior applies to all the supported architectures: the payload is either
- a default payload, independent of the arguments, or
- the payload of one of the NaN arguments, if any.

For each supported architecture, the functions [Archi.choose_nan_64]
and [Archi.choose_nan_32] determine the payload of the result as a
function of the payloads of the NaN arguments.

Additionally, signaling NaNs are converted to quiet NaNs, as required by the standard.
*)

Definition cons_pl (x: float) (l: list (bool * positive)) :=
  match x with B754_nan s p _ => (s, p) :: l | _ => l end.

Definition unop_nan (x: float) : {x : float | is_nan _ _ x = true} :=
  quiet_nan_64 (Archi.choose_nan_64 (cons_pl x [])).

Definition binop_nan (x y: float) : {x : float | is_nan _ _ x = true} :=
  quiet_nan_64 (Archi.choose_nan_64 (cons_pl x (cons_pl y []))).

(** For fused multiply-add, the order in which arguments are examined
  to select a NaN payload varies across platforms.  E.g. in [fma x y z],
  x86 considers [x] first, then [y], then [z], while ARM considers [z] first,
  then [x], then [y].  The corresponding permutation is defined
  for each target, as function [Archi.fma_order]. *)

Definition fma_nan_1 (x y z: float) : {x : float | is_nan _ _ x = true} :=
  let '(a, b, c) := Archi.fma_order x y z in
  quiet_nan_64 (Archi.choose_nan_64 (cons_pl a (cons_pl b (cons_pl c [])))).

(** One last wrinkle for fused multiply-add: [fma zero infinity nan]
  can return either the quiesced [nan], or the default NaN arising out
  of the invalid operation [zero * infinity].  Of our target platforms,
  only ARM honors the latter case.  The choice between the default NaN
  and [nan] is done as in the case of two-argument arithmetic operations. *)

Definition fma_nan (x y z: float) : {x : float | is_nan _ _ x = true} :=
  match x, y with
  | B754_infinity _, B754_zero _ | B754_zero _, B754_infinity _ =>
      if Archi.fma_invalid_mul_is_nan
      then quiet_nan_64 (Archi.choose_nan_64 (Archi.default_nan_64 :: cons_pl z []))
      else fma_nan_1 x y z
  | _, _ =>
      fma_nan_1 x y z
  end.

(** ** Operations over double-precision floats *)

Definition zero: float := B754_zero _ _ false. (**r the float [+0.0] *)

Definition eq_dec: forall (f1 f2: float), {f1 = f2} + {f1 <> f2} := Beq_dec _ _.

(** Arithmetic operations *)

Definition neg: float -> float := Bopp _ _ neg_nan. (**r opposite (change sign) *)
Definition abs: float -> float := Babs _ _ abs_nan. (**r absolute value (set sign to [+]) *)
Definition sqrt: float -> float :=
  Bsqrt 53 1024 __ __ unop_nan mode_NE.  (**r square root *)
Definition add: float -> float -> float :=
  Bplus 53 1024 __ __ binop_nan mode_NE. (**r addition *)
Definition sub: float -> float -> float :=
  Bminus 53 1024 __ __ binop_nan mode_NE. (**r subtraction *)
Definition mul: float -> float -> float :=
  Bmult 53 1024 __ __ binop_nan mode_NE. (**r multiplication *)
Definition div: float -> float -> float :=
  Bdiv 53 1024 __ __ binop_nan mode_NE. (**r division *)
Definition fma: float -> float -> float -> float :=
  Bfma 53 1024 __ __ fma_nan mode_NE. (**r fused multiply-add [x * y + z] *)
Definition compare (f1 f2: float) : option Datatypes.comparison := (**r general comparison *)
  Bcompare 53 1024 f1 f2.
Definition cmp (c:comparison) (f1 f2: float) : bool := (**r Boolean comparison *)
  cmp_of_comparison c (compare f1 f2).
Definition ordered (f1 f2: float) : bool :=
  ordered_of_comparison (compare f1 f2).

(** Conversions *)

Definition of_single: float32 -> float := Bconv _ _ 53 1024 __ __ of_single_nan mode_NE.
Definition to_single: float -> float32 := Bconv _ _ 24 128 __ __ to_single_nan mode_NE.

Definition to_int (f:float): option int := (**r conversion to signed 32-bit int *)
  option_map Int.repr (ZofB_range _ _ f Int.min_signed Int.max_signed).
Definition to_intu (f:float): option int := (**r conversion to unsigned 32-bit int *)
  option_map Int.repr (ZofB_range _ _ f 0 Int.max_unsigned).
Definition to_long (f:float): option int64 := (**r conversion to signed 64-bit int *)
  option_map Int64.repr (ZofB_range _ _ f Int64.min_signed Int64.max_signed).
Definition to_longu (f:float): option int64 := (**r conversion to unsigned 64-bit int *)
  option_map Int64.repr (ZofB_range _ _ f 0 Int64.max_unsigned).

Definition of_int (n:int): float := (**r conversion from signed 32-bit int *)
  BofZ 53 1024 __ __ (Int.signed n).
Definition of_intu (n:int): float:= (**r conversion from unsigned 32-bit int *)
  BofZ 53 1024 __ __ (Int.unsigned n).

Definition of_long (n:int64): float := (**r conversion from signed 64-bit int *)
  BofZ 53 1024 __ __ (Int64.signed n).
Definition of_longu (n:int64): float:= (**r conversion from unsigned 64-bit int *)
  BofZ 53 1024 __ __ (Int64.unsigned n).

Definition from_parsed (base:positive) (intPart:positive) (expPart:Z) : float :=
  Bparse 53 1024 __ __ base intPart expPart.

(** Conversions between floats and their concrete in-memory representation
    as a sequence of 64 bits. *)

Definition to_bits (f: float): int64 := Int64.repr (bits_of_b64 f).
Definition of_bits (b: int64): float := b64_of_bits (Int64.unsigned b).

Definition from_words (hi lo: int) : float := of_bits (Int64.ofwords hi lo).

(** ** Properties *)

(** Below are the only properties of floating-point arithmetic that we
  rely on in the compiler proof. *)

(** Some tactics **)

Ltac compute_this val :=
  let x := fresh in set val as x in *; vm_compute in x; subst x.

Ltac smart_omega :=
  simpl radix_val in *; simpl Z.pow in *;
  compute_this Int.modulus; compute_this Int.half_modulus;
  compute_this Int.max_unsigned;
  compute_this Int.min_signed; compute_this Int.max_signed;
  compute_this Int64.modulus; compute_this Int64.half_modulus;
  compute_this Int64.max_unsigned;
  compute_this (Z.pow_pos 2 1024); compute_this (Z.pow_pos 2 53); compute_this (Z.pow_pos 2 52); compute_this (Z.pow_pos 2 32);
  zify; lia.

(** Commutativity properties of addition and multiplication. *)

Theorem add_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> add x y = add y x.
Proof.
  intros. apply Bplus_commut.
  destruct x, y; try reflexivity; now destruct H.
Qed.

Theorem mul_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> mul x y = mul y x.
Proof.
  intros. apply Bmult_commut.
  destruct x, y; try reflexivity; now destruct H.
Qed.

(** Multiplication by 2 is diagonal addition. *)

Theorem mul2_add:
  forall f, add f f = mul f (of_int (Int.repr 2%Z)).
Proof.
  intros. apply Bmult2_Bplus.
  intros x y Hx Hy. unfold binop_nan.
  destruct x; try discriminate. simpl. rewrite Archi.choose_nan_64_idem. 
  destruct y; reflexivity || discriminate.
Qed.

(** Divisions that can be turned into multiplication by an inverse. *)

Definition exact_inverse : float -> option float := Bexact_inverse 53 1024 __ __.

Theorem div_mul_inverse:
  forall x y z, exact_inverse y = Some z -> div x y = mul x z.
Proof.
  intros. apply Bdiv_mult_inverse. 2: easy.
  intros x0 y0 z0 Hx Hy Hz. unfold binop_nan.
  destruct x0; try discriminate.
  destruct y0, z0; reflexivity || discriminate.
Qed.

(** Properties of comparisons. *)

Theorem cmp_swap:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  unfold cmp, compare; intros. rewrite (Bcompare_swap _ _ x y).
  apply cmp_of_comparison_swap.
Qed.

Theorem cmp_ne_eq:
  forall f1 f2, cmp Cne f1 f2 = negb (cmp Ceq f1 f2).
Proof.
  intros; apply cmp_of_comparison_ne_eq.
Qed.

Theorem cmp_lt_eq_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Ceq f1 f2 = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_lt_eq_false.
Qed.

Theorem cmp_le_lt_eq:
  forall f1 f2, cmp Cle f1 f2 = cmp Clt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros f1 f2; apply cmp_of_comparison_le_lt_eq.
Qed.

Theorem cmp_gt_eq_false:
  forall x y, cmp Cgt x y = true -> cmp Ceq x y = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_gt_eq_false.
Qed.

Theorem cmp_ge_gt_eq:
  forall f1 f2, cmp Cge f1 f2 = cmp Cgt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros f1 f2; apply cmp_of_comparison_ge_gt_eq.
Qed.

Theorem cmp_lt_gt_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Cgt f1 f2 = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_lt_gt_false.
Qed.

(** Properties of conversions to/from in-memory representation.
  The conversions are bijective (one-to-one). *)

Theorem of_to_bits:
  forall f, of_bits (to_bits f) = f.
Proof.
  intros; unfold of_bits, to_bits, bits_of_b64, b64_of_bits.
  rewrite Int64.unsigned_repr, binary_float_of_bits_of_binary_float; [reflexivity|].
  generalize (bits_of_binary_float_range 52 11 __ __ f).
  change (2^(52+11+1)) with (Int64.max_unsigned + 1). lia.
Qed.

Theorem to_of_bits:
  forall b, to_bits (of_bits b) = b.
Proof.
  intros; unfold of_bits, to_bits, bits_of_b64, b64_of_bits.
  rewrite bits_of_binary_float_of_bits. apply Int64.repr_unsigned.
  apply Int64.unsigned_range.
Qed.

(** Conversions between floats and unsigned ints can be defined
  in terms of conversions between floats and signed ints.
  (Most processors provide only the latter, forcing the compiler
  to emulate the former.)   *)

Definition ox8000_0000 := Int.repr Int.half_modulus.  (**r [0x8000_0000] *)
Definition ox7FFF_FFFF := Int.repr Int.max_signed.    (**r [0x7FFF_FFFF] *)

Theorem of_intu_of_int_1:
  forall x,
  Int.ltu x ox8000_0000 = true ->
  of_intu x = of_int x.
Proof.
  unfold of_intu, of_int, Int.signed, Int.ltu; intro.
  change (Int.unsigned ox8000_0000) with Int.half_modulus.
  destruct (zlt (Int.unsigned x) Int.half_modulus); now intuition.
Qed.

Theorem of_intu_of_int_2:
  forall x,
  Int.ltu x ox8000_0000 = false ->
  of_intu x = add (of_int (Int.sub x ox8000_0000)) (of_intu ox8000_0000).
Proof.
  unfold add, of_intu, of_int; intros.
  set (y := Int.sub x ox8000_0000).
  pose proof (Int.unsigned_range x); pose proof (Int.signed_range y).
  assert (Ry: integer_representable 53 1024 (Int.signed y)).
  { apply integer_representable_n; auto; smart_omega. }
  assert (R8: integer_representable 53 1024 (Int.unsigned ox8000_0000)).
  { apply integer_representable_2p with (p := 31);auto; smart_omega. }
  rewrite BofZ_plus by auto.
  f_equal.
  unfold Int.ltu in H. destruct zlt in H; try discriminate.
  unfold y, Int.sub. rewrite Int.signed_repr. lia.
  compute_this (Int.unsigned ox8000_0000); smart_omega.
Qed.

Theorem of_intu_of_int_3:
  forall x,
  of_intu x = sub (of_int (Int.and x ox7FFF_FFFF)) (of_int (Int.and x ox8000_0000)).
Proof.
  intros.
  set (hi := Int.and x ox8000_0000).
  set (lo := Int.and x ox7FFF_FFFF).
  assert (R: forall n, integer_representable 53 1024 (Int.signed n)).
  { intros. pose proof (Int.signed_range n).
    apply integer_representable_n; auto; smart_omega. }
  unfold sub, of_int. rewrite BofZ_minus by auto. unfold of_intu. f_equal.
  assert (E: Int.add hi lo = x).
  { unfold hi, lo. rewrite Int.add_is_or. 
  - rewrite <- Int.and_or_distrib. apply Int.and_mone.
  - rewrite Int.and_assoc. rewrite (Int.and_commut ox8000_0000). rewrite Int.and_assoc.
    change (Int.and ox7FFF_FFFF ox8000_0000) with Int.zero. rewrite ! Int.and_zero; auto.
  }
  assert (RNG: 0 <= Int.unsigned lo < two_p 31).
  { unfold lo. change ox7FFF_FFFF with (Int.repr (two_p 31 - 1)). rewrite <- Int.zero_ext_and by lia.
    apply Int.zero_ext_range. compute_this Int.zwordsize. lia. }
  assert (B: forall i, 0 <= i < Int.zwordsize -> Int.testbit ox8000_0000 i = if zeq i 31 then true else false).
  { intros; unfold Int.testbit. change (Int.unsigned ox8000_0000) with (2^31).
    destruct (zeq i 31). subst i; auto. apply Z.pow2_bits_false; auto. } 
  assert (EITHER: hi = Int.zero \/ hi = ox8000_0000).
  { unfold hi; destruct (Int.testbit x 31) eqn:B31; [right|left];
    Int.bit_solve; rewrite B by auto.
  - destruct (zeq i 31). subst i; rewrite B31; auto. apply andb_false_r.
  - destruct (zeq i 31). subst i; rewrite B31; auto. apply andb_false_r.
  }
  assert (SU: - Int.signed hi = Int.unsigned hi).
  { destruct EITHER as [EQ|EQ]; rewrite EQ; reflexivity. }
  unfold Z.sub; rewrite SU, <- E. 
  unfold Int.add; rewrite Int.unsigned_repr, Int.signed_eq_unsigned. lia.
  - assert (Int.max_signed = two_p 31 - 1) by reflexivity. lia.
  - assert (Int.unsigned hi = 0 \/ Int.unsigned hi = two_p 31)
    by (destruct EITHER as [EQ|EQ]; rewrite EQ; [left|right]; reflexivity).
    assert (Int.max_unsigned = two_p 31 + two_p 31 - 1) by reflexivity.
    lia.
Qed.

Theorem to_intu_to_int_1:
  forall x n,
  cmp Clt x (of_intu ox8000_0000) = true ->
  to_intu x = Some n ->
  to_int x = Some n.
Proof.
  intros. unfold to_intu in H0.
  destruct (ZofB_range 53 1024 x 0 Int.max_unsigned) as [p|] eqn:E; simpl in H0; inv H0.
  exploit ZofB_range_inversion; eauto. intros (A & B & C).
  unfold to_int, ZofB_range. rewrite C.
  rewrite Zle_bool_true by smart_omega. rewrite Zle_bool_true; auto.
  exploit (BofZ_exact 53 1024 __ __ (Int.unsigned ox8000_0000)).
  vm_compute; intuition congruence.
  set (y := of_intu ox8000_0000) in *.
  change (BofZ 53 1024 eq_refl eq_refl (Int.unsigned ox8000_0000)) with y.
  intros (EQy & FINy & SIGNy).
  assert (FINx: is_finite _ _ x = true).
  { rewrite ZofB_correct in C. destruct (is_finite _ _ x) eqn:FINx; congruence. }
  destruct (zeq p 0).
  subst p; smart_omega.
  destruct (ZofB_range_pos 53 1024 __ __ x p C) as [P Q]. lia.
  assert (CMP: Bcompare _ _ x y = Some Lt).
  { unfold cmp, cmp_of_comparison, compare in H. destruct (Bcompare _ _ x y) as [[]|]; auto; discriminate. }
  rewrite Bcompare_correct in CMP by auto.
  inv CMP. apply Rcompare_Lt_inv in H1. rewrite EQy in H1.
  assert (p < Int.unsigned ox8000_0000).
  { apply lt_IZR. apply Rle_lt_trans with (1 := P) (2 := H1). }
  change Int.max_signed with (Int.unsigned ox8000_0000 - 1). lia.
Qed.

Theorem to_intu_to_int_2:
  forall x n,
  cmp Clt x (of_intu ox8000_0000) = false ->
  to_intu x = Some n ->
  to_int (sub x (of_intu ox8000_0000)) = Some (Int.sub n ox8000_0000).
Proof.
  intros. unfold to_intu in H0.
  destruct (ZofB_range _ _ x 0 Int.max_unsigned) as [p|] eqn:E; simpl in H0; inv H0.
  exploit ZofB_range_inversion; eauto. intros (A & B & C).
  exploit (BofZ_exact 53 1024 __ __ (Int.unsigned ox8000_0000)).
  vm_compute; intuition congruence.
  set (y := of_intu ox8000_0000) in *.
  change (BofZ 53 1024 __ __ (Int.unsigned ox8000_0000)) with y.
  intros (EQy & FINy & SIGNy).
  assert (FINx: is_finite _ _ x = true).
  { rewrite ZofB_correct in C. destruct (is_finite _ _ x) eqn:FINx; congruence. }
  assert (GE: (B2R _ _ x >= IZR (Int.unsigned ox8000_0000))%R).
  { rewrite <- EQy. unfold cmp, cmp_of_comparison, compare in H.
    rewrite Bcompare_correct in H by auto.
    destruct (Rcompare (B2R 53 1024 x) (B2R 53 1024 y)) eqn:CMP.
    apply Req_ge; apply Rcompare_Eq_inv; auto.
    discriminate.
    apply Rgt_ge; apply Rcompare_Gt_inv; auto.
  }
  assert (EQ: ZofB_range _ _ (sub x y) Int.min_signed Int.max_signed = Some (p - Int.unsigned ox8000_0000)).
  { apply ZofB_range_minus. exact E.
    compute_this (Int.unsigned ox8000_0000). smart_omega.
    apply Rge_le; auto.
  }
  unfold to_int; rewrite EQ. simpl. unfold Int.sub. rewrite Int.unsigned_repr by lia. auto.
Qed.

(** Conversions from ints to floats can be defined as bitwise manipulations
  over the in-memory representation.  This is what the PowerPC port does.
  The trick is that [from_words 0x4330_0000 x] is the float
  [2^52 + of_intu x]. *)

Definition ox4330_0000 := Int.repr 1127219200.        (**r [0x4330_0000] *)

Lemma split_bits_or:
  forall x,
  split_bits 52 11 (Int64.unsigned (Int64.ofwords ox4330_0000 x)) = (false, Int.unsigned x, 1075).
Proof.
  intros.
  transitivity (split_bits 52 11 (join_bits 52 11 false (Int.unsigned x) 1075)).
  - f_equal. rewrite Int64.ofwords_add'. reflexivity.
  - apply split_join_bits.
    generalize (Int.unsigned_range x).
    compute_this Int.modulus; compute_this (2^52); lia.
    compute_this (2^11); lia.
Qed.

Lemma from_words_value:
  forall x,
     B2R _ _ (from_words ox4330_0000 x) = (bpow radix2 52 + IZR (Int.unsigned x))%R
  /\ is_finite _ _ (from_words ox4330_0000 x) = true
  /\ Bsign _ _ (from_words ox4330_0000 x) = false.
Proof.
  intros; unfold from_words, of_bits, b64_of_bits, binary_float_of_bits.
  rewrite B2R_FF2B, is_finite_FF2B, Bsign_FF2B.
  unfold binary_float_of_bits_aux; rewrite split_bits_or; simpl; pose proof (Int.unsigned_range x).
  destruct (Int.unsigned x + Z.pow_pos 2 52) eqn:?.
  exfalso; now smart_omega.
  simpl; rewrite <- Heqz;  unfold F2R; simpl. split; auto.
  rewrite Rmult_1_r, plus_IZR. apply Rplus_comm.
  exfalso; now smart_omega.
Qed.

Lemma from_words_eq:
  forall x, from_words ox4330_0000 x = BofZ 53 1024 __ __ (2^52 + Int.unsigned x).
Proof.
  intros.
  pose proof (Int.unsigned_range x).
  destruct (from_words_value x) as (A & B & C).
  destruct (BofZ_exact 53 1024 __ __ (2^52 + Int.unsigned x)) as (D & E & F).
  smart_omega.
  apply B2R_Bsign_inj; auto.
  rewrite A, D. rewrite plus_IZR. auto.
  rewrite C, F. symmetry. apply Zlt_bool_false. smart_omega.
Qed.

Theorem of_intu_from_words:
  forall x,
  of_intu x = sub (from_words ox4330_0000 x) (from_words ox4330_0000 Int.zero).
Proof.
  intros. pose proof (Int.unsigned_range x).
  rewrite ! from_words_eq. unfold sub. rewrite BofZ_minus.
  unfold of_intu. apply (f_equal (BofZ 53 1024 __ __)). rewrite Int.unsigned_zero. lia.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; rewrite Int.unsigned_zero; smart_omega.
Qed.

Lemma ox8000_0000_signed_unsigned:
  forall x,
    Int.unsigned (Int.add x ox8000_0000) = Int.signed x + Int.half_modulus.
Proof.
  intro; unfold Int.signed, Int.add; pose proof (Int.unsigned_range x).
  destruct (zlt (Int.unsigned x) Int.half_modulus).
  rewrite Int.unsigned_repr; compute_this (Int.unsigned ox8000_0000); now smart_omega.
  rewrite (Int.eqm_samerepr _ (Int.unsigned x + -2147483648)).
  rewrite Int.unsigned_repr; now smart_omega.
  apply Int.eqm_add; [now apply Int.eqm_refl|exists 1;reflexivity].
Qed.

Theorem of_int_from_words:
  forall x,
  of_int x = sub (from_words ox4330_0000 (Int.add x ox8000_0000))
                 (from_words ox4330_0000 ox8000_0000).
Proof.
  intros.
  pose proof (Int.signed_range x).
  rewrite ! from_words_eq. rewrite ox8000_0000_signed_unsigned.
  change (Int.unsigned ox8000_0000) with Int.half_modulus.
  unfold sub. rewrite BofZ_minus.
  unfold of_int. apply f_equal. lia.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; smart_omega.
Qed.

Definition ox4530_0000 := Int.repr 1160773632.        (**r [0x4530_0000] *)

Lemma split_bits_or':
  forall x,
  split_bits 52 11 (Int64.unsigned (Int64.ofwords ox4530_0000 x)) = (false, Int.unsigned x, 1107).
Proof.
  intros.
  transitivity (split_bits 52 11 (join_bits 52 11 false (Int.unsigned x) 1107)).
  - f_equal. rewrite Int64.ofwords_add'. reflexivity.
  - apply split_join_bits.
    generalize (Int.unsigned_range x).
    compute_this Int.modulus; compute_this (2^52); lia.
    compute_this (2^11); lia.
Qed.

Lemma from_words_value':
  forall x,
     B2R _ _ (from_words ox4530_0000 x) = (bpow radix2 84 + IZR (Int.unsigned x * two_p 32))%R
  /\ is_finite _ _ (from_words ox4530_0000 x) = true
  /\ Bsign _ _ (from_words ox4530_0000 x) = false.
Proof.
  intros; unfold from_words, of_bits, b64_of_bits, binary_float_of_bits.
  rewrite B2R_FF2B, is_finite_FF2B, Bsign_FF2B.
  unfold binary_float_of_bits_aux; rewrite split_bits_or'; simpl; pose proof (Int.unsigned_range x).
  destruct (Int.unsigned x + Z.pow_pos 2 52) eqn:?.
  exfalso; now smart_omega.
  simpl; rewrite <- Heqz;  unfold F2R; simpl. split; auto.
  rewrite plus_IZR, Rmult_plus_distr_r, <- 2!mult_IZR, Rplus_comm.
  easy.
  assert (Zneg p < 0) by reflexivity.
  exfalso; now smart_omega.
Qed.

Lemma from_words_eq':
  forall x, from_words ox4530_0000 x = BofZ 53 1024 __ __ (2^84 + Int.unsigned x * 2^32).
Proof.
  intros.
  pose proof (Int.unsigned_range x).
  destruct (from_words_value' x) as (A & B & C).
  destruct (BofZ_representable 53 1024 __ __ (2^84 + Int.unsigned x * 2^32)) as (D & E & F).
  replace (2^84 + Int.unsigned x * 2^32)
    with  ((2^52 + Int.unsigned x) * 2^32) by ring.
  apply integer_representable_n2p; auto. smart_omega. lia. lia.
  apply B2R_Bsign_inj; auto.
  rewrite A, D. rewrite <- IZR_Zpower by lia. rewrite <- plus_IZR. auto.
  rewrite C, F. symmetry. apply Zlt_bool_false.
  compute_this (2^84); compute_this (2^32); lia.
Qed.

Theorem of_longu_from_words:
  forall l,
  of_longu l =
    add (sub (from_words ox4530_0000 (Int64.hiword l))
             (from_words ox4530_0000 (Int.repr (two_p 20))))
        (from_words ox4330_0000 (Int64.loword l)).
Proof.
  intros.
  pose proof (Int64.unsigned_range l).
  pose proof (Int.unsigned_range (Int64.hiword l)).
  pose proof (Int.unsigned_range (Int64.loword l)).
  rewrite ! from_words_eq, ! from_words_eq'.
  set (p20 := Int.unsigned (Int.repr (two_p 20))).
  set (x := Int64.unsigned l) in *;
  set (xl := Int.unsigned (Int64.loword l)) in *;
  set (xh := Int.unsigned (Int64.hiword l)) in *.
  unfold sub. rewrite BofZ_minus.
  replace (2^84 + xh * 2^32 - (2^84 + p20 * 2^32))
     with ((xh - p20) * 2^32) by ring.
  unfold add. rewrite BofZ_plus.
  unfold of_longu. f_equal.
  rewrite <- (Int64.ofwords_recompose l) at 1. rewrite Int64.ofwords_add'.
  fold xh; fold xl. compute_this (two_p 32); compute_this p20; ring.
  apply integer_representable_n2p; auto.
  compute_this p20; smart_omega. lia. lia.
  apply integer_representable_n; auto; smart_omega.
  replace (2^84 + xh * 2^32) with ((2^52 + xh) * 2^32) by ring.
  apply integer_representable_n2p; auto. smart_omega. lia. lia.
  change (2^84 + p20 * 2^32) with ((2^52 + 1048576) * 2^32).
  apply integer_representable_n2p; auto. lia. lia.
Qed.

Theorem of_long_from_words:
  forall l,
  of_long l =
    add (sub (from_words ox4530_0000 (Int.add (Int64.hiword l) ox8000_0000))
             (from_words ox4530_0000 (Int.repr (two_p 20+two_p 31))))
        (from_words ox4330_0000 (Int64.loword l)).
Proof.
  intros.
  pose proof (Int64.signed_range l).
  pose proof (Int.signed_range (Int64.hiword l)).
  pose proof (Int.unsigned_range (Int64.loword l)).
  rewrite ! from_words_eq, ! from_words_eq'.
  set (p := Int.unsigned (Int.repr (two_p 20 + two_p 31))).
  set (x := Int64.signed l) in *;
  set (xl := Int.unsigned (Int64.loword l)) in *;
  set (xh := Int.signed (Int64.hiword l)) in *.
  rewrite ox8000_0000_signed_unsigned. fold xh.
  unfold sub. rewrite BofZ_minus.
  replace (2^84 + (xh + Int.half_modulus) * 2^32 - (2^84 + p * 2^32))
     with ((xh - 2^20) * 2^32)
       by (compute_this p; compute_this Int.half_modulus; ring).
  unfold add. rewrite BofZ_plus.
  unfold of_long. apply f_equal.
  rewrite <- (Int64.ofwords_recompose l) at 1. rewrite Int64.ofwords_add''.
  fold xh; fold xl. compute_this (two_p 32); ring.
  apply integer_representable_n2p; auto.
  compute_this (2^20); smart_omega. lia. lia.
  apply integer_representable_n; auto; smart_omega.
  replace (2^84 + (xh + Int.half_modulus) * 2^32)
     with ((2^52 + xh + Int.half_modulus) * 2^32)
       by (compute_this Int.half_modulus; ring).
  apply integer_representable_n2p; auto. smart_omega. lia. lia.
  change (2^84 + p * 2^32) with ((2^52 + p) * 2^32).
  apply integer_representable_n2p; auto.
  compute_this p; smart_omega. lia.
Qed.

(** Conversions from 64-bit integers can be expressed in terms of
  conversions from their 32-bit halves. *)

Theorem of_longu_decomp:
  forall l,
  of_longu l = add (mul (of_intu (Int64.hiword l)) (BofZ 53 1024 __ __ (2^32)))
                   (of_intu (Int64.loword l)).
Proof.
  intros.
  unfold of_longu, of_intu, add, mul.
  pose proof (Int.unsigned_range (Int64.loword l)).
  pose proof (Int.unsigned_range (Int64.hiword l)).
  pose proof (Int64.unsigned_range l).
  set (x := Int64.unsigned l) in *.
  set (yl := Int.unsigned (Int64.loword l)) in *.
  set (yh := Int.unsigned (Int64.hiword l)) in *.
  assert (DECOMP: x = yh * 2^32 + yl).
  { unfold x. rewrite <- (Int64.ofwords_recompose l). apply Int64.ofwords_add'. }
  rewrite BofZ_mult. rewrite BofZ_plus. rewrite DECOMP; auto.
  apply integer_representable_n2p; auto. smart_omega. lia. lia.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; smart_omega.
  compute; auto.
Qed.

Theorem of_long_decomp:
  forall l,
  of_long l = add (mul (of_int (Int64.hiword l)) (BofZ 53 1024 __ __ (2^32)))
                  (of_intu (Int64.loword l)).
Proof.
  intros.
  unfold of_long, of_int, of_intu, add, mul.
  pose proof (Int.unsigned_range (Int64.loword l)).
  pose proof (Int.signed_range (Int64.hiword l)).
  pose proof (Int64.signed_range l).
  set (x := Int64.signed l) in *.
  set (yl := Int.unsigned (Int64.loword l)) in *.
  set (yh := Int.signed (Int64.hiword l)) in *.
  assert (DECOMP: x = yh * 2^32 + yl).
  { unfold x. rewrite <- (Int64.ofwords_recompose l), Int64.ofwords_add''. auto. }
  rewrite BofZ_mult. rewrite BofZ_plus. rewrite DECOMP; auto.
  apply integer_representable_n2p; auto. smart_omega. lia. lia.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto; smart_omega.
  apply integer_representable_n; auto. compute; intuition congruence.
  compute; auto.
Qed.

(** Conversions from unsigned longs can be expressed in terms of conversions from signed longs.
    If the unsigned long is too big, a round-to-odd must be performed on it
    to avoid double rounding. *)

Theorem of_longu_of_long_1:
  forall x,
  Int64.ltu x (Int64.repr Int64.half_modulus) = true ->
  of_longu x = of_long x.
Proof.
  unfold of_longu, of_long, Int64.signed, Int64.ltu; intro.
  change (Int64.unsigned (Int64.repr Int64.half_modulus)) with Int64.half_modulus.
  destruct (zlt (Int64.unsigned x) Int64.half_modulus); now intuition.
Qed.

Theorem of_longu_of_long_2:
  forall x,
  Int64.ltu x (Int64.repr Int64.half_modulus) = false ->
  of_longu x = mul (of_long (Int64.or (Int64.shru x Int64.one)
                                      (Int64.and x Int64.one)))
                   (of_int (Int.repr 2)).
Proof.
  intros. change (of_int (Int.repr 2)) with (BofZ 53 1024 __ __ (2^1)).
  pose proof (Int64.unsigned_range x).
  unfold Int64.ltu in H.
  change (Int64.unsigned (Int64.repr Int64.half_modulus)) with (2^63) in H.
  destruct (zlt (Int64.unsigned x) (2^63)); inv H.
  assert (Int64.modulus <= 2^1024 - 2^(1024-53)) by (vm_compute; intuition congruence).
  set (n := Int64.or (Int64.shru x Int64.one) (Int64.and x Int64.one)).
  assert (NB: forall i, 0 <= i < 64 ->
              Int64.testbit n i =
                if zeq i 0 then Int64.testbit x 1 || Int64.testbit x 0
                else if zeq i 63 then false else Int64.testbit x (i + 1)).
  { intros; unfold n; autorewrite with ints; auto. rewrite Int64.unsigned_one.
    rewrite Int64.bits_one. compute_this Int64.zwordsize.
    destruct (zeq i 0); simpl proj_sumbool.
    rewrite zlt_true by lia. rewrite andb_true_r. subst i; auto.
    rewrite andb_false_r, orb_false_r.
    destruct (zeq i 63). subst i. apply zlt_false; lia.
    apply zlt_true; lia. }
  assert (NB2: forall i, 0 <= i ->
               Z.testbit (Int64.signed n * 2^1) i =
               if zeq i 0 then false else
               if zeq i 1 then Int64.testbit x 1 || Int64.testbit x 0 else
               Int64.testbit x i).
  { intros. rewrite Z.mul_pow2_bits by lia. destruct (zeq i 0).
    apply Z.testbit_neg_r; lia.
    rewrite Int64.bits_signed by lia. compute_this Int64.zwordsize.
    destruct (zlt (i-1) 64).
    rewrite NB by lia. destruct (zeq i 1).
    subst. rewrite dec_eq_true by auto. auto.
    rewrite dec_eq_false by lia. destruct (zeq (i - 1) 63).
    symmetry. apply Int64.bits_above. compute_this Int64.zwordsize; lia.
    f_equal; lia.
    rewrite NB by lia. rewrite dec_eq_false by lia. rewrite dec_eq_true by auto.
    rewrite dec_eq_false by lia. symmetry. apply Int64.bits_above. compute_this Int64.zwordsize; lia.
  }
  assert (EQ: Int64.signed n * 2 = int_round_odd (Int64.unsigned x) 1).
  {
  symmetry. apply int_round_odd_bits. lia.
  intros. rewrite NB2 by lia. replace i with 0 by lia. auto.
  rewrite NB2 by lia. rewrite dec_eq_false by lia. rewrite dec_eq_true.
  rewrite orb_comm. unfold Int64.testbit. change (2^1) with 2.
  destruct (Z.testbit (Int64.unsigned x) 0) eqn:B0;
  [rewrite Z.testbit_true in B0 by lia|rewrite Z.testbit_false in B0 by lia];
  change (2^0) with 1 in B0; rewrite Zdiv_1_r in B0; rewrite B0; auto.
  intros. rewrite NB2 by lia. rewrite ! dec_eq_false by lia. auto.
  }
  unfold mul, of_long, of_longu.
  rewrite BofZ_mult_2p.
- change (2^1) with 2. rewrite EQ. apply BofZ_round_odd with (p := 1).
+ lia.
+ apply Z.le_trans with Int64.modulus; trivial. smart_omega.
+ lia.
+ apply Z.le_trans with (2^63). compute; intuition congruence. extlia.
- apply Z.le_trans with Int64.modulus; trivial.
  pose proof (Int64.signed_range n).
  compute_this Int64.min_signed; compute_this Int64.max_signed;
  compute_this Int64.modulus; extlia.
- assert (2^63 <= int_round_odd (Int64.unsigned x) 1).
  { change (2^63) with (int_round_odd (2^63) 1). apply int_round_odd_le; lia. }
  rewrite <- EQ in H1. compute_this (2^63). compute_this (2^53). extlia.
- lia.
Qed.

(** Conversions to/from 32-bit integers can be implemented by going through 64-bit integers. *)

Remark ZofB_range_widen:
  forall (f: float) n min1 max1 min2 max2,
  ZofB_range _ _ f min1 max1 = Some n ->
  min2 <= min1 -> max1 <= max2 ->
  ZofB_range _ _ f min2 max2 = Some n.
Proof.
  intros. exploit ZofB_range_inversion; eauto. intros (A & B & C).
  unfold ZofB_range; rewrite C.
  replace (min2 <=? n) with true. replace (n <=? max2) with true. auto.
  symmetry; apply Z.leb_le; lia.
  symmetry; apply Z.leb_le; lia.
Qed.

Theorem to_int_to_long:
  forall f n, to_int f = Some n -> to_long f = Some (Int64.repr (Int.signed n)).
Proof.
  unfold to_int, to_long; intros.
  destruct (ZofB_range 53 1024 f Int.min_signed Int.max_signed) as [z|] eqn:Z; inv H.
  exploit ZofB_range_inversion; eauto. intros (A & B & C).
  replace (ZofB_range 53 1024 f Int64.min_signed Int64.max_signed) with (Some z).
  simpl. rewrite Int.signed_repr; auto.
  symmetry; eapply ZofB_range_widen; eauto. compute; congruence. compute; congruence.
Qed.

Theorem to_intu_to_longu:
  forall f n, to_intu f = Some n -> to_longu f = Some (Int64.repr (Int.unsigned n)).
Proof.
  unfold to_intu, to_longu; intros.
  destruct (ZofB_range 53 1024 f 0 Int.max_unsigned) as [z|] eqn:Z; inv H.
  exploit ZofB_range_inversion; eauto. intros (A & B & C).
  replace (ZofB_range 53 1024 f 0 Int64.max_unsigned) with (Some z).
  simpl. rewrite Int.unsigned_repr; auto.
  symmetry; eapply ZofB_range_widen; eauto. lia. compute; congruence.
Qed.

Theorem to_intu_to_long:
  forall f n, to_intu f = Some n -> to_long f = Some (Int64.repr (Int.unsigned n)).
Proof.
  unfold to_intu, to_long; intros.
  destruct (ZofB_range 53 1024 f 0 Int.max_unsigned) as [z|] eqn:Z; inv H.
  exploit ZofB_range_inversion; eauto. intros (A & B & C).
  replace (ZofB_range 53 1024 f Int64.min_signed Int64.max_signed) with (Some z).
  simpl. rewrite Int.unsigned_repr; auto.
  symmetry; eapply ZofB_range_widen; eauto. compute; congruence. compute; congruence.
Qed.

Theorem of_int_of_long:
  forall n, of_int n = of_long (Int64.repr (Int.signed n)).
Proof.
  unfold of_int, of_long. intros. f_equal. rewrite Int64.signed_repr. auto.
  generalize (Int.signed_range n). compute_this Int64.min_signed. compute_this Int64.max_signed. smart_omega.
Qed.

Theorem of_intu_of_longu:
  forall n, of_intu n = of_longu (Int64.repr (Int.unsigned n)).
Proof.
  unfold of_intu, of_longu. intros. f_equal. rewrite Int64.unsigned_repr. auto.
  generalize (Int.unsigned_range n). smart_omega.
Qed.

Theorem of_intu_of_long:
  forall n, of_intu n = of_long (Int64.repr (Int.unsigned n)).
Proof.
  unfold of_intu, of_long. intros. f_equal. rewrite Int64.signed_repr. auto.
  generalize (Int.unsigned_range n). compute_this Int64.min_signed; compute_this Int64.max_signed; smart_omega.
Qed.

End Float.

(** * Single-precision FP numbers *)

Module Float32.

Definition neg_nan (f : float32) : { x : float32 | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => exist _ (B754_nan 24 128 (negb s) p H) (eq_refl true)
  | _ => default_nan_32
  end.

Definition abs_nan (f : float32) : { x : float32 | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => exist _ (B754_nan 24 128 false p H) (eq_refl true)
  | _ => default_nan_32
  end.

Definition cons_pl (x: float32) (l: list (bool * positive)) :=
  match x with B754_nan s p _ => (s, p) :: l | _ => l end.

Definition unop_nan (x: float32) : {x : float32 | is_nan _ _ x = true} :=
  quiet_nan_32 (Archi.choose_nan_32 (cons_pl x [])).

Definition binop_nan (x y: float32) : {x : float32 | is_nan _ _ x = true} :=
  quiet_nan_32 (Archi.choose_nan_32 (cons_pl x (cons_pl y []))).

Definition fma_nan_1 (x y z: float32) : {x : float32 | is_nan _ _ x = true} :=
  let '(a, b, c) := Archi.fma_order x y z in
  quiet_nan_32 (Archi.choose_nan_32 (cons_pl a (cons_pl b (cons_pl c [])))).

Definition fma_nan (x y z: float32) : {x : float32 | is_nan _ _ x = true} :=
  match x, y with
  | B754_infinity _, B754_zero _ | B754_zero _, B754_infinity _ =>
      if Archi.fma_invalid_mul_is_nan
      then quiet_nan_32 (Archi.choose_nan_32 (Archi.default_nan_32 :: cons_pl z []))
      else fma_nan_1 x y z
  | _, _ =>
      fma_nan_1 x y z
  end.

(** ** Operations over single-precision floats *)

Definition zero: float32 := B754_zero _ _ false. (**r the float [+0.0] *)

Definition eq_dec: forall (f1 f2: float32), {f1 = f2} + {f1 <> f2} := Beq_dec _ _.

(** Arithmetic operations *)

Definition neg: float32 -> float32 := Bopp _ _ neg_nan. (**r opposite (change sign) *)
Definition abs: float32 -> float32 := Babs _ _ abs_nan. (**r absolute value (set sign to [+]) *)
Definition sqrt: float32 -> float32 :=
  Bsqrt 24 128 __ __ unop_nan mode_NE.  (**r square root *)
Definition add: float32 -> float32 -> float32 :=
  Bplus 24 128 __ __ binop_nan mode_NE. (**r addition *)
Definition sub: float32 -> float32 -> float32 :=
  Bminus 24 128 __ __ binop_nan mode_NE. (**r subtraction *)
Definition mul: float32 -> float32 -> float32 :=
  Bmult 24 128 __ __ binop_nan mode_NE. (**r multiplication *)
Definition div: float32 -> float32 -> float32 :=
  Bdiv 24 128 __ __ binop_nan mode_NE. (**r division *)
Definition fma: float32 -> float32 -> float32 -> float32 :=
  Bfma 24 128 __ __ fma_nan mode_NE. (**r fused multiply-add [x * y + z] *)
Definition compare (f1 f2: float32) : option Datatypes.comparison := (**r general comparison *)
  Bcompare 24 128 f1 f2.
Definition cmp (c:comparison) (f1 f2: float32) : bool := (**r comparison *)
  cmp_of_comparison c (compare f1 f2).
Definition ordered (f1 f2: float32) : bool :=
  ordered_of_comparison (compare f1 f2).

(** Conversions *)

Definition of_double : float -> float32 := Float.to_single.
Definition to_double : float32 -> float := Float.of_single.

Definition to_int (f:float32): option int := (**r conversion to signed 32-bit int *)
  option_map Int.repr (ZofB_range _ _ f Int.min_signed Int.max_signed).
Definition to_intu (f:float32): option int := (**r conversion to unsigned 32-bit int *)
  option_map Int.repr (ZofB_range _ _ f 0 Int.max_unsigned).
Definition to_long (f:float32): option int64 := (**r conversion to signed 64-bit int *)
  option_map Int64.repr (ZofB_range _ _ f Int64.min_signed Int64.max_signed).
Definition to_longu (f:float32): option int64 := (**r conversion to unsigned 64-bit int *)
  option_map Int64.repr (ZofB_range _ _ f 0 Int64.max_unsigned).

Definition of_int (n:int): float32 := (**r conversion from signed 32-bit int to single-precision float *)
  BofZ 24 128 __ __ (Int.signed n).
Definition of_intu (n:int): float32 := (**r conversion from unsigned 32-bit int to single-precision float *)
  BofZ 24 128 __ __ (Int.unsigned n).

Definition of_long (n:int64): float32 := (**r conversion from signed 64-bit int to single-precision float *)
  BofZ 24 128 __ __ (Int64.signed n).
Definition of_longu (n:int64): float32 := (**r conversion from unsigned 64-bit int to single-precision float *)
  BofZ 24 128 __ __ (Int64.unsigned n).

Definition from_parsed (base:positive) (intPart:positive) (expPart:Z) : float32 :=
  Bparse 24 128 __ __ base intPart expPart.

(** Conversions between floats and their concrete in-memory representation
    as a sequence of 32 bits. *)

Definition to_bits (f: float32) : int := Int.repr (bits_of_b32 f).
Definition of_bits (b: int): float32 := b32_of_bits (Int.unsigned b).

(** ** Properties *)

(** Commutativity properties of addition and multiplication. *)

Theorem add_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> add x y = add y x.
Proof.
  intros. apply Bplus_commut. 
  destruct x, y; try reflexivity; now destruct H.
Qed.

Theorem mul_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> mul x y = mul y x.
Proof.
  intros. apply Bmult_commut.
  destruct x, y; try reflexivity; now destruct H.
Qed.

(** Multiplication by 2 is diagonal addition. *)

Theorem mul2_add:
  forall f, add f f = mul f (of_int (Int.repr 2%Z)).
Proof.
  intros. apply Bmult2_Bplus.
  intros x y Hx Hy. unfold binop_nan.
  destruct x; try discriminate. simpl. rewrite Archi.choose_nan_32_idem. 
  destruct y; reflexivity || discriminate.
Qed.

(** Divisions that can be turned into multiplication by an inverse. *)

Definition exact_inverse : float32 -> option float32 := Bexact_inverse 24 128 __ __.

Theorem div_mul_inverse:
  forall x y z, exact_inverse y = Some z -> div x y = mul x z.
Proof.
  intros. apply Bdiv_mult_inverse. 2: easy.
  intros x0 y0 z0 Hx Hy Hz. unfold binop_nan.
  destruct x0; try discriminate.
  destruct y0, z0; reflexivity || discriminate.
Qed.

(** Properties of comparisons. *)

Theorem cmp_swap:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  unfold cmp, compare; intros. rewrite (Bcompare_swap _ _ x y).
  apply cmp_of_comparison_swap.
Qed.

Theorem cmp_ne_eq:
  forall f1 f2, cmp Cne f1 f2 = negb (cmp Ceq f1 f2).
Proof.
  intros; apply cmp_of_comparison_ne_eq.
Qed.

Theorem cmp_lt_eq_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Ceq f1 f2 = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_lt_eq_false.
Qed.

Theorem cmp_le_lt_eq:
  forall f1 f2, cmp Cle f1 f2 = cmp Clt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros f1 f2; apply cmp_of_comparison_le_lt_eq.
Qed.

Theorem cmp_gt_eq_false:
  forall x y, cmp Cgt x y = true -> cmp Ceq x y = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_gt_eq_false.
Qed.

Theorem cmp_ge_gt_eq:
  forall f1 f2, cmp Cge f1 f2 = cmp Cgt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros f1 f2; apply cmp_of_comparison_ge_gt_eq.
Qed.

Theorem cmp_lt_gt_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Cgt f1 f2 = true -> False.
Proof.
  intros f1 f2; apply cmp_of_comparison_lt_gt_false.
Qed.

Theorem cmp_double:
  forall f1 f2 c, cmp c f1 f2 = Float.cmp c (to_double f1) (to_double f2).
Proof.
  unfold cmp, Float.cmp; intros. f_equal. symmetry. apply Bcompare_Bconv_widen.
  red; lia. lia. lia.
Qed.

(** Properties of conversions to/from in-memory representation.
  The conversions are bijective (one-to-one). *)

Theorem of_to_bits:
  forall f, of_bits (to_bits f) = f.
Proof.
  intros; unfold of_bits, to_bits, bits_of_b32, b32_of_bits.
  rewrite Int.unsigned_repr, binary_float_of_bits_of_binary_float; [reflexivity|].
  generalize (bits_of_binary_float_range 23 8 __ __ f).
  change (2^(23+8+1)) with (Int.max_unsigned + 1). lia.
Qed.

Theorem to_of_bits:
  forall b, to_bits (of_bits b) = b.
Proof.
  intros; unfold of_bits, to_bits, bits_of_b32, b32_of_bits.
  rewrite bits_of_binary_float_of_bits. apply Int.repr_unsigned.
  apply Int.unsigned_range.
Qed.

(** Conversions from 32-bit integers to single-precision floats can
  be decomposed into a conversion to a double-precision float,
  followed by a [Float32.of_double] conversion.  No double rounding occurs. *)

Theorem of_int_double:
  forall n, of_int n = of_double (Float.of_int n).
Proof.
  intros. symmetry. apply Bconv_BofZ.
  apply integer_representable_n; auto. generalize (Int.signed_range n); Float.smart_omega.
Qed.

Theorem of_intu_double:
  forall n, of_intu n = of_double (Float.of_intu n).
Proof.
  intros. symmetry. apply Bconv_BofZ.
  apply integer_representable_n; auto. generalize (Int.unsigned_range n); Float.smart_omega.
Qed.

(** Conversion of single-precision floats to integers can be decomposed
  into a [Float32.to_double] extension, followed by a double-precision-to-int
  conversion. *)

Theorem to_int_double:
  forall f n, to_int f = Some n -> Float.to_int (to_double f) = Some n.
Proof.
  intros.
  unfold to_int in H.
  destruct (ZofB_range _ _ f Int.min_signed Int.max_signed) as [n'|] eqn:E; inv H.
  unfold Float.to_int, to_double, Float.of_single.
  erewrite ZofB_range_Bconv; eauto. auto. lia. lia. lia. lia.
Qed.

Theorem to_intu_double:
  forall f n, to_intu f = Some n -> Float.to_intu (to_double f) = Some n.
Proof.
  intros.
  unfold to_intu in H.
  destruct (ZofB_range _ _ f 0 Int.max_unsigned) as [n'|] eqn:E; inv H.
  unfold Float.to_intu, to_double, Float.of_single.
  erewrite ZofB_range_Bconv; eauto. auto. lia. lia. lia. lia.
Qed.

Theorem to_long_double:
  forall f n, to_long f = Some n -> Float.to_long (to_double f) = Some n.
Proof.
  intros.
  unfold to_long in H.
  destruct (ZofB_range _ _ f Int64.min_signed Int64.max_signed) as [n'|] eqn:E; inv H.
  unfold Float.to_long, to_double, Float.of_single.
  erewrite ZofB_range_Bconv; eauto. auto. lia. lia. lia. lia.
Qed.

Theorem to_longu_double:
  forall f n, to_longu f = Some n -> Float.to_longu (to_double f) = Some n.
Proof.
  intros.
  unfold to_longu in H.
  destruct (ZofB_range _ _ f 0 Int64.max_unsigned) as [n'|] eqn:E; inv H.
  unfold Float.to_longu, to_double, Float.of_single.
  erewrite ZofB_range_Bconv; eauto. auto. lia. lia. lia. lia.
Qed.

(** Conversions from 64-bit integers to single-precision floats can be expressed
  as conversion to a double-precision float followed by a [Float32.of_double] conversion.
  To avoid double rounding when the integer is large (above [2^53]), a round
  to odd must be performed on the integer before conversion to double-precision float. *)

Lemma int_round_odd_plus:
  forall p n, 0 <= p ->
  int_round_odd n p = Z.land (Z.lor n (Z.land n (2^p-1) + (2^p-1))) (-(2^p)).
Proof.
  intros.
  assert (POS: 0 < 2^p) by (apply (Zpower_gt_0 radix2); auto).
  assert (A: Z.land n (2^p-1) = n mod 2^p).
  { rewrite <- Z.land_ones by auto. f_equal. rewrite Z.ones_equiv. lia. }
  rewrite A.
  assert (B: 0 <= n mod 2^p < 2^p).
  { apply Z_mod_lt. lia. }
  set (m := n mod 2^p + (2^p-1)) in *.
  assert (C: m / 2^p = if zeq (n mod 2^p) 0 then 0 else 1).
  { unfold m. destruct (zeq (n mod 2^p) 0).
    rewrite e. apply Z.div_small. lia.
    eapply Coqlib.Zdiv_unique with (n mod 2^p - 1). ring. lia. }
  assert (D: Z.testbit m p = if zeq (n mod 2^p) 0 then false else true).
  { destruct (zeq (n mod 2^p) 0).
    apply Z.testbit_false; auto. rewrite C; auto.
    apply Z.testbit_true; auto. rewrite C; auto. }
  assert (E: forall i, p < i -> Z.testbit m i = false).
  { intros. apply Z.testbit_false. lia.
    replace (m / 2^i) with 0. auto. symmetry. apply Z.div_small.
    unfold m. split. lia. apply Z.lt_le_trans with (2 * 2^p). lia.
    change 2 with (2^1) at 1. rewrite <- (Zpower_plus radix2) by lia.
    apply Zpower_le. lia. }
  assert (F: forall i, 0 <= i -> Z.testbit (-2^p) i = if zlt i p then false else true).
  { intros. rewrite Z.bits_opp by auto. rewrite <- Z.ones_equiv.
    destruct (zlt i p).
    rewrite Z.ones_spec_low by lia. auto.
    rewrite Z.ones_spec_high by lia. auto. }
  apply int_round_odd_bits; auto.
  - intros. rewrite Z.land_spec, F, zlt_true by lia. apply andb_false_r.
  - rewrite Z.land_spec, Z.lor_spec, D, F, zlt_false, andb_true_r by lia.
    destruct (Z.eqb (n mod 2^p) 0) eqn:Z.
    rewrite Z.eqb_eq in Z. rewrite Z, zeq_true. apply orb_false_r.
    rewrite Z.eqb_neq in Z. rewrite zeq_false by auto. apply orb_true_r.
  - intros. rewrite Z.land_spec, Z.lor_spec, E, F, zlt_false, andb_true_r by lia.
    apply orb_false_r.
Qed.

Lemma of_long_round_odd:
  forall n conv_nan,
  2^36 <= Z.abs n < 2^64 ->
  BofZ 24 128 __ __ n = Bconv _ _ 24 128 __ __ conv_nan mode_NE (BofZ 53 1024 __ __ (Z.land (Z.lor n ((Z.land n 2047) + 2047)) (-2048))).
Proof.
  intros. rewrite <- (int_round_odd_plus 11) by lia.
  assert (-2^64 <= int_round_odd n 11).
  { change (-2^64) with (int_round_odd (-2^64) 11). apply int_round_odd_le; extlia. }
  assert (int_round_odd n 11 <= 2^64).
  { change (2^64) with (int_round_odd (2^64) 11). apply int_round_odd_le; extlia. }
  rewrite Bconv_BofZ.
  apply BofZ_round_odd with (p := 11).
  lia.
  apply Z.le_trans with (2^64). lia. compute; intuition congruence.
  lia.
  exact (proj1 H).
  unfold int_round_odd. apply integer_representable_n2p_wide. auto. lia.
  unfold int_round_odd in H0, H1.
  split; (apply Zmult_le_reg_r with (2^11); [compute; auto | assumption]).
  lia.
  lia.
Qed.

Theorem of_longu_double_1:
  forall n,
  Int64.unsigned n <= 2^53 ->
  of_longu n = of_double (Float.of_longu n).
Proof.
  intros. symmetry; apply Bconv_BofZ. apply integer_representable_n; auto.
  pose proof (Int64.unsigned_range n); lia.
Qed.

Theorem of_longu_double_2:
  forall n,
  2^36 <= Int64.unsigned n ->
  of_longu n = of_double (Float.of_longu
                           (Int64.and (Int64.or n
                                                (Int64.add (Int64.and n (Int64.repr 2047))
                                                           (Int64.repr 2047)))
                                      (Int64.repr (-2048)))).
Proof.
  intros.
  pose proof (Int64.unsigned_range n).
  unfold of_longu. erewrite of_long_round_odd.
  unfold of_double, Float.to_single. instantiate (1 := Float.to_single_nan).
  f_equal. unfold Float.of_longu. f_equal.
  set (n' := Z.land (Z.lor (Int64.unsigned n) (Z.land (Int64.unsigned n) 2047 + 2047)) (-2048)).
  assert (int_round_odd (Int64.unsigned n) 11 = n') by (apply int_round_odd_plus; lia).
  assert (0 <= n').
  { rewrite <- H1. change 0 with (int_round_odd 0 11). apply int_round_odd_le; lia. }
  assert (n' < Int64.modulus).
  { apply Z.le_lt_trans with (int_round_odd (Int64.modulus - 1) 11).
    rewrite <- H1. apply int_round_odd_le; lia.
    compute; auto. }
  rewrite <- (Int64.unsigned_repr n') by (unfold Int64.max_unsigned; lia).
  f_equal. Int64.bit_solve. rewrite Int64.testbit_repr by auto. unfold n'.
  rewrite Z.land_spec, Z.lor_spec. f_equal. f_equal.
  unfold Int64.testbit. rewrite Int64.add_unsigned.
  fold (Int64.testbit (Int64.repr
        (Int64.unsigned (Int64.and n (Int64.repr 2047)) +
         Int64.unsigned (Int64.repr 2047))) i).
  rewrite Int64.testbit_repr by auto. f_equal. f_equal. unfold Int64.and.
  symmetry. apply Int64.unsigned_repr. change 2047 with (Z.ones 11).
  rewrite Z.land_ones by lia.
  exploit (Z_mod_lt (Int64.unsigned n) (2^11)). compute; auto.
  assert (2^11 < Int64.max_unsigned) by (compute; auto). lia.
  apply Int64.same_bits_eqm; auto. exists (-1); auto.
  split. extlia. change (2^64) with Int64.modulus. extlia.
Qed.

Theorem of_long_double_1:
  forall n,
  Z.abs (Int64.signed n) <= 2^53 ->
  of_long n = of_double (Float.of_long n).
Proof.
  intros. symmetry; apply Bconv_BofZ. apply integer_representable_n; auto. extlia.
Qed.

Theorem of_long_double_2:
  forall n,
  2^36 <= Z.abs (Int64.signed n) ->
  of_long n = of_double (Float.of_long
                           (Int64.and (Int64.or n
                                                (Int64.add (Int64.and n (Int64.repr 2047))
                                                           (Int64.repr 2047)))
                                      (Int64.repr (-2048)))).
Proof.
  intros.
  pose proof (Int64.signed_range n).
  unfold of_long. erewrite of_long_round_odd.
  unfold of_double, Float.to_single. instantiate (1 := Float.to_single_nan).
  f_equal. unfold Float.of_long. f_equal.
  set (n' := Z.land (Z.lor (Int64.signed n) (Z.land (Int64.signed n) 2047 + 2047)) (-2048)).
  assert (int_round_odd (Int64.signed n) 11 = n') by (apply int_round_odd_plus; lia).
  assert (Int64.min_signed <= n').
  { rewrite <- H1. change Int64.min_signed with (int_round_odd Int64.min_signed 11). apply int_round_odd_le; lia. }
  assert (n' <= Int64.max_signed).
  { apply Z.le_trans with (int_round_odd Int64.max_signed 11).
    rewrite <- H1. apply int_round_odd_le; lia.
    compute; intuition congruence. }
  rewrite <- (Int64.signed_repr n') by lia.
  f_equal. Int64.bit_solve. rewrite Int64.testbit_repr by auto. unfold n'.
  rewrite Z.land_spec, Z.lor_spec. f_equal. f_equal.
  rewrite Int64.bits_signed by lia. rewrite zlt_true by lia. auto.
  unfold Int64.testbit. rewrite Int64.add_unsigned.
  fold (Int64.testbit (Int64.repr
        (Int64.unsigned (Int64.and n (Int64.repr 2047)) +
         Int64.unsigned (Int64.repr 2047))) i).
  rewrite Int64.testbit_repr by auto. f_equal. f_equal. unfold Int64.and.
  change (Int64.unsigned (Int64.repr 2047)) with 2047.
  change 2047 with (Z.ones 11). rewrite ! Z.land_ones by lia.
  rewrite Int64.unsigned_repr. apply eqmod_mod_eq.
  apply Z.lt_gt. apply (Zpower_gt_0 radix2); lia.
  apply eqmod_divides with (2^64). apply Int64.eqm_signed_unsigned.
  exists (2^(64-11)); auto.
  exploit (Z_mod_lt (Int64.unsigned n) (2^11)). compute; auto.
  assert (2^11 < Int64.max_unsigned) by (compute; auto). lia.
  apply Int64.same_bits_eqm; auto. exists (-1); auto.
  split. auto. assert (-2^64 < Int64.min_signed) by (compute; auto).
  assert (Int64.max_signed < 2^64) by (compute; auto).
  extlia.
Qed.

End Float32.

Global Opaque
  Float.zero Float.eq_dec Float.neg Float.abs Float.of_single Float.to_single
  Float.of_int Float.of_intu Float.of_long Float.of_longu
  Float.to_int Float.to_intu Float.to_long Float.to_longu
  Float.add Float.sub Float.mul Float.div Float.cmp Float.ordered
  Float.to_bits Float.of_bits Float.from_words.

Global Opaque
  Float32.zero Float32.eq_dec Float32.neg Float32.abs
  Float32.of_int Float32.of_intu Float32.of_long Float32.of_longu
  Float32.to_int Float32.to_intu Float32.to_long Float32.to_longu
  Float32.add Float32.sub Float32.mul Float32.div Float32.cmp Float32.ordered
  Float32.to_bits Float32.of_bits.

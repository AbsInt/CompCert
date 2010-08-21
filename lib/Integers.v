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

(** Formalizations of machine integers modulo $2^N$ #2<sup>N</sup>#. *)

Require Import Axioms.
Require Import Coqlib.

(** * Comparisons *)

Inductive comparison : Type :=
  | Ceq : comparison               (**r same *)
  | Cne : comparison               (**r different *)
  | Clt : comparison               (**r less than *)
  | Cle : comparison               (**r less than or equal *)
  | Cgt : comparison               (**r greater than *)
  | Cge : comparison.              (**r greater than or equal *)

Definition negate_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Cne
  | Cne => Ceq
  | Clt => Cge
  | Cle => Cgt
  | Cgt => Cle
  | Cge => Clt
  end.

Definition swap_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Ceq
  | Cne => Cne
  | Clt => Cgt
  | Cle => Cge
  | Cgt => Clt
  | Cge => Cle
  end.

(** * Parameterization by the word size, in bits. *)

Module Type WORDSIZE.
  Variable wordsize: nat.
  Axiom wordsize_not_zero: wordsize <> 0%nat.
End WORDSIZE.

Module Make(WS: WORDSIZE).

Definition wordsize: nat := WS.wordsize.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := modulus / 2.
Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Remark wordsize_pos:
  Z_of_nat wordsize > 0.
Proof.
  unfold wordsize. generalize WS.wordsize_not_zero. omega.
Qed.

Remark modulus_power:
  modulus = two_p (Z_of_nat wordsize).
Proof.
  unfold modulus. apply two_power_nat_two_p.
Qed.

Remark modulus_pos:
  modulus > 0.
Proof.
  rewrite modulus_power. apply two_p_gt_ZERO. generalize wordsize_pos; omega.
Qed.

(** * Representation of machine integers *)

(** A machine integer (type [int]) is represented as a Coq arbitrary-precision
  integer (type [Z]) plus a proof that it is in the range 0 (included) to
  [modulus] (excluded. *)

Record int: Type := mkint { intval: Z; intrange: 0 <= intval < modulus }.

(** The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed 
  respectively. *)

Definition unsigned (n: int) : Z := intval n.

Definition signed (n: int) : Z :=
  if zlt (unsigned n) half_modulus
  then unsigned n
  else unsigned n - modulus.

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

Definition repr (x: Z) : int := 
  mkint (Zmod x modulus) (Z_mod_lt x modulus modulus_pos).

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).
Definition iwordsize := repr (Z_of_nat wordsize).

Lemma mkint_eq:
  forall x y Px Py, x = y -> mkint x Px = mkint y Py.
Proof.
  intros. subst y. 
  generalize (proof_irr Px Py); intro.
  subst Py. reflexivity.
Qed.

Lemma eq_dec: forall (x y: int), {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y. case (zeq intval0 intval1); intro.
  left. apply mkint_eq. auto.
  right. red; intro. injection H. exact n.
Qed.

(** * Arithmetic and logical operations over machine integers *)

Definition eq (x y: int) : bool := 
  if zeq (unsigned x) (unsigned y) then true else false.
Definition lt (x y: int) : bool :=
  if zlt (signed x) (signed y) then true else false.
Definition ltu (x y: int) : bool :=
  if zlt (unsigned x) (unsigned y) then true else false.

Definition neg (x: int) : int := repr (- unsigned x).

Definition add (x y: int) : int :=
  repr (unsigned x + unsigned y).
Definition sub (x y: int) : int :=
  repr (unsigned x - unsigned y).
Definition mul (x y: int) : int :=
  repr (unsigned x * unsigned y).

(** [Zdiv_round] and [Zmod_round] implement signed division and modulus
  with round-towards-zero behavior. *)

Definition Zdiv_round (x y: Z) : Z :=
  if zlt x 0 then
    if zlt y 0 then (-x) / (-y) else - ((-x) / y)
  else
    if zlt y 0 then -(x / (-y)) else x / y.

Definition Zmod_round (x y: Z) : Z :=
  x - (Zdiv_round x y) * y.

Definition divs (x y: int) : int :=
  repr (Zdiv_round (signed x) (signed y)).
Definition mods (x y: int) : int :=
  repr (Zmod_round (signed x) (signed y)).

Definition divu (x y: int) : int :=
  repr (unsigned x / unsigned y).
Definition modu (x y: int) : int :=
  repr (Zmod (unsigned x) (unsigned y)).

(** For bitwise operations, we need to convert between Coq integers [Z]
  and their bit-level representations.  Bit-level representations are
  represented as characteristic functions, that is, functions [f]
  of type [nat -> bool] such that [f i] is the value of the [i]-th bit
  of the number.  For [i] less than 0 or greater or equal to [wordsize],
  the characteristic function is [false]. *)

Definition Z_shift_add (b: bool) (x: Z) :=
  if b then 2 * x + 1 else 2 * x.

Definition Z_bin_decomp (x: Z) : bool * Z :=
  match x with
  | Z0 => (false, 0)
  | Zpos p =>
      match p with
      | xI q => (true, Zpos q)
      | xO q => (false, Zpos q)
      | xH => (true, 0)
      end
  | Zneg p =>
      match p with
      | xI q => (true, Zneg q - 1)
      | xO q => (false, Zneg q)
      | xH => (true, -1)
      end
  end.

Fixpoint bits_of_Z (n: nat) (x: Z) {struct n}: Z -> bool :=
  match n with
  | O =>
      (fun i: Z => false)
  | S m =>
      let (b, y) := Z_bin_decomp x in
      let f := bits_of_Z m y in
      (fun i: Z => if zeq i 0 then b else f (i - 1))
  end.

Fixpoint Z_of_bits (n: nat) (f: Z -> bool) (i: Z) {struct n}: Z :=
  match n with
  | O => 0
  | S m => Z_shift_add (f i) (Z_of_bits m f (Zsucc i))
  end.

(** Bitwise logical "and", "or" and "xor" operations. *)

Definition bitwise_binop (f: bool -> bool -> bool) (x y: int) :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let fy := bits_of_Z wordsize (unsigned y) in
  repr(Z_of_bits wordsize (fun i => f (fx i) (fy i)) 0).

Definition and (x y: int): int := bitwise_binop andb x y.
Definition or (x y: int): int := bitwise_binop orb x y.
Definition xor (x y: int) : int := bitwise_binop xorb x y.

Definition not (x: int) : int := xor x mone.

(** Shifts and rotates. *)

Definition shl (x y: int): int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  repr (Z_of_bits wordsize fx (- unsigned y)).

Definition shru (x y: int): int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  repr (Z_of_bits wordsize fx (unsigned y)).

Definition shr (x y: int): int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let sx := fun i => fx (if zlt i (Z_of_nat wordsize) then i else Z_of_nat wordsize - 1) in
  repr (Z_of_bits wordsize sx (unsigned y)).

(** Viewed as signed divisions by powers of two, [shrx] rounds towards
  zero, while [shr] rounds towards minus infinity. *)

Definition shrx (x y: int): int :=
  divs x (shl one y).

Definition shr_carry (x y: int) :=
  sub (shrx x y) (shr x y).

Definition rol (x y: int) : int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let rx := fun i => fx (Zmod i (Z_of_nat wordsize)) in
  repr (Z_of_bits wordsize rx (-unsigned y)).

Definition ror (x y: int) : int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let rx := fun i => fx (Zmod i (Z_of_nat wordsize)) in
  repr (Z_of_bits wordsize rx (unsigned y)).

Definition rolm (x a m: int): int := and (rol x a) m.

(** Zero and sign extensions *)

Definition zero_ext (n: Z) (x: int) : int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  repr (Z_of_bits wordsize (fun i => if zlt i n then fx i else false) 0).

Definition sign_ext (n: Z) (x: int) : int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  repr (Z_of_bits wordsize (fun i => if zlt i n then fx i else fx (n - 1)) 0).

(** Decomposition of a number as a sum of powers of two. *)

Fixpoint Z_one_bits (n: nat) (x: Z) (i: Z) {struct n}: list Z :=
  match n with
  | O => nil
  | S m =>
      let (b, y) := Z_bin_decomp x in
      if b then i :: Z_one_bits m y (i+1) else Z_one_bits m y (i+1)
  end.

Definition one_bits (x: int) : list int :=
  List.map repr (Z_one_bits wordsize (unsigned x) 0).

(** Recognition of powers of two. *)

Definition is_power2 (x: int) : option int :=
  match Z_one_bits wordsize (unsigned x) 0 with
  | i :: nil => Some (repr i)
  | _ => None
  end.

(** Comparisons. *)

Definition cmp (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => lt x y
  | Cle => negb (lt y x)
  | Cgt => lt y x
  | Cge => negb (lt x y)
  end.

Definition cmpu (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => ltu x y
  | Cle => negb (ltu y x)
  | Cgt => ltu y x
  | Cge => negb (ltu x y)
  end.

Definition is_false (x: int) : Prop := x = zero.
Definition is_true  (x: int) : Prop := x <> zero.
Definition notbool  (x: int) : int  := if eq x zero then one else zero.

(** * Properties of integers and integer arithmetic *)

(** ** Properties of [modulus], [max_unsigned], etc. *)

Remark half_modulus_power:
  half_modulus = two_p (Z_of_nat wordsize - 1).
Proof.
  unfold half_modulus. rewrite modulus_power. 
  set (ws1 := Z_of_nat wordsize - 1). 
  replace (Z_of_nat wordsize) with (Zsucc ws1).
  rewrite two_p_S. rewrite Zmult_comm. apply Z_div_mult. omega.
  unfold ws1. generalize wordsize_pos; omega.
  unfold ws1. omega.
Qed.

Remark half_modulus_modulus: modulus = 2 * half_modulus.
Proof.
  rewrite half_modulus_power. rewrite modulus_power. 
  rewrite <- two_p_S. decEq. omega. 
  generalize wordsize_pos; omega.
Qed.

(** Relative positions, from greatest to smallest:
<<
      max_unsigned
      max_signed
      2*wordsize-1
      wordsize
      0
      min_signed
>>
*)

Remark half_modulus_pos: half_modulus > 0.
Proof.
  rewrite half_modulus_power. apply two_p_gt_ZERO. generalize wordsize_pos; omega.
Qed.

Remark min_signed_neg: min_signed < 0.
Proof.
  unfold min_signed. generalize half_modulus_pos. omega.
Qed.

Remark max_signed_pos: max_signed >= 0.
Proof.
  unfold max_signed. generalize half_modulus_pos. omega.
Qed.

Remark wordsize_max_unsigned: Z_of_nat wordsize <= max_unsigned.
Proof.
  assert (Z_of_nat wordsize < modulus).
    rewrite modulus_power. apply two_p_strict. 
    generalize wordsize_pos. omega. 
  unfold max_unsigned. omega.
Qed.

Remark two_wordsize_max_unsigned: 2 * Z_of_nat wordsize - 1 <= max_unsigned.
Proof.
  assert (2 * Z_of_nat wordsize - 1 < modulus).
    rewrite modulus_power. apply two_p_strict_2. generalize wordsize_pos; omega.
  unfold max_unsigned; omega.
Qed.

Remark max_signed_unsigned: max_signed < max_unsigned.
Proof.
  unfold max_signed, max_unsigned. rewrite half_modulus_modulus. 
  generalize half_modulus_pos. omega.
Qed.

(** ** Modulo arithmetic *)

(** We define and state properties of equality and arithmetic modulo a
  positive integer. *)

Section EQ_MODULO.

Variable modul: Z.
Hypothesis modul_pos: modul > 0.

Definition eqmod (x y: Z) : Prop := exists k, x = k * modul + y.

Lemma eqmod_refl: forall x, eqmod x x.
Proof.
  intros; red. exists 0. omega.
Qed.

Lemma eqmod_refl2: forall x y, x = y -> eqmod x y.
Proof.
  intros. subst y. apply eqmod_refl.
Qed.

Lemma eqmod_sym: forall x y, eqmod x y -> eqmod y x.
Proof.
  intros x y [k EQ]; red. exists (-k). subst x. ring.
Qed.

Lemma eqmod_trans: forall x y z, eqmod x y -> eqmod y z -> eqmod x z.
Proof.
  intros x y z [k1 EQ1] [k2 EQ2]; red.
  exists (k1 + k2). subst x; subst y. ring.
Qed.

Lemma eqmod_small_eq:
  forall x y, eqmod x y -> 0 <= x < modul -> 0 <= y < modul -> x = y.
Proof.
  intros x y [k EQ] I1 I2.
  generalize (Zdiv_unique _ _ _ _ EQ I2). intro.
  rewrite (Zdiv_small x modul I1) in H. subst k. omega.
Qed.

Lemma eqmod_mod_eq:
  forall x y, eqmod x y -> x mod modul = y mod modul.
Proof.
  intros x y [k EQ]. subst x. 
  rewrite Zplus_comm. apply Z_mod_plus. auto.
Qed.

Lemma eqmod_mod:
  forall x, eqmod x (x mod modul).
Proof.
  intros; red. exists (x / modul). 
  rewrite Zmult_comm. apply Z_div_mod_eq. auto.
Qed.

Lemma eqmod_add:
  forall a b c d, eqmod a b -> eqmod c d -> eqmod (a + c) (b + d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst c. exists (k1 + k2). ring.
Qed.

Lemma eqmod_neg:
  forall x y, eqmod x y -> eqmod (-x) (-y).
Proof.
  intros x y [k EQ]; red. exists (-k). rewrite EQ. ring. 
Qed.

Lemma eqmod_sub:
  forall a b c d, eqmod a b -> eqmod c d -> eqmod (a - c) (b - d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst c. exists (k1 - k2). ring.
Qed.

Lemma eqmod_mult:
  forall a b c d, eqmod a c -> eqmod b d -> eqmod (a * b) (c * d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst b.
  exists (k1 * k2 * modul + c * k2 + k1 * d).
  ring.
Qed.

End EQ_MODULO.

Lemma eqmod_divides:
  forall n m x y, eqmod n x y -> Zdivide m n -> eqmod m x y.
Proof.
  intros. destruct H as [k1 EQ1]. destruct H0 as [k2 EQ2]. 
  exists (k1*k2). rewrite <- Zmult_assoc. rewrite <- EQ2. auto.
Qed. 

(** We then specialize these definitions to equality modulo 
  $2^{wordsize}$ #2<sup>wordsize</sup>#. *)

Hint Resolve modulus_pos: ints.

Definition eqm := eqmod modulus.

Lemma eqm_refl: forall x, eqm x x.
Proof (eqmod_refl modulus).
Hint Resolve eqm_refl: ints.

Lemma eqm_refl2:
  forall x y, x = y -> eqm x y.
Proof (eqmod_refl2 modulus).
Hint Resolve eqm_refl2: ints.

Lemma eqm_sym: forall x y, eqm x y -> eqm y x.
Proof (eqmod_sym modulus).
Hint Resolve eqm_sym: ints.

Lemma eqm_trans: forall x y z, eqm x y -> eqm y z -> eqm x z.
Proof (eqmod_trans modulus).
Hint Resolve eqm_trans: ints.

Lemma eqm_small_eq:
  forall x y, eqm x y -> 0 <= x < modulus -> 0 <= y < modulus -> x = y.
Proof (eqmod_small_eq modulus).
Hint Resolve eqm_small_eq: ints.

Lemma eqm_add:
  forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof (eqmod_add modulus).
Hint Resolve eqm_add: ints.

Lemma eqm_neg:
  forall x y, eqm x y -> eqm (-x) (-y).
Proof (eqmod_neg modulus).
Hint Resolve eqm_neg: ints.

Lemma eqm_sub:
  forall a b c d, eqm a b -> eqm c d -> eqm (a - c) (b - d).
Proof (eqmod_sub modulus).
Hint Resolve eqm_sub: ints.

Lemma eqm_mult:
  forall a b c d, eqm a c -> eqm b d -> eqm (a * b) (c * d).
Proof (eqmod_mult modulus).
Hint Resolve eqm_mult: ints.

(** ** Properties of the coercions between [Z] and [int] *)

Lemma eqm_samerepr: forall x y, eqm x y -> repr x = repr y.
Proof.
  intros. unfold repr. apply mkint_eq. 
  apply eqmod_mod_eq. auto with ints. exact H.
Qed.

Lemma eqm_unsigned_repr:
  forall z, eqm z (unsigned (repr z)).
Proof.
  unfold eqm, repr, unsigned; intros; simpl. apply eqmod_mod. auto with ints.
Qed.
Hint Resolve eqm_unsigned_repr: ints.

Lemma eqm_unsigned_repr_l:
  forall a b, eqm a b -> eqm (unsigned (repr a)) b.
Proof.
  intros. apply eqm_trans with a. 
  apply eqm_sym. apply eqm_unsigned_repr. auto.
Qed.
Hint Resolve eqm_unsigned_repr_l: ints.

Lemma eqm_unsigned_repr_r:
  forall a b, eqm a b -> eqm a (unsigned (repr b)).
Proof.
  intros. apply eqm_trans with b. auto.
  apply eqm_unsigned_repr. 
Qed.
Hint Resolve eqm_unsigned_repr_r: ints.

Lemma eqm_signed_unsigned:
  forall x, eqm (signed x) (unsigned x).
Proof.
  intro; red; unfold signed. set (y := unsigned x).
  case (zlt y half_modulus); intro.
  apply eqmod_refl. red; exists (-1); ring. 
Qed.

Theorem unsigned_range:
  forall i, 0 <= unsigned i < modulus.
Proof.
  destruct i; auto.
Qed.
Hint Resolve unsigned_range: ints.

Theorem unsigned_range_2:
  forall i, 0 <= unsigned i <= max_unsigned.
Proof.
  intro; unfold max_unsigned. 
  generalize (unsigned_range i). omega.
Qed.
Hint Resolve unsigned_range_2: ints.

Theorem signed_range:
  forall i, min_signed <= signed i <= max_signed.
Proof.
  intros. unfold signed. 
  generalize (unsigned_range i). set (n := unsigned i). intros.
  case (zlt n half_modulus); intro.
  unfold max_signed. generalize min_signed_neg. omega.
  unfold min_signed, max_signed.
  rewrite half_modulus_modulus in *. omega. 
Qed.  

Theorem repr_unsigned:
  forall i, repr (unsigned i) = i.
Proof.
  destruct i; simpl. unfold repr. apply mkint_eq. apply Zmod_small; auto.
Qed.
Hint Resolve repr_unsigned: ints.

Lemma repr_signed:
  forall i, repr (signed i) = i.
Proof.
  intros. transitivity (repr (unsigned i)). 
  apply eqm_samerepr. apply eqm_signed_unsigned. auto with ints.
Qed.
Hint Resolve repr_signed: ints.

Lemma eqm_repr_eq: forall x y, eqm x (unsigned y) -> repr x = y.
Proof.
  intros. rewrite <- (repr_unsigned y). apply eqm_samerepr; auto.
Qed.

Theorem unsigned_repr:
  forall z, 0 <= z <= max_unsigned -> unsigned (repr z) = z.
Proof.
  intros. unfold repr, unsigned; simpl.
  apply Zmod_small. unfold max_unsigned in H. fold modulus. omega.
Qed.
Hint Resolve unsigned_repr: ints.

Theorem signed_repr:
  forall z, min_signed <= z <= max_signed -> signed (repr z) = z.
Proof.
  intros. unfold signed. case (zle 0 z); intro.
  replace (unsigned (repr z)) with z.
  rewrite zlt_true. auto. unfold max_signed in H. omega.
  symmetry. apply unsigned_repr. generalize max_signed_unsigned. omega. 
  pose (z' := z + modulus).
  replace (repr z) with (repr z').
  replace (unsigned (repr z')) with z'.
  rewrite zlt_false. unfold z'. omega.
  unfold z'. unfold min_signed in H.
  rewrite half_modulus_modulus. omega. 
  symmetry. apply unsigned_repr.
  unfold z', max_unsigned. unfold min_signed, max_signed in H.
  rewrite half_modulus_modulus. omega. 
  apply eqm_samerepr. unfold z'; red. exists 1. omega.
Qed.

Theorem signed_eq_unsigned:
  forall x, unsigned x <= max_signed -> signed x = unsigned x.
Proof.
  intros. unfold signed. destruct (zlt (unsigned x) half_modulus).
  auto. unfold max_signed in H. omegaContradiction.
Qed.

(** ** Properties of zero, one, minus one *)

Theorem unsigned_zero: unsigned zero = 0.
Proof.
  simpl. apply Zmod_0_l.
Qed.

Theorem unsigned_one: unsigned one = 1.
Proof.
  simpl. apply Zmod_small. split. omega. 
  unfold modulus. replace wordsize with (S(pred wordsize)). 
  rewrite two_power_nat_S. generalize (two_power_nat_pos (pred wordsize)). 
  omega.
  generalize wordsize_pos. omega. 
Qed.

Theorem unsigned_mone: unsigned mone = modulus - 1.
Proof.
  simpl unsigned. 
  replace (-1) with ((modulus - 1) + (-1) * modulus).
  rewrite Z_mod_plus_full. apply Zmod_small.
  generalize modulus_pos. omega. omega.
Qed.

Theorem signed_zero: signed zero = 0.
Proof.
  unfold signed. rewrite unsigned_zero. apply zlt_true. generalize half_modulus_pos; omega.
Qed.

Theorem signed_mone: signed mone = -1.
Proof.
  unfold signed. rewrite unsigned_mone.
  rewrite zlt_false. omega.
  rewrite half_modulus_modulus. generalize half_modulus_pos. omega.  
Qed.

Theorem one_not_zero: one <> zero.
Proof.
  assert (unsigned one <> unsigned zero). 
  rewrite unsigned_one; rewrite unsigned_zero; congruence.
  congruence.
Qed.

Theorem unsigned_repr_wordsize:
  unsigned iwordsize = Z_of_nat wordsize.
Proof.
  simpl. apply Zmod_small. 
  generalize wordsize_pos wordsize_max_unsigned; unfold max_unsigned; omega.
Qed.

(** ** Properties of equality *)

Theorem eq_sym:
  forall x y, eq x y = eq y x.
Proof.
  intros; unfold eq. case (zeq (unsigned x) (unsigned y)); intro.
  rewrite e. rewrite zeq_true. auto.
  rewrite zeq_false. auto. auto.
Qed.

Theorem eq_spec: forall (x y: int), if eq x y then x = y else x <> y.
Proof.
  intros; unfold eq. case (eq_dec x y); intro.
  subst y. rewrite zeq_true. auto.
  rewrite zeq_false. auto. 
  destruct x; destruct y.
  simpl. red; intro. elim n. apply mkint_eq. auto.
Qed.

Theorem eq_true: forall x, eq x x = true.
Proof.
  intros. generalize (eq_spec x x); case (eq x x); intros; congruence.
Qed.

Theorem eq_false: forall x y, x <> y -> eq x y = false.
Proof.
  intros. generalize (eq_spec x y); case (eq x y); intros; congruence.
Qed.

(** ** Properties of addition *)

Theorem add_unsigned: forall x y, add x y = repr (unsigned x + unsigned y).
Proof. intros; reflexivity.
Qed.

Theorem add_signed: forall x y, add x y = repr (signed x + signed y).
Proof. 
  intros. rewrite add_unsigned. apply eqm_samerepr.
  apply eqm_add; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof. intros; unfold add. decEq. omega. Qed.

Theorem add_zero: forall x, add x zero = x.
Proof.
  intros. unfold add. rewrite unsigned_zero.
  rewrite Zplus_0_r. apply repr_unsigned.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  intros; unfold add.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr. 
  apply eqm_trans with ((x' + y') + z').
  auto with ints.
  rewrite <- Zplus_assoc. auto with ints.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut. 
Qed.

Theorem add_neg_zero: forall x, add x (neg x) = zero.
Proof.
  intros; unfold add, neg, zero. apply eqm_samerepr.
  replace 0 with (unsigned x + (- (unsigned x))).
  auto with ints. omega.
Qed.

(** ** Properties of negation *)

Theorem neg_repr: forall z, neg (repr z) = repr (-z).
Proof.
  intros; unfold neg. apply eqm_samerepr. auto with ints.
Qed.

Theorem neg_zero: neg zero = zero.
Proof.
  unfold neg. rewrite unsigned_zero. auto. 
Qed.

Theorem neg_involutive: forall x, neg (neg x) = x.
Proof.
  intros; unfold neg.
  apply eqm_repr_eq. eapply eqm_trans. apply eqm_neg.
  apply eqm_unsigned_repr_l. apply eqm_refl. apply eqm_refl2. omega.
Qed. 

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  intros; unfold neg, add. apply eqm_samerepr.
  apply eqm_trans with (- (unsigned x + unsigned y)).
  auto with ints.
  replace (- (unsigned x + unsigned y))
     with ((- unsigned x) + (- unsigned y)).
  auto with ints. omega.
Qed.

(** ** Properties of subtraction *)

Theorem sub_zero_l: forall x, sub x zero = x.
Proof.
  intros; unfold sub. rewrite unsigned_zero. 
  replace (unsigned x - 0) with (unsigned x) by omega. apply repr_unsigned.
Qed.

Theorem sub_zero_r: forall x, sub zero x = neg x.
Proof.
  intros; unfold sub, neg. rewrite unsigned_zero. auto.
Qed.

Theorem sub_add_opp: forall x y, sub x y = add x (neg y).
Proof.
  intros; unfold sub, add, neg. apply eqm_samerepr.
  apply eqm_add; auto with ints.
Qed.

Theorem sub_idem: forall x, sub x x = zero.
Proof.
  intros; unfold sub. unfold zero. decEq. omega.
Qed.

Theorem sub_add_l: forall x y z, sub (add x y) z = add (sub x z) y.
Proof.
  intros. repeat rewrite sub_add_opp. 
  repeat rewrite add_assoc. decEq. apply add_commut.
Qed.

Theorem sub_add_r: forall x y z, sub x (add y z) = add (sub x z) (neg y).
Proof.
  intros. repeat rewrite sub_add_opp.
  rewrite neg_add_distr. rewrite add_permut. apply add_commut.
Qed.

Theorem sub_shifted:
  forall x y z,
  sub (add x z) (add y z) = sub x y.
Proof.
  intros. rewrite sub_add_opp. rewrite neg_add_distr.
  rewrite add_assoc. 
  rewrite (add_commut (neg y) (neg z)).
  rewrite <- (add_assoc z). rewrite add_neg_zero.
  rewrite (add_commut zero). rewrite add_zero.
  symmetry. apply sub_add_opp.
Qed.

Theorem sub_signed:
  forall x y, sub x y = repr (signed x - signed y).
Proof.
  intros. unfold sub. apply eqm_samerepr.
  apply eqm_sub; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

(** ** Properties of multiplication *)

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  intros; unfold mul. decEq. ring. 
Qed.

Theorem mul_zero: forall x, mul x zero = zero.
Proof.
  intros; unfold mul. rewrite unsigned_zero. 
  unfold zero. decEq. ring.
Qed.

Theorem mul_one: forall x, mul x one = x.
Proof.
  intros; unfold mul. rewrite unsigned_one.
  transitivity (repr (unsigned x)). decEq. ring.
  apply repr_unsigned.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  intros; unfold mul.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr. apply eqm_trans with ((x' * y') * z').
  auto with ints.
  rewrite <- Zmult_assoc. auto with ints.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  intros; unfold mul, add.
  apply eqm_samerepr.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_trans with ((x' + y') * z').
  auto with ints.
  replace ((x' + y') * z') with (x' * z' + y' * z').
  auto with ints.
  ring.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  intros. rewrite mul_commut. rewrite mul_add_distr_l. 
  decEq; apply mul_commut.
Qed. 

Theorem neg_mul_distr_l: 
  forall x y, neg(mul x y) = mul (neg x) y.
Proof.
  intros. unfold mul, neg.
  set (x' := unsigned x).  set (y' := unsigned y).
  apply eqm_samerepr. apply eqm_trans with (- (x' * y')).
  auto with ints.
  replace (- (x' * y')) with ((-x') * y') by ring.
  auto with ints.
Qed.

Theorem neg_mul_distr_r:
   forall x y, neg(mul x y) = mul x (neg y).
Proof.
  intros. rewrite (mul_commut x y). rewrite (mul_commut x (neg y)).
  apply neg_mul_distr_l. 
Qed.

Theorem mul_signed:
  forall x y, mul x y = repr (signed x * signed y).
Proof.
  intros; unfold mul. apply eqm_samerepr.
  apply eqm_mult; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

(** ** Properties of division and modulus *)

Lemma modu_divu_Euclid:
  forall x y, y <> zero -> x = add (mul (divu x y) y) (modu x y).
Proof.
  intros. unfold add, mul, divu, modu.
  transitivity (repr (unsigned x)). auto with ints. 
  apply eqm_samerepr. 
  set (x' := unsigned x). set (y' := unsigned y).
  apply eqm_trans with ((x' / y') * y' + x' mod y').
  apply eqm_refl2. rewrite Zmult_comm. apply Z_div_mod_eq.
  generalize (unsigned_range y); intro.
  assert (unsigned y <> 0). red; intro. 
  elim H. rewrite <- (repr_unsigned y). unfold zero. congruence.
  unfold y'. omega.
  auto with ints.
Qed.

Theorem modu_divu:
  forall x y, y <> zero -> modu x y = sub x (mul (divu x y) y).
Proof.
  intros. 
  assert (forall a b c, a = add b c -> c = sub a b).
  intros. subst a. rewrite sub_add_l. rewrite sub_idem.
  rewrite add_commut. rewrite add_zero. auto.
  apply H0. apply modu_divu_Euclid. auto.
Qed.

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
Proof.
  intros; unfold mods, sub, mul, divs.
  apply eqm_samerepr.
  unfold Zmod_round.
  apply eqm_sub. apply eqm_signed_unsigned. 
  apply eqm_unsigned_repr_r. 
  apply eqm_mult. auto with ints. apply eqm_signed_unsigned.
Qed.

(** ** Properties of binary decompositions *)

Lemma Z_shift_add_bin_decomp:
  forall x,
  Z_shift_add (fst (Z_bin_decomp x)) (snd (Z_bin_decomp x)) = x.
Proof.
  destruct x; simpl.
  auto.
  destruct p; reflexivity.
  destruct p; try reflexivity. simpl. 
  assert (forall z, 2 * (z + 1) - 1 = 2 * z + 1). intro; omega.
  generalize (H (Zpos p)); simpl. congruence.
Qed.

Lemma Z_bin_decomp_shift_add:
  forall b x, Z_bin_decomp (Z_shift_add b x) = (b, x).
Proof.
  intros.
  intros. unfold Z_shift_add. destruct b; destruct x; simpl; auto.
  destruct p; simpl; auto. f_equal. f_equal. 
  rewrite <- Pplus_one_succ_r. apply Psucc_o_double_minus_one_eq_xO.
Qed.

Lemma Z_shift_add_inj:
  forall b1 x1 b2 x2,
  Z_shift_add b1 x1 = Z_shift_add b2 x2 -> b1 = b2 /\ x1 = x2.
Proof.
  intros. 
  assert ((b1, x1) = (b2, x2)).
    repeat rewrite <- Z_bin_decomp_shift_add. rewrite H; auto. 
  split; congruence.
Qed.

Lemma Z_of_bits_exten:
  forall f1 f2 n i1 i2,
  (forall i, 0 <= i < Z_of_nat n -> f1 (i + i1) = f2 (i + i2)) ->
  Z_of_bits n f1 i1 = Z_of_bits n f2 i2.
Proof.
  induction n; intros; simpl.
  auto.
  rewrite inj_S in H. decEq. apply (H 0). omega. 
  apply IHn. intros. 
  replace (i + Zsucc i1) with (Zsucc i + i1) by omega.
  replace (i + Zsucc i2) with (Zsucc i + i2) by omega.
  apply H. omega.
Qed.

Lemma Z_of_bits_of_Z:
  forall x, eqm (Z_of_bits wordsize (bits_of_Z wordsize x) 0) x.
Proof.
  assert (forall n x, exists k,
    Z_of_bits n (bits_of_Z n x) 0 = k * two_power_nat n + x).
  induction n; intros; simpl.
  rewrite two_power_nat_O. exists (-x). omega.
  rewrite two_power_nat_S. simpl bits_of_Z. caseEq (Z_bin_decomp x). intros b y ZBD.
  rewrite zeq_true. destruct (IHn y) as [k EQ]. 
  replace (Z_of_bits n (fun i => if zeq i 0 then b else bits_of_Z n y (i - 1)) 1)
     with (Z_of_bits n (bits_of_Z n y) 0).
  rewrite EQ. exists k. 
  rewrite <- (Z_shift_add_bin_decomp x). rewrite ZBD. simpl fst; simpl snd.
  unfold Z_shift_add; destruct b; ring.
  apply Z_of_bits_exten. intros.
  rewrite zeq_false. decEq. omega. omega. 
  intro. exact (H wordsize x).
Qed.

Lemma bits_of_Z_zero:
  forall n x, bits_of_Z n 0 x = false.
Proof.
  induction n; simpl; intros. auto. case (zeq x 0); intro. auto. auto.
Qed.

Remark Z_bin_decomp_2xm1:
  forall x, Z_bin_decomp (2 * x - 1) = (true, x - 1).
Proof.
  intros. caseEq (Z_bin_decomp (2 * x - 1)). intros b y EQ.
  generalize (Z_shift_add_bin_decomp (2 * x - 1)).
  rewrite EQ; simpl fst; simpl snd. 
  replace (2 * x - 1) with (Z_shift_add true (x - 1)).
  intro. elim (Z_shift_add_inj _ _ _ _ H); intros.
  congruence. unfold Z_shift_add. omega.
Qed.

Lemma bits_of_Z_two_p:
  forall n x i,
  x >= 0 -> 0 <= i < Z_of_nat n ->
  bits_of_Z n (two_p x - 1) i = zlt i x.
Proof.
  induction n; intros.
  simpl in H0. omegaContradiction.
  destruct (zeq x 0). subst x. change (two_p 0 - 1) with 0. rewrite bits_of_Z_zero.
  unfold proj_sumbool; rewrite zlt_false. auto. omega.
  simpl. replace (two_p x) with (2 * two_p (x - 1)). rewrite Z_bin_decomp_2xm1. 
  destruct (zeq i 0). subst. unfold proj_sumbool. rewrite zlt_true. auto. omega.
  rewrite inj_S in H0. rewrite IHn. unfold proj_sumbool. destruct (zlt i x).
  apply zlt_true. omega.
  apply zlt_false. omega.
  omega. omega. rewrite <- two_p_S. decEq. omega. omega.
Qed.

Lemma bits_of_Z_mone:
  forall x,
  0 <= x < Z_of_nat wordsize ->
  bits_of_Z wordsize (modulus - 1) x = true.
Proof.
  intros. unfold modulus. rewrite two_power_nat_two_p. 
  rewrite bits_of_Z_two_p. unfold proj_sumbool. apply zlt_true; omega.
  omega. omega.
Qed.

Lemma Z_of_bits_range:
  forall f n i, 0 <= Z_of_bits n f i < two_power_nat n.
Proof.
  induction n; simpl; intros.
  rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S.
  generalize (IHn (Zsucc i)).
  intro. destruct (f i); unfold Z_shift_add; omega.
Qed.

Lemma Z_of_bits_range_1:
  forall f i, 0 <= Z_of_bits wordsize f i < modulus.
Proof.
  intros. apply Z_of_bits_range. 
Qed.
Hint Resolve Z_of_bits_range_1: ints.

Lemma Z_of_bits_range_2:
  forall f i, 0 <= Z_of_bits wordsize f i <= max_unsigned.
Proof.
  intros. unfold max_unsigned.
  generalize (Z_of_bits_range_1 f i). omega.
Qed.
Hint Resolve Z_of_bits_range_2: ints.

Lemma bits_of_Z_of_bits_gen:
  forall n f i j,
  0 <= i < Z_of_nat n ->
  bits_of_Z n (Z_of_bits n f j) i = f (i + j).
Proof.
  induction n; intros; simpl.
  simpl in H. omegaContradiction.
  rewrite Z_bin_decomp_shift_add.
  destruct (zeq i 0).
  f_equal. omega.
  rewrite IHn. f_equal. omega. 
  rewrite inj_S in H. omega.
Qed.  

Lemma bits_of_Z_of_bits:
  forall n f i,
  0 <= i < Z_of_nat n ->
  bits_of_Z n (Z_of_bits n f 0) i = f i.
Proof.
  intros. rewrite bits_of_Z_of_bits_gen; auto. decEq; omega.
Qed.  

Lemma bits_of_Z_below:
  forall n x i, i < 0 -> bits_of_Z n x i = false.
Proof.
  induction n; intros; simpl. auto.
  destruct (Z_bin_decomp x). rewrite zeq_false. apply IHn.
  omega. omega.
Qed.

Lemma bits_of_Z_above:
  forall n x i, i >= Z_of_nat n -> bits_of_Z n x i = false.
Proof.
  induction n; intros; simpl.
  auto.
  caseEq (Z_bin_decomp x); intros b x1 EQ. rewrite zeq_false.
  rewrite IHn. 
  destruct x; simpl in EQ. inv EQ. auto. 
  destruct p; inv EQ; auto.
  destruct p; inv EQ; auto. 
  rewrite inj_S in H. omega. rewrite inj_S in H. omega.
Qed.

Lemma bits_of_Z_of_bits_gen':
  forall n f i j,
  bits_of_Z n (Z_of_bits n f j) i =
  if zlt i 0 then false 
  else if zle (Z_of_nat n) i then false
  else f (i + j).
Proof.
  intros. 
  destruct (zlt i 0). apply bits_of_Z_below; auto.
  destruct (zle (Z_of_nat n) i). apply bits_of_Z_above. omega.
  apply bits_of_Z_of_bits_gen. omega.
Qed. 

Lemma Z_of_bits_excl:
  forall n f g h j,
  (forall i, j <= i < j + Z_of_nat n -> f i && g i = false) ->
  (forall i, j <= i < j + Z_of_nat n -> f i || g i = h i) ->
  Z_of_bits n f j + Z_of_bits n g j = Z_of_bits n h j.
Proof.
  induction n.
  intros; reflexivity.
  intros. simpl. rewrite inj_S in H. rewrite inj_S in H0.
  rewrite <- (IHn f g h (Zsucc j)). 
  assert (j <= j < j + Zsucc(Z_of_nat n)). omega.
  unfold Z_shift_add.
  rewrite <- H0; auto.
  caseEq (f j); intros; caseEq (g j); intros; simpl orb.
  generalize (H j H1). rewrite H2; rewrite H3. simpl andb; congruence.
  omega. omega. omega.
  intros; apply H. omega.
  intros; apply H0. omega.
Qed.

Lemma Z_of_bits_compose:
  forall f m n i,
  Z_of_bits (m + n) f i =
     Z_of_bits n f (i + Z_of_nat m) * two_power_nat m
   + Z_of_bits m f i.
Proof.
  induction m; intros.
  simpl. repeat rewrite Zplus_0_r. rewrite two_power_nat_O. omega.
  rewrite inj_S. rewrite two_power_nat_S. simpl Z_of_bits. 
  rewrite IHm. replace (i + Zsucc (Z_of_nat m)) with (Zsucc i + Z_of_nat m) by omega.
  unfold Z_shift_add. destruct (f i); ring. 
Qed.

Lemma Z_of_bits_truncate:
  forall f n i,
  eqm (Z_of_bits (wordsize + n) f i) (Z_of_bits wordsize f i).
Proof.
  intros. exists (Z_of_bits n f (i + Z_of_nat wordsize)). 
  rewrite Z_of_bits_compose. fold modulus. auto.
Qed.

Lemma Z_of_bits_false:
  forall f n i,
  (forall j, i <= j < i + Z_of_nat n -> f j = false) ->
  Z_of_bits n f i = 0.
Proof.
  induction n; intros; simpl. auto.
  rewrite inj_S in H. rewrite H. rewrite IHn. auto. 
  intros; apply H; omega. omega.
Qed.

Lemma Z_of_bits_true:
  forall f n i,
  (forall j, i <= j < i + Z_of_nat n -> f j = true) ->
  Z_of_bits n f i = two_power_nat n - 1.
Proof.
  induction n; intros.
  simpl. auto.
  rewrite two_power_nat_S. simpl Z_of_bits. rewrite inj_S in H.
  rewrite H. rewrite IHn. unfold Z_shift_add. omega.  
  intros; apply H. omega. omega.
Qed.

(** ** Properties of bitwise and, or, xor *)

Lemma bitwise_binop_commut:
  forall f,
  (forall a b, f a b = f b a) ->
  forall x y,
  bitwise_binop f x y = bitwise_binop f y x.
Proof.
  unfold bitwise_binop; intros. decEq; apply Z_of_bits_exten; intros. auto.
Qed.

Lemma bitwise_binop_assoc:
  forall f,
  (forall a b c, f a (f b c) = f (f a b) c) ->
  forall x y z,
  bitwise_binop f (bitwise_binop f x y) z =
  bitwise_binop f x (bitwise_binop f y z).
Proof.
  unfold bitwise_binop; intros. repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros.  
  repeat rewrite Zplus_0_r. repeat rewrite bits_of_Z_of_bits; auto.
Qed.

Lemma bitwise_binop_idem:
  forall f,
  (forall a, f a a = a) ->
  forall x,
  bitwise_binop f x x = x.
Proof.
  unfold bitwise_binop; intros.
  apply eqm_repr_eq. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten. auto. 
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof (bitwise_binop_commut andb andb_comm).

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof (bitwise_binop_assoc andb andb_assoc).

Theorem and_zero: forall x, and x zero = zero.
Proof.
  intros. unfold and, bitwise_binop.
  apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_zero. rewrite bits_of_Z_zero. apply andb_b_false.
Qed.

Theorem and_mone: forall x, and x mone = x.
Proof.
  intros. unfold and, bitwise_binop.
  apply eqm_repr_eq. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten; intros.
  rewrite unsigned_mone. rewrite bits_of_Z_mone. apply andb_b_true.
  omega.
Qed.

Theorem and_idem: forall x, and x x = x.
Proof.
  intros. apply (bitwise_binop_idem andb). destruct a; auto.
Qed.

Theorem add_and:
  forall x y z,
  and y z = zero ->
  add (and x y) (and x z) = and x (or y z).
Proof.
  intros. unfold add, and, bitwise_binop.
  repeat rewrite unsigned_repr; auto with ints. decEq.
  apply Z_of_bits_excl; intros.
  assert (forall a b c, a && b && (a && c) = a && (b && c)).
    destruct a; destruct b; destruct c; reflexivity.
  rewrite H1. 
  replace (bits_of_Z wordsize (unsigned y) i &&
           bits_of_Z wordsize (unsigned z) i)
     with (bits_of_Z wordsize (unsigned (and y z)) i).
  rewrite H. rewrite unsigned_zero.  
  rewrite bits_of_Z_zero. apply andb_b_false.
  unfold and, bitwise_binop. rewrite unsigned_repr; auto with ints. 
  rewrite bits_of_Z_of_bits. reflexivity. auto. 
  rewrite <- demorgan1.
  unfold or, bitwise_binop. rewrite unsigned_repr; auto with ints.
  rewrite bits_of_Z_of_bits; auto.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof (bitwise_binop_commut orb orb_comm).

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof (bitwise_binop_assoc orb orb_assoc).

Theorem or_zero: forall x, or x zero = x.
Proof.
  intros. unfold or, bitwise_binop. 
  apply eqm_repr_eq. eapply eqm_trans. 2: apply Z_of_bits_of_Z.
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_zero. rewrite bits_of_Z_zero. apply orb_b_false. 
Qed.

Theorem or_mone: forall x, or x mone = mone.
Proof.
  intros. unfold or, bitwise_binop.
  apply eqm_repr_eq. eapply eqm_trans. 2: apply Z_of_bits_of_Z.
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_mone. rewrite bits_of_Z_mone. apply orb_b_true. 
  omega.
Qed.

Theorem or_idem: forall x, or x x = x.
Proof.
  intros. apply (bitwise_binop_idem orb). destruct a; auto.
Qed.

Theorem and_or_distrib:
  forall x y z,
  and x (or y z) = or (and x y) (and x z).
Proof.
  intros; unfold and, or, bitwise_binop.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; repeat rewrite Zplus_0_r; auto.
  apply demorgan1.
Qed.  

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof (bitwise_binop_commut xorb xorb_comm).

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  intros. apply (bitwise_binop_assoc xorb).
  intros. symmetry. apply xorb_assoc.
Qed.

Theorem xor_zero: forall x, xor x zero = x.
Proof.
  intros. unfold xor, bitwise_binop.
  apply eqm_repr_eq. eapply eqm_trans. 2: apply Z_of_bits_of_Z.
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_zero. rewrite bits_of_Z_zero. apply xorb_false. 
Qed.

Theorem xor_idem: forall x, xor x x = zero.
Proof.
  intros. unfold xor, bitwise_binop.
  apply eqm_repr_eq. eapply eqm_trans. 2: apply Z_of_bits_of_Z.
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_zero. rewrite bits_of_Z_zero. apply xorb_nilpotent. 
Qed.

Theorem xor_zero_one: xor zero one = one.
Proof. rewrite xor_commut. apply xor_zero. Qed.

Theorem xor_one_one: xor one one = zero.
Proof. apply xor_idem. Qed.

Theorem and_xor_distrib:
  forall x y z,
  and x (xor y z) = xor (and x y) (and x z).
Proof.
  intros; unfold and, xor, bitwise_binop.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; repeat rewrite Zplus_0_r; auto.
  assert (forall a b c, a && (xorb b c) = xorb (a && b) (a && c)).
    destruct a; destruct b; destruct c; reflexivity.
  auto.
Qed.  

Theorem not_involutive:
  forall (x: int), not (not x) = x.
Proof.
  intros. unfold not. rewrite xor_assoc. rewrite xor_idem. apply xor_zero. 
Qed.

(** ** Properties of shifts *)

Theorem shl_zero: forall x, shl x zero = x.
Proof.
  intros. unfold shl. rewrite unsigned_zero. simpl (-0).
  transitivity (repr (unsigned x)). apply eqm_samerepr. apply Z_of_bits_of_Z. 
  auto with ints.
Qed.

Lemma bitwise_binop_shl:
  forall f x y n,
  f false false = false ->
  bitwise_binop f (shl x n) (shl y n) = shl (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, shl.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros.
  repeat rewrite Zplus_0_r.
  destruct (zlt (i + -unsigned n) 0).
  rewrite bits_of_Z_of_bits_gen; auto.
  rewrite bits_of_Z_of_bits_gen; auto.
  repeat rewrite bits_of_Z_below; auto.
  repeat rewrite bits_of_Z_of_bits_gen; auto. repeat rewrite Zplus_0_r. auto. 
  generalize (unsigned_range n). omega.
Qed.

Theorem and_shl:
  forall x y n,
  and (shl x n) (shl y n) = shl (and x y) n.
Proof.
  unfold and; intros. apply bitwise_binop_shl. reflexivity.
Qed.

Theorem or_shl:
  forall x y n,
  or (shl x n) (shl y n) = shl (or x y) n.
Proof.
  unfold or; intros. apply bitwise_binop_shl. reflexivity.
Qed.

Theorem xor_shl:
  forall x y n,
  xor (shl x n) (shl y n) = shl (xor x y) n.
Proof.
  unfold xor; intros. apply bitwise_binop_shl. reflexivity.
Qed.

Lemma ltu_inv:
  forall x y, ltu x y = true -> 0 <= unsigned x < unsigned y.
Proof.
  unfold ltu; intros. destruct (zlt (unsigned x) (unsigned y)).
  split; auto. generalize (unsigned_range x); omega.
  discriminate.
Qed.

Theorem shl_shl:
  forall x y z,
  ltu y iwordsize = true -> 
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shl (shl x y) z = shl x (add y z).
Proof.
  intros. unfold shl, add.
  generalize (ltu_inv _ _ H). 
  generalize (ltu_inv _ _ H0).
  rewrite unsigned_repr_wordsize.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  intros.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros n R.
  rewrite bits_of_Z_of_bits_gen'. 
  destruct (zlt (n + - z') 0).
  symmetry. apply bits_of_Z_below. omega.
  destruct (zle (Z_of_nat wordsize) (n + - z')).
  symmetry. apply bits_of_Z_below. omega.
  decEq. omega.
  generalize two_wordsize_max_unsigned; omega.
Qed.

Theorem shru_zero: forall x, shru x zero = x.
Proof.
  intros. unfold shru. rewrite unsigned_zero.
  transitivity (repr (unsigned x)). apply eqm_samerepr. apply Z_of_bits_of_Z. 
  auto with ints.
Qed.

Lemma bitwise_binop_shru:
  forall f x y n,
  f false false = false ->
  bitwise_binop f (shru x n) (shru y n) = shru (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, shru.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros.
  repeat rewrite Zplus_0_r.
  rewrite bits_of_Z_of_bits_gen; auto.
  rewrite bits_of_Z_of_bits_gen; auto.
  destruct (zlt (i + unsigned n) (Z_of_nat wordsize)).
  rewrite bits_of_Z_of_bits. auto. generalize (unsigned_range n); omega.
  repeat rewrite bits_of_Z_above; auto.
Qed.

Theorem and_shru:
  forall x y n,
  and (shru x n) (shru y n) = shru (and x y) n.
Proof.
  unfold and; intros. apply bitwise_binop_shru. reflexivity.
Qed.

Theorem or_shru:
  forall x y n,
  or (shru x n) (shru y n) = shru (or x y) n.
Proof.
  unfold or; intros. apply bitwise_binop_shru. reflexivity.
Qed.

Theorem xor_shru:
  forall x y n,
  xor (shru x n) (shru y n) = shru (xor x y) n.
Proof.
  unfold xor; intros. apply bitwise_binop_shru. reflexivity.
Qed.

Theorem shru_shru:
  forall x y z,
  ltu y iwordsize = true -> 
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shru (shru x y) z = shru x (add y z).
Proof.
  intros. unfold shru, add.
  generalize (ltu_inv _ _ H). 
  generalize (ltu_inv _ _ H0).
  rewrite unsigned_repr_wordsize.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  intros. repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten. intros n R.
  rewrite bits_of_Z_of_bits_gen'. 
  destruct (zlt (n + z') 0). omegaContradiction.
  destruct (zle (Z_of_nat wordsize) (n + z')).
  symmetry. apply bits_of_Z_above. omega.
  decEq. omega.
  generalize two_wordsize_max_unsigned; omega.
Qed.

Theorem shr_zero: forall x, shr x zero = x.
Proof.
  intros. unfold shr. rewrite unsigned_zero.
  transitivity (repr (unsigned x)). apply eqm_samerepr.
  eapply eqm_trans. 2: apply Z_of_bits_of_Z.
  apply eqm_refl2. apply Z_of_bits_exten; intros. 
  rewrite zlt_true. auto. omega. 
  auto with ints.
Qed.

Lemma bitwise_binop_shr:
  forall f x y n,
  bitwise_binop f (shr x n) (shr y n) = shr (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, shr.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits_gen; repeat rewrite Zplus_0_r; auto.
  generalize (unsigned_range n); intro.
  destruct (zlt (i + unsigned n) (Z_of_nat wordsize)); omega. 
Qed.

Theorem and_shr:
  forall x y n,
  and (shr x n) (shr y n) = shr (and x y) n.
Proof.
  unfold and; intros. apply bitwise_binop_shr.
Qed.

Theorem or_shr:
  forall x y n,
  or (shr x n) (shr y n) = shr (or x y) n.
Proof.
  unfold or; intros. apply bitwise_binop_shr.
Qed.

Theorem xor_shr:
  forall x y n,
  xor (shr x n) (shr y n) = shr (xor x y) n.
Proof.
  unfold xor; intros. apply bitwise_binop_shr. 
Qed.

Theorem shr_shr:
  forall x y z,
  ltu y iwordsize = true -> 
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shr (shr x y) z = shr x (add y z).
Proof.
  intros. unfold shr, add.
  generalize (ltu_inv _ _ H). 
  generalize (ltu_inv _ _ H0).
  rewrite unsigned_repr_wordsize.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  intros. repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros n R.
  destruct (zlt (n + z') (Z_of_nat wordsize)).
  rewrite bits_of_Z_of_bits_gen.
  rewrite (Zplus_comm y' z'). rewrite Zplus_assoc. auto.
  omega.
  rewrite bits_of_Z_of_bits_gen. 
  decEq. symmetry. rewrite zlt_false. 
  destruct (zeq y' 0). rewrite zlt_true; omega. rewrite zlt_false; omega. 
  omega. omega. 
  generalize two_wordsize_max_unsigned; omega.
Qed.

Remark two_p_m1_range:
  forall n,
  0 <= n <= Z_of_nat wordsize ->
  0 <= two_p n - 1 <= max_unsigned.
Proof.
  intros. split. 
  assert (two_p n > 0). apply two_p_gt_ZERO. omega. omega.
  assert (two_p n <= two_p (Z_of_nat wordsize)). apply two_p_monotone. auto. 
  unfold max_unsigned. unfold modulus. rewrite two_power_nat_two_p. omega.
Qed.

Theorem shru_shl_and:
  forall x y,
  ltu y iwordsize = true ->
  shru (shl x y) y = and x (repr (two_p (Z_of_nat wordsize - unsigned y) - 1)).
Proof.
  intros. exploit ltu_inv; eauto. rewrite unsigned_repr_wordsize. intros.
  unfold and, bitwise_binop, shl, shru.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros. rewrite Zplus_0_r. 
  rewrite bits_of_Z_two_p.
  destruct (zlt (i + unsigned y) (Z_of_nat wordsize)).
  rewrite bits_of_Z_of_bits_gen. unfold proj_sumbool. rewrite zlt_true. 
  rewrite andb_true_r. f_equal. omega. 
  omega. omega. 
  rewrite bits_of_Z_above. unfold proj_sumbool. rewrite zlt_false. rewrite andb_false_r; auto. 
  omega. omega. omega. auto. 
  apply two_p_m1_range. omega. 
Qed.

(** ** Properties of rotations *)

Theorem shl_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shl x n = rolm x n (shl mone n).
Proof.
  intros. exploit ltu_inv; eauto. rewrite unsigned_repr_wordsize; intros.
  unfold shl, rolm, rol, and, bitwise_binop.
  repeat rewrite unsigned_repr; auto with ints. 
  decEq; apply Z_of_bits_exten; intros. rewrite Zplus_0_r. 
  repeat rewrite bits_of_Z_of_bits_gen; auto.
  destruct (zlt i (unsigned n)).
  assert (i + - unsigned n < 0). omega.
  rewrite (bits_of_Z_below wordsize (unsigned x) _ H2).
  rewrite (bits_of_Z_below wordsize (unsigned mone) _ H2).
  symmetry. apply andb_b_false. 
  assert (0 <= i + - unsigned n < Z_of_nat wordsize).
    generalize (unsigned_range n). omega.
  rewrite unsigned_mone. 
  rewrite bits_of_Z_mone; auto. rewrite andb_b_true. decEq.
  rewrite Zmod_small. omega. omega.
Qed.

Theorem shru_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shru x n = rolm x (sub iwordsize n) (shru mone n).
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize. intro. 
  unfold shru, rolm, rol, and, bitwise_binop.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros. rewrite Zplus_0_r.
  repeat rewrite bits_of_Z_of_bits_gen; auto. 
  unfold sub. rewrite unsigned_repr_wordsize. 
  rewrite unsigned_repr. 
  case (zlt (i + unsigned n) (Z_of_nat wordsize)); intro LT2.
  rewrite unsigned_mone. rewrite bits_of_Z_mone. rewrite andb_b_true.
  decEq. 
  replace (i + - (Z_of_nat wordsize - unsigned n))
     with ((i + unsigned n) + (-1) * Z_of_nat wordsize) by omega.
  rewrite Z_mod_plus. symmetry. apply Zmod_small.
  generalize (unsigned_range n). omega. omega. omega.
  rewrite (bits_of_Z_above wordsize (unsigned x) _ LT2).
  rewrite (bits_of_Z_above wordsize (unsigned mone) _ LT2).
  symmetry. apply andb_b_false.
  split. omega. apply Zle_trans with (Z_of_nat wordsize).
  generalize (unsigned_range n); omega. apply wordsize_max_unsigned.
Qed.

Theorem rol_zero:
  forall x,
  rol x zero = x.
Proof.
  intros. transitivity (repr (unsigned x)). 
  unfold rol. apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten; intros. decEq. rewrite unsigned_zero. 
  replace (i + - 0) with (i + 0) by omega. apply Zmod_small. omega.
  apply repr_unsigned.
Qed.

Lemma bitwise_binop_rol:
  forall f x y n,
  bitwise_binop f (rol x n) (rol y n) = rol (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, rol.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits_gen.
  repeat rewrite Zplus_0_r. auto.
  apply Z_mod_lt. generalize wordsize_pos; omega.
  omega. omega.
Qed.

Theorem rol_and:
  forall x y n,
  rol (and x y) n = and (rol x n) (rol y n).
Proof.
  intros. symmetry. unfold and. apply bitwise_binop_rol.
Qed.

Theorem rol_or:
  forall x y n,
  rol (or x y) n = or (rol x n) (rol y n).
Proof.
  intros. symmetry. unfold or. apply bitwise_binop_rol.
Qed.

Theorem rol_xor:
  forall x y n,
  rol (xor x y) n = xor (rol x n) (rol y n).
Proof.
  intros. symmetry. unfold xor. apply bitwise_binop_rol.
Qed.

Theorem rol_rol:
  forall x n m,
  Zdivide (Z_of_nat wordsize) modulus ->
  rol (rol x n) m = rol x (modu (add n m) iwordsize).
Proof.
  intros. unfold rol. 
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; repeat rewrite Zplus_0_r; auto.
  rewrite bits_of_Z_of_bits_gen. decEq. 
  unfold modu, add. 
  set (W := Z_of_nat wordsize).
  set (M := unsigned m); set (N := unsigned n).
  assert (W > 0). unfold W; generalize wordsize_pos; omega.
  assert (forall a, eqmod W a (unsigned (repr a))).
    intros. eapply eqmod_divides. apply eqm_unsigned_repr. assumption.
  apply eqmod_mod_eq. auto.
  replace (unsigned iwordsize) with W.
  apply eqmod_trans with (i - (N + M) mod W).
  apply eqmod_trans with ((i - M) - N).
  apply eqmod_sub. apply eqmod_sym. apply eqmod_mod. auto.
  apply eqmod_refl. 
  replace (i - M - N) with (i - (N + M)).
  apply eqmod_sub. apply eqmod_refl. apply eqmod_mod. auto.
  omega.
  apply eqmod_sub. apply eqmod_refl. 
  eapply eqmod_trans; [idtac|apply H2].
  eapply eqmod_trans; [idtac|apply eqmod_mod].
  apply eqmod_sym. eapply eqmod_trans; [idtac|apply eqmod_mod].
  apply eqmod_sym. apply H2. auto. auto.
  symmetry. unfold W. apply unsigned_repr_wordsize.
  apply Z_mod_lt. generalize wordsize_pos; omega. 
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x zero m = and x m.
Proof.
  intros. unfold rolm. rewrite rol_zero. auto.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  Zdivide (Z_of_nat wordsize) modulus ->
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (modu (add n1 n2) iwordsize)
           (and (rol m1 n2) m2).
Proof.
  intros.
  unfold rolm. rewrite rol_and. rewrite and_assoc. 
  rewrite rol_rol. reflexivity. auto.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2).
Proof.
  intros; unfold rolm. symmetry. apply and_or_distrib. 
Qed.

Theorem ror_rol:
  forall x y,
  ltu y iwordsize = true ->
  ror x y = rol x (sub iwordsize y).
Proof.
  intros. unfold ror, rol, sub.
  generalize (ltu_inv _ _ H).
  rewrite unsigned_repr_wordsize. 
  intro. repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros. decEq.
  apply eqmod_mod_eq. omega. 
  exists 1. omega.
  generalize wordsize_pos; generalize wordsize_max_unsigned; omega. 
Qed.

Theorem or_ror:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  add y z = iwordsize ->
  ror x z = or (shl x y) (shru x z).
Proof.
  intros.
  generalize (ltu_inv _ _ H).
  generalize (ltu_inv _ _ H0).
  rewrite unsigned_repr_wordsize.
  intros.
  unfold or, bitwise_binop, shl, shru, ror.
  set (ux := unsigned x).
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten. intros i iRANGE. rewrite Zplus_0_r.
  repeat rewrite bits_of_Z_of_bits_gen; auto.
  assert (y = sub iwordsize z).
    rewrite <- H1. rewrite add_commut. rewrite sub_add_l. rewrite sub_idem. 
    rewrite add_commut. rewrite add_zero. auto.
  assert (unsigned y = Z_of_nat wordsize - unsigned z).
    rewrite H4. unfold sub. rewrite unsigned_repr_wordsize. apply unsigned_repr. 
    generalize wordsize_max_unsigned; omega. 
  destruct (zlt (i + unsigned z) (Z_of_nat wordsize)). 
  rewrite Zmod_small. 
  replace (bits_of_Z wordsize ux (i + - unsigned y)) with false. auto.
  symmetry. apply bits_of_Z_below. omega. omega. 
  replace (bits_of_Z wordsize ux (i + unsigned z)) with false. rewrite orb_false_r.
  decEq. 
  replace (i + unsigned z) with (i - unsigned y + 1 * Z_of_nat wordsize) by omega.
  rewrite Z_mod_plus. apply Zmod_small. omega. generalize wordsize_pos; omega. 
  symmetry. apply bits_of_Z_above. auto. 
Qed.

(** ** Properties of [Z_one_bits] and [is_power2]. *)

Fixpoint powerserie (l: list Z): Z :=
  match l with
  | nil => 0
  | x :: xs => two_p x + powerserie xs
  end.

Lemma Z_bin_decomp_range:
  forall x n,
  0 <= x < 2 * n -> 0 <= snd (Z_bin_decomp x) < n.
Proof.
  intros. rewrite <- (Z_shift_add_bin_decomp x) in H.
  unfold Z_shift_add in H. destruct (fst (Z_bin_decomp x)); omega.
Qed.

Lemma Z_one_bits_powerserie:
  forall x, 0 <= x < modulus -> x = powerserie (Z_one_bits wordsize x 0).
Proof.
  assert (forall n x i, 
    0 <= i ->
    0 <= x < two_power_nat n ->
    x * two_p i = powerserie (Z_one_bits n x i)).
  induction n; intros.
  simpl. rewrite two_power_nat_O in H0. 
  assert (x = 0). omega. subst x. omega.
  rewrite two_power_nat_S in H0. simpl Z_one_bits.
  generalize (Z_shift_add_bin_decomp x).
  generalize (Z_bin_decomp_range x _ H0).
  case (Z_bin_decomp x). simpl. intros b y RANGE SHADD. 
  subst x. unfold Z_shift_add.
  destruct b. simpl powerserie. rewrite <- IHn. 
  rewrite two_p_is_exp. change (two_p 1) with 2. ring.
  auto. omega. omega. auto.
  rewrite <- IHn. 
  rewrite two_p_is_exp. change (two_p 1) with 2. ring.
  auto. omega. omega. auto.
  intros. rewrite <- H. change (two_p 0) with 1. omega.
  omega. exact H0.
Qed.

Lemma Z_one_bits_range:
  forall x i, In i (Z_one_bits wordsize x 0) -> 0 <= i < Z_of_nat wordsize.
Proof.
  assert (forall n x i j,
    In j (Z_one_bits n x i) -> i <= j < i + Z_of_nat n).
  induction n; simpl In.
  intros; elim H.
  intros x i j. destruct (Z_bin_decomp x). case b.
  rewrite inj_S. simpl. intros [A|B]. subst j. omega.
  generalize (IHn _ _ _ B). omega.
  intros B. rewrite inj_S. generalize (IHn _ _ _ B). omega.
  intros. generalize (H wordsize x 0 i H0). omega.
Qed.

Lemma is_power2_rng:
  forall n logn,
  is_power2 n = Some logn ->
  0 <= unsigned logn < Z_of_nat wordsize.
Proof.
  intros n logn. unfold is_power2.
  generalize (Z_one_bits_range (unsigned n)).
  destruct (Z_one_bits wordsize (unsigned n) 0).
  intros; discriminate.
  destruct l.
  intros. injection H0; intro; subst logn; clear H0.
  assert (0 <= z < Z_of_nat wordsize).
  apply H. auto with coqlib.
  rewrite unsigned_repr. auto. generalize wordsize_max_unsigned; omega.
  intros; discriminate.
Qed.

Theorem is_power2_range:
  forall n logn,
  is_power2 n = Some logn -> ltu logn iwordsize = true.
Proof.
  intros. unfold ltu. rewrite unsigned_repr_wordsize.
  generalize (is_power2_rng _ _ H). 
  case (zlt (unsigned logn) (Z_of_nat wordsize)); intros.
  auto. omegaContradiction. 
Qed. 

Lemma is_power2_correct:
  forall n logn,
  is_power2 n = Some logn ->
  unsigned n = two_p (unsigned logn).
Proof.
  intros n logn. unfold is_power2.
  generalize (Z_one_bits_powerserie (unsigned n) (unsigned_range n)).
  generalize (Z_one_bits_range (unsigned n)).
  destruct (Z_one_bits wordsize (unsigned n) 0).
  intros; discriminate.
  destruct l.
  intros. simpl in H0. injection H1; intros; subst logn; clear H1.
  rewrite unsigned_repr. replace (two_p z) with (two_p z + 0).
  auto. omega. elim (H z); intros.
  generalize wordsize_max_unsigned; omega.
  auto with coqlib. 
  intros; discriminate.
Qed.

Remark two_p_range:
  forall n,
  0 <= n < Z_of_nat wordsize ->
  0 <= two_p n <= max_unsigned.
Proof.
  intros. split.
  assert (two_p n > 0). apply two_p_gt_ZERO. omega. omega.
  generalize (two_p_monotone_strict _ _ H). rewrite <- two_power_nat_two_p. 
  unfold max_unsigned, modulus. omega. 
Qed.

Remark Z_one_bits_zero:
  forall n i, Z_one_bits n 0 i = nil.
Proof.
  induction n; intros; simpl; auto.
Qed.

Remark Z_one_bits_two_p:
  forall n x i,
  0 <= x < Z_of_nat n ->
  Z_one_bits n (two_p x) i = (i + x) :: nil.
Proof.
  induction n; intros; simpl. simpl in H. omegaContradiction.
  rewrite inj_S in H. 
  assert (x = 0 \/ 0 < x) by omega. destruct H0.
  subst x; simpl. decEq. omega. apply Z_one_bits_zero.
  replace (two_p x) with (Z_shift_add false (two_p (x-1))).
  rewrite Z_bin_decomp_shift_add.
  replace (i + x) with ((i + 1) + (x - 1)) by omega. 
  apply IHn. omega.
  unfold Z_shift_add. rewrite <- two_p_S. decEq; omega. omega.
Qed.

Lemma is_power2_two_p:
  forall n, 0 <= n < Z_of_nat wordsize ->
  is_power2 (repr (two_p n)) = Some (repr n).
Proof.
  intros. unfold is_power2. rewrite unsigned_repr. 
  rewrite Z_one_bits_two_p. auto. auto.
  apply two_p_range. auto.
Qed.

(** ** Relation between bitwise operations and multiplications / divisions by powers of 2 *)

(** Left shifts and multiplications by powers of 2. *)

Lemma Z_of_bits_shift_left:
  forall f m,
  m >= 0 ->
  (forall i, i < 0 -> f i = false) ->
  eqm (Z_of_bits wordsize f (-m)) (two_p m * Z_of_bits wordsize f 0).
Proof.
  intros. 
  set (m' := nat_of_Z m). 
  assert (Z_of_nat m' = m). apply nat_of_Z_eq. auto.
  generalize (Z_of_bits_compose f m' wordsize (-m)). rewrite H1. 
  replace (-m+m) with 0 by omega. rewrite two_power_nat_two_p. rewrite H1. 
  replace (Z_of_bits m' f (-m)) with 0. intro EQ.
  eapply eqm_trans. apply eqm_sym. eapply Z_of_bits_truncate with (n := m').
  rewrite plus_comm. rewrite EQ. apply eqm_refl2. ring. 
  symmetry. apply Z_of_bits_false. rewrite H1. intros. apply H0. omega. 
Qed.

Lemma shl_mul_two_p:
  forall x y,
  shl x y = mul x (repr (two_p (unsigned y))).
Proof.
  intros. unfold shl, mul. apply eqm_samerepr. 
  eapply eqm_trans.
  apply Z_of_bits_shift_left.
  generalize (unsigned_range y). omega.
  intros; apply bits_of_Z_below; auto.
  rewrite Zmult_comm. apply eqm_mult.
  apply Z_of_bits_of_Z. apply eqm_unsigned_repr.
Qed.

Theorem shl_mul:
  forall x y,
  shl x y = mul x (shl one y).
Proof.
  intros. 
  assert (shl one y = repr (two_p (unsigned y))).
  rewrite shl_mul_two_p. rewrite mul_commut. rewrite mul_one. auto.
  rewrite H. apply shl_mul_two_p.
Qed.

Theorem mul_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  mul x n = shl x logn.
Proof.
  intros. generalize (is_power2_correct n logn H); intro.
  rewrite shl_mul_two_p. rewrite <- H0. rewrite repr_unsigned.
  auto.
Qed.

(** Unsigned right shifts and unsigned divisions by powers of 2. *)

Lemma Z_of_bits_shift_right:
  forall m f,
  m >= 0 ->
  (forall i, i >= Z_of_nat wordsize -> f i = false) ->
  exists k,
  Z_of_bits wordsize f 0 = k + two_p m * Z_of_bits wordsize f m /\ 0 <= k < two_p m.
Proof.
  intros. 
  set (m' := nat_of_Z m). 
  assert (Z_of_nat m' = m). apply nat_of_Z_eq. auto.
  generalize (Z_of_bits_compose f m' wordsize 0).
  rewrite two_power_nat_two_p. rewrite H1.
  rewrite plus_comm. rewrite Z_of_bits_compose.
  replace (Z_of_bits m' f (0 + Z_of_nat wordsize)) with 0.
  repeat rewrite Zplus_0_l. intros EQ. 
  exists (Z_of_bits m' f 0); split. rewrite EQ. ring. 
  rewrite <- H1. rewrite <- two_power_nat_two_p. apply Z_of_bits_range. 
  symmetry. apply Z_of_bits_false. intros. apply H0. omega. 
Qed.

Lemma shru_div_two_p:
  forall x y,
  shru x y = repr (unsigned x / two_p (unsigned y)).
Proof.
  intros. unfold shru. 
  set (x' := unsigned x). set (y' := unsigned y).
  destruct (Z_of_bits_shift_right y' (bits_of_Z wordsize x')) as [k [EQ RANGE]].
  generalize (unsigned_range y). unfold y'; omega.
  intros. rewrite bits_of_Z_above; auto. 
  decEq. symmetry. apply Zdiv_unique with k; auto. 
  transitivity (Z_of_bits wordsize (bits_of_Z wordsize x') 0).
  apply eqm_small_eq. apply eqm_sym. apply Z_of_bits_of_Z.
  unfold x'; auto with ints. auto with ints.
  rewrite EQ. ring. 
Qed.

Theorem divu_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divu x n = shru x logn.
Proof.
  intros. generalize (is_power2_correct n logn H). intro.
  symmetry. unfold divu. rewrite H0. apply shru_div_two_p.
Qed.

(** Signed right shifts and signed divisions by powers of 2. *)

Lemma Z_of_bits_shift_right_neg:
  forall m f,
  m >= 0 ->
  (forall i, i >= Z_of_nat wordsize -> f i = true) ->
  exists k,
  Z_of_bits wordsize f 0 - modulus =
           k + two_p m * (Z_of_bits wordsize f m - modulus) 
  /\ 0 <= k < two_p m.
Proof.
  intros. 
  set (m' := nat_of_Z m). 
  assert (Z_of_nat m' = m). apply nat_of_Z_eq. auto.
  generalize (Z_of_bits_compose f m' wordsize 0).
  rewrite two_power_nat_two_p. rewrite H1.
  rewrite plus_comm. rewrite Z_of_bits_compose.
  repeat rewrite Zplus_0_l. fold modulus. 
  replace (Z_of_bits m' f (Z_of_nat wordsize)) with (two_p m - 1).
  intros EQ.
  exists (Z_of_bits m' f 0); split.
  replace (Z_of_bits wordsize f 0)
     with (Z_of_bits wordsize f m * two_p m + Z_of_bits m' f 0 - (two_p m - 1) * modulus)
  by omega.
  ring. 
  rewrite <- H1. rewrite <- two_power_nat_two_p. apply Z_of_bits_range.
  rewrite <- H1. rewrite <- two_power_nat_two_p. 
  symmetry. apply Z_of_bits_true. intros. apply H0. omega. 
Qed.

Lemma sign_bit_of_Z_rec:
  forall n x,
  0 <= x < two_power_nat (S n) ->
  bits_of_Z (S n) x (Z_of_nat n) = if zlt x (two_power_nat n) then false else true.
Proof.
  induction n; intros.
  rewrite two_power_nat_S in H. rewrite two_power_nat_O in *. simpl. 
  caseEq (Z_bin_decomp x); intros b x1 ZBD. rewrite zeq_true. 
  generalize (Z_shift_add_bin_decomp x). rewrite ZBD; simpl. intros. subst x. 
  unfold Z_shift_add in *.
  destruct b. rewrite zlt_false. auto. omega. rewrite zlt_true. auto. omega. 
  rewrite inj_S. remember (S n) as sn. simpl. rewrite two_power_nat_S in H. 
  generalize (Z_shift_add_bin_decomp x). destruct (Z_bin_decomp x) as [b x1].
  simpl. intros. rewrite zeq_false. 
  replace (Zsucc (Z_of_nat n) - 1) with (Z_of_nat n). rewrite IHn.
  rewrite <- H0. subst sn. rewrite two_power_nat_S. 
  destruct (zlt x1 (two_power_nat n)).
  rewrite zlt_true. auto. unfold Z_shift_add; destruct b; omega.
  rewrite zlt_false. auto. unfold Z_shift_add; destruct b; omega.
  subst x. unfold Z_shift_add in H. destruct b; omega.
  omega. omega.
Qed.

Lemma sign_bit_of_Z:
  forall x,
  bits_of_Z wordsize (unsigned x) (Z_of_nat wordsize - 1) =
  if zlt (unsigned x) half_modulus then false else true.
Proof.
  intros. 
  rewrite half_modulus_power. 
  set (w1 := nat_of_Z (Z_of_nat wordsize - 1)).
  assert (Z_of_nat wordsize - 1 = Z_of_nat w1).
      unfold w1. rewrite nat_of_Z_eq; auto. generalize wordsize_pos; omega.
  assert (wordsize = 1 + w1)%nat.
      apply inj_eq_rev. rewrite inj_plus. simpl (Z_of_nat 1). omega.
  rewrite H. rewrite <- two_power_nat_two_p. rewrite H0.
  apply sign_bit_of_Z_rec. simpl in H0; rewrite <- H0. auto with ints.
Qed.

Lemma shr_div_two_p:
  forall x y,
  shr x y = repr (signed x / two_p (unsigned y)).
Proof.
  intros. unfold shr.
  generalize (sign_bit_of_Z x); intro SIGN.
  unfold signed. destruct (zlt (unsigned x) half_modulus).
(* positive case *)
  rewrite <- shru_div_two_p. unfold shru. decEq; apply Z_of_bits_exten; intros.
  destruct (zlt (i + unsigned y) (Z_of_nat wordsize)). auto.
  rewrite SIGN. symmetry. apply bits_of_Z_above. auto. 
(* negative case *)
  set (x' := unsigned x) in *. set (y' := unsigned y) in *.
  set (f := fun i => bits_of_Z wordsize x'
                      (if zlt i (Z_of_nat wordsize) then i else Z_of_nat wordsize - 1)).
  destruct (Z_of_bits_shift_right_neg y' f) as [k [EQ RANGE]].
  generalize (unsigned_range y). unfold y'; omega.
  intros. unfold f. rewrite zlt_false; auto. 
  set (A := Z_of_bits wordsize f y') in *.
  set (B := Z_of_bits wordsize f 0) in *.
  assert (B = Z_of_bits wordsize (bits_of_Z wordsize x') 0).
    unfold B. apply Z_of_bits_exten; intros. 
    unfold f. rewrite zlt_true. auto. omega. 
  assert (B = x').
    apply eqm_small_eq. rewrite H. apply Z_of_bits_of_Z. 
    unfold B; apply Z_of_bits_range. 
    unfold x'; apply unsigned_range.
  assert (Q: (x' - modulus) / two_p y' = A - modulus).
    apply Zdiv_unique with k; auto. rewrite <- H0. rewrite EQ. ring.
  rewrite Q. apply eqm_samerepr. exists 1; ring. 
Qed.

Theorem divs_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divs x n = shrx x logn.
Proof.
  intros. generalize (is_power2_correct _ _ H); intro.
  unfold shrx. rewrite shl_mul_two_p.
  rewrite mul_commut. rewrite mul_one.
  rewrite <- H0. rewrite repr_unsigned. auto.
Qed.

(** Unsigned modulus over [2^n] is masking with [2^n-1]. *)

Lemma Z_of_bits_mod_mask:
  forall f n,
  0 <= n <= Z_of_nat wordsize ->
  Z_of_bits wordsize (fun i => if zlt i n then f i else false) 0 =
  (Z_of_bits wordsize f 0) mod (two_p n).
Proof.
  intros. set (f' := fun i => if zlt i n then f i else false).
  set (n1 := nat_of_Z n). set (m1 := nat_of_Z (Z_of_nat wordsize - n)).
  assert (Z_of_nat n1 = n). apply nat_of_Z_eq; omega.
  assert (Z_of_nat m1 = Z_of_nat wordsize - n). apply nat_of_Z_eq; omega.
  assert (n1 + m1 = wordsize)%nat. apply inj_eq_rev. rewrite inj_plus. omega.
  generalize (Z_of_bits_compose f n1 m1 0).
  rewrite H2. rewrite Zplus_0_l. rewrite two_power_nat_two_p. rewrite H0. intros.
  generalize (Z_of_bits_compose f' n1 m1 0).
  rewrite H2. rewrite Zplus_0_l. rewrite two_power_nat_two_p. rewrite H0. intros.
  assert (Z_of_bits n1 f' 0 = Z_of_bits n1 f 0).
    apply Z_of_bits_exten; intros. unfold f'. apply zlt_true. omega. 
  assert (Z_of_bits m1 f' n = 0).
    apply Z_of_bits_false; intros. unfold f'. apply zlt_false. omega. 
  assert (Z_of_bits wordsize f' 0 = Z_of_bits n1 f 0).
    rewrite H4. rewrite H5. rewrite H6. ring.
  symmetry. apply Zmod_unique with (Z_of_bits m1 f n). omega. 
  rewrite H7. rewrite <- H0. rewrite <- two_power_nat_two_p. apply Z_of_bits_range.
Qed.

Theorem modu_and:
  forall x n logn,
  is_power2 n = Some logn ->
  modu x n = and x (sub n one).
Proof.
  intros. generalize (is_power2_correct _ _ H); intro.
  generalize (is_power2_rng _ _ H); intro.
  unfold modu, and, bitwise_binop. decEq.
  set (ux := unsigned x).
  replace ux with (Z_of_bits wordsize (bits_of_Z wordsize ux) 0).
  rewrite H0. rewrite <- Z_of_bits_mod_mask. 
  apply Z_of_bits_exten; intros. rewrite Zplus_0_r. 
  rewrite bits_of_Z_of_bits; auto. 
  replace (unsigned (sub n one)) with (two_p (unsigned logn) - 1).
  rewrite bits_of_Z_two_p. unfold proj_sumbool.
  destruct (zlt i (unsigned logn)). rewrite andb_true_r; auto. rewrite andb_false_r; auto. 
  omega. auto. 
  rewrite <- H0. unfold sub. symmetry. rewrite unsigned_one. apply unsigned_repr.
  rewrite H0. 
  assert (two_p (unsigned logn) > 0). apply two_p_gt_ZERO. omega.
  generalize (two_p_range _ H1). omega. 
  omega.
  apply eqm_small_eq. apply Z_of_bits_of_Z. apply Z_of_bits_range. 
  unfold ux. apply unsigned_range.
Qed.

(** ** Properties of [shrx] (signed division by a power of 2) *)

Theorem shrx_carry:
  forall x y,
  add (shr x y) (shr_carry x y) = shrx x y.
Proof.
  intros. unfold shr_carry. 
  rewrite sub_add_opp. rewrite add_permut. 
  rewrite add_neg_zero. apply add_zero.
Qed.

Lemma Zdiv_round_Zdiv:
  forall x y,
  y > 0 ->
  Zdiv_round x y = if zlt x 0 then (x + y - 1) / y else x / y.
Proof.
  intros. unfold Zdiv_round.
  destruct (zlt x 0). 
  rewrite zlt_false; try omega.
  generalize (Z_div_mod_eq (-x) y H).
  generalize (Z_mod_lt (-x) y H).
  set (q := (-x) / y). set (r := (-x) mod y). intros.
  symmetry.
  apply Zdiv_unique with (y - r - 1).
  replace x with (- (y * q) - r) by omega.
  replace (-(y * q)) with ((-q) * y) by ring.
  omega.
  omega.
  apply zlt_false. omega.
Qed.

Theorem shrx_shr:
  forall x y,
  ltu y (repr (Z_of_nat wordsize - 1)) = true ->
  shrx x y =
  shr (if lt x zero then add x (sub (shl one y) one) else x) y.
Proof.
  intros. rewrite shr_div_two_p. unfold shrx. unfold divs.  
  exploit ltu_inv; eauto. rewrite unsigned_repr. 
  set (uy := unsigned y). intro RANGE.
  assert (shl one y = repr (two_p uy)).
    transitivity (mul one (repr (two_p uy))).
    symmetry. apply mul_pow2. replace y with (repr uy). 
    apply is_power2_two_p. omega. apply repr_unsigned.
    rewrite mul_commut. apply mul_one.
  assert (two_p uy > 0). apply two_p_gt_ZERO. omega.
  assert (two_p uy < half_modulus). 
    rewrite half_modulus_power. 
    apply two_p_monotone_strict. auto.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. omega. 
  assert (unsigned (shl one y) = two_p uy).
    rewrite H0. apply unsigned_repr. unfold max_unsigned. omega.
  assert (signed (shl one y) = two_p uy).
    rewrite H0. apply signed_repr.
    unfold max_signed. generalize min_signed_neg. omega.
  rewrite H5. 
  rewrite Zdiv_round_Zdiv; auto.
  unfold lt. rewrite signed_zero.  
  destruct (zlt (signed x) 0); auto.
  rewrite add_signed.
  assert (signed (sub (shl one y) one) = two_p uy - 1).
    unfold sub. rewrite H4. rewrite unsigned_one.  
    apply signed_repr.
    generalize min_signed_neg. unfold max_signed. omega. 
  rewrite H6. rewrite signed_repr. decEq. decEq. omega.
  generalize (signed_range x). intros.  
  assert (two_p uy - 1 <= max_signed). unfold max_signed. omega.
  omega.
  generalize wordsize_pos wordsize_max_unsigned; omega.
Qed.

(** ** Properties of integer zero extension and sign extension. *)

Section EXTENSIONS.

Variable n: Z.
Hypothesis RANGE: 0 < n < Z_of_nat wordsize.

Remark two_p_n_pos:
  two_p n > 0.
Proof. apply two_p_gt_ZERO. omega. Qed.

Remark two_p_n_range:
  0 <= two_p n <= max_unsigned.
Proof. apply two_p_range. omega. Qed.

Remark two_p_n_range':
  two_p n <= max_signed + 1.
Proof.
  unfold max_signed. rewrite half_modulus_power. 
  assert (two_p n <= two_p (Z_of_nat wordsize - 1)).
  apply two_p_monotone. omega.
  omega.
Qed.

Remark unsigned_repr_two_p:
  unsigned (repr (two_p n)) = two_p n.
Proof.
  apply unsigned_repr. apply two_p_n_range. 
Qed.

Remark eqm_eqmod_two_p:
  forall a b, eqm a b -> eqmod (two_p n) a b.
Proof.
  intros a b [k EQ].
  exists (k * two_p (Z_of_nat wordsize - n)).
  rewrite EQ. decEq. rewrite <- Zmult_assoc. decEq.
  rewrite <- two_p_is_exp. unfold modulus. rewrite two_power_nat_two_p.
  decEq. omega. omega. omega.
Qed.

Theorem zero_ext_and:
  forall x, zero_ext n x = and x (repr (two_p n - 1)).
Proof.
  intros; unfold zero_ext, and, bitwise_binop.
  decEq; apply Z_of_bits_exten; intros.
  rewrite unsigned_repr. rewrite bits_of_Z_two_p. 
  unfold proj_sumbool. destruct (zlt (i+0) n). 
  rewrite andb_true_r; auto. rewrite andb_false_r; auto. 
  omega. omega. 
  generalize two_p_n_range two_p_n_pos; omega.
Qed.

Theorem zero_ext_mod:
  forall x, unsigned (zero_ext n x) = Zmod (unsigned x) (two_p n).
Proof.
  intros.
  replace (unsigned x) with (Z_of_bits wordsize (bits_of_Z wordsize (unsigned x)) 0).
  unfold zero_ext. rewrite unsigned_repr; auto with ints. 
  apply Z_of_bits_mod_mask. omega.
  apply eqm_small_eq; auto with ints. apply Z_of_bits_of_Z.
Qed.

Theorem zero_ext_idem:
  forall x, zero_ext n (zero_ext n x) = zero_ext n x.
Proof.
  intros. repeat rewrite zero_ext_and. 
  rewrite and_assoc. rewrite and_idem. auto.
Qed.

Theorem sign_ext_idem:
  forall x, sign_ext n (sign_ext n x) = sign_ext n x.
Proof.
  intros. unfold sign_ext.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros. rewrite Zplus_0_r.
  repeat rewrite bits_of_Z_of_bits; auto. 
  destruct (zlt i n). auto. destruct (zlt (n - 1) n); auto.
  omega.
Qed.

Theorem sign_ext_zero_ext:
  forall x, sign_ext n (zero_ext n x) = sign_ext n x.
Proof.
  intros. unfold sign_ext, zero_ext.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros. rewrite Zplus_0_r.
  destruct (zlt i n); rewrite bits_of_Z_of_bits; auto.
  rewrite zlt_true; auto. rewrite zlt_true; auto. omega. omega.
Qed.

Theorem zero_ext_sign_ext:
  forall x, zero_ext n (sign_ext n x) = zero_ext n x.
Proof.
  intros. unfold sign_ext, zero_ext.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros. rewrite Zplus_0_r.
  destruct (zlt i n); auto.
  rewrite bits_of_Z_of_bits; auto.
  rewrite zlt_true; auto.
Qed.

Theorem sign_ext_equal_if_zero_equal:
  forall x y,
  zero_ext n x = zero_ext n y ->
  sign_ext n x = sign_ext n y.
Proof.
  intros. rewrite <- (sign_ext_zero_ext x).
  rewrite <- (sign_ext_zero_ext y). congruence.
Qed.

Theorem zero_ext_shru_shl:
  forall x, 
  let y := repr (Z_of_nat wordsize - n) in
  zero_ext n x = shru (shl x y) y.
Proof.
  intros.
  assert (unsigned y = Z_of_nat wordsize - n).
    unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. omega.
  rewrite zero_ext_and. symmetry. 
  replace n with (Z_of_nat wordsize - unsigned y).
  apply shru_shl_and. unfold ltu. apply zlt_true.
  rewrite H. rewrite unsigned_repr_wordsize. omega. omega.
Qed.

Theorem sign_ext_shr_shl:
  forall x, 
  let y := repr (Z_of_nat wordsize - n) in
  sign_ext n x = shr (shl x y) y.
Proof.
  intros.
  assert (unsigned y = Z_of_nat wordsize - n).
    unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. omega.
  unfold sign_ext, shr, shl.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros; rewrite Zplus_0_r.
  destruct (zlt i n). rewrite zlt_true. rewrite bits_of_Z_of_bits_gen.
  decEq. omega.  omega. omega. 
  rewrite zlt_false. rewrite bits_of_Z_of_bits_gen. 
  decEq. omega. omega. omega.
Qed.

(** [zero_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [0...2^n-1]. *)

Lemma zero_ext_range:
  forall x, 0 <= unsigned (zero_ext n x) < two_p n.
Proof.
  intros. rewrite zero_ext_mod. apply Z_mod_lt. apply two_p_gt_ZERO. omega. 
Qed.

Lemma eqmod_zero_ext:
  forall x, eqmod (two_p n) (unsigned (zero_ext n x)) (unsigned x).
Proof.
  intros. rewrite zero_ext_mod. apply eqmod_sym. apply eqmod_mod. 
  apply two_p_gt_ZERO. omega.
Qed.

(** [sign_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [-2^(n-1)...2^(n-1) - 1]. *)

Lemma sign_ext_div:
  forall x,
  signed (sign_ext n x) =
  signed (repr (unsigned x * two_p (Z_of_nat wordsize - n))) / two_p (Z_of_nat wordsize - n).
Proof.
  intros. 
  assert (two_p (Z_of_nat wordsize - n) > 0). apply two_p_gt_ZERO. omega.
  rewrite sign_ext_shr_shl. rewrite shr_div_two_p. rewrite shl_mul_two_p.
  unfold mul. repeat rewrite unsigned_repr. rewrite signed_repr. auto. 
  apply Zdiv_interval_2. apply signed_range. 
  generalize min_signed_neg; omega. apply max_signed_pos.
  auto.
  generalize wordsize_max_unsigned; omega.
  assert (two_p (Z_of_nat wordsize - n) < modulus). 
    rewrite modulus_power. apply two_p_monotone_strict. omega. 
  unfold max_unsigned. omega.
  generalize wordsize_max_unsigned; omega.
Qed.

Lemma sign_ext_range:
  forall x, -two_p (n-1) <= signed (sign_ext n x) < two_p (n-1).
Proof.
  intros.
  assert (two_p (n - 1) > 0). apply two_p_gt_ZERO. omega.
  rewrite sign_ext_div. apply Zdiv_interval_1. omega. auto. apply two_p_gt_ZERO; omega.
  rewrite <- Zopp_mult_distr_l. rewrite <- two_p_is_exp.
  replace (n - 1 + (Z_of_nat wordsize - n)) with (Z_of_nat wordsize - 1) by omega.
  rewrite <- half_modulus_power. 
  generalize (signed_range (repr (unsigned x * two_p (Z_of_nat wordsize - n)))).
  unfold min_signed, max_signed. omega. 
  omega. omega.
Qed.

Lemma eqmod_sign_ext:
  forall x, eqmod (two_p n) (signed (sign_ext n x)) (unsigned x).
Proof.
  intros. rewrite sign_ext_div. 
  assert (eqm (signed (repr (unsigned x * two_p (Z_of_nat wordsize - n))))
              (unsigned x * two_p (Z_of_nat wordsize - n))).
  eapply eqm_trans. apply eqm_signed_unsigned. apply eqm_sym. apply eqm_unsigned_repr.
  destruct H as [k EQ]. exists k.
  rewrite EQ. rewrite Z_div_plus. decEq. 
  replace modulus with (two_p (n + (Z_of_nat wordsize - n))).
  rewrite two_p_is_exp. rewrite Zmult_assoc. apply Z_div_mult.
  apply two_p_gt_ZERO; omega.
  omega. omega.
  rewrite modulus_power. decEq. omega.
  apply two_p_gt_ZERO; omega.
Qed.

Lemma eqmod_sign_ext':
  forall x, eqmod (two_p n) (unsigned (sign_ext n x)) (unsigned x).
Proof.
  intros. eapply eqmod_trans. 
  apply eqm_eqmod_two_p. auto. apply eqm_sym. apply eqm_signed_unsigned. 
  apply eqmod_sign_ext. 
Qed.

End EXTENSIONS.

Theorem zero_ext_widen:
  forall x n n',
  0 < n < Z_of_nat wordsize -> n <= n' < Z_of_nat wordsize ->
  zero_ext n' (zero_ext n x) = zero_ext n x.
Proof.
  intros. unfold zero_ext.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros; rewrite Zplus_0_r.
  destruct (zlt i n). rewrite zlt_true. rewrite bits_of_Z_of_bits. apply zlt_true. 
  auto. omega. omega. 
  destruct (zlt i n'); auto. rewrite bits_of_Z_of_bits. apply zlt_false.
  auto. omega.
Qed.

Theorem sign_ext_widen:
  forall x n n',
  0 < n < Z_of_nat wordsize -> n <= n' < Z_of_nat wordsize ->
  sign_ext n' (sign_ext n x) = sign_ext n x.
Proof.
  intros. unfold sign_ext.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros; rewrite Zplus_0_r.
  destruct (zlt i n). rewrite zlt_true. rewrite bits_of_Z_of_bits. apply zlt_true. 
  auto. omega. omega. 
  destruct (zlt i n'). rewrite bits_of_Z_of_bits. apply zlt_false.
  auto. omega.
  rewrite bits_of_Z_of_bits.
  destruct (zlt (n' - 1) n). assert (n' = n) by omega. congruence. auto.
  omega. 
Qed.

Theorem sign_zero_ext_widen:
  forall x n n',
  0 < n < Z_of_nat wordsize -> n < n' < Z_of_nat wordsize ->
  sign_ext n' (zero_ext n x) = zero_ext n x.
Proof.
  intros. unfold sign_ext, zero_ext.
  repeat rewrite unsigned_repr; auto with ints.
  decEq; apply Z_of_bits_exten; intros; rewrite Zplus_0_r.
  destruct (zlt i n). rewrite zlt_true. rewrite bits_of_Z_of_bits. apply zlt_true. 
  auto. omega. omega. 
  destruct (zlt i n'). rewrite bits_of_Z_of_bits. apply zlt_false.
  auto. omega.
  rewrite bits_of_Z_of_bits. apply zlt_false. omega. omega.
Qed.

(** ** Properties of [one_bits] (decomposition in sum of powers of two) *)

Opaque Z_one_bits. (* Otherwise, next Qed blows up! *)

Theorem one_bits_range:
  forall x i, In i (one_bits x) -> ltu i iwordsize = true.
Proof.
  intros. unfold one_bits in H.
  elim (list_in_map_inv _ _ _ H). intros i0 [EQ IN].
  subst i. unfold ltu. unfold iwordsize. apply zlt_true. 
  generalize (Z_one_bits_range _ _ IN). intros.
  assert (0 <= Z_of_nat wordsize <= max_unsigned).
    generalize wordsize_pos wordsize_max_unsigned; omega.
  repeat rewrite unsigned_repr; omega.
Qed.

Fixpoint int_of_one_bits (l: list int) : int :=
  match l with
  | nil => zero
  | a :: b => add (shl one a) (int_of_one_bits b)
  end.

Theorem one_bits_decomp:
  forall x, x = int_of_one_bits (one_bits x).
Proof.
  intros. 
  transitivity (repr (powerserie (Z_one_bits wordsize (unsigned x) 0))).
  transitivity (repr (unsigned x)).
  auto with ints. decEq. apply Z_one_bits_powerserie.
  auto with ints.
  unfold one_bits. 
  generalize (Z_one_bits_range (unsigned x)).
  generalize (Z_one_bits wordsize (unsigned x) 0).
  induction l.
  intros; reflexivity.
  intros; simpl. rewrite <- IHl. unfold add. apply eqm_samerepr.
  apply eqm_add. rewrite shl_mul_two_p. rewrite mul_commut. 
  rewrite mul_one. apply eqm_unsigned_repr_r. 
  rewrite unsigned_repr. auto with ints.
  generalize (H a (in_eq _ _)). generalize wordsize_max_unsigned. omega.  
  auto with ints.
  intros; apply H; auto with coqlib.
Qed.

(** ** Properties of comparisons *)

Theorem negate_cmp:
  forall c x y, cmp (negate_comparison c) x y = negb (cmp c x y).
Proof.
  intros. destruct c; simpl; try rewrite negb_elim; auto.
Qed.

Theorem negate_cmpu:
  forall c x y, cmpu (negate_comparison c) x y = negb (cmpu c x y).
Proof.
  intros. destruct c; simpl; try rewrite negb_elim; auto.
Qed.

Theorem swap_cmp:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  intros. destruct c; simpl; auto. apply eq_sym. decEq. apply eq_sym.
Qed.

Theorem swap_cmpu:
  forall c x y, cmpu (swap_comparison c) x y = cmpu c y x.
Proof.
  intros. destruct c; simpl; auto. apply eq_sym. decEq. apply eq_sym.
Qed.

Lemma translate_eq:
  forall x y d,
  eq (add x d) (add y d) = eq x y.
Proof.
  intros. unfold eq. case (zeq (unsigned x) (unsigned y)); intro.
  unfold add. rewrite e. apply zeq_true.
  apply zeq_false. unfold add. red; intro. apply n. 
  apply eqm_small_eq; auto with ints.
  replace (unsigned x) with ((unsigned x + unsigned d) - unsigned d).
  replace (unsigned y) with ((unsigned y + unsigned d) - unsigned d).
  apply eqm_sub. apply eqm_trans with (unsigned (repr (unsigned x + unsigned d))).
  eauto with ints. apply eqm_trans with (unsigned (repr (unsigned y + unsigned d))).
  eauto with ints. eauto with ints. eauto with ints.
  omega. omega.
Qed.

Lemma translate_lt:
  forall x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  lt (add x d) (add y d) = lt x y.
Proof.
  intros. repeat rewrite add_signed. unfold lt.
  repeat rewrite signed_repr; auto. case (zlt (signed x) (signed y)); intro.
  apply zlt_true. omega.
  apply zlt_false. omega.
Qed.

Theorem translate_cmp:
  forall c x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  cmp c (add x d) (add y d) = cmp c x y.
Proof.
  intros. unfold cmp.
  rewrite translate_eq. repeat rewrite translate_lt; auto.
Qed.  

Theorem notbool_isfalse_istrue:
  forall x, is_false x -> is_true (notbool x).
Proof.
  unfold is_false, is_true, notbool; intros; subst x. 
  rewrite eq_true. apply one_not_zero. 
Qed.

Theorem notbool_istrue_isfalse:
  forall x, is_true x -> is_false (notbool x).
Proof.
  unfold is_false, is_true, notbool; intros.
  generalize (eq_spec x zero). case (eq x zero); intro.
  contradiction. auto.
Qed.

Theorem shru_lt_zero:
  forall x,
  shru x (repr (Z_of_nat wordsize - 1)) = if lt x zero then one else zero.
Proof.
  intros. rewrite shru_div_two_p. 
  replace (two_p (unsigned (repr (Z_of_nat wordsize - 1))))
    with half_modulus.
  generalize (unsigned_range x); intro. 
  unfold lt. rewrite signed_zero. unfold signed. 
  destruct (zlt (unsigned x) half_modulus).
  rewrite zlt_false.
  replace (unsigned x / half_modulus) with 0. reflexivity. 
  symmetry. apply Zdiv_unique with (unsigned x). ring. omega. omega.
  rewrite zlt_true. 
  replace (unsigned x / half_modulus) with 1. reflexivity.
  symmetry. apply Zdiv_unique with (unsigned x - half_modulus). ring.
  rewrite half_modulus_modulus in H. omega. omega.
  rewrite unsigned_repr. apply half_modulus_power. 
  generalize wordsize_pos wordsize_max_unsigned; omega.
Qed.

Theorem ltu_range_test:
  forall x y,
  ltu x y = true -> unsigned y <= max_signed ->
  0 <= signed x < unsigned y.
Proof.
  intros.
  unfold ltu in H. destruct (zlt (unsigned x) (unsigned y)); try discriminate.
  rewrite signed_eq_unsigned.
  generalize (unsigned_range x). omega. omega.
Qed.

End Make.

(** * Specialization to integers of size 8, 32, and 64 bits *)

Module Wordsize_32.
  Definition wordsize := 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_32.

Module Int := Make(Wordsize_32).

Notation int := Int.int.

Remark int_wordsize_divides_modulus:
  Zdivide (Z_of_nat Int.wordsize) Int.modulus.
Proof.
  exists (two_p (32-5)); reflexivity. 
Qed.

Module Wordsize_8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_8.

Module Byte := Make(Wordsize_8).

Notation byte := Byte.int.

Module Wordsize_64.
  Definition wordsize := 64%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_64.

Module Int64 := Make(Wordsize_64).

Notation int64 := Int64.int.



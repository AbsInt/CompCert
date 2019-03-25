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

Require Import Eqdep_dec Zquot Zwf.
Require Import Coqlib.
Require Archi.

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
  Parameter wordsize: nat.
  Axiom wordsize_not_zero: wordsize <> 0%nat.
End WORDSIZE.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Make(WS: WORDSIZE).

Definition wordsize: nat := WS.wordsize.
Definition zwordsize: Z := Z.of_nat wordsize.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := modulus / 2.
Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Remark wordsize_pos: zwordsize > 0.
Proof.
  unfold zwordsize, wordsize. generalize WS.wordsize_not_zero. omega.
Qed.

Remark modulus_power: modulus = two_p zwordsize.
Proof.
  unfold modulus. apply two_power_nat_two_p.
Qed.

Remark modulus_gt_one: modulus > 1.
Proof.
  rewrite modulus_power. apply Z.lt_gt. apply (two_p_monotone_strict 0).
  generalize wordsize_pos; omega.
Qed.

Remark modulus_pos: modulus > 0.
Proof.
  generalize modulus_gt_one; omega.
Qed.

(** * Representation of machine integers *)

(** A machine integer (type [int]) is represented as a Coq arbitrary-precision
  integer (type [Z]) plus a proof that it is in the range 0 (included) to
  [modulus] (excluded). *)

Record int: Type := mkint { intval: Z; intrange: -1 < intval < modulus }.

(** Fast normalization modulo [2^wordsize] *)

Fixpoint P_mod_two_p (p: positive) (n: nat) {struct n} : Z :=
  match n with
  | O => 0
  | S m =>
      match p with
      | xH => 1
      | xO q => Z.double (P_mod_two_p q m)
      | xI q => Z.succ_double (P_mod_two_p q m)
      end
  end.

Definition Z_mod_modulus (x: Z) : Z :=
  match x with
  | Z0 => 0
  | Zpos p => P_mod_two_p p wordsize
  | Zneg p => let r := P_mod_two_p p wordsize in if zeq r 0 then 0 else modulus - r
  end.

Lemma P_mod_two_p_range:
  forall n p, 0 <= P_mod_two_p p n < two_power_nat n.
Proof.
  induction n; simpl; intros.
  - rewrite two_power_nat_O. omega.
  - rewrite two_power_nat_S. destruct p.
    + generalize (IHn p). rewrite Z.succ_double_spec. omega.
    + generalize (IHn p). rewrite Z.double_spec. omega.
    + generalize (two_power_nat_pos n). omega.
Qed.

Lemma P_mod_two_p_eq:
  forall n p, P_mod_two_p p n = (Zpos p) mod (two_power_nat n).
Proof.
  assert (forall n p, exists y, Zpos p = y * two_power_nat n + P_mod_two_p p n).
  {
    induction n; simpl; intros.
    - rewrite two_power_nat_O. exists (Zpos p). ring.
    - rewrite two_power_nat_S. destruct p.
      + destruct (IHn p) as [y EQ]. exists y.
        change (Zpos p~1) with (2 * Zpos p + 1). rewrite EQ.
        rewrite Z.succ_double_spec. ring.
      + destruct (IHn p) as [y EQ]. exists y.
        change (Zpos p~0) with (2 * Zpos p). rewrite EQ.
        rewrite (Z.double_spec (P_mod_two_p p n)). ring.
      + exists 0; omega.
  }
  intros.
  destruct (H n p) as [y EQ].
  symmetry. apply Zmod_unique with y. auto. apply P_mod_two_p_range.
Qed.

Lemma Z_mod_modulus_range:
  forall x, 0 <= Z_mod_modulus x < modulus.
Proof.
  intros; unfold Z_mod_modulus.
  destruct x.
  - generalize modulus_pos; intuition.
  - apply P_mod_two_p_range.
  - set (r := P_mod_two_p p wordsize).
    assert (0 <= r < modulus) by apply P_mod_two_p_range.
    destruct (zeq r 0).
    + generalize modulus_pos; intuition.
    + Psatz.lia.
Qed.

Lemma Z_mod_modulus_range':
  forall x, -1 < Z_mod_modulus x < modulus.
Proof.
  intros. generalize (Z_mod_modulus_range x); intuition.
Qed.

Lemma Z_mod_modulus_eq:
  forall x, Z_mod_modulus x = x mod modulus.
Proof.
  intros. unfold Z_mod_modulus. destruct x.
  - rewrite Zmod_0_l. auto.
  - apply P_mod_two_p_eq.
  - generalize (P_mod_two_p_range wordsize p) (P_mod_two_p_eq wordsize p).
    fold modulus. intros A B.
    exploit (Z_div_mod_eq (Zpos p) modulus). apply modulus_pos. intros C.
    set (q := Zpos p / modulus) in *.
    set (r := P_mod_two_p p wordsize) in *.
    rewrite <- B in C.
    change (Z.neg p) with (- (Z.pos p)). destruct (zeq r 0).
    + symmetry. apply Zmod_unique with (-q). rewrite C; rewrite e. Psatz.lia.
      intuition.
    + symmetry. apply Zmod_unique with (-q - 1). rewrite C. Psatz.lia.
      intuition.
Qed.

(** The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed
  respectively. *)

Definition unsigned (n: int) : Z := intval n.

Definition signed (n: int) : Z :=
  let x := unsigned n in
  if zlt x half_modulus then x else x - modulus.

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

Definition repr (x: Z) : int :=
  mkint (Z_mod_modulus x) (Z_mod_modulus_range' x).

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).
Definition iwordsize := repr zwordsize.

Lemma mkint_eq:
  forall x y Px Py, x = y -> mkint x Px = mkint y Py.
Proof.
  intros. subst y.
  assert (forall (n m: Z) (P1 P2: n < m), P1 = P2).
  {
    unfold Z.lt; intros.
    apply eq_proofs_unicity.
    intros c1 c2. destruct c1; destruct c2; (left; reflexivity) || (right; congruence).
  }
  destruct Px as [Px1 Px2]. destruct Py as [Py1 Py2].
  rewrite (H _ _ Px1 Py1).
  rewrite (H _ _ Px2 Py2).
  reflexivity.
Qed.

Lemma eq_dec: forall (x y: int), {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y. destruct (zeq intval0 intval1).
  left. apply mkint_eq. auto.
  right. red; intro. injection H. exact n.
Defined.

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

Definition divs (x y: int) : int :=
  repr (Z.quot (signed x) (signed y)).
Definition mods (x y: int) : int :=
  repr (Z.rem (signed x) (signed y)).

Definition divu (x y: int) : int :=
  repr (unsigned x / unsigned y).
Definition modu (x y: int) : int :=
  repr ((unsigned x) mod (unsigned y)).

(** Bitwise boolean operations. *)

Definition and (x y: int): int := repr (Z.land (unsigned x) (unsigned y)).
Definition or (x y: int): int := repr (Z.lor (unsigned x) (unsigned y)).
Definition xor (x y: int) : int := repr (Z.lxor (unsigned x) (unsigned y)).

Definition not (x: int) : int := xor x mone.

(** Shifts and rotates. *)

Definition shl (x y: int): int := repr (Z.shiftl (unsigned x) (unsigned y)).
Definition shru (x y: int): int := repr (Z.shiftr (unsigned x) (unsigned y)).
Definition shr (x y: int): int := repr (Z.shiftr (signed x) (unsigned y)).

Definition rol (x y: int) : int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftl (unsigned x) n) (Z.shiftr (unsigned x) (zwordsize - n))).
Definition ror (x y: int) : int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftr (unsigned x) n) (Z.shiftl (unsigned x) (zwordsize - n))).

Definition rolm (x a m: int): int := and (rol x a) m.

(** Viewed as signed divisions by powers of two, [shrx] rounds towards
  zero, while [shr] rounds towards minus infinity. *)

Definition shrx (x y: int): int :=
  divs x (shl one y).

(** High half of full multiply. *)

Definition mulhu (x y: int): int := repr ((unsigned x * unsigned y) / modulus).
Definition mulhs (x y: int): int := repr ((signed x * signed y) / modulus).

(** Condition flags *)

Definition negative (x: int): int :=
  if lt x zero then one else zero.

Definition add_carry (x y cin: int): int :=
  if zlt (unsigned x + unsigned y + unsigned cin) modulus then zero else one.

Definition add_overflow (x y cin: int): int :=
  let s := signed x + signed y + signed cin in
  if zle min_signed s && zle s max_signed then zero else one.

Definition sub_borrow (x y bin: int): int :=
  if zlt (unsigned x - unsigned y - unsigned bin) 0 then one else zero.

Definition sub_overflow (x y bin: int): int :=
  let s := signed x - signed y - signed bin in
  if zle min_signed s && zle s max_signed then zero else one.

(** [shr_carry x y] is 1 if [x] is negative and at least one 1 bit is shifted away. *)

Definition shr_carry (x y: int) : int :=
  if lt x zero && negb (eq (and x (sub (shl one y) one)) zero)
  then one else zero.

(** Zero and sign extensions *)

Definition Zshiftin (b: bool) (x: Z) : Z :=
  if b then Z.succ_double x else Z.double x.

(** In pseudo-code:
<<
    Fixpoint Zzero_ext (n: Z) (x: Z) : Z :=
      if zle n 0 then
        0
      else
        Zshiftin (Z.odd x) (Zzero_ext (Z.pred n) (Z.div2 x)).
    Fixpoint Zsign_ext (n: Z) (x: Z) : Z :=
      if zle n 1 then
        if Z.odd x then -1 else 0
      else
        Zshiftin (Z.odd x) (Zzero_ext (Z.pred n) (Z.div2 x)).
>>
  We encode this [nat]-like recursion using the [Z.iter] iteration
  function, in order to make the [Zzero_ext] and [Zsign_ext]
  functions efficiently executable within Coq.
*)

Definition Zzero_ext (n: Z) (x: Z) : Z :=
  Z.iter n
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => 0)
    x.

Definition Zsign_ext (n: Z) (x: Z) : Z :=
  Z.iter (Z.pred n)
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => if Z.odd x then -1 else 0)
    x.

Definition zero_ext (n: Z) (x: int) : int := repr (Zzero_ext n (unsigned x)).

Definition sign_ext (n: Z) (x: int) : int := repr (Zsign_ext n (unsigned x)).

(** Decomposition of a number as a sum of powers of two. *)

Fixpoint Z_one_bits (n: nat) (x: Z) (i: Z) {struct n}: list Z :=
  match n with
  | O => nil
  | S m =>
      if Z.odd x
      then i :: Z_one_bits m (Z.div2 x) (i+1)
      else Z_one_bits m (Z.div2 x) (i+1)
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

(** x86-style extended division and modulus *)

Definition divmodu2 (nhi nlo: int) (d: int) : option (int * int) :=
  if eq_dec d zero then None else
   (let (q, r) := Z.div_eucl (unsigned nhi * modulus + unsigned nlo) (unsigned d) in
    if zle q max_unsigned then Some(repr q, repr r) else None).

Definition divmods2 (nhi nlo: int) (d: int) : option (int * int) :=
  if eq_dec d zero then None else
   (let (q, r) := Z.quotrem (signed nhi * modulus + unsigned nlo) (signed d) in
    if zle min_signed q && zle q max_signed then Some(repr q, repr r) else None).

(** * Properties of integers and integer arithmetic *)

(** ** Properties of [modulus], [max_unsigned], etc. *)

Remark half_modulus_power:
  half_modulus = two_p (zwordsize - 1).
Proof.
  unfold half_modulus. rewrite modulus_power.
  set (ws1 := zwordsize - 1).
  replace (zwordsize) with (Z.succ ws1).
  rewrite two_p_S. rewrite Z.mul_comm. apply Z_div_mult. omega.
  unfold ws1. generalize wordsize_pos; omega.
  unfold ws1. omega.
Qed.

Remark half_modulus_modulus: modulus = 2 * half_modulus.
Proof.
  rewrite half_modulus_power. rewrite modulus_power.
  rewrite <- two_p_S. apply f_equal. omega.
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

Remark wordsize_max_unsigned: zwordsize <= max_unsigned.
Proof.
  assert (zwordsize < modulus).
    rewrite modulus_power. apply two_p_strict.
    generalize wordsize_pos. omega.
  unfold max_unsigned. omega.
Qed.

Remark two_wordsize_max_unsigned: 2 * zwordsize - 1 <= max_unsigned.
Proof.
  assert (2 * zwordsize - 1 < modulus).
    rewrite modulus_power. apply two_p_strict_2. generalize wordsize_pos; omega.
  unfold max_unsigned; omega.
Qed.

Remark max_signed_unsigned: max_signed < max_unsigned.
Proof.
  unfold max_signed, max_unsigned. rewrite half_modulus_modulus.
  generalize half_modulus_pos. omega.
Qed.

Lemma unsigned_repr_eq:
  forall x, unsigned (repr x) = Z.modulo x modulus.
Proof.
  intros. simpl. apply Z_mod_modulus_eq.
Qed.

Lemma signed_repr_eq:
  forall x, signed (repr x) = if zlt (Z.modulo x modulus) half_modulus then Z.modulo x modulus else Z.modulo x modulus - modulus.
Proof.
  intros. unfold signed. rewrite unsigned_repr_eq. auto.
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
  rewrite Z.add_comm. apply Z_mod_plus. auto.
Qed.

Lemma eqmod_mod:
  forall x, eqmod x (x mod modul).
Proof.
  intros; red. exists (x / modul).
  rewrite Z.mul_comm. apply Z_div_mod_eq. auto.
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
  forall n m x y, eqmod n x y -> Z.divide m n -> eqmod m x y.
Proof.
  intros. destruct H as [k1 EQ1]. destruct H0 as [k2 EQ2].
  exists (k1*k2). rewrite <- Z.mul_assoc. rewrite <- EQ2. auto.
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
  rewrite !Z_mod_modulus_eq. apply eqmod_mod_eq. auto with ints. exact H.
Qed.

Lemma eqm_unsigned_repr:
  forall z, eqm z (unsigned (repr z)).
Proof.
  unfold eqm; intros. rewrite unsigned_repr_eq. apply eqmod_mod. auto with ints.
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
  intros; red. unfold signed. set (y := unsigned x).
  case (zlt y half_modulus); intro.
  apply eqmod_refl. red; exists (-1); ring.
Qed.

Theorem unsigned_range:
  forall i, 0 <= unsigned i < modulus.
Proof.
  destruct i. simpl. omega.
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
  destruct i; simpl. unfold repr. apply mkint_eq.
  rewrite Z_mod_modulus_eq. apply Zmod_small; omega.
Qed.
Hint Resolve repr_unsigned: ints.

Lemma repr_signed:
  forall i, repr (signed i) = i.
Proof.
  intros. transitivity (repr (unsigned i)).
  apply eqm_samerepr. apply eqm_signed_unsigned. auto with ints.
Qed.
Hint Resolve repr_signed: ints.

Opaque repr.

Lemma eqm_repr_eq: forall x y, eqm x (unsigned y) -> repr x = y.
Proof.
  intros. rewrite <- (repr_unsigned y). apply eqm_samerepr; auto.
Qed.

Theorem unsigned_repr:
  forall z, 0 <= z <= max_unsigned -> unsigned (repr z) = z.
Proof.
  intros. rewrite unsigned_repr_eq.
  apply Zmod_small. unfold max_unsigned in H. omega.
Qed.
Hint Resolve unsigned_repr: ints.

Theorem signed_repr:
  forall z, min_signed <= z <= max_signed -> signed (repr z) = z.
Proof.
  intros. unfold signed. destruct (zle 0 z).
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

Theorem signed_positive:
  forall x, signed x >= 0 <-> unsigned x <= max_signed.
Proof.
  intros. unfold signed, max_signed.
  generalize (unsigned_range x) half_modulus_modulus half_modulus_pos; intros.
  destruct (zlt (unsigned x) half_modulus); omega.
Qed.

(** ** Properties of zero, one, minus one *)

Theorem unsigned_zero: unsigned zero = 0.
Proof.
  unfold zero; rewrite unsigned_repr_eq. apply Zmod_0_l.
Qed.

Theorem unsigned_one: unsigned one = 1.
Proof.
  unfold one; rewrite unsigned_repr_eq. apply Zmod_small. split. omega.
  unfold modulus. replace wordsize with (S(Init.Nat.pred wordsize)).
  rewrite two_power_nat_S. generalize (two_power_nat_pos (Init.Nat.pred wordsize)).
  omega.
  generalize wordsize_pos. unfold zwordsize. omega.
Qed.

Theorem unsigned_mone: unsigned mone = modulus - 1.
Proof.
  unfold mone; rewrite unsigned_repr_eq.
  replace (-1) with ((modulus - 1) + (-1) * modulus).
  rewrite Z_mod_plus_full. apply Zmod_small.
  generalize modulus_pos. omega. omega.
Qed.

Theorem signed_zero: signed zero = 0.
Proof.
  unfold signed. rewrite unsigned_zero. apply zlt_true. generalize half_modulus_pos; omega.
Qed.

Theorem signed_one: zwordsize > 1 -> signed one = 1.
Proof.
  intros. unfold signed. rewrite unsigned_one. apply zlt_true. 
  change 1 with (two_p 0). rewrite half_modulus_power. apply two_p_monotone_strict. omega. 
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
  unsigned iwordsize = zwordsize.
Proof.
  unfold iwordsize; rewrite unsigned_repr_eq. apply Zmod_small.
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

Theorem eq_signed:
  forall x y, eq x y = if zeq (signed x) (signed y) then true else false.
Proof.
  intros. predSpec eq eq_spec x y.
  subst x. rewrite zeq_true; auto.
  destruct (zeq (signed x) (signed y)); auto.
  elim H. rewrite <- (repr_signed x). rewrite <- (repr_signed y). congruence.
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
  rewrite Z.add_0_r. apply repr_unsigned.
Qed.

Theorem add_zero_l: forall x, add zero x = x.
Proof.
  intros. rewrite add_commut. apply add_zero.
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
  rewrite <- Z.add_assoc. auto with ints.
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

Theorem unsigned_add_carry:
  forall x y,
  unsigned (add x y) = unsigned x + unsigned y - unsigned (add_carry x y zero) * modulus.
Proof.
  intros.
  unfold add, add_carry. rewrite unsigned_zero. rewrite Z.add_0_r.
  rewrite unsigned_repr_eq.
  generalize (unsigned_range x) (unsigned_range y). intros.
  destruct (zlt (unsigned x + unsigned y) modulus).
  rewrite unsigned_zero. apply Zmod_unique with 0. omega. omega.
  rewrite unsigned_one. apply Zmod_unique with 1. omega. omega.
Qed.

Corollary unsigned_add_either:
  forall x y,
  unsigned (add x y) = unsigned x + unsigned y
  \/ unsigned (add x y) = unsigned x + unsigned y - modulus.
Proof.
  intros. rewrite unsigned_add_carry. unfold add_carry.
  rewrite unsigned_zero. rewrite Z.add_0_r.
  destruct (zlt (unsigned x + unsigned y) modulus).
  rewrite unsigned_zero. left; omega.
  rewrite unsigned_one. right; omega.
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

Theorem unsigned_sub_borrow:
  forall x y,
  unsigned (sub x y) = unsigned x - unsigned y + unsigned (sub_borrow x y zero) * modulus.
Proof.
  intros.
  unfold sub, sub_borrow. rewrite unsigned_zero. rewrite Z.sub_0_r.
  rewrite unsigned_repr_eq.
  generalize (unsigned_range x) (unsigned_range y). intros.
  destruct (zlt (unsigned x - unsigned y) 0).
  rewrite unsigned_one. apply Zmod_unique with (-1). omega. omega.
  rewrite unsigned_zero. apply Zmod_unique with 0. omega. omega.
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

Theorem mul_mone: forall x, mul x mone = neg x.
Proof.
  intros; unfold mul, neg. rewrite unsigned_mone.
  apply eqm_samerepr.
  replace (-unsigned x) with (0 - unsigned x) by omega.
  replace (unsigned x * (modulus - 1)) with (unsigned x * modulus - unsigned x) by ring.
  apply eqm_sub. exists (unsigned x). omega. apply eqm_refl.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  intros; unfold mul.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr. apply eqm_trans with ((x' * y') * z').
  auto with ints.
  rewrite <- Z.mul_assoc. auto with ints.
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
  apply eqm_refl2. rewrite Z.mul_comm. apply Z_div_mod_eq.
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

Lemma mods_divs_Euclid:
  forall x y, x = add (mul (divs x y) y) (mods x y).
Proof.
  intros. unfold add, mul, divs, mods.
  transitivity (repr (signed x)). auto with ints.
  apply eqm_samerepr.
  set (x' := signed x). set (y' := signed y).
  apply eqm_trans with ((Z.quot x' y') * y' + Z.rem x' y').
  apply eqm_refl2. rewrite Z.mul_comm. apply Z.quot_rem'.
  apply eqm_add; auto with ints.
  apply eqm_unsigned_repr_r. apply eqm_mult; auto with ints.
  unfold y'. apply eqm_signed_unsigned.
Qed.

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
Proof.
  intros.
  assert (forall a b c, a = add b c -> c = sub a b).
  intros. subst a. rewrite sub_add_l. rewrite sub_idem.
  rewrite add_commut. rewrite add_zero. auto.
  apply H. apply mods_divs_Euclid.
Qed.

Theorem divu_one:
  forall x, divu x one = x.
Proof.
  unfold divu; intros. rewrite unsigned_one. rewrite Zdiv_1_r. apply repr_unsigned.
Qed.

Theorem divs_one:
  forall x, zwordsize > 1 -> divs x one = x.
Proof.
  unfold divs; intros. rewrite signed_one. rewrite Z.quot_1_r. apply repr_signed. auto.
Qed.

Theorem modu_one:
  forall x, modu x one = zero.
Proof.
  intros. rewrite modu_divu. rewrite divu_one. rewrite mul_one. apply sub_idem.
  apply one_not_zero.
Qed.

Theorem divs_mone:
  forall x, divs x mone = neg x.
Proof.
  unfold divs, neg; intros.
  rewrite signed_mone.
  replace (Z.quot (signed x) (-1)) with (- (signed x)).
  apply eqm_samerepr. apply eqm_neg. apply eqm_signed_unsigned.
  set (x' := signed x).
  set (one := 1).
  change (-1) with (- one). rewrite Zquot_opp_r.
  assert (Z.quot x' one = x').
  symmetry. apply Zquot_unique_full with 0. red.
  change (Z.abs one) with 1.
  destruct (zle 0 x'). left. omega. right. omega.
  unfold one; ring.
  congruence.
Qed.

Theorem mods_mone:
  forall x, mods x mone = zero.
Proof.
  intros. rewrite mods_divs. rewrite divs_mone.
  rewrite <- neg_mul_distr_l. rewrite mul_mone. rewrite neg_involutive. apply sub_idem.
Qed.

Theorem divmodu2_divu_modu:
  forall n d,
  d <> zero -> divmodu2 zero n d = Some (divu n d, modu n d).
Proof.
  unfold divmodu2, divu, modu; intros.
  rewrite dec_eq_false by auto.
  set (N := unsigned zero * modulus + unsigned n).
  assert (E1: unsigned n = N) by (unfold N; rewrite unsigned_zero; ring). rewrite ! E1.
  set (D := unsigned d).
  set (Q := N / D); set (R := N mod D).
  assert (E2: Z.div_eucl N D = (Q, R)).
  { unfold Q, R, Z.div, Z.modulo. destruct (Z.div_eucl N D); auto. }
  rewrite E2. rewrite zle_true. auto.
  assert (unsigned d <> 0).
  { red; intros. elim H. rewrite <- (repr_unsigned d). rewrite H0; auto. }
  assert (0 < D).
  { unfold D. generalize (unsigned_range d); intros. omega. }
  assert (0 <= Q <= max_unsigned).
  { unfold Q. apply Zdiv_interval_2.
    rewrite <- E1; apply unsigned_range_2.
    omega. unfold max_unsigned; generalize modulus_pos; omega. omega. }
  omega.
Qed.

Lemma unsigned_signed:
  forall n, unsigned n = if lt n zero then signed n + modulus else signed n.
Proof.
  intros. unfold lt. rewrite signed_zero. unfold signed.
  generalize (unsigned_range n). rewrite half_modulus_modulus. intros.
  destruct (zlt (unsigned n) half_modulus).
- rewrite zlt_false by omega. auto.
- rewrite zlt_true by omega. ring.
Qed.

Theorem divmods2_divs_mods:
  forall n d,
  d <> zero -> n <> repr min_signed \/ d <> mone ->
  divmods2 (if lt n zero then mone else zero) n d = Some (divs n d, mods n d).
Proof.
  unfold divmods2, divs, mods; intros.
  rewrite dec_eq_false by auto.
  set (N := signed (if lt n zero then mone else zero) * modulus + unsigned n).
  set (D := signed d).
  assert (D <> 0).
  { unfold D; red; intros. elim H. rewrite <- (repr_signed d). rewrite H1; auto. }
  assert (N = signed n).
  { unfold N. rewrite unsigned_signed. destruct (lt n zero).
    rewrite signed_mone. ring.
    rewrite signed_zero. ring. }
  set (Q := Z.quot N D); set (R := Z.rem N D).
  assert (E2: Z.quotrem N D = (Q, R)).
  { unfold Q, R, Z.quot, Z.rem. destruct (Z.quotrem N D); auto. }
  rewrite E2.
  assert (min_signed <= N <= max_signed) by (rewrite H2; apply signed_range).
  assert (min_signed <= Q <= max_signed).
  { unfold Q. destruct (zeq D 1); [ | destruct (zeq D (-1))].
  - (* D = 1 *)
    rewrite e. rewrite Z.quot_1_r; auto.
  - (* D = -1 *)
    rewrite e. change (-1) with (Z.opp 1). rewrite Z.quot_opp_r by omega.
    rewrite Z.quot_1_r.
    assert (N <> min_signed).
    { red; intros; destruct H0.
    + elim H0. rewrite <- (repr_signed n). rewrite <- H2. rewrite H4. auto.
    + elim H0. rewrite <- (repr_signed d). unfold D in e; rewrite e; auto. }
    unfold min_signed, max_signed in *. omega.
  - (* |D| > 1 *)
    assert (Z.abs (Z.quot N D) < half_modulus).
    { rewrite <- Z.quot_abs by omega. apply Zquot_lt_upper_bound.
      xomega. xomega.
      apply Z.le_lt_trans with (half_modulus * 1).
      rewrite Z.mul_1_r. unfold min_signed, max_signed in H3; xomega.
      apply Zmult_lt_compat_l. generalize half_modulus_pos; omega. xomega. }
    rewrite Z.abs_lt in H4.
    unfold min_signed, max_signed; omega.
  }
  unfold proj_sumbool; rewrite ! zle_true by omega; simpl.
  unfold Q, R; rewrite H2; auto.
Qed.

(** ** Bit-level properties *)

(** ** Properties of bit-level operations over [Z] *)

Remark Ztestbit_0: forall n, Z.testbit 0 n = false.
Proof Z.testbit_0_l.

Remark Ztestbit_1: forall n, Z.testbit 1 n = zeq n 0.
Proof.
  intros. destruct n; simpl; auto.
Qed.

Remark Ztestbit_m1: forall n, 0 <= n -> Z.testbit (-1) n = true.
Proof.
  intros. destruct n; simpl; auto.
Qed.

Remark Zshiftin_spec:
  forall b x, Zshiftin b x = 2 * x + (if b then 1 else 0).
Proof.
  unfold Zshiftin; intros. destruct b.
  - rewrite Z.succ_double_spec. omega.
  - rewrite Z.double_spec. omega.
Qed.

Remark Zshiftin_inj:
  forall b1 x1 b2 x2,
  Zshiftin b1 x1 = Zshiftin b2 x2 -> b1 = b2 /\ x1 = x2.
Proof.
  intros. rewrite !Zshiftin_spec in H.
  destruct b1; destruct b2.
  split; [auto|omega].
  omegaContradiction.
  omegaContradiction.
  split; [auto|omega].
Qed.

Remark Zdecomp:
  forall x, x = Zshiftin (Z.odd x) (Z.div2 x).
Proof.
  intros. destruct x; simpl.
  - auto.
  - destruct p; auto.
  - destruct p; auto. simpl. rewrite Pos.pred_double_succ. auto.
Qed.

Remark Ztestbit_shiftin:
  forall b x n,
  0 <= n ->
  Z.testbit (Zshiftin b x) n = if zeq n 0 then b else Z.testbit x (Z.pred n).
Proof.
  intros. rewrite Zshiftin_spec. destruct (zeq n 0).
  - subst n. destruct b.
    + apply Z.testbit_odd_0.
    + rewrite Z.add_0_r. apply Z.testbit_even_0.
  - assert (0 <= Z.pred n) by omega.
    set (n' := Z.pred n) in *.
    replace n with (Z.succ n') by (unfold n'; omega).
    destruct b.
    + apply Z.testbit_odd_succ; auto.
    + rewrite Z.add_0_r. apply Z.testbit_even_succ; auto.
Qed.

Remark Ztestbit_shiftin_base:
  forall b x, Z.testbit (Zshiftin b x) 0 = b.
Proof.
  intros. rewrite Ztestbit_shiftin. apply zeq_true. omega.
Qed.

Remark Ztestbit_shiftin_succ:
  forall b x n, 0 <= n -> Z.testbit (Zshiftin b x) (Z.succ n) = Z.testbit x n.
Proof.
  intros. rewrite Ztestbit_shiftin. rewrite zeq_false. rewrite Z.pred_succ. auto.
  omega. omega.
Qed.

Remark Ztestbit_eq:
  forall n x, 0 <= n ->
  Z.testbit x n = if zeq n 0 then Z.odd x else Z.testbit (Z.div2 x) (Z.pred n).
Proof.
  intros. rewrite (Zdecomp x) at 1. apply Ztestbit_shiftin; auto.
Qed.

Remark Ztestbit_base:
  forall x, Z.testbit x 0 = Z.odd x.
Proof.
  intros. rewrite Ztestbit_eq. apply zeq_true. omega.
Qed.

Remark Ztestbit_succ:
  forall n x, 0 <= n -> Z.testbit x (Z.succ n) = Z.testbit (Z.div2 x) n.
Proof.
  intros. rewrite Ztestbit_eq. rewrite zeq_false. rewrite Z.pred_succ. auto.
  omega. omega.
Qed.

Lemma eqmod_same_bits:
  forall n x y,
  (forall i, 0 <= i < Z.of_nat n -> Z.testbit x i = Z.testbit y i) ->
  eqmod (two_power_nat n) x y.
Proof.
  induction n; intros.
  - change (two_power_nat 0) with 1. exists (x-y); ring.
  - rewrite two_power_nat_S.
    assert (eqmod (two_power_nat n) (Z.div2 x) (Z.div2 y)).
      apply IHn. intros. rewrite <- !Ztestbit_succ. apply H. rewrite Nat2Z.inj_succ; omega.
      omega. omega.
  destruct H0 as [k EQ].
  exists k. rewrite (Zdecomp x). rewrite (Zdecomp y).
  replace (Z.odd y) with (Z.odd x).
  rewrite EQ. rewrite !Zshiftin_spec. ring.
  exploit (H 0). rewrite Nat2Z.inj_succ; omega.
  rewrite !Ztestbit_base. auto.
Qed.

Lemma eqm_same_bits:
  forall x y,
  (forall i, 0 <= i < zwordsize -> Z.testbit x i = Z.testbit y i) ->
  eqm x y.
Proof (eqmod_same_bits wordsize).

Lemma same_bits_eqmod:
  forall n x y i,
  eqmod (two_power_nat n) x y -> 0 <= i < Z.of_nat n ->
  Z.testbit x i = Z.testbit y i.
Proof.
  induction n; intros.
  - simpl in H0. omegaContradiction.
  - rewrite Nat2Z.inj_succ in H0. rewrite two_power_nat_S in H.
    rewrite !(Ztestbit_eq i); intuition.
    destruct H as [k EQ].
    assert (EQ': Zshiftin (Z.odd x) (Z.div2 x) =
                 Zshiftin (Z.odd y) (k * two_power_nat n + Z.div2 y)).
    {
      rewrite (Zdecomp x) in EQ. rewrite (Zdecomp y) in EQ.
      rewrite EQ. rewrite !Zshiftin_spec. ring.
    }
    exploit Zshiftin_inj; eauto. intros [A B].
    destruct (zeq i 0).
    + auto.
    + apply IHn. exists k; auto. omega.
Qed.

Lemma same_bits_eqm:
  forall x y i,
  eqm x y ->
  0 <= i < zwordsize ->
  Z.testbit x i = Z.testbit y i.
Proof (same_bits_eqmod wordsize).

Remark two_power_nat_infinity:
  forall x, 0 <= x -> exists n, x < two_power_nat n.
Proof.
  intros x0 POS0; pattern x0; apply natlike_ind; auto.
  exists O. compute; auto.
  intros. destruct H0 as [n LT]. exists (S n). rewrite two_power_nat_S.
  generalize (two_power_nat_pos n). omega.
Qed.

Lemma equal_same_bits:
  forall x y,
  (forall i, 0 <= i -> Z.testbit x i = Z.testbit y i) ->
  x = y.
Proof.
  intros.
  set (z := if zlt x y then y - x else x - y).
  assert (0 <= z).
    unfold z; destruct (zlt x y); omega.
  exploit (two_power_nat_infinity z); auto. intros [n LT].
  assert (eqmod (two_power_nat n) x y).
    apply eqmod_same_bits. intros. apply H. tauto.
  assert (eqmod (two_power_nat n) z 0).
    unfold z. destruct (zlt x y).
    replace 0 with (y - y) by omega. apply eqmod_sub. apply eqmod_refl. auto.
    replace 0 with (x - x) by omega. apply eqmod_sub. apply eqmod_refl. apply eqmod_sym; auto.
  assert (z = 0).
    apply eqmod_small_eq with (two_power_nat n). auto. omega. generalize (two_power_nat_pos n); omega.
  unfold z in H3. destruct (zlt x y); omega.
Qed.

Lemma Z_one_complement:
  forall i, 0 <= i ->
  forall x, Z.testbit (-x-1) i = negb (Z.testbit x i).
Proof.
  intros i0 POS0. pattern i0. apply Zlt_0_ind; auto.
  intros i IND POS x.
  rewrite (Zdecomp x). set (y := Z.div2 x).
  replace (- Zshiftin (Z.odd x) y - 1)
     with (Zshiftin (negb (Z.odd x)) (- y - 1)).
  rewrite !Ztestbit_shiftin; auto.
  destruct (zeq i 0). auto. apply IND. omega.
  rewrite !Zshiftin_spec. destruct (Z.odd x); simpl negb; ring.
Qed.

Lemma Ztestbit_above:
  forall n x i,
  0 <= x < two_power_nat n ->
  i >= Z.of_nat n ->
  Z.testbit x i = false.
Proof.
  induction n; intros.
  - change (two_power_nat 0) with 1 in H.
    replace x with 0 by omega.
    apply Z.testbit_0_l.
  - rewrite Nat2Z.inj_succ in H0. rewrite Ztestbit_eq. rewrite zeq_false.
    apply IHn. rewrite two_power_nat_S in H. rewrite (Zdecomp x) in H.
    rewrite Zshiftin_spec in H. destruct (Z.odd x); omega.
    omega. omega. omega.
Qed.

Lemma Ztestbit_above_neg:
  forall n x i,
  -two_power_nat n <= x < 0 ->
  i >= Z.of_nat n ->
  Z.testbit x i = true.
Proof.
  intros. set (y := -x-1).
  assert (Z.testbit y i = false).
    apply Ztestbit_above with n.
    unfold y; omega. auto.
  unfold y in H1. rewrite Z_one_complement in H1.
  change true with (negb false). rewrite <- H1. rewrite negb_involutive; auto.
  omega.
Qed.

Lemma Zsign_bit:
  forall n x,
  0 <= x < two_power_nat (S n) ->
  Z.testbit x (Z.of_nat n) = if zlt x (two_power_nat n) then false else true.
Proof.
  induction n; intros.
  - change (two_power_nat 1) with 2 in H.
    assert (x = 0 \/ x = 1) by omega.
    destruct H0; subst x; reflexivity.
  - rewrite Nat2Z.inj_succ. rewrite Ztestbit_eq. rewrite zeq_false. rewrite Z.pred_succ.
    rewrite IHn. rewrite two_power_nat_S.
    destruct (zlt (Z.div2 x) (two_power_nat n)); rewrite (Zdecomp x); rewrite Zshiftin_spec.
    rewrite zlt_true. auto. destruct (Z.odd x); omega.
    rewrite zlt_false. auto. destruct (Z.odd x); omega.
    rewrite (Zdecomp x) in H; rewrite Zshiftin_spec in H.
    rewrite two_power_nat_S in H. destruct (Z.odd x); omega.
    omega. omega.
Qed.

Lemma Zshiftin_ind:
  forall (P: Z -> Prop),
  P 0 ->
  (forall b x, 0 <= x -> P x -> P (Zshiftin b x)) ->
  forall x, 0 <= x -> P x.
Proof.
  intros. destruct x.
  - auto.
  - induction p.
    + change (P (Zshiftin true (Z.pos p))). auto.
    + change (P (Zshiftin false (Z.pos p))). auto.
    + change (P (Zshiftin true 0)). apply H0. omega. auto.
  - compute in H1. intuition congruence.
Qed.

Lemma Zshiftin_pos_ind:
  forall (P: Z -> Prop),
  P 1 ->
  (forall b x, 0 < x -> P x -> P (Zshiftin b x)) ->
  forall x, 0 < x -> P x.
Proof.
  intros. destruct x; simpl in H1; try discriminate.
  induction p.
    + change (P (Zshiftin true (Z.pos p))). auto.
    + change (P (Zshiftin false (Z.pos p))). auto.
    + auto.
Qed.

Lemma Ztestbit_le:
  forall x y,
  0 <= y ->
  (forall i, 0 <= i -> Z.testbit x i = true -> Z.testbit y i = true) ->
  x <= y.
Proof.
  intros x y0 POS0; revert x; pattern y0; apply Zshiftin_ind; auto; intros.
  - replace x with 0. omega. apply equal_same_bits; intros.
    rewrite Ztestbit_0. destruct (Z.testbit x i) as [] eqn:E; auto.
    exploit H; eauto. rewrite Ztestbit_0. auto.
  - assert (Z.div2 x0 <= x).
    { apply H0. intros. exploit (H1 (Z.succ i)).
        omega. rewrite Ztestbit_succ; auto. rewrite Ztestbit_shiftin_succ; auto.
    }
    rewrite (Zdecomp x0). rewrite !Zshiftin_spec.
    destruct (Z.odd x0) as [] eqn:E1; destruct b as [] eqn:E2; try omega.
    exploit (H1 0). omega. rewrite Ztestbit_base; auto.
    rewrite Ztestbit_shiftin_base. congruence.
Qed.

(** ** Bit-level reasoning over type [int] *)

Definition testbit (x: int) (i: Z) : bool := Z.testbit (unsigned x) i.

Lemma testbit_repr:
  forall x i,
  0 <= i < zwordsize ->
  testbit (repr x) i = Z.testbit x i.
Proof.
  intros. unfold testbit. apply same_bits_eqm; auto with ints.
Qed.

Lemma same_bits_eq:
  forall x y,
  (forall i, 0 <= i < zwordsize -> testbit x i = testbit y i) ->
  x = y.
Proof.
  intros. rewrite <- (repr_unsigned x). rewrite <- (repr_unsigned y).
  apply eqm_samerepr. apply eqm_same_bits. auto.
Qed.

Lemma bits_above:
  forall x i, i >= zwordsize -> testbit x i = false.
Proof.
  intros. apply Ztestbit_above with wordsize; auto. apply unsigned_range.
Qed.

Lemma bits_zero:
  forall i, testbit zero i = false.
Proof.
  intros. unfold testbit. rewrite unsigned_zero. apply Ztestbit_0.
Qed.

Remark bits_one: forall n, testbit one n = zeq n 0.
Proof.
  unfold testbit; intros. rewrite unsigned_one. apply Ztestbit_1.
Qed.

Lemma bits_mone:
  forall i, 0 <= i < zwordsize -> testbit mone i = true.
Proof.
  intros. unfold mone. rewrite testbit_repr; auto. apply Ztestbit_m1. omega.
Qed.

Hint Rewrite bits_zero bits_mone : ints.

Ltac bit_solve :=
  intros; apply same_bits_eq; intros; autorewrite with ints; auto with bool.

Lemma sign_bit_of_unsigned:
  forall x, testbit x (zwordsize - 1) = if zlt (unsigned x) half_modulus then false else true.
Proof.
  intros. unfold testbit.
  set (ws1 := Init.Nat.pred wordsize).
  assert (zwordsize - 1 = Z.of_nat ws1).
    unfold zwordsize, ws1, wordsize.
    destruct WS.wordsize as [] eqn:E.
    elim WS.wordsize_not_zero; auto.
    rewrite Nat2Z.inj_succ. simpl. omega.
  assert (half_modulus = two_power_nat ws1).
    rewrite two_power_nat_two_p. rewrite <- H. apply half_modulus_power.
  rewrite H; rewrite H0.
  apply Zsign_bit. rewrite two_power_nat_S. rewrite <- H0.
  rewrite <- half_modulus_modulus. apply unsigned_range.
Qed.

Lemma bits_signed:
  forall x i, 0 <= i ->
  Z.testbit (signed x) i = testbit x (if zlt i zwordsize then i else zwordsize - 1).
Proof.
  intros.
  destruct (zlt i zwordsize).
  - apply same_bits_eqm. apply eqm_signed_unsigned. omega.
  - unfold signed. rewrite sign_bit_of_unsigned. destruct (zlt (unsigned x) half_modulus).
    + apply Ztestbit_above with wordsize. apply unsigned_range. auto.
    + apply Ztestbit_above_neg with wordsize.
      fold modulus. generalize (unsigned_range x). omega. auto.
Qed.

Lemma bits_le:
  forall x y,
  (forall i, 0 <= i < zwordsize -> testbit x i = true -> testbit y i = true) ->
  unsigned x <= unsigned y.
Proof.
  intros. apply Ztestbit_le. generalize (unsigned_range y); omega.
  intros. fold (testbit y i). destruct (zlt i zwordsize).
  apply H. omega. auto.
  fold (testbit x i) in H1. rewrite bits_above in H1; auto. congruence.
Qed.

(** ** Properties of bitwise and, or, xor *)

Lemma bits_and:
  forall x y i, 0 <= i < zwordsize ->
  testbit (and x y) i = testbit x i && testbit y i.
Proof.
  intros. unfold and. rewrite testbit_repr; auto. rewrite Z.land_spec; intuition.
Qed.

Lemma bits_or:
  forall x y i, 0 <= i < zwordsize ->
  testbit (or x y) i = testbit x i || testbit y i.
Proof.
  intros. unfold or. rewrite testbit_repr; auto. rewrite Z.lor_spec; intuition.
Qed.

Lemma bits_xor:
  forall x y i, 0 <= i < zwordsize ->
  testbit (xor x y) i = xorb (testbit x i) (testbit y i).
Proof.
  intros. unfold xor. rewrite testbit_repr; auto. rewrite Z.lxor_spec; intuition.
Qed.

Lemma bits_not:
  forall x i, 0 <= i < zwordsize ->
  testbit (not x) i = negb (testbit x i).
Proof.
  intros. unfold not. rewrite bits_xor; auto. rewrite bits_mone; auto.
Qed.

Hint Rewrite bits_and bits_or bits_xor bits_not: ints.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  bit_solve.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  bit_solve.
Qed.

Theorem and_zero: forall x, and x zero = zero.
Proof.
  bit_solve. apply andb_b_false.
Qed.

Corollary and_zero_l: forall x, and zero x = zero.
Proof.
  intros. rewrite and_commut. apply and_zero.
Qed.

Theorem and_mone: forall x, and x mone = x.
Proof.
  bit_solve. apply andb_b_true.
Qed.

Corollary and_mone_l: forall x, and mone x = x.
Proof.
  intros. rewrite and_commut. apply and_mone.
Qed.

Theorem and_idem: forall x, and x x = x.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  bit_solve.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  bit_solve.
Qed.

Theorem or_zero: forall x, or x zero = x.
Proof.
  bit_solve.
Qed.

Corollary or_zero_l: forall x, or zero x = x.
Proof.
  intros. rewrite or_commut. apply or_zero.
Qed.

Theorem or_mone: forall x, or x mone = mone.
Proof.
  bit_solve.
Qed.

Theorem or_idem: forall x, or x x = x.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Theorem and_or_distrib:
  forall x y z,
  and x (or y z) = or (and x y) (and x z).
Proof.
  bit_solve. apply demorgan1.
Qed.

Corollary and_or_distrib_l:
  forall x y z,
  and (or x y) z = or (and x z) (and y z).
Proof.
  intros. rewrite (and_commut (or x y)). rewrite and_or_distrib. f_equal; apply and_commut.
Qed.

Theorem or_and_distrib:
  forall x y z,
  or x (and y z) = and (or x y) (or x z).
Proof.
  bit_solve. apply orb_andb_distrib_r.
Qed.

Corollary or_and_distrib_l:
  forall x y z,
  or (and x y) z = and (or x z) (or y z).
Proof.
  intros. rewrite (or_commut (and x y)). rewrite or_and_distrib. f_equal; apply or_commut.
Qed.

Theorem and_or_absorb: forall x y, and x (or x y) = x.
Proof.
  bit_solve.
  assert (forall a b, a && (a || b) = a) by destr_bool.
  auto.
Qed.

Theorem or_and_absorb: forall x y, or x (and x y) = x.
Proof.
  bit_solve.
  assert (forall a b, a || (a && b) = a) by destr_bool.
  auto.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  bit_solve. apply xorb_comm.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  bit_solve. apply xorb_assoc.
Qed.

Theorem xor_zero: forall x, xor x zero = x.
Proof.
  bit_solve. apply xorb_false.
Qed.

Corollary xor_zero_l: forall x, xor zero x = x.
Proof.
  intros. rewrite xor_commut. apply xor_zero.
Qed.

Theorem xor_idem: forall x, xor x x = zero.
Proof.
  bit_solve. apply xorb_nilpotent.
Qed.

Theorem xor_zero_one: xor zero one = one.
Proof. rewrite xor_commut. apply xor_zero. Qed.

Theorem xor_one_one: xor one one = zero.
Proof. apply xor_idem. Qed.

Theorem xor_zero_equal: forall x y, xor x y = zero -> x = y.
Proof.
  intros. apply same_bits_eq; intros.
  assert (xorb (testbit x i) (testbit y i) = false).
    rewrite <- bits_xor; auto. rewrite H. apply bits_zero.
  destruct (testbit x i); destruct (testbit y i); reflexivity || discriminate.
Qed.

Theorem xor_is_zero: forall x y, eq (xor x y) zero = eq x y.
Proof.
  intros. predSpec eq eq_spec (xor x y) zero.
- apply xor_zero_equal in H. subst y. rewrite eq_true; auto. 
- predSpec eq eq_spec x y.
+ elim H; subst y; apply xor_idem. 
+ auto.
Qed. 

Theorem and_xor_distrib:
  forall x y z,
  and x (xor y z) = xor (and x y) (and x z).
Proof.
  bit_solve.
  assert (forall a b c, a && (xorb b c) = xorb (a && b) (a && c)) by destr_bool.
  auto.
Qed.

Theorem and_le:
  forall x y, unsigned (and x y) <= unsigned x.
Proof.
  intros. apply bits_le; intros.
  rewrite bits_and in H0; auto. rewrite andb_true_iff in H0. tauto.
Qed.

Theorem or_le:
  forall x y, unsigned x <= unsigned (or x y).
Proof.
  intros. apply bits_le; intros.
  rewrite bits_or; auto. rewrite H0; auto.
Qed.

(** Properties of bitwise complement.*)

Theorem not_involutive:
  forall (x: int), not (not x) = x.
Proof.
  intros. unfold not. rewrite xor_assoc. rewrite xor_idem. apply xor_zero.
Qed.

Theorem not_zero:
  not zero = mone.
Proof.
  unfold not. rewrite xor_commut. apply xor_zero.
Qed.

Theorem not_mone:
  not mone = zero.
Proof.
  rewrite <- (not_involutive zero). symmetry. decEq. apply not_zero.
Qed.

Theorem not_or_and_not:
  forall x y, not (or x y) = and (not x) (not y).
Proof.
  bit_solve. apply negb_orb.
Qed.

Theorem not_and_or_not:
  forall x y, not (and x y) = or (not x) (not y).
Proof.
  bit_solve. apply negb_andb.
Qed.

Theorem and_not_self:
  forall x, and x (not x) = zero.
Proof.
  bit_solve.
Qed.

Theorem or_not_self:
  forall x, or x (not x) = mone.
Proof.
  bit_solve.
Qed.

Theorem xor_not_self:
  forall x, xor x (not x) = mone.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Lemma unsigned_not:
  forall x, unsigned (not x) = max_unsigned - unsigned x.
Proof.
  intros. transitivity (unsigned (repr(-unsigned x - 1))).
  f_equal. bit_solve. rewrite testbit_repr; auto. symmetry. apply Z_one_complement. omega.
  rewrite unsigned_repr_eq. apply Zmod_unique with (-1).
  unfold max_unsigned. omega.
  generalize (unsigned_range x). unfold max_unsigned. omega.
Qed.

Theorem not_neg:
  forall x, not x = add (neg x) mone.
Proof.
  bit_solve.
  rewrite <- (repr_unsigned x) at 1. unfold add.
  rewrite !testbit_repr; auto.
  transitivity (Z.testbit (-unsigned x - 1) i).
  symmetry. apply Z_one_complement. omega.
  apply same_bits_eqm; auto.
  replace (-unsigned x - 1) with (-unsigned x + (-1)) by omega.
  apply eqm_add.
  unfold neg. apply eqm_unsigned_repr.
  rewrite unsigned_mone. exists (-1). ring.
Qed.

Theorem neg_not:
  forall x, neg x = add (not x) one.
Proof.
  intros. rewrite not_neg. rewrite add_assoc.
  replace (add mone one) with zero. rewrite add_zero. auto.
  apply eqm_samerepr. rewrite unsigned_mone. rewrite unsigned_one.
  exists (-1). ring.
Qed.

Theorem sub_add_not:
  forall x y, sub x y = add (add x (not y)) one.
Proof.
  intros. rewrite sub_add_opp. rewrite neg_not.
  rewrite ! add_assoc. auto.
Qed.

Theorem sub_add_not_3:
  forall x y b,
  b = zero \/ b = one ->
  sub (sub x y) b = add (add x (not y)) (xor b one).
Proof.
  intros. rewrite ! sub_add_not. rewrite ! add_assoc. f_equal. f_equal.
  rewrite <- neg_not. rewrite <- sub_add_opp. destruct H; subst b.
  rewrite xor_zero_l. rewrite sub_zero_l. auto.
  rewrite xor_idem. rewrite sub_idem. auto.
Qed.

Theorem sub_borrow_add_carry:
  forall x y b,
  b = zero \/ b = one ->
  sub_borrow x y b = xor (add_carry x (not y) (xor b one)) one.
Proof.
  intros. unfold sub_borrow, add_carry. rewrite unsigned_not.
  replace (unsigned (xor b one)) with (1 - unsigned b).
  destruct (zlt (unsigned x - unsigned y - unsigned b)).
  rewrite zlt_true. rewrite xor_zero_l; auto.
  unfold max_unsigned; omega.
  rewrite zlt_false. rewrite xor_idem; auto.
  unfold max_unsigned; omega.
  destruct H; subst b.
  rewrite xor_zero_l. rewrite unsigned_one, unsigned_zero; auto.
  rewrite xor_idem. rewrite unsigned_one, unsigned_zero; auto.
Qed.

(** Connections between [add] and bitwise logical operations. *)

Lemma Z_add_is_or:
  forall i, 0 <= i ->
  forall x y,
  (forall j, 0 <= j <= i -> Z.testbit x j && Z.testbit y j = false) ->
  Z.testbit (x + y) i = Z.testbit x i || Z.testbit y i.
Proof.
  intros i0 POS0. pattern i0. apply Zlt_0_ind; auto.
  intros i IND POS x y EXCL.
  rewrite (Zdecomp x) in *. rewrite (Zdecomp y) in *.
  transitivity (Z.testbit (Zshiftin (Z.odd x || Z.odd y) (Z.div2 x + Z.div2 y)) i).
  - f_equal. rewrite !Zshiftin_spec.
    exploit (EXCL 0). omega. rewrite !Ztestbit_shiftin_base. intros.
Opaque Z.mul.
    destruct (Z.odd x); destruct (Z.odd y); simpl in *; discriminate || ring.
  - rewrite !Ztestbit_shiftin; auto.
    destruct (zeq i 0).
    + auto.
    + apply IND. omega. intros.
      exploit (EXCL (Z.succ j)). omega.
      rewrite !Ztestbit_shiftin_succ. auto.
      omega. omega.
Qed.

Theorem add_is_or:
  forall x y,
  and x y = zero ->
  add x y = or x y.
Proof.
  bit_solve. unfold add. rewrite testbit_repr; auto.
  apply Z_add_is_or. omega.
  intros.
  assert (testbit (and x y) j = testbit zero j) by congruence.
  autorewrite with ints in H2. assumption. omega.
Qed.

Theorem xor_is_or:
  forall x y, and x y = zero -> xor x y = or x y.
Proof.
  bit_solve.
  assert (testbit (and x y) i = testbit zero i) by congruence.
  autorewrite with ints in H1; auto.
  destruct (testbit x i); destruct (testbit y i); simpl in *; congruence.
Qed.

Theorem add_is_xor:
  forall x y,
  and x y = zero ->
  add x y = xor x y.
Proof.
  intros. rewrite xor_is_or; auto. apply add_is_or; auto.
Qed.

Theorem add_and:
  forall x y z,
  and y z = zero ->
  add (and x y) (and x z) = and x (or y z).
Proof.
  intros. rewrite add_is_or.
  rewrite and_or_distrib; auto.
  rewrite (and_commut x y).
  rewrite and_assoc.
  repeat rewrite <- (and_assoc x).
  rewrite (and_commut (and x x)).
  rewrite <- and_assoc.
  rewrite H. rewrite and_commut. apply and_zero.
Qed.

(** ** Properties of shifts *)

Lemma bits_shl:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shl x y) i =
  if zlt i (unsigned y) then false else testbit x (i - unsigned y).
Proof.
  intros. unfold shl. rewrite testbit_repr; auto.
  destruct (zlt i (unsigned y)).
  apply Z.shiftl_spec_low. auto.
  apply Z.shiftl_spec_high. omega. omega.
Qed.

Lemma bits_shru:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shru x y) i =
  if zlt (i + unsigned y) zwordsize then testbit x (i + unsigned y) else false.
Proof.
  intros. unfold shru. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. fold (testbit x (i + unsigned y)).
  destruct (zlt (i + unsigned y) zwordsize).
  auto.
  apply bits_above; auto.
  omega.
Qed.

Lemma bits_shr:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shr x y) i =
  testbit x (if zlt (i + unsigned y) zwordsize then i + unsigned y else zwordsize - 1).
Proof.
  intros. unfold shr. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. apply bits_signed.
  generalize (unsigned_range y); omega.
  omega.
Qed.

Hint Rewrite bits_shl bits_shru bits_shr: ints.

Theorem shl_zero: forall x, shl x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_false. f_equal; omega. omega.
Qed.

Lemma bitwise_binop_shl:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f' false false = false ->
  f (shl x n) (shl y n) = shl (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shl; auto.
  destruct (zlt i (unsigned n)); auto.
  rewrite H; auto. generalize (unsigned_range n); omega.
Qed.

Theorem and_shl:
  forall x y n,
  and (shl x n) (shl y n) = shl (and x y) n.
Proof.
  intros. apply bitwise_binop_shl with andb. exact bits_and. auto.
Qed.

Theorem or_shl:
  forall x y n,
  or (shl x n) (shl y n) = shl (or x y) n.
Proof.
  intros. apply bitwise_binop_shl with orb. exact bits_or. auto.
Qed.

Theorem xor_shl:
  forall x y n,
  xor (shl x n) (shl y n) = shl (xor x y) n.
Proof.
  intros. apply bitwise_binop_shl with xorb. exact bits_xor. auto.
Qed.

Lemma ltu_inv:
  forall x y, ltu x y = true -> 0 <= unsigned x < unsigned y.
Proof.
  unfold ltu; intros. destruct (zlt (unsigned x) (unsigned y)).
  split; auto. generalize (unsigned_range x); omega.
  discriminate.
Qed.

Lemma ltu_iwordsize_inv:
  forall x, ltu x iwordsize = true -> 0 <= unsigned x < zwordsize.
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize. auto.
Qed.

Theorem shl_shl:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shl (shl x y) z = shl x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; omega.
  apply same_bits_eq; intros.
  rewrite bits_shl; auto.
  destruct (zlt i (unsigned z)).
  - rewrite bits_shl; auto. rewrite zlt_true. auto. omega.
  - rewrite bits_shl. destruct (zlt (i - unsigned z) (unsigned y)).
    + rewrite bits_shl; auto. rewrite zlt_true. auto. omega.
    + rewrite bits_shl; auto. rewrite zlt_false. f_equal. omega. omega.
    + omega.
Qed.

Theorem sub_ltu:
  forall x y,
    ltu x y = true ->
    0 <= unsigned y - unsigned x <= unsigned y.
Proof.
  intros.
  generalize (ltu_inv x y H). intros .
  split. omega. omega.
Qed.

Theorem shru_zero: forall x, shru x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_true. f_equal; omega. omega.
Qed.

Lemma bitwise_binop_shru:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f' false false = false ->
  f (shru x n) (shru y n) = shru (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shru; auto.
  destruct (zlt (i + unsigned n) zwordsize); auto.
  rewrite H; auto. generalize (unsigned_range n); omega.
Qed.

Theorem and_shru:
  forall x y n,
  and (shru x n) (shru y n) = shru (and x y) n.
Proof.
  intros. apply bitwise_binop_shru with andb; auto. exact bits_and.
Qed.

Theorem or_shru:
  forall x y n,
  or (shru x n) (shru y n) = shru (or x y) n.
Proof.
  intros. apply bitwise_binop_shru with orb; auto. exact bits_or.
Qed.

Theorem xor_shru:
  forall x y n,
  xor (shru x n) (shru y n) = shru (xor x y) n.
Proof.
  intros. apply bitwise_binop_shru with xorb; auto. exact bits_xor.
Qed.

Theorem shru_shru:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shru (shru x y) z = shru x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; omega.
  apply same_bits_eq; intros.
  rewrite bits_shru; auto.
  destruct (zlt (i + unsigned z) zwordsize).
  - rewrite bits_shru. destruct (zlt (i + unsigned z + unsigned y) zwordsize).
    + rewrite bits_shru; auto. rewrite zlt_true. f_equal. omega. omega.
    + rewrite bits_shru; auto. rewrite zlt_false. auto. omega.
    + omega.
  - rewrite bits_shru; auto. rewrite zlt_false. auto. omega.
Qed.

Theorem shr_zero: forall x, shr x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_true. f_equal; omega. omega.
Qed.

Lemma bitwise_binop_shr:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f (shr x n) (shr y n) = shr (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shr; auto.
  rewrite H; auto.
  destruct (zlt (i + unsigned n) zwordsize).
  generalize (unsigned_range n); omega.
  omega.
Qed.

Theorem and_shr:
  forall x y n,
  and (shr x n) (shr y n) = shr (and x y) n.
Proof.
  intros. apply bitwise_binop_shr with andb. exact bits_and.
Qed.

Theorem or_shr:
  forall x y n,
  or (shr x n) (shr y n) = shr (or x y) n.
Proof.
  intros. apply bitwise_binop_shr with orb. exact bits_or.
Qed.

Theorem xor_shr:
  forall x y n,
  xor (shr x n) (shr y n) = shr (xor x y) n.
Proof.
  intros. apply bitwise_binop_shr with xorb. exact bits_xor.
Qed.

Theorem shr_shr:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shr (shr x y) z = shr x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; omega.
  apply same_bits_eq; intros.
  rewrite !bits_shr; auto. f_equal.
  destruct (zlt (i + unsigned z) zwordsize).
  rewrite H4. replace (i + (unsigned y + unsigned z)) with (i + unsigned z + unsigned y) by omega. auto.
  rewrite (zlt_false _ (i + unsigned (add y z))).
  destruct (zlt (zwordsize - 1 + unsigned y) zwordsize); omega.
  omega.
  destruct (zlt (i + unsigned z) zwordsize); omega.
Qed.

Theorem and_shr_shru:
  forall x y z,
  and (shr x z) (shru y z) = shru (and x y) z.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite bits_shr; auto. rewrite !bits_shru; auto.
  destruct (zlt (i + unsigned z) zwordsize).
  - rewrite bits_and; auto. generalize (unsigned_range z); omega.
  - apply andb_false_r.
Qed.

Theorem shr_and_shru_and:
  forall x y z,
  shru (shl z y) y = z ->
  and (shr x y) z = and (shru x y) z.
Proof.
  intros.
  rewrite <- H.
  rewrite and_shru. rewrite and_shr_shru. auto.
Qed.

Theorem shru_lt_zero:
  forall x,
  shru x (repr (zwordsize - 1)) = if lt x zero then one else zero.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_shru; auto.
  rewrite unsigned_repr.
  destruct (zeq i 0).
  subst i. rewrite Z.add_0_l. rewrite zlt_true.
  rewrite sign_bit_of_unsigned.
  unfold lt. rewrite signed_zero. unfold signed.
  destruct (zlt (unsigned x) half_modulus).
  rewrite zlt_false. auto. generalize (unsigned_range x); omega.
  rewrite zlt_true. unfold one; rewrite testbit_repr; auto.
  generalize (unsigned_range x); omega.
  omega.
  rewrite zlt_false.
  unfold testbit. rewrite Ztestbit_eq. rewrite zeq_false.
  destruct (lt x zero).
  rewrite unsigned_one. simpl Z.div2. rewrite Z.testbit_0_l; auto.
  rewrite unsigned_zero. simpl Z.div2. rewrite Z.testbit_0_l; auto.
  auto. omega. omega.
  generalize wordsize_max_unsigned; omega.
Qed.

Theorem shr_lt_zero:
  forall x,
  shr x (repr (zwordsize - 1)) = if lt x zero then mone else zero.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_shr; auto.
  rewrite unsigned_repr.
  transitivity (testbit x (zwordsize - 1)).
  f_equal. destruct (zlt (i + (zwordsize - 1)) zwordsize); omega.
  rewrite sign_bit_of_unsigned.
  unfold lt. rewrite signed_zero. unfold signed.
  destruct (zlt (unsigned x) half_modulus).
  rewrite zlt_false. rewrite bits_zero; auto. generalize (unsigned_range x); omega.
  rewrite zlt_true. rewrite bits_mone; auto. generalize (unsigned_range x); omega.
  generalize wordsize_max_unsigned; omega.
Qed.

(** ** Properties of rotations *)

Lemma bits_rol:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (rol x y) i = testbit x ((i - unsigned y) mod zwordsize).
Proof.
  intros. unfold rol.
  exploit (Z_div_mod_eq (unsigned y) zwordsize). apply wordsize_pos.
  set (j := unsigned y mod zwordsize). set (k := unsigned y / zwordsize).
  intros EQ.
  exploit (Z_mod_lt (unsigned y) zwordsize). apply wordsize_pos.
  fold j. intros RANGE.
  rewrite testbit_repr; auto.
  rewrite Z.lor_spec. rewrite Z.shiftr_spec. 2: omega.
  destruct (zlt i j).
  - rewrite Z.shiftl_spec_low; auto. simpl.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with (-k - 1).
    rewrite EQ. ring.
    omega.
  - rewrite Z.shiftl_spec_high.
    fold (testbit x (i + (zwordsize - j))).
    rewrite bits_above. rewrite orb_false_r.
    fold (testbit x (i - j)).
    f_equal. symmetry. apply Zmod_unique with (-k).
    rewrite EQ. ring.
    omega. omega. omega. omega.
Qed.

Lemma bits_ror:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (ror x y) i = testbit x ((i + unsigned y) mod zwordsize).
Proof.
  intros. unfold ror.
  exploit (Z_div_mod_eq (unsigned y) zwordsize). apply wordsize_pos.
  set (j := unsigned y mod zwordsize). set (k := unsigned y / zwordsize).
  intros EQ.
  exploit (Z_mod_lt (unsigned y) zwordsize). apply wordsize_pos.
  fold j. intros RANGE.
  rewrite testbit_repr; auto.
  rewrite Z.lor_spec. rewrite Z.shiftr_spec. 2: omega.
  destruct (zlt (i + j) zwordsize).
  - rewrite Z.shiftl_spec_low; auto. rewrite orb_false_r.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with k.
    rewrite EQ. ring.
    omega. omega.
  - rewrite Z.shiftl_spec_high.
    fold (testbit x (i + j)).
    rewrite bits_above. simpl.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with (k + 1).
    rewrite EQ. ring.
    omega. omega. omega. omega.
Qed.

Hint Rewrite bits_rol bits_ror: ints.

Theorem shl_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shl x n = rolm x n (shl mone n).
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize; intros.
  unfold rolm. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite !bits_shl; auto. rewrite bits_rol; auto.
  destruct (zlt i (unsigned n)).
  - rewrite andb_false_r; auto.
  - generalize (unsigned_range n); intros.
    rewrite bits_mone. rewrite andb_true_r. f_equal.
    symmetry. apply Zmod_small. omega.
    omega.
Qed.

Theorem shru_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shru x n = rolm x (sub iwordsize n) (shru mone n).
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize; intros.
  unfold rolm. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite !bits_shru; auto. rewrite bits_rol; auto.
  destruct (zlt (i + unsigned n) zwordsize).
  - generalize (unsigned_range n); intros.
    rewrite bits_mone. rewrite andb_true_r. f_equal.
    unfold sub. rewrite unsigned_repr. rewrite unsigned_repr_wordsize.
    symmetry. apply Zmod_unique with (-1). ring. omega.
    rewrite unsigned_repr_wordsize. generalize wordsize_max_unsigned. omega.
    omega.
  - rewrite andb_false_r; auto.
Qed.

Theorem rol_zero:
  forall x,
  rol x zero = x.
Proof.
  bit_solve. f_equal. rewrite unsigned_zero. rewrite Z.sub_0_r.
  apply Zmod_small; auto.
Qed.

Lemma bitwise_binop_rol:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  rol (f x y) n = f (rol x n) (rol y n).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_rol; auto. rewrite H; auto.
  apply Z_mod_lt. apply wordsize_pos.
Qed.

Theorem rol_and:
  forall x y n,
  rol (and x y) n = and (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with andb. exact bits_and.
Qed.

Theorem rol_or:
  forall x y n,
  rol (or x y) n = or (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with orb. exact bits_or.
Qed.

Theorem rol_xor:
  forall x y n,
  rol (xor x y) n = xor (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with xorb. exact bits_xor.
Qed.

Theorem rol_rol:
  forall x n m,
  Z.divide zwordsize modulus ->
  rol (rol x n) m = rol x (modu (add n m) iwordsize).
Proof.
  bit_solve. f_equal. apply eqmod_mod_eq. apply wordsize_pos.
  set (M := unsigned m); set (N := unsigned n).
  apply eqmod_trans with (i - M - N).
  apply eqmod_sub.
  apply eqmod_sym. apply eqmod_mod. apply wordsize_pos.
  apply eqmod_refl.
  replace (i - M - N) with (i - (M + N)) by omega.
  apply eqmod_sub.
  apply eqmod_refl.
  apply eqmod_trans with (Z.modulo (unsigned n + unsigned m) zwordsize).
  replace (M + N) with (N + M) by omega. apply eqmod_mod. apply wordsize_pos.
  unfold modu, add. fold M; fold N. rewrite unsigned_repr_wordsize.
  assert (forall a, eqmod zwordsize a (unsigned (repr a))).
    intros. eapply eqmod_divides. apply eqm_unsigned_repr. assumption.
  eapply eqmod_trans. 2: apply H1.
  apply eqmod_refl2. apply eqmod_mod_eq. apply wordsize_pos. auto.
  apply Z_mod_lt. apply wordsize_pos.
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x zero m = and x m.
Proof.
  intros. unfold rolm. rewrite rol_zero. auto.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  Z.divide zwordsize modulus ->
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
  intros.
  generalize (ltu_iwordsize_inv _ H); intros.
  apply same_bits_eq; intros.
  rewrite bits_ror; auto. rewrite bits_rol; auto. f_equal.
  unfold sub. rewrite unsigned_repr. rewrite unsigned_repr_wordsize.
  apply eqmod_mod_eq. apply wordsize_pos. exists 1. ring.
  rewrite unsigned_repr_wordsize.
  generalize wordsize_pos; generalize wordsize_max_unsigned; omega.
Qed.

Theorem ror_rol_neg:
  forall x y, (zwordsize | modulus) -> ror x y = rol x (neg y).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_ror by auto. rewrite bits_rol by auto.
  f_equal. apply eqmod_mod_eq. omega.
  apply eqmod_trans with (i - (- unsigned y)).
  apply eqmod_refl2; omega.
  apply eqmod_sub. apply eqmod_refl.
  apply eqmod_divides with modulus.
  apply eqm_unsigned_repr. auto.
Qed.

Theorem or_ror:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  add y z = iwordsize ->
  ror x z = or (shl x y) (shru x z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  unfold ror, or, shl, shru. apply same_bits_eq; intros.
  rewrite !testbit_repr; auto.
  rewrite !Z.lor_spec. rewrite orb_comm. f_equal; apply same_bits_eqm; auto.
  - apply eqm_unsigned_repr_r. apply eqm_refl2. f_equal.
    rewrite Zmod_small; auto.
    assert (unsigned (add y z) = zwordsize).
      rewrite H1. apply unsigned_repr_wordsize.
    unfold add in H5. rewrite unsigned_repr in H5.
    omega.
    generalize two_wordsize_max_unsigned; omega.
  - apply eqm_unsigned_repr_r. apply eqm_refl2. f_equal.
    apply Zmod_small; auto.
Qed.

(** ** Properties of [Z_one_bits] and [is_power2]. *)

Fixpoint powerserie (l: list Z): Z :=
  match l with
  | nil => 0
  | x :: xs => two_p x + powerserie xs
  end.

Lemma Z_one_bits_powerserie:
  forall x, 0 <= x < modulus -> x = powerserie (Z_one_bits wordsize x 0).
Proof.
  assert (forall n x i,
    0 <= i ->
    0 <= x < two_power_nat n ->
    x * two_p i = powerserie (Z_one_bits n x i)).
  {
  induction n; intros.
  simpl. rewrite two_power_nat_O in H0.
  assert (x = 0) by omega. subst x. omega.
  rewrite two_power_nat_S in H0. simpl Z_one_bits.
  rewrite (Zdecomp x) in H0. rewrite Zshiftin_spec in H0.
  assert (EQ: Z.div2 x * two_p (i + 1) = powerserie (Z_one_bits n (Z.div2 x) (i + 1))).
    apply IHn. omega.
    destruct (Z.odd x); omega.
  rewrite two_p_is_exp in EQ. change (two_p 1) with 2 in EQ.
  rewrite (Zdecomp x) at 1. rewrite Zshiftin_spec.
  destruct (Z.odd x); simpl powerserie; rewrite <- EQ; ring.
  omega. omega.
  }
  intros. rewrite <- H. change (two_p 0) with 1. omega.
  omega. exact H0.
Qed.

Lemma Z_one_bits_range:
  forall x i, In i (Z_one_bits wordsize x 0) -> 0 <= i < zwordsize.
Proof.
  assert (forall n x i j,
    In j (Z_one_bits n x i) -> i <= j < i + Z.of_nat n).
  {
  induction n; simpl In.
  tauto.
  intros x i j. rewrite Nat2Z.inj_succ.
  assert (In j (Z_one_bits n (Z.div2 x) (i + 1)) -> i <= j < i + Z.succ (Z.of_nat n)).
    intros. exploit IHn; eauto. omega.
  destruct (Z.odd x); simpl.
  intros [A|B]. subst j. omega. auto.
  auto.
  }
  intros. generalize (H wordsize x 0 i H0). fold zwordsize; omega.
Qed.

Lemma is_power2_rng:
  forall n logn,
  is_power2 n = Some logn ->
  0 <= unsigned logn < zwordsize.
Proof.
  intros n logn. unfold is_power2.
  generalize (Z_one_bits_range (unsigned n)).
  destruct (Z_one_bits wordsize (unsigned n) 0).
  intros; discriminate.
  destruct l.
  intros. injection H0; intro; subst logn; clear H0.
  assert (0 <= z < zwordsize).
  apply H. auto with coqlib.
  rewrite unsigned_repr. auto. generalize wordsize_max_unsigned; omega.
  intros; discriminate.
Qed.

Theorem is_power2_range:
  forall n logn,
  is_power2 n = Some logn -> ltu logn iwordsize = true.
Proof.
  intros. unfold ltu. rewrite unsigned_repr_wordsize.
  apply zlt_true. generalize (is_power2_rng _ _ H). tauto.
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
  0 <= n < zwordsize ->
  0 <= two_p n <= max_unsigned.
Proof.
  intros. split.
  assert (two_p n > 0). apply two_p_gt_ZERO. omega. omega.
  generalize (two_p_monotone_strict _ _ H).
  unfold zwordsize; rewrite <- two_power_nat_two_p.
  unfold max_unsigned, modulus. omega.
Qed.

Remark Z_one_bits_zero:
  forall n i, Z_one_bits n 0 i = nil.
Proof.
  induction n; intros; simpl; auto.
Qed.

Remark Z_one_bits_two_p:
  forall n x i,
  0 <= x < Z.of_nat n ->
  Z_one_bits n (two_p x) i = (i + x) :: nil.
Proof.
  induction n; intros; simpl. simpl in H. omegaContradiction.
  rewrite Nat2Z.inj_succ in H.
  assert (x = 0 \/ 0 < x) by omega. destruct H0.
  subst x; simpl. decEq. omega. apply Z_one_bits_zero.
  assert (Z.odd (two_p x) = false /\ Z.div2 (two_p x) = two_p (x-1)).
    apply Zshiftin_inj. rewrite <- Zdecomp. rewrite !Zshiftin_spec.
    rewrite <- two_p_S. rewrite Z.add_0_r. f_equal; omega. omega.
  destruct H1 as [A B]; rewrite A; rewrite B.
  rewrite IHn. f_equal; omega. omega.
Qed.

Lemma is_power2_two_p:
  forall n, 0 <= n < zwordsize ->
  is_power2 (repr (two_p n)) = Some (repr n).
Proof.
  intros. unfold is_power2. rewrite unsigned_repr.
  rewrite Z_one_bits_two_p. auto. auto.
  apply two_p_range. auto.
Qed.

(** ** Relation between bitwise operations and multiplications / divisions by powers of 2 *)

(** Left shifts and multiplications by powers of 2. *)

Lemma Zshiftl_mul_two_p:
  forall x n, 0 <= n -> Z.shiftl x n = x * two_p n.
Proof.
  intros. destruct n; simpl.
  - omega.
  - pattern p. apply Pos.peano_ind.
    + change (two_power_pos 1) with 2. simpl. ring.
    + intros. rewrite Pos.iter_succ. rewrite H0.
      rewrite Pplus_one_succ_l. rewrite two_power_pos_is_exp.
      change (two_power_pos 1) with 2. ring.
  - compute in H. congruence.
Qed.

Lemma shl_mul_two_p:
  forall x y,
  shl x y = mul x (repr (two_p (unsigned y))).
Proof.
  intros. unfold shl, mul. apply eqm_samerepr.
  rewrite Zshiftl_mul_two_p. auto with ints.
  generalize (unsigned_range y); omega.
Qed.

Theorem shl_mul:
  forall x y,
  shl x y = mul x (shl one y).
Proof.
  intros.
  assert (shl one y = repr (two_p (unsigned y))).
  {
    rewrite shl_mul_two_p. rewrite mul_commut. rewrite mul_one. auto.
  }
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

Theorem shifted_or_is_add:
  forall x y n,
  0 <= n < zwordsize ->
  unsigned y < two_p n ->
  or (shl x (repr n)) y = repr(unsigned x * two_p n + unsigned y).
Proof.
  intros. rewrite <- add_is_or.
  - unfold add. apply eqm_samerepr. apply eqm_add; auto with ints.
    rewrite shl_mul_two_p. unfold mul. apply eqm_unsigned_repr_l.
    apply eqm_mult; auto with ints. apply eqm_unsigned_repr_l.
    apply eqm_refl2. rewrite unsigned_repr. auto.
    generalize wordsize_max_unsigned; omega.
  - bit_solve.
    rewrite unsigned_repr.
    destruct (zlt i n).
    + auto.
    + replace (testbit y i) with false. apply andb_false_r.
      symmetry. unfold testbit.
      assert (EQ: Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; omega).
      apply Ztestbit_above with (Z.to_nat n).
      rewrite <- EQ in H0. rewrite <- two_power_nat_two_p in H0.
      generalize (unsigned_range y); omega.
      rewrite EQ; auto.
    + generalize wordsize_max_unsigned; omega.
Qed.

(** Unsigned right shifts and unsigned divisions by powers of 2. *)

Lemma Zshiftr_div_two_p:
  forall x n, 0 <= n -> Z.shiftr x n = x / two_p n.
Proof.
  intros. destruct n; unfold Z.shiftr; simpl.
  - rewrite Zdiv_1_r. auto.
  - pattern p. apply Pos.peano_ind.
    + change (two_power_pos 1) with 2. simpl. apply Zdiv2_div.
    + intros. rewrite Pos.iter_succ. rewrite H0.
      rewrite Pplus_one_succ_l. rewrite two_power_pos_is_exp.
      change (two_power_pos 1) with 2.
      rewrite Zdiv2_div. rewrite Z.mul_comm. apply Zdiv_Zdiv.
      rewrite two_power_pos_nat. apply two_power_nat_pos. omega.
  - compute in H. congruence.
Qed.

Lemma shru_div_two_p:
  forall x y,
  shru x y = repr (unsigned x / two_p (unsigned y)).
Proof.
  intros. unfold shru.
  rewrite Zshiftr_div_two_p. auto.
  generalize (unsigned_range y); omega.
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

Lemma shr_div_two_p:
  forall x y,
  shr x y = repr (signed x / two_p (unsigned y)).
Proof.
  intros. unfold shr.
  rewrite Zshiftr_div_two_p. auto.
  generalize (unsigned_range y); omega.
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

Lemma Ztestbit_mod_two_p:
  forall n x i,
  0 <= n -> 0 <= i ->
  Z.testbit (x mod (two_p n)) i = if zlt i n then Z.testbit x i else false.
Proof.
  intros n0 x i N0POS. revert x i; pattern n0; apply natlike_ind; auto.
  - intros. change (two_p 0) with 1. rewrite Zmod_1_r. rewrite Z.testbit_0_l.
    rewrite zlt_false; auto. omega.
  - intros. rewrite two_p_S; auto.
    replace (x0 mod (2 * two_p x))
       with (Zshiftin (Z.odd x0) (Z.div2 x0 mod two_p x)).
    rewrite Ztestbit_shiftin; auto. rewrite (Ztestbit_eq i x0); auto. destruct (zeq i 0).
    + rewrite zlt_true; auto. omega.
    + rewrite H0. destruct (zlt (Z.pred i) x).
      * rewrite zlt_true; auto. omega.
      * rewrite zlt_false; auto. omega.
      * omega.
    + rewrite (Zdecomp x0) at 3. set (x1 := Z.div2 x0). symmetry.
      apply Zmod_unique with (x1 / two_p x).
      rewrite !Zshiftin_spec. rewrite Z.add_assoc. f_equal.
      transitivity (2 * (two_p x * (x1 / two_p x) + x1 mod two_p x)).
      f_equal. apply Z_div_mod_eq. apply two_p_gt_ZERO; auto.
      ring.
      rewrite Zshiftin_spec. exploit (Z_mod_lt x1 (two_p x)). apply two_p_gt_ZERO; auto.
      destruct (Z.odd x0); omega.
Qed.

Corollary Ztestbit_two_p_m1:
  forall n i, 0 <= n -> 0 <= i ->
  Z.testbit (two_p n - 1) i = if zlt i n then true else false.
Proof.
  intros. replace (two_p n - 1) with ((-1) mod (two_p n)).
  rewrite Ztestbit_mod_two_p; auto. destruct (zlt i n); auto. apply Ztestbit_m1; auto.
  apply Zmod_unique with (-1). ring.
  exploit (two_p_gt_ZERO n). auto. omega.
Qed.

Theorem modu_and:
  forall x n logn,
  is_power2 n = Some logn ->
  modu x n = and x (sub n one).
Proof.
  intros. generalize (is_power2_correct _ _ H); intro.
  generalize (is_power2_rng _ _ H); intro.
  apply same_bits_eq; intros.
  rewrite bits_and; auto.
  unfold sub. rewrite testbit_repr; auto.
  rewrite H0. rewrite unsigned_one.
  unfold modu. rewrite testbit_repr; auto. rewrite H0.
  rewrite Ztestbit_mod_two_p. rewrite Ztestbit_two_p_m1.
  destruct (zlt i (unsigned logn)).
  rewrite andb_true_r; auto.
  rewrite andb_false_r; auto.
  tauto. tauto. tauto. tauto.
Qed.

(** ** Properties of [shrx] (signed division by a power of 2) *)

Lemma Zquot_Zdiv:
  forall x y,
  y > 0 ->
  Z.quot x y = if zlt x 0 then (x + y - 1) / y else x / y.
Proof.
  intros. destruct (zlt x 0).
  - symmetry. apply Zquot_unique_full with ((x + y - 1) mod y - (y - 1)).
     + red. right; split. omega.
       exploit (Z_mod_lt (x + y - 1) y); auto.
       rewrite Z.abs_eq. omega. omega.
     + transitivity ((y * ((x + y - 1) / y) + (x + y - 1) mod y) - (y-1)).
       rewrite <- Z_div_mod_eq. ring. auto. ring.
  - apply Zquot_Zdiv_pos; omega.
Qed.

Theorem shrx_zero:
  forall x, zwordsize > 1 -> shrx x zero = x.
Proof.
  intros. unfold shrx. rewrite shl_zero. unfold divs. rewrite signed_one by auto.
  rewrite Z.quot_1_r. apply repr_signed.
Qed. 

Theorem shrx_shr:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = shr (if lt x zero then add x (sub (shl one y) one) else x) y.
Proof.
  intros.
  set (uy := unsigned y).
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; omega.
  rewrite shr_div_two_p. unfold shrx. unfold divs.
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
    rewrite H1. apply unsigned_repr. unfold max_unsigned. omega.
  assert (signed (shl one y) = two_p uy).
    rewrite H1. apply signed_repr.
    unfold max_signed. generalize min_signed_neg. omega.
  rewrite H6.
  rewrite Zquot_Zdiv; auto.
  unfold lt. rewrite signed_zero.
  destruct (zlt (signed x) 0); auto.
  rewrite add_signed.
  assert (signed (sub (shl one y) one) = two_p uy - 1).
    unfold sub. rewrite H5. rewrite unsigned_one.
    apply signed_repr.
    generalize min_signed_neg. unfold max_signed. omega.
  rewrite H7. rewrite signed_repr. f_equal. f_equal. omega.
  generalize (signed_range x). intros.
  assert (two_p uy - 1 <= max_signed). unfold max_signed. omega. omega.
Qed.

Theorem shrx_shr_2:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = shr (add x (shru (shr x (repr (zwordsize - 1))) (sub iwordsize y))) y.
Proof.
  intros.
  rewrite shrx_shr by auto. f_equal.
  rewrite shr_lt_zero. destruct (lt x zero).
- set (uy := unsigned y).
  generalize (unsigned_range y); fold uy; intros.
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; omega.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. omega.
  f_equal. rewrite shl_mul_two_p. fold uy. rewrite mul_commut. rewrite mul_one.
  unfold sub. rewrite unsigned_one. rewrite unsigned_repr.
  rewrite unsigned_repr_wordsize. fold uy.
  apply same_bits_eq; intros. rewrite bits_shru by auto.
  rewrite testbit_repr by auto. rewrite Ztestbit_two_p_m1 by omega.
  rewrite unsigned_repr by (generalize wordsize_max_unsigned; omega).
  destruct (zlt i uy).
  rewrite zlt_true by omega. rewrite bits_mone by omega. auto.
  rewrite zlt_false by omega. auto.
  assert (two_p uy > 0) by (apply two_p_gt_ZERO; omega). unfold max_unsigned; omega.
- replace (shru zero (sub iwordsize y)) with zero.
  rewrite add_zero; auto.
  bit_solve. destruct (zlt (i + unsigned (sub iwordsize y)) zwordsize); auto.
Qed.

Lemma Zdiv_shift:
  forall x y, y > 0 ->
  (x + (y - 1)) / y = x / y + if zeq (Z.modulo x y) 0 then 0 else 1.
Proof.
  intros. generalize (Z_div_mod_eq x y H). generalize (Z_mod_lt x y H).
  set (q := x / y). set (r := x mod y). intros.
  destruct (zeq r 0).
  apply Zdiv_unique with (y - 1). rewrite H1. rewrite e. ring. omega.
  apply Zdiv_unique with (r - 1). rewrite H1. ring. omega.
Qed.

Theorem shrx_carry:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = add (shr x y) (shr_carry x y).
Proof.
  intros. rewrite shrx_shr; auto. unfold shr_carry.
  unfold lt. set (sx := signed x). rewrite signed_zero.
  destruct (zlt sx 0); simpl.
  2: rewrite add_zero; auto.
  set (uy := unsigned y).
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; omega.
  assert (shl one y = repr (two_p uy)).
    rewrite shl_mul_two_p. rewrite mul_commut. apply mul_one.
  assert (and x (sub (shl one y) one) = modu x (repr (two_p uy))).
    symmetry. rewrite H1. apply modu_and with (logn := y).
    rewrite is_power2_two_p. unfold uy. rewrite repr_unsigned. auto.
    omega.
  rewrite H2. rewrite H1.
  repeat rewrite shr_div_two_p. fold sx. fold uy.
  assert (two_p uy > 0). apply two_p_gt_ZERO. omega.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. omega.
  assert (two_p uy < half_modulus).
    rewrite half_modulus_power.
    apply two_p_monotone_strict. auto.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. omega.
  assert (sub (repr (two_p uy)) one = repr (two_p uy - 1)).
    unfold sub. apply eqm_samerepr. apply eqm_sub. apply eqm_sym; apply eqm_unsigned_repr.
    rewrite unsigned_one. apply eqm_refl.
  rewrite H7. rewrite add_signed. fold sx.
  rewrite (signed_repr (two_p uy - 1)). rewrite signed_repr.
  unfold modu. rewrite unsigned_repr.
  unfold eq. rewrite unsigned_zero. rewrite unsigned_repr.
  assert (unsigned x mod two_p uy = sx mod two_p uy).
    apply eqmod_mod_eq; auto. apply eqmod_divides with modulus.
    fold eqm. unfold sx. apply eqm_sym. apply eqm_signed_unsigned.
    unfold modulus. rewrite two_power_nat_two_p.
    exists (two_p (zwordsize - uy)). rewrite <- two_p_is_exp.
    f_equal. fold zwordsize; omega. omega. omega.
  rewrite H8. rewrite Zdiv_shift; auto.
  unfold add. apply eqm_samerepr. apply eqm_add.
  apply eqm_unsigned_repr.
  destruct (zeq (sx mod two_p uy) 0); simpl.
  rewrite unsigned_zero. apply eqm_refl.
  rewrite unsigned_one. apply eqm_refl.
  generalize (Z_mod_lt (unsigned x) (two_p uy) H3). unfold max_unsigned. omega.
  unfold max_unsigned; omega.
  generalize (signed_range x). fold sx. intros. split. omega. unfold max_signed. omega.
  generalize min_signed_neg. unfold max_signed. omega.
Qed.

(** Connections between [shr] and [shru]. *)

Lemma shr_shru_positive:
  forall x y,
  signed x >= 0 ->
  shr x y = shru x y.
Proof.
  intros.
  rewrite shr_div_two_p. rewrite shru_div_two_p.
  rewrite signed_eq_unsigned. auto. apply signed_positive. auto.
Qed.

Lemma and_positive:
  forall x y, signed y >= 0 -> signed (and x y) >= 0.
Proof.
  intros.
  assert (unsigned y < half_modulus). rewrite signed_positive in H. unfold max_signed in H; omega.
  generalize (sign_bit_of_unsigned y). rewrite zlt_true; auto. intros A.
  generalize (sign_bit_of_unsigned (and x y)). rewrite bits_and. rewrite A.
  rewrite andb_false_r. unfold signed.
  destruct (zlt (unsigned (and x y)) half_modulus).
  intros. generalize (unsigned_range (and x y)); omega.
  congruence.
  generalize wordsize_pos; omega.
Qed.

Theorem shr_and_is_shru_and:
  forall x y z,
  lt y zero = false -> shr (and x y) z = shru (and x y) z.
Proof.
  intros. apply shr_shru_positive. apply and_positive.
  unfold lt in H. rewrite signed_zero in H. destruct (zlt (signed y) 0). congruence. auto.
Qed.

(** ** Properties of integer zero extension and sign extension. *)

Lemma Ziter_base:
  forall (A: Type) n (f: A -> A) x, n <= 0 -> Z.iter n f x = x.
Proof.
  intros. unfold Z.iter. destruct n; auto. compute in H. elim H; auto.
Qed.

Lemma Ziter_succ:
  forall (A: Type) n (f: A -> A) x,
  0 <= n -> Z.iter (Z.succ n) f x = f (Z.iter n f x).
Proof.
  intros. destruct n; simpl.
  - auto.
  - rewrite Pos.add_1_r. apply Pos.iter_succ.
  - compute in H. elim H; auto.
Qed.

Lemma Znatlike_ind:
  forall (P: Z -> Prop),
  (forall n, n <= 0 -> P n) ->
  (forall n, 0 <= n -> P n -> P (Z.succ n)) ->
  forall n, P n.
Proof.
  intros. destruct (zle 0 n).
  apply natlike_ind; auto. apply H; omega.
  apply H. omega.
Qed.

Lemma Zzero_ext_spec:
  forall n x i, 0 <= i ->
  Z.testbit (Zzero_ext n x) i = if zlt i n then Z.testbit x i else false.
Proof.
  unfold Zzero_ext. induction n using Znatlike_ind.
  - intros. rewrite Ziter_base; auto.
    rewrite zlt_false. rewrite Ztestbit_0; auto. omega.
  - intros. rewrite Ziter_succ; auto.
    rewrite Ztestbit_shiftin; auto.
    rewrite (Ztestbit_eq i x); auto.
    destruct (zeq i 0).
    + subst i. rewrite zlt_true; auto. omega.
    + rewrite IHn. destruct (zlt (Z.pred i) n).
      rewrite zlt_true; auto. omega.
      rewrite zlt_false; auto. omega.
      omega.
Qed.

Lemma bits_zero_ext:
  forall n x i, 0 <= i ->
  testbit (zero_ext n x) i = if zlt i n then testbit x i else false.
Proof.
  intros. unfold zero_ext. destruct (zlt i zwordsize).
  rewrite testbit_repr; auto. rewrite Zzero_ext_spec. auto. auto.
  rewrite !bits_above; auto. destruct (zlt i n); auto.
Qed.

Lemma Zsign_ext_spec:
  forall n x i, 0 <= i -> 0 < n ->
  Z.testbit (Zsign_ext n x) i = Z.testbit x (if zlt i n then i else n - 1).
Proof.
  intros n0 x i I0 N0.
  revert x i I0. pattern n0. apply Zlt_lower_bound_ind with (z := 1).
  - unfold Zsign_ext. intros.
    destruct (zeq x 1).
    + subst x; simpl.
      replace (if zlt i 1 then i else 0) with 0.
      rewrite Ztestbit_base.
      destruct (Z.odd x0).
      apply Ztestbit_m1; auto.
      apply Ztestbit_0.
      destruct (zlt i 1); omega.
    + set (x1 := Z.pred x). replace x1 with (Z.succ (Z.pred x1)).
      rewrite Ziter_succ. rewrite Ztestbit_shiftin.
      destruct (zeq i 0).
      * subst i. rewrite zlt_true. rewrite Ztestbit_base; auto. omega.
      * rewrite H. unfold x1. destruct (zlt (Z.pred i) (Z.pred x)).
        rewrite zlt_true. rewrite (Ztestbit_eq i x0); auto. rewrite zeq_false; auto. omega.
        rewrite zlt_false. rewrite (Ztestbit_eq (x - 1) x0). rewrite zeq_false; auto.
        omega. omega. omega. unfold x1; omega. omega.
      * omega.
      * unfold x1; omega.
      * omega.
  - omega.
Qed.

Lemma bits_sign_ext:
  forall n x i, 0 <= i < zwordsize -> 0 < n ->
  testbit (sign_ext n x) i = testbit x (if zlt i n then i else n - 1).
Proof.
  intros. unfold sign_ext.
  rewrite testbit_repr; auto. rewrite Zsign_ext_spec. destruct (zlt i n); auto.
  omega. auto.
Qed.

Hint Rewrite bits_zero_ext bits_sign_ext: ints.

Theorem zero_ext_above:
  forall n x, n >= zwordsize -> zero_ext n x = x.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_zero_ext. apply zlt_true. omega. omega.
Qed.

Theorem sign_ext_above:
  forall n x, n >= zwordsize -> sign_ext n x = x.
Proof.
  intros. apply same_bits_eq; intros.
  unfold sign_ext; rewrite testbit_repr; auto.
  rewrite Zsign_ext_spec. rewrite zlt_true. auto. omega. omega. omega.
Qed.

Theorem zero_ext_and:
  forall n x, 0 <= n -> zero_ext n x = and x (repr (two_p n - 1)).
Proof.
  bit_solve. rewrite testbit_repr; auto. rewrite Ztestbit_two_p_m1; intuition.
  destruct (zlt i n).
  rewrite andb_true_r; auto.
  rewrite andb_false_r; auto.
  tauto.
Qed.

Theorem zero_ext_mod:
  forall n x, 0 <= n < zwordsize ->
  unsigned (zero_ext n x) = Z.modulo (unsigned x) (two_p n).
Proof.
  intros. apply equal_same_bits. intros.
  rewrite Ztestbit_mod_two_p; auto.
  fold (testbit (zero_ext n x) i).
  destruct (zlt i zwordsize).
  rewrite bits_zero_ext; auto.
  rewrite bits_above. rewrite zlt_false; auto. omega. omega.
  omega.
Qed.

Theorem zero_ext_widen:
  forall x n n', 0 <= n <= n' ->
  zero_ext n' (zero_ext n x) = zero_ext n x.
Proof.
  bit_solve. destruct (zlt i n).
  apply zlt_true. omega.
  destruct (zlt i n'); auto.
  tauto. tauto.
Qed.

Theorem sign_ext_widen:
  forall x n n', 0 < n  <= n' ->
  sign_ext n' (sign_ext n x) = sign_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve. destruct (zlt i n').
  auto.
  rewrite (zlt_false _ i n).
  destruct (zlt (n' - 1) n); f_equal; omega.
  omega. omega.
  destruct (zlt i n'); omega.
  omega. omega.
  apply sign_ext_above; auto.
Qed.

Theorem sign_zero_ext_widen:
  forall x n n', 0 <= n < n' ->
  sign_ext n' (zero_ext n x) = zero_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve.
  destruct (zlt i n').
  auto.
  rewrite !zlt_false. auto. omega. omega. omega.
  destruct (zlt i n'); omega.
  omega.
  apply sign_ext_above; auto.
Qed.

Theorem zero_ext_narrow:
  forall x n n', 0 <= n <= n' ->
  zero_ext n (zero_ext n' x) = zero_ext n x.
Proof.
  bit_solve. destruct (zlt i n).
  apply zlt_true. omega.
  auto.
  omega. omega. omega.
Qed.

Theorem sign_ext_narrow:
  forall x n n', 0 < n <= n' ->
  sign_ext n (sign_ext n' x) = sign_ext n x.
Proof.
  intros. destruct (zlt n zwordsize).
  bit_solve. destruct (zlt i n); f_equal; apply zlt_true; omega.
  omega.
  destruct (zlt i n); omega.
  omega. omega.
  rewrite (sign_ext_above n'). auto. omega.
Qed.

Theorem zero_sign_ext_narrow:
  forall x n n', 0 < n <= n' ->
  zero_ext n (sign_ext n' x) = zero_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve.
  destruct (zlt i n); auto.
  rewrite zlt_true; auto. omega.
  omega. omega. omega.
  rewrite sign_ext_above; auto.
Qed.

Theorem zero_ext_idem:
  forall n x, 0 <= n -> zero_ext n (zero_ext n x) = zero_ext n x.
Proof.
  intros. apply zero_ext_widen. omega.
Qed.

Theorem sign_ext_idem:
  forall n x, 0 < n -> sign_ext n (sign_ext n x) = sign_ext n x.
Proof.
  intros. apply sign_ext_widen. omega.
Qed.

Theorem sign_ext_zero_ext:
  forall n x, 0 < n -> sign_ext n (zero_ext n x) = sign_ext n x.
Proof.
  intros. destruct (zlt n zwordsize).
  bit_solve.
  destruct (zlt i n).
  rewrite zlt_true; auto.
  rewrite zlt_true; auto. omega.
  destruct (zlt i n); omega.
  rewrite zero_ext_above; auto.
Qed.

Theorem zero_ext_sign_ext:
  forall n x, 0 < n -> zero_ext n (sign_ext n x) = zero_ext n x.
Proof.
  intros. apply zero_sign_ext_narrow. omega.
Qed.

Theorem sign_ext_equal_if_zero_equal:
  forall n x y, 0 < n ->
  zero_ext n x = zero_ext n y ->
  sign_ext n x = sign_ext n y.
Proof.
  intros. rewrite <- (sign_ext_zero_ext n x H).
  rewrite <- (sign_ext_zero_ext n y H). congruence.
Qed.

Theorem zero_ext_shru_shl:
  forall n x,
  0 < n < zwordsize ->
  let y := repr (zwordsize - n) in
  zero_ext n x = shru (shl x y) y.
Proof.
  intros.
  assert (unsigned y = zwordsize - n).
    unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. omega.
  apply same_bits_eq; intros.
  rewrite bits_zero_ext.
  rewrite bits_shru; auto.
  destruct (zlt i n).
  rewrite zlt_true. rewrite bits_shl. rewrite zlt_false. f_equal. omega.
  omega. omega. omega.
  rewrite zlt_false. auto. omega.
  omega.
Qed.

Theorem sign_ext_shr_shl:
  forall n x,
  0 < n < zwordsize ->
  let y := repr (zwordsize - n) in
  sign_ext n x = shr (shl x y) y.
Proof.
  intros.
  assert (unsigned y = zwordsize - n).
    unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. omega.
  apply same_bits_eq; intros.
  rewrite bits_sign_ext.
  rewrite bits_shr; auto.
  destruct (zlt i n).
  rewrite zlt_true. rewrite bits_shl. rewrite zlt_false. f_equal. omega.
  omega. omega. omega.
  rewrite zlt_false. rewrite bits_shl. rewrite zlt_false. f_equal. omega.
  omega. omega. omega. omega. omega.
Qed.

(** [zero_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [0...2^n-1]. *)

Lemma zero_ext_range:
  forall n x, 0 <= n < zwordsize -> 0 <= unsigned (zero_ext n x) < two_p n.
Proof.
  intros. rewrite zero_ext_mod; auto. apply Z_mod_lt. apply two_p_gt_ZERO. omega.
Qed.

Lemma eqmod_zero_ext:
  forall n x, 0 <= n < zwordsize -> eqmod (two_p n) (unsigned (zero_ext n x)) (unsigned x).
Proof.
  intros. rewrite zero_ext_mod; auto. apply eqmod_sym. apply eqmod_mod.
  apply two_p_gt_ZERO. omega.
Qed.

(** [sign_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [-2^(n-1)...2^(n-1) - 1]. *)

Lemma sign_ext_range:
  forall n x, 0 < n < zwordsize -> -two_p (n-1) <= signed (sign_ext n x) < two_p (n-1).
Proof.
  intros. rewrite sign_ext_shr_shl; auto.
  set (X := shl x (repr (zwordsize - n))).
  assert (two_p (n - 1) > 0) by (apply two_p_gt_ZERO; omega).
  assert (unsigned (repr (zwordsize - n)) = zwordsize - n).
    apply unsigned_repr.
    split. omega. generalize wordsize_max_unsigned; omega.
  rewrite shr_div_two_p.
  rewrite signed_repr.
  rewrite H1.
  apply Zdiv_interval_1.
  omega. omega. apply two_p_gt_ZERO; omega.
  replace (- two_p (n - 1) * two_p (zwordsize - n))
     with (- (two_p (n - 1) * two_p (zwordsize - n))) by ring.
  rewrite <- two_p_is_exp.
  replace (n - 1 + (zwordsize - n)) with (zwordsize - 1) by omega.
  rewrite <- half_modulus_power.
  generalize (signed_range X). unfold min_signed, max_signed. omega.
  omega. omega.
  apply Zdiv_interval_2. apply signed_range.
  generalize min_signed_neg; omega.
  generalize max_signed_pos; omega.
  rewrite H1. apply two_p_gt_ZERO. omega.
Qed.

Lemma eqmod_sign_ext':
  forall n x, 0 < n < zwordsize ->
  eqmod (two_p n) (unsigned (sign_ext n x)) (unsigned x).
Proof.
  intros.
  set (N := Z.to_nat n).
  assert (Z.of_nat N = n) by (apply Z2Nat.id; omega).
  rewrite <- H0. rewrite <- two_power_nat_two_p.
  apply eqmod_same_bits; intros.
  rewrite H0 in H1. rewrite H0.
  fold (testbit (sign_ext n x) i). rewrite bits_sign_ext.
  rewrite zlt_true. auto. omega. omega. omega.
Qed.

Lemma eqmod_sign_ext:
  forall n x, 0 < n < zwordsize ->
  eqmod (two_p n) (signed (sign_ext n x)) (unsigned x).
Proof.
  intros. apply eqmod_trans with (unsigned (sign_ext n x)).
  apply eqmod_divides with modulus. apply eqm_signed_unsigned.
  exists (two_p (zwordsize - n)).
  unfold modulus. rewrite two_power_nat_two_p. fold zwordsize.
  rewrite <- two_p_is_exp. f_equal. omega. omega. omega.
  apply eqmod_sign_ext'; auto.
Qed.

(** ** Properties of [one_bits] (decomposition in sum of powers of two) *)

Theorem one_bits_range:
  forall x i, In i (one_bits x) -> ltu i iwordsize = true.
Proof.
  assert (A: forall p, 0 <= p < zwordsize -> ltu (repr p) iwordsize = true).
    intros. unfold ltu, iwordsize. apply zlt_true.
    repeat rewrite unsigned_repr. tauto.
    generalize wordsize_max_unsigned; omega.
    generalize wordsize_max_unsigned; omega.
  unfold one_bits. intros.
  destruct (list_in_map_inv _ _ _ H) as [i0 [EQ IN]].
  subst i. apply A. apply Z_one_bits_range with (unsigned x); auto.
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

Lemma translate_ltu:
  forall x y d,
  0 <= unsigned x + unsigned d <= max_unsigned ->
  0 <= unsigned y + unsigned d <= max_unsigned ->
  ltu (add x d) (add y d) = ltu x y.
Proof.
  intros. unfold add. unfold ltu.
  repeat rewrite unsigned_repr; auto. case (zlt (unsigned x) (unsigned y)); intro.
  apply zlt_true. omega.
  apply zlt_false. omega.
Qed.

Theorem translate_cmpu:
  forall c x y d,
  0 <= unsigned x + unsigned d <= max_unsigned ->
  0 <= unsigned y + unsigned d <= max_unsigned ->
  cmpu c (add x d) (add y d) = cmpu c x y.
Proof.
  intros. unfold cmpu.
  rewrite translate_eq. repeat rewrite translate_ltu; auto.
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

Theorem lt_sub_overflow:
  forall x y,
  xor (sub_overflow x y zero) (negative (sub x y)) = if lt x y then one else zero.
Proof.
  intros. unfold negative, sub_overflow, lt. rewrite sub_signed.
  rewrite signed_zero. rewrite Z.sub_0_r.
  generalize (signed_range x) (signed_range y).
  set (X := signed x); set (Y := signed y). intros RX RY.
  unfold min_signed, max_signed in *.
  generalize half_modulus_pos half_modulus_modulus; intros HM MM.
  destruct (zle 0 (X - Y)).
- unfold proj_sumbool at 1; rewrite zle_true at 1 by omega. simpl.
  rewrite (zlt_false _ X) by omega.
  destruct (zlt (X - Y) half_modulus).
  + unfold proj_sumbool; rewrite zle_true by omega.
    rewrite signed_repr. rewrite zlt_false by omega. apply xor_idem.
    unfold min_signed, max_signed; omega.
  + unfold proj_sumbool; rewrite zle_false by omega.
    replace (signed (repr (X - Y))) with (X - Y - modulus).
    rewrite zlt_true by omega. apply xor_idem.
    rewrite signed_repr_eq. replace ((X - Y) mod modulus) with (X - Y).
    rewrite zlt_false; auto.
    symmetry. apply Zmod_unique with 0; omega.
- unfold proj_sumbool at 2. rewrite zle_true at 1 by omega. rewrite andb_true_r.
  rewrite (zlt_true _ X) by omega.
  destruct (zlt (X - Y) (-half_modulus)).
  + unfold proj_sumbool; rewrite zle_false by omega.
    replace (signed (repr (X - Y))) with (X - Y + modulus).
    rewrite zlt_false by omega. apply xor_zero.
    rewrite signed_repr_eq. replace ((X - Y) mod modulus) with (X - Y + modulus).
    rewrite zlt_true by omega; auto.
    symmetry. apply Zmod_unique with (-1); omega.
  + unfold proj_sumbool; rewrite zle_true by omega.
    rewrite signed_repr. rewrite zlt_true by omega. apply xor_zero_l.
    unfold min_signed, max_signed; omega.
Qed.

Lemma signed_eq:
  forall x y, eq x y = zeq (signed x) (signed y).
Proof.
  intros. unfold eq. unfold proj_sumbool.
  destruct (zeq (unsigned x) (unsigned y));
  destruct (zeq (signed x) (signed y)); auto.
  elim n. unfold signed. rewrite e; auto.
  elim n. apply eqm_small_eq; auto with ints.
  eapply eqm_trans. apply eqm_sym. apply eqm_signed_unsigned.
  rewrite e. apply eqm_signed_unsigned.
Qed.

Lemma not_lt:
  forall x y, negb (lt y x) = (lt x y || eq x y).
Proof.
  intros. unfold lt. rewrite signed_eq. unfold proj_sumbool.
  destruct (zlt (signed y) (signed x)).
  rewrite zlt_false. rewrite zeq_false. auto. omega. omega.
  destruct (zeq (signed x) (signed y)).
  rewrite zlt_false. auto. omega.
  rewrite zlt_true. auto. omega.
Qed.

Lemma lt_not:
  forall x y, lt y x = negb (lt x y) && negb (eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- not_lt. rewrite negb_involutive. auto.
Qed.

Lemma not_ltu:
  forall x y, negb (ltu y x) = (ltu x y || eq x y).
Proof.
  intros. unfold ltu, eq.
  destruct (zlt (unsigned y) (unsigned x)).
  rewrite zlt_false. rewrite zeq_false. auto. omega. omega.
  destruct (zeq (unsigned x) (unsigned y)).
  rewrite zlt_false. auto. omega.
  rewrite zlt_true. auto. omega.
Qed.

Lemma ltu_not:
  forall x y, ltu y x = negb (ltu x y) && negb (eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- not_ltu. rewrite negb_involutive. auto.
Qed.


(** Non-overlapping test *)

Definition no_overlap (ofs1: int) (sz1: Z) (ofs2: int) (sz2: Z) : bool :=
  let x1 := unsigned ofs1 in let x2 := unsigned ofs2 in
     zlt (x1 + sz1) modulus && zlt (x2 + sz2) modulus
  && (zle (x1 + sz1) x2 || zle (x2 + sz2) x1).

Lemma no_overlap_sound:
  forall ofs1 sz1 ofs2 sz2 base,
  sz1 > 0 -> sz2 > 0 -> no_overlap ofs1 sz1 ofs2 sz2 = true ->
  unsigned (add base ofs1) + sz1 <= unsigned (add base ofs2)
  \/ unsigned (add base ofs2) + sz2 <= unsigned (add base ofs1).
Proof.
  intros.
  destruct (andb_prop _ _ H1). clear H1.
  destruct (andb_prop _ _ H2). clear H2.
  apply proj_sumbool_true in H1.
  apply proj_sumbool_true in H4.
  assert (unsigned ofs1 + sz1 <= unsigned ofs2 \/ unsigned ofs2 + sz2 <= unsigned ofs1).
  destruct (orb_prop _ _ H3). left. eapply proj_sumbool_true; eauto. right. eapply proj_sumbool_true; eauto.
  clear H3.
  generalize (unsigned_range ofs1) (unsigned_range ofs2). intros P Q.
  generalize (unsigned_add_either base ofs1) (unsigned_add_either base ofs2).
  intros [C|C] [D|D]; omega.
Qed.

(** Size of integers, in bits. *)

Definition Zsize (x: Z) : Z :=
  match x with
  | Zpos p => Zpos (Pos.size p)
  | _ => 0
  end.

Definition size (x: int) : Z := Zsize (unsigned x).

Remark Zsize_pos: forall x, 0 <= Zsize x.
Proof.
  destruct x; simpl. omega. compute; intuition congruence. omega.
Qed.

Remark Zsize_pos': forall x, 0 < x -> 0 < Zsize x.
Proof.
  destruct x; simpl; intros; try discriminate. compute; auto.
Qed.

Lemma Zsize_shiftin:
  forall b x, 0 < x -> Zsize (Zshiftin b x) = Z.succ (Zsize x).
Proof.
  intros. destruct x; compute in H; try discriminate.
  destruct b.
  change (Zshiftin true (Zpos p)) with (Zpos (p~1)).
  simpl. f_equal. rewrite Pos.add_1_r; auto.
  change (Zshiftin false (Zpos p)) with (Zpos (p~0)).
  simpl. f_equal. rewrite Pos.add_1_r; auto.
Qed.

Lemma Ztestbit_size_1:
  forall x, 0 < x -> Z.testbit x (Z.pred (Zsize x)) = true.
Proof.
  intros x0 POS0; pattern x0; apply Zshiftin_pos_ind; auto.
  intros. rewrite Zsize_shiftin; auto.
  replace (Z.pred (Z.succ (Zsize x))) with (Z.succ (Z.pred (Zsize x))) by omega.
  rewrite Ztestbit_shiftin_succ. auto. generalize (Zsize_pos' x H); omega.
Qed.

Lemma Ztestbit_size_2:
  forall x, 0 <= x -> forall i, i >= Zsize x -> Z.testbit x i = false.
Proof.
  intros x0 POS0. destruct (zeq x0 0).
  - subst x0; intros. apply Ztestbit_0.
  - pattern x0; apply Zshiftin_pos_ind.
    + simpl. intros. change 1 with (Zshiftin true 0). rewrite Ztestbit_shiftin.
      rewrite zeq_false. apply Ztestbit_0. omega. omega.
    + intros. rewrite Zsize_shiftin in H1; auto.
      generalize (Zsize_pos' _ H); intros.
      rewrite Ztestbit_shiftin. rewrite zeq_false. apply H0. omega.
      omega. omega.
    + omega.
Qed.

Lemma Zsize_interval_1:
  forall x, 0 <= x -> 0 <= x < two_p (Zsize x).
Proof.
  intros.
  assert (x = x mod (two_p (Zsize x))).
    apply equal_same_bits; intros.
    rewrite Ztestbit_mod_two_p; auto.
    destruct (zlt i (Zsize x)). auto. apply Ztestbit_size_2; auto.
    apply Zsize_pos; auto.
  rewrite H0 at 1. rewrite H0 at 3. apply Z_mod_lt. apply two_p_gt_ZERO. apply Zsize_pos; auto.
Qed.

Lemma Zsize_interval_2:
  forall x n, 0 <= n -> 0 <= x < two_p n -> n >= Zsize x.
Proof.
  intros. set (N := Z.to_nat n).
  assert (Z.of_nat N = n) by (apply Z2Nat.id; auto).
  rewrite <- H1 in H0. rewrite <- two_power_nat_two_p in H0.
  destruct (zeq x 0).
  subst x; simpl; omega.
  destruct (zlt n (Zsize x)); auto.
  exploit (Ztestbit_above N x (Z.pred (Zsize x))). auto. omega.
  rewrite Ztestbit_size_1. congruence. omega.
Qed.

Lemma Zsize_monotone:
  forall x y, 0 <= x <= y -> Zsize x <= Zsize y.
Proof.
  intros. apply Z.ge_le. apply Zsize_interval_2. apply Zsize_pos.
  exploit (Zsize_interval_1 y). omega.
  omega.
Qed.

Theorem size_zero: size zero = 0.
Proof.
  unfold size; rewrite unsigned_zero; auto.
Qed.

Theorem bits_size_1:
  forall x, x = zero \/ testbit x (Z.pred (size x)) = true.
Proof.
  intros. destruct (zeq (unsigned x) 0).
  left. rewrite <- (repr_unsigned x). rewrite e; auto.
  right. apply Ztestbit_size_1. generalize (unsigned_range x); omega.
Qed.

Theorem bits_size_2:
  forall x i, size x <= i -> testbit x i = false.
Proof.
  intros. apply Ztestbit_size_2. generalize (unsigned_range x); omega.
  fold (size x); omega.
Qed.

Theorem size_range:
  forall x, 0 <= size x <= zwordsize.
Proof.
  intros; split. apply Zsize_pos.
  destruct (bits_size_1 x).
  subst x; unfold size; rewrite unsigned_zero; simpl. generalize wordsize_pos; omega.
  destruct (zle (size x) zwordsize); auto.
  rewrite bits_above in H. congruence. omega.
Qed.

Theorem bits_size_3:
  forall x n,
  0 <= n ->
  (forall i, n <= i < zwordsize -> testbit x i = false) ->
  size x <= n.
Proof.
  intros. destruct (zle (size x) n). auto.
  destruct (bits_size_1 x).
  subst x. unfold size; rewrite unsigned_zero; assumption.
  rewrite (H0 (Z.pred (size x))) in H1. congruence.
  generalize (size_range x); omega.
Qed.

Theorem bits_size_4:
  forall x n,
  0 <= n ->
  testbit x (Z.pred n) = true ->
  (forall i, n <= i < zwordsize -> testbit x i = false) ->
  size x = n.
Proof.
  intros.
  assert (size x <= n).
    apply bits_size_3; auto.
  destruct (zlt (size x) n).
  rewrite bits_size_2 in H0. congruence. omega.
  omega.
Qed.

Theorem size_interval_1:
  forall x, 0 <= unsigned x < two_p (size x).
Proof.
  intros; apply Zsize_interval_1. generalize (unsigned_range x); omega.
Qed.

Theorem size_interval_2:
  forall x n, 0 <= n -> 0 <= unsigned x < two_p n -> n >= size x.
Proof.
  intros. apply Zsize_interval_2; auto.
Qed.

Theorem size_and:
  forall a b, size (and a b) <= Z.min (size a) (size b).
Proof.
  intros.
  assert (0 <= Z.min (size a) (size b)).
    generalize (size_range a) (size_range b). zify; omega.
  apply bits_size_3. auto. intros.
  rewrite bits_and. zify. subst z z0. destruct H1.
  rewrite (bits_size_2 a). auto. omega.
  rewrite (bits_size_2 b). apply andb_false_r. omega.
  omega.
Qed.

Corollary and_interval:
  forall a b, 0 <= unsigned (and a b) < two_p (Z.min (size a) (size b)).
Proof.
  intros.
  generalize (size_interval_1 (and a b)); intros.
  assert (two_p (size (and a b)) <= two_p (Z.min (size a) (size b))).
  apply two_p_monotone. split. generalize (size_range (and a b)); omega.
  apply size_and.
  omega.
Qed.

Theorem size_or:
  forall a b, size (or a b) = Z.max (size a) (size b).
Proof.
  intros. generalize (size_range a) (size_range b); intros.
  destruct (bits_size_1 a).
  subst a. rewrite size_zero. rewrite or_zero_l. zify; omega.
  destruct (bits_size_1 b).
  subst b. rewrite size_zero. rewrite or_zero. zify; omega.
  zify. destruct H3 as [[P Q] | [P Q]]; subst.
  apply bits_size_4. tauto. rewrite bits_or. rewrite H2. apply orb_true_r.
  omega.
  intros. rewrite bits_or. rewrite !bits_size_2. auto. omega. omega. omega.
  apply bits_size_4. tauto. rewrite bits_or. rewrite H1. apply orb_true_l.
  destruct (zeq (size a) 0). unfold testbit in H1. rewrite Z.testbit_neg_r in H1.
  congruence. omega. omega.
  intros. rewrite bits_or. rewrite !bits_size_2. auto. omega. omega. omega.
Qed.

Corollary or_interval:
  forall a b, 0 <= unsigned (or a b) < two_p (Z.max (size a) (size b)).
Proof.
  intros. rewrite <- size_or. apply size_interval_1.
Qed.

Theorem size_xor:
  forall a b, size (xor a b) <= Z.max (size a) (size b).
Proof.
  intros.
  assert (0 <= Z.max (size a) (size b)).
    generalize (size_range a) (size_range b). zify; omega.
  apply bits_size_3. auto. intros.
  rewrite bits_xor. rewrite !bits_size_2. auto.
  zify; omega.
  zify; omega.
  omega.
Qed.

Corollary xor_interval:
  forall a b, 0 <= unsigned (xor a b) < two_p (Z.max (size a) (size b)).
Proof.
  intros.
  generalize (size_interval_1 (xor a b)); intros.
  assert (two_p (size (xor a b)) <= two_p (Z.max (size a) (size b))).
  apply two_p_monotone. split. generalize (size_range (xor a b)); omega.
  apply size_xor.
  omega.
Qed.

End Make.

(** * Specialization to integers of size 8, 32, and 64 bits *)

Module Wordsize_32.
  Definition wordsize := 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_32.

Strategy opaque [Wordsize_32.wordsize].

Module Int := Make(Wordsize_32).

Strategy 0 [Wordsize_32.wordsize].

Notation int := Int.int.

Remark int_wordsize_divides_modulus:
  Z.divide (Z.of_nat Int.wordsize) Int.modulus.
Proof.
  exists (two_p (32-5)); reflexivity.
Qed.

Module Wordsize_8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_8.

Strategy opaque [Wordsize_8.wordsize].

Module Byte := Make(Wordsize_8).

Strategy 0 [Wordsize_8.wordsize].

Notation byte := Byte.int.

Module Wordsize_64.
  Definition wordsize := 64%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_64.

Strategy opaque [Wordsize_64.wordsize].

Module Int64.

Include Make(Wordsize_64).

(** Shifts with amount given as a 32-bit integer *)

Definition iwordsize': Int.int := Int.repr zwordsize.

Definition shl' (x: int) (y: Int.int): int :=
  repr (Z.shiftl (unsigned x) (Int.unsigned y)).
Definition shru' (x: int) (y: Int.int): int :=
  repr (Z.shiftr (unsigned x) (Int.unsigned y)).
Definition shr' (x: int) (y: Int.int): int :=
  repr (Z.shiftr (signed x) (Int.unsigned y)).
Definition rol' (x: int) (y: Int.int): int :=
  rol x (repr (Int.unsigned y)).
Definition shrx' (x: int) (y: Int.int): int :=
  divs x (shl' one y).
Definition shr_carry' (x: int) (y: Int.int): int :=
  if lt x zero && negb (eq (and x (sub (shl' one y) one)) zero)
  then one else zero.

Lemma bits_shl':
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shl' x y) i =
  if zlt i (Int.unsigned y) then false else testbit x (i - Int.unsigned y).
Proof.
  intros. unfold shl'. rewrite testbit_repr; auto.
  destruct (zlt i (Int.unsigned y)).
  apply Z.shiftl_spec_low. auto.
  apply Z.shiftl_spec_high. omega. omega.
Qed.

Lemma bits_shru':
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shru' x y) i =
  if zlt (i + Int.unsigned y) zwordsize then testbit x (i + Int.unsigned y) else false.
Proof.
  intros. unfold shru'. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. fold (testbit x (i + Int.unsigned y)).
  destruct (zlt (i + Int.unsigned y) zwordsize).
  auto.
  apply bits_above; auto.
  omega.
Qed.

Lemma bits_shr':
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shr' x y) i =
  testbit x (if zlt (i + Int.unsigned y) zwordsize then i + Int.unsigned y else zwordsize - 1).
Proof.
  intros. unfold shr'. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. apply bits_signed.
  generalize (Int.unsigned_range y); omega.
  omega.
Qed.

Lemma shl'_mul_two_p:
  forall x y,
  shl' x y = mul x (repr (two_p (Int.unsigned y))).
Proof.
  intros. unfold shl', mul. apply eqm_samerepr.
  rewrite Zshiftl_mul_two_p. apply eqm_mult. apply eqm_refl. apply eqm_unsigned_repr.
  generalize (Int.unsigned_range y); omega.
Qed.

Lemma shl'_one_two_p:
  forall y, shl' one y = repr (two_p (Int.unsigned y)).
Proof.
  intros. rewrite shl'_mul_two_p. rewrite mul_commut. rewrite mul_one. auto.
Qed.

Theorem shl'_mul:
  forall x y,
  shl' x y = mul x (shl' one y).
Proof.
  intros. rewrite shl'_one_two_p. apply shl'_mul_two_p.
Qed.

Theorem shl'_zero:
  forall x, shl' x Int.zero = x.
Proof.
  intros. unfold shl'. rewrite Int.unsigned_zero. unfold Z.shiftl.
  apply repr_unsigned.
Qed.

Theorem shru'_zero :
  forall x, shru' x Int.zero = x.
Proof.
  intros. unfold shru'. rewrite Int.unsigned_zero. unfold Z.shiftr.
  apply repr_unsigned.
Qed.

Theorem shr'_zero :
  forall x, shr' x Int.zero = x.
Proof.
  intros. unfold shr'. rewrite Int.unsigned_zero. unfold Z.shiftr.
  apply repr_signed.
Qed.

Theorem shrx'_zero:
  forall x, shrx' x Int.zero = x.
Proof.
  intros. change (shrx' x Int.zero) with (shrx x zero). apply shrx_zero. compute; auto.
Qed.

Theorem shrx'_carry:
  forall x y,
  Int.ltu y (Int.repr 63) = true ->
  shrx' x y = add (shr' x y) (shr_carry' x y).
Proof.
  intros. apply Int.ltu_inv in H. change (Int.unsigned (Int.repr 63)) with 63 in H.
  set (y1 := Int64.repr (Int.unsigned y)).
  assert (U: unsigned y1 = Int.unsigned y).
  { apply unsigned_repr. assert (63 < max_unsigned) by reflexivity. omega. }
  transitivity (shrx x y1).
- unfold shrx', shrx, shl', shl. rewrite U; auto.
- rewrite shrx_carry. 
+ f_equal. 
  unfold shr, shr'. rewrite U; auto.
  unfold shr_carry, shr_carry', shl, shl'. rewrite U; auto.
+ unfold ltu. apply zlt_true. rewrite U; tauto. 
Qed.

Theorem shrx'_shr_2:
  forall x y,
  Int.ltu y (Int.repr 63) = true ->
  shrx' x y = shr' (add x (shru' (shr' x (Int.repr 63)) (Int.sub (Int.repr 64) y))) y.
Proof.
  intros.
  set (z := repr (Int.unsigned y)).
  apply Int.ltu_inv in H. change (Int.unsigned (Int.repr 63)) with 63 in H.
  assert (N1: 63 < max_unsigned) by reflexivity.
  assert (N2: 63 < Int.max_unsigned) by reflexivity.
  assert (A: unsigned z = Int.unsigned y).
  { unfold z; apply unsigned_repr; omega. }
  assert (B: unsigned (sub (repr 64) z) = Int.unsigned (Int.sub (Int.repr 64) y)).
  { unfold z. unfold sub, Int.sub.
    change (unsigned (repr 64)) with 64.
    change (Int.unsigned (Int.repr 64)) with 64.
    rewrite (unsigned_repr (Int.unsigned y)) by omega.
    rewrite unsigned_repr, Int.unsigned_repr by omega.
    auto. }
  unfold shrx', shr', shru', shl'.
  rewrite <- A.
  change (Int.unsigned (Int.repr 63)) with (unsigned (repr 63)).
  rewrite <- B.
  apply shrx_shr_2.
  unfold ltu. apply zlt_true. change (unsigned z < 63). rewrite A; omega.
Qed.

Remark int_ltu_2_inv:
  forall y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.unsigned (Int.add y z) <= Int.unsigned iwordsize' ->
  let y' := repr (Int.unsigned y) in
  let z' := repr (Int.unsigned z) in
     Int.unsigned y = unsigned y'
  /\ Int.unsigned z = unsigned z'
  /\ ltu y' iwordsize = true
  /\ ltu z' iwordsize = true
  /\ Int.unsigned (Int.add y z) = unsigned (add y' z')
  /\ add y' z' = repr (Int.unsigned (Int.add y z)).
Proof.
  intros. apply Int.ltu_inv in H. apply Int.ltu_inv in H0.
  change (Int.unsigned iwordsize') with 64 in *.
  assert (128 < max_unsigned) by reflexivity.
  assert (128 < Int.max_unsigned) by reflexivity.
  assert (Y: unsigned y' = Int.unsigned y) by (apply unsigned_repr; omega).
  assert (Z: unsigned z' = Int.unsigned z) by (apply unsigned_repr; omega).
  assert (P: Int.unsigned (Int.add y z) = unsigned (add y' z')).
  { unfold Int.add. rewrite Int.unsigned_repr by omega.
    unfold add. rewrite unsigned_repr by omega. congruence. }
  intuition auto.
  apply zlt_true. rewrite Y; auto.
  apply zlt_true. rewrite Z; auto.
  rewrite P. rewrite repr_unsigned. auto.
Qed.

Theorem or_ror':
  forall x y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.add y z = iwordsize' ->
  ror x (repr (Int.unsigned z)) = or (shl' x y) (shru' x z).
Proof.
  intros. destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. rewrite H1; omega.
  replace (shl' x y) with (shl x (repr (Int.unsigned y))).
  replace (shru' x z) with (shru x (repr (Int.unsigned z))).
  apply or_ror; auto. rewrite F, H1. reflexivity.
  unfold shru, shru'; rewrite <- B; auto.
  unfold shl, shl'; rewrite <- A; auto.
Qed.

Theorem shl'_shl':
  forall x y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.ltu (Int.add y z) iwordsize' = true ->
  shl' (shl' x y) z = shl' x (Int.add y z).
Proof.
  intros. apply Int.ltu_inv in H1.
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. omega.
  set (y' := repr (Int.unsigned y)) in *.
  set (z' := repr (Int.unsigned z)) in *.
  replace (shl' x y) with (shl x y').
  replace (shl' (shl x y') z) with (shl (shl x y') z').
  replace (shl' x (Int.add y z)) with (shl x (add y' z')).
  apply shl_shl; auto. apply zlt_true. rewrite <- E.
  change (unsigned iwordsize) with zwordsize. tauto.
  unfold shl, shl'. rewrite E; auto.
  unfold shl at 1, shl'. rewrite <- B; auto.
  unfold shl, shl'; rewrite <- A; auto.
Qed.

Theorem shru'_shru':
  forall x y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.ltu (Int.add y z) iwordsize' = true ->
  shru' (shru' x y) z = shru' x (Int.add y z).
Proof.
  intros. apply Int.ltu_inv in H1.
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. omega.
  set (y' := repr (Int.unsigned y)) in *.
  set (z' := repr (Int.unsigned z)) in *.
  replace (shru' x y) with (shru x y').
  replace (shru' (shru x y') z) with (shru (shru x y') z').
  replace (shru' x (Int.add y z)) with (shru x (add y' z')).
  apply shru_shru; auto. apply zlt_true. rewrite <- E.
  change (unsigned iwordsize) with zwordsize. tauto.
  unfold shru, shru'. rewrite E; auto.
  unfold shru at 1, shru'. rewrite <- B; auto.
  unfold shru, shru'; rewrite <- A; auto.
Qed.

Theorem shr'_shr':
  forall x y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.ltu (Int.add y z) iwordsize' = true ->
  shr' (shr' x y) z = shr' x (Int.add y z).
Proof.
  intros. apply Int.ltu_inv in H1.
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. omega.
  set (y' := repr (Int.unsigned y)) in *.
  set (z' := repr (Int.unsigned z)) in *.
  replace (shr' x y) with (shr x y').
  replace (shr' (shr x y') z) with (shr (shr x y') z').
  replace (shr' x (Int.add y z)) with (shr x (add y' z')).
  apply shr_shr; auto. apply zlt_true. rewrite <- E.
  change (unsigned iwordsize) with zwordsize. tauto.
  unfold shr, shr'. rewrite E; auto.
  unfold shr at 1, shr'. rewrite <- B; auto.
  unfold shr, shr'; rewrite <- A; auto.
Qed.

(** Powers of two with exponents given as 32-bit ints *)

Definition one_bits' (x: int) : list Int.int :=
  List.map Int.repr (Z_one_bits wordsize (unsigned x) 0).

Definition is_power2' (x: int) : option Int.int :=
  match Z_one_bits wordsize (unsigned x) 0 with
  | i :: nil => Some (Int.repr i)
  | _ => None
  end.

Theorem one_bits'_range:
  forall x i, In i (one_bits' x) -> Int.ltu i iwordsize' = true.
Proof.
  intros.
  destruct (list_in_map_inv _ _ _ H) as [i0 [EQ IN]].
  exploit Z_one_bits_range; eauto. intros R.
  unfold Int.ltu. rewrite EQ. rewrite Int.unsigned_repr.
  change (Int.unsigned iwordsize') with zwordsize. apply zlt_true. omega.
  assert (zwordsize < Int.max_unsigned) by reflexivity. omega.
Qed.

Fixpoint int_of_one_bits' (l: list Int.int) : int :=
  match l with
  | nil => zero
  | a :: b => add (shl' one a) (int_of_one_bits' b)
  end.

Theorem one_bits'_decomp:
  forall x, x = int_of_one_bits' (one_bits' x).
Proof.
  assert (REC: forall l,
           (forall i, In i l -> 0 <= i < zwordsize) ->
           int_of_one_bits' (List.map Int.repr l) = repr (powerserie l)).
  { induction l; simpl; intros.
  - auto.
  - rewrite IHl by eauto. apply eqm_samerepr; apply eqm_add.
  + rewrite shl'_one_two_p. rewrite Int.unsigned_repr. apply eqm_sym; apply eqm_unsigned_repr.
    exploit (H a). auto. assert (zwordsize < Int.max_unsigned) by reflexivity. omega.
  + apply eqm_sym; apply eqm_unsigned_repr.
  }
  intros. rewrite <- (repr_unsigned x) at 1. unfold one_bits'. rewrite REC.
  rewrite <- Z_one_bits_powerserie. auto. apply unsigned_range.
  apply Z_one_bits_range.
Qed.

Lemma is_power2'_rng:
  forall n logn,
  is_power2' n = Some logn ->
  0 <= Int.unsigned logn < zwordsize.
Proof.
  unfold is_power2'; intros n logn P2.
  destruct (Z_one_bits wordsize (unsigned n) 0) as [ | i [ | ? ?]] eqn:B; inv P2.
  assert (0 <= i < zwordsize).
  { apply Z_one_bits_range with (unsigned n). rewrite B; auto with coqlib. }
  rewrite Int.unsigned_repr. auto.
  assert (zwordsize < Int.max_unsigned) by reflexivity.
  omega.
Qed.

Theorem is_power2'_range:
  forall n logn,
  is_power2' n = Some logn -> Int.ltu logn iwordsize' = true.
Proof.
  intros. unfold Int.ltu. change (Int.unsigned iwordsize') with zwordsize.
  apply zlt_true. generalize (is_power2'_rng _ _ H). tauto.
Qed.

Lemma is_power2'_correct:
  forall n logn,
  is_power2' n = Some logn ->
  unsigned n = two_p (Int.unsigned logn).
Proof.
  unfold is_power2'; intros.
  destruct (Z_one_bits wordsize (unsigned n) 0) as [ | i [ | ? ?]] eqn:B; inv H.
  rewrite (Z_one_bits_powerserie (unsigned n)) by (apply unsigned_range).
  rewrite Int.unsigned_repr. rewrite B; simpl. omega.
  assert (0 <= i < zwordsize).
  { apply Z_one_bits_range with (unsigned n). rewrite B; auto with coqlib. }
  assert (zwordsize < Int.max_unsigned) by reflexivity.
  omega.
Qed.

Theorem mul_pow2':
  forall x n logn,
  is_power2' n = Some logn ->
  mul x n = shl' x logn.
Proof.
  intros. rewrite shl'_mul. f_equal. rewrite shl'_one_two_p.
  rewrite <- (repr_unsigned n). f_equal. apply is_power2'_correct; auto.
Qed.

Theorem divu_pow2':
  forall x n logn,
  is_power2' n = Some logn ->
  divu x n = shru' x logn.
Proof.
  intros. generalize (is_power2'_correct n logn H). intro.
  symmetry. unfold divu. rewrite H0. unfold shru'. rewrite Zshiftr_div_two_p. auto.
  eapply is_power2'_rng; eauto.
Qed.

(** Decomposing 64-bit ints as pairs of 32-bit ints *)

Definition loword (n: int) : Int.int := Int.repr (unsigned n).

Definition hiword (n: int) : Int.int := Int.repr (unsigned (shru n (repr Int.zwordsize))).

Definition ofwords (hi lo: Int.int) : int :=
  or (shl (repr (Int.unsigned hi)) (repr Int.zwordsize)) (repr (Int.unsigned lo)).

Lemma bits_loword:
  forall n i, 0 <= i < Int.zwordsize -> Int.testbit (loword n) i = testbit n i.
Proof.
  intros. unfold loword. rewrite Int.testbit_repr; auto.
Qed.

Lemma bits_hiword:
  forall n i, 0 <= i < Int.zwordsize -> Int.testbit (hiword n) i = testbit n (i + Int.zwordsize).
Proof.
  intros. unfold hiword. rewrite Int.testbit_repr; auto.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  fold (testbit (shru n (repr Int.zwordsize)) i). rewrite bits_shru.
  change (unsigned (repr Int.zwordsize)) with Int.zwordsize.
  apply zlt_true. omega. omega.
Qed.

Lemma bits_ofwords:
  forall hi lo i, 0 <= i < zwordsize ->
  testbit (ofwords hi lo) i =
  if zlt i Int.zwordsize then Int.testbit lo i else Int.testbit hi (i - Int.zwordsize).
Proof.
  intros. unfold ofwords. rewrite bits_or; auto. rewrite bits_shl; auto.
  change (unsigned (repr Int.zwordsize)) with Int.zwordsize.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  destruct (zlt i Int.zwordsize).
  rewrite testbit_repr; auto.
  rewrite !testbit_repr; auto.
  fold (Int.testbit lo i). rewrite Int.bits_above. apply orb_false_r. auto.
  omega.
Qed.

Lemma lo_ofwords:
  forall hi lo, loword (ofwords hi lo) = lo.
Proof.
  intros. apply Int.same_bits_eq; intros.
  rewrite bits_loword; auto. rewrite bits_ofwords. apply zlt_true. omega.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity. omega.
Qed.

Lemma hi_ofwords:
  forall hi lo, hiword (ofwords hi lo) = hi.
Proof.
  intros. apply Int.same_bits_eq; intros.
  rewrite bits_hiword; auto. rewrite bits_ofwords.
  rewrite zlt_false. f_equal. omega. omega.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity. omega.
Qed.

Lemma ofwords_recompose:
  forall n, ofwords (hiword n) (loword n) = n.
Proof.
  intros. apply same_bits_eq; intros. rewrite bits_ofwords; auto.
  destruct (zlt i Int.zwordsize).
  apply bits_loword. omega.
  rewrite bits_hiword. f_equal. omega.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity. omega.
Qed.

Lemma ofwords_add:
  forall lo hi, ofwords hi lo = repr (Int.unsigned hi * two_p 32 + Int.unsigned lo).
Proof.
  intros. unfold ofwords. rewrite shifted_or_is_add.
  apply eqm_samerepr. apply eqm_add. apply eqm_mult.
  apply eqm_sym; apply eqm_unsigned_repr.
  apply eqm_refl.
  apply eqm_sym; apply eqm_unsigned_repr.
  change Int.zwordsize with 32; change zwordsize with 64; omega.
  rewrite unsigned_repr. generalize (Int.unsigned_range lo). intros [A B]. exact B.
  assert (Int.max_unsigned < max_unsigned) by (compute; auto).
  generalize (Int.unsigned_range_2 lo); omega.
Qed.

Lemma ofwords_add':
  forall lo hi, unsigned (ofwords hi lo) = Int.unsigned hi * two_p 32 + Int.unsigned lo.
Proof.
  intros. rewrite ofwords_add. apply unsigned_repr.
  generalize (Int.unsigned_range hi) (Int.unsigned_range lo).
  change (two_p 32) with Int.modulus.
  change Int.modulus with 4294967296.
  change max_unsigned with 18446744073709551615.
  omega.
Qed.

Remark eqm_mul_2p32:
  forall x y, Int.eqm x y -> eqm (x * two_p 32) (y * two_p 32).
Proof.
  intros. destruct H as [k EQ]. exists k. rewrite EQ.
  change Int.modulus with (two_p 32).
  change modulus with (two_p 32 * two_p 32).
  ring.
Qed.

Lemma ofwords_add'':
  forall lo hi, signed (ofwords hi lo) = Int.signed hi * two_p 32 + Int.unsigned lo.
Proof.
  intros. rewrite ofwords_add.
  replace (repr (Int.unsigned hi * two_p 32 + Int.unsigned lo))
     with (repr (Int.signed hi * two_p 32 + Int.unsigned lo)).
  apply signed_repr.
  generalize (Int.signed_range hi) (Int.unsigned_range lo).
  change (two_p 32) with Int.modulus.
  change min_signed with (Int.min_signed * Int.modulus).
  change max_signed with (Int.max_signed * Int.modulus + Int.modulus - 1).
  change Int.modulus with 4294967296.
  omega.
  apply eqm_samerepr. apply eqm_add. apply eqm_mul_2p32. apply Int.eqm_signed_unsigned. apply eqm_refl.
Qed.

(** Expressing 64-bit operations in terms of 32-bit operations *)

Lemma decompose_bitwise_binop:
  forall f f64 f32 xh xl yh yl,
  (forall x y i, 0 <= i < zwordsize -> testbit (f64 x y) i = f (testbit x i) (testbit y i)) ->
  (forall x y i, 0 <= i < Int.zwordsize -> Int.testbit (f32 x y) i = f (Int.testbit x i) (Int.testbit y i)) ->
  f64 (ofwords xh xl) (ofwords yh yl) = ofwords (f32 xh yh) (f32 xl yl).
Proof.
  intros. apply Int64.same_bits_eq; intros.
  rewrite H by auto. rewrite ! bits_ofwords by auto.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  destruct (zlt i Int.zwordsize); rewrite H0 by omega; auto.
Qed.

Lemma decompose_and:
  forall xh xl yh yl,
  and (ofwords xh xl) (ofwords yh yl) = ofwords (Int.and xh yh) (Int.and xl yl).
Proof.
  intros. apply decompose_bitwise_binop with andb.
  apply bits_and. apply Int.bits_and.
Qed.

Lemma decompose_or:
  forall xh xl yh yl,
  or (ofwords xh xl) (ofwords yh yl) = ofwords (Int.or xh yh) (Int.or xl yl).
Proof.
  intros. apply decompose_bitwise_binop with orb.
  apply bits_or. apply Int.bits_or.
Qed.

Lemma decompose_xor:
  forall xh xl yh yl,
  xor (ofwords xh xl) (ofwords yh yl) = ofwords (Int.xor xh yh) (Int.xor xl yl).
Proof.
  intros. apply decompose_bitwise_binop with xorb.
  apply bits_xor. apply Int.bits_xor.
Qed.

Lemma decompose_not:
  forall xh xl,
  not (ofwords xh xl) = ofwords (Int.not xh) (Int.not xl).
Proof.
  intros. unfold not, Int.not. rewrite <- decompose_xor. f_equal.
  apply (Int64.eq_spec mone (ofwords Int.mone Int.mone)).
Qed.

Lemma decompose_shl_1:
  forall xh xl y,
  0 <= Int.unsigned y < Int.zwordsize ->
  shl' (ofwords xh xl) y =
  ofwords (Int.or (Int.shl xh y) (Int.shru xl (Int.sub Int.iwordsize y)))
          (Int.shl xl y).
Proof.
  intros.
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.zwordsize - Int.unsigned y).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; omega. }
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  apply Int64.same_bits_eq; intros.
  rewrite bits_shl' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize). rewrite Int.bits_shl by omega.
  destruct (zlt i (Int.unsigned y)). auto.
  rewrite bits_ofwords by omega. rewrite zlt_true by omega. auto.
  rewrite zlt_false by omega. rewrite bits_ofwords by omega.
  rewrite Int.bits_or by omega. rewrite Int.bits_shl by omega.
  rewrite Int.bits_shru by omega. rewrite H0.
  destruct (zlt (i - Int.unsigned y) (Int.zwordsize)).
  rewrite zlt_true by omega. rewrite zlt_true by omega.
  rewrite orb_false_l. f_equal. omega.
  rewrite zlt_false by omega. rewrite zlt_false by omega.
  rewrite orb_false_r. f_equal. omega.
Qed.

Lemma decompose_shl_2:
  forall xh xl y,
  Int.zwordsize <= Int.unsigned y < zwordsize ->
  shl' (ofwords xh xl) y =
  ofwords (Int.shl xl (Int.sub y Int.iwordsize)) Int.zero.
Proof.
  intros.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.zwordsize).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). omega. }
  apply Int64.same_bits_eq; intros.
  rewrite bits_shl' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize). rewrite zlt_true by omega. apply Int.bits_zero.
  rewrite Int.bits_shl by omega.
  destruct (zlt i (Int.unsigned y)).
  rewrite zlt_true by omega. auto.
  rewrite zlt_false by omega.
  rewrite bits_ofwords by omega. rewrite zlt_true by omega. f_equal. omega.
Qed.

Lemma decompose_shru_1:
  forall xh xl y,
  0 <= Int.unsigned y < Int.zwordsize ->
  shru' (ofwords xh xl) y =
  ofwords (Int.shru xh y)
          (Int.or (Int.shru xl y) (Int.shl xh (Int.sub Int.iwordsize y))).
Proof.
  intros.
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.zwordsize - Int.unsigned y).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; omega. }
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  apply Int64.same_bits_eq; intros.
  rewrite bits_shru' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  rewrite zlt_true by omega.
  rewrite bits_ofwords by omega.
  rewrite Int.bits_or by omega. rewrite Int.bits_shl by omega.
  rewrite Int.bits_shru by omega. rewrite H0.
  destruct (zlt (i + Int.unsigned y) (Int.zwordsize)).
  rewrite zlt_true by omega.
  rewrite orb_false_r. auto.
  rewrite zlt_false by omega.
  rewrite orb_false_l. f_equal. omega.
  rewrite Int.bits_shru by omega.
  destruct (zlt (i + Int.unsigned y) zwordsize).
  rewrite bits_ofwords by omega.
  rewrite zlt_true by omega. rewrite zlt_false by omega. f_equal. omega.
  rewrite zlt_false by omega. auto.
Qed.

Lemma decompose_shru_2:
  forall xh xl y,
  Int.zwordsize <= Int.unsigned y < zwordsize ->
  shru' (ofwords xh xl) y =
  ofwords Int.zero (Int.shru xh (Int.sub y Int.iwordsize)).
Proof.
  intros.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.zwordsize).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). omega. }
  apply Int64.same_bits_eq; intros.
  rewrite bits_shru' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  rewrite Int.bits_shru by omega. rewrite H1.
  destruct (zlt (i + Int.unsigned y) zwordsize).
  rewrite zlt_true by omega. rewrite bits_ofwords by omega.
  rewrite zlt_false by omega. f_equal; omega.
  rewrite zlt_false by omega. auto.
  rewrite zlt_false by omega. apply Int.bits_zero.
Qed.

Lemma decompose_shr_1:
  forall xh xl y,
  0 <= Int.unsigned y < Int.zwordsize ->
  shr' (ofwords xh xl) y =
  ofwords (Int.shr xh y)
          (Int.or (Int.shru xl y) (Int.shl xh (Int.sub Int.iwordsize y))).
Proof.
  intros.
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.zwordsize - Int.unsigned y).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; omega. }
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  apply Int64.same_bits_eq; intros.
  rewrite bits_shr' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  rewrite zlt_true by omega.
  rewrite bits_ofwords by omega.
  rewrite Int.bits_or by omega. rewrite Int.bits_shl by omega.
  rewrite Int.bits_shru by omega. rewrite H0.
  destruct (zlt (i + Int.unsigned y) (Int.zwordsize)).
  rewrite zlt_true by omega.
  rewrite orb_false_r. auto.
  rewrite zlt_false by omega.
  rewrite orb_false_l. f_equal. omega.
  rewrite Int.bits_shr by omega.
  destruct (zlt (i + Int.unsigned y) zwordsize).
  rewrite bits_ofwords by omega.
  rewrite zlt_true by omega. rewrite zlt_false by omega. f_equal. omega.
  rewrite zlt_false by omega. rewrite bits_ofwords by omega.
  rewrite zlt_false by omega. f_equal.
Qed.

Lemma decompose_shr_2:
  forall xh xl y,
  Int.zwordsize <= Int.unsigned y < zwordsize ->
  shr' (ofwords xh xl) y =
  ofwords (Int.shr xh (Int.sub Int.iwordsize Int.one))
          (Int.shr xh (Int.sub y Int.iwordsize)).
Proof.
  intros.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.zwordsize).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). omega. }
  apply Int64.same_bits_eq; intros.
  rewrite bits_shr' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  rewrite Int.bits_shr by omega. rewrite H1.
  destruct (zlt (i + Int.unsigned y) zwordsize).
  rewrite zlt_true by omega. rewrite bits_ofwords by omega.
  rewrite zlt_false by omega. f_equal; omega.
  rewrite zlt_false by omega. rewrite bits_ofwords by omega.
  rewrite zlt_false by omega. auto.
  rewrite Int.bits_shr by omega.
  change (Int.unsigned (Int.sub Int.iwordsize Int.one)) with (Int.zwordsize - 1).
  destruct (zlt (i + Int.unsigned y) zwordsize);
  rewrite bits_ofwords by omega.
  symmetry. rewrite zlt_false by omega. f_equal.
  destruct (zlt (i - Int.zwordsize + (Int.zwordsize - 1)) Int.zwordsize); omega.
  symmetry. rewrite zlt_false by omega. f_equal.
  destruct (zlt (i - Int.zwordsize + (Int.zwordsize - 1)) Int.zwordsize); omega.
Qed.

Lemma decompose_add:
  forall xh xl yh yl,
  add (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add xh yh) (Int.add_carry xl yl Int.zero))
          (Int.add xl yl).
Proof.
  intros. symmetry. rewrite ofwords_add. rewrite add_unsigned.
  apply eqm_samerepr.
  rewrite ! ofwords_add'. rewrite (Int.unsigned_add_carry xl yl).
  set (cc := Int.add_carry xl yl Int.zero).
  set (Xl := Int.unsigned xl); set (Xh := Int.unsigned xh);
  set (Yl := Int.unsigned yl); set (Yh := Int.unsigned yh).
  change Int.modulus with (two_p 32).
  replace (Xh * two_p 32 + Xl + (Yh * two_p 32 + Yl))
     with ((Xh + Yh) * two_p 32 + (Xl + Yl)) by ring.
  replace (Int.unsigned (Int.add (Int.add xh yh) cc) * two_p 32 +
              (Xl + Yl - Int.unsigned cc * two_p 32))
     with ((Int.unsigned (Int.add (Int.add xh yh) cc) - Int.unsigned cc) * two_p 32
           + (Xl + Yl)) by ring.
  apply eqm_add. 2: apply eqm_refl. apply eqm_mul_2p32.
  replace (Xh + Yh) with ((Xh + Yh + Int.unsigned cc) - Int.unsigned cc) by ring.
  apply Int.eqm_sub. 2: apply Int.eqm_refl.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_add. 2: apply Int.eqm_refl.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
Qed.

Lemma decompose_sub:
  forall xh xl yh yl,
  sub (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.sub (Int.sub xh yh) (Int.sub_borrow xl yl Int.zero))
          (Int.sub xl yl).
Proof.
  intros. symmetry. rewrite ofwords_add.
  apply eqm_samerepr.
  rewrite ! ofwords_add'. rewrite (Int.unsigned_sub_borrow xl yl).
  set (bb := Int.sub_borrow xl yl Int.zero).
  set (Xl := Int.unsigned xl); set (Xh := Int.unsigned xh);
  set (Yl := Int.unsigned yl); set (Yh := Int.unsigned yh).
  change Int.modulus with (two_p 32).
  replace (Xh * two_p 32 + Xl - (Yh * two_p 32 + Yl))
     with ((Xh - Yh) * two_p 32 + (Xl - Yl)) by ring.
  replace (Int.unsigned (Int.sub (Int.sub xh yh) bb) * two_p 32 +
              (Xl - Yl + Int.unsigned bb * two_p 32))
     with ((Int.unsigned (Int.sub (Int.sub xh yh) bb) + Int.unsigned bb) * two_p 32
           + (Xl - Yl)) by ring.
  apply eqm_add. 2: apply eqm_refl. apply eqm_mul_2p32.
  replace (Xh - Yh) with ((Xh - Yh - Int.unsigned bb) + Int.unsigned bb) by ring.
  apply Int.eqm_add. 2: apply Int.eqm_refl.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_add. 2: apply Int.eqm_refl.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
Qed.

Lemma decompose_sub':
  forall xh xl yh yl,
  sub (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add xh (Int.not yh)) (Int.add_carry xl (Int.not yl) Int.one))
          (Int.sub xl yl).
Proof.
  intros. rewrite decompose_sub. f_equal.
  rewrite Int.sub_borrow_add_carry by auto.
  rewrite Int.sub_add_not_3. rewrite Int.xor_assoc. rewrite Int.xor_idem.
  rewrite Int.xor_zero. auto.
  rewrite Int.xor_zero_l. unfold Int.add_carry.
  destruct (zlt (Int.unsigned xl + Int.unsigned (Int.not yl) + Int.unsigned Int.one) Int.modulus);
  compute; [right|left]; apply Int.mkint_eq; auto.
Qed.

Definition mul' (x y: Int.int) : int := repr (Int.unsigned x * Int.unsigned y).

Lemma mul'_mulhu:
  forall x y, mul' x y = ofwords (Int.mulhu x y) (Int.mul x y).
Proof.
  intros.
  rewrite ofwords_add. unfold mul', Int.mulhu, Int.mul.
  set (p := Int.unsigned x * Int.unsigned y).
  set (ph := p / Int.modulus). set (pl := p mod Int.modulus).
  transitivity (repr (ph * Int.modulus + pl)).
- f_equal. rewrite Z.mul_comm. apply Z_div_mod_eq. apply Int.modulus_pos.
- apply eqm_samerepr. apply eqm_add. apply eqm_mul_2p32. auto with ints.
  rewrite Int.unsigned_repr_eq. apply eqm_refl.
Qed.

Lemma decompose_mul:
  forall xh xl yh yl,
  mul (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add (hiword (mul' xl yl)) (Int.mul xl yh)) (Int.mul xh yl))
          (loword (mul' xl yl)).
Proof.
  intros.
  set (pl := loword (mul' xl yl)); set (ph := hiword (mul' xl yl)).
  assert (EQ0: unsigned (mul' xl yl) = Int.unsigned ph * two_p 32 + Int.unsigned pl).
  { rewrite <- (ofwords_recompose (mul' xl yl)). apply ofwords_add'. }
  symmetry. rewrite ofwords_add. unfold mul. rewrite !ofwords_add'.
  set (XL := Int.unsigned xl); set (XH := Int.unsigned xh);
  set (YL := Int.unsigned yl); set (YH := Int.unsigned yh).
  set (PH := Int.unsigned ph) in *. set (PL := Int.unsigned pl) in *.
  transitivity (repr (((PH + XL * YH) + XH * YL) * two_p 32 + PL)).
  apply eqm_samerepr. apply eqm_add. 2: apply eqm_refl.
  apply eqm_mul_2p32.
  rewrite Int.add_unsigned. apply Int.eqm_unsigned_repr_l. apply Int.eqm_add.
  rewrite Int.add_unsigned. apply Int.eqm_unsigned_repr_l. apply Int.eqm_add.
  apply Int.eqm_refl.
  unfold Int.mul. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
  unfold Int.mul. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
  transitivity (repr (unsigned (mul' xl yl) + (XL * YH + XH * YL) * two_p 32)).
  rewrite EQ0. f_equal. ring.
  transitivity (repr ((XL * YL + (XL * YH + XH * YL) * two_p 32))).
  apply eqm_samerepr. apply eqm_add. 2: apply eqm_refl.
  unfold mul'. apply eqm_unsigned_repr_l. apply eqm_refl.
  transitivity (repr (0 + (XL * YL + (XL * YH + XH * YL) * two_p 32))).
  rewrite Z.add_0_l; auto.
  transitivity (repr (XH * YH * (two_p 32 * two_p 32) + (XL * YL + (XL * YH + XH * YL) * two_p 32))).
  apply eqm_samerepr. apply eqm_add. 2: apply eqm_refl.
  change (two_p 32 * two_p 32) with modulus. exists (- XH * YH). ring.
  f_equal. ring.
Qed.

Lemma decompose_mul_2:
  forall xh xl yh yl,
  mul (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add (Int.mulhu xl yl) (Int.mul xl yh)) (Int.mul xh yl))
          (Int.mul xl yl).
Proof.
  intros. rewrite decompose_mul. rewrite mul'_mulhu.
  rewrite hi_ofwords, lo_ofwords. auto.
Qed.

Lemma decompose_ltu:
  forall xh xl yh yl,
  ltu (ofwords xh xl) (ofwords yh yl) = if Int.eq xh yh then Int.ltu xl yl else Int.ltu xh yh.
Proof.
  intros. unfold ltu. rewrite ! ofwords_add'. unfold Int.ltu, Int.eq.
  destruct (zeq (Int.unsigned xh) (Int.unsigned yh)).
  rewrite e. destruct (zlt (Int.unsigned xl) (Int.unsigned yl)).
  apply zlt_true; omega.
  apply zlt_false; omega.
  change (two_p 32) with Int.modulus.
  generalize (Int.unsigned_range xl) (Int.unsigned_range yl).
  change Int.modulus with 4294967296. intros.
  destruct (zlt (Int.unsigned xh) (Int.unsigned yh)).
  apply zlt_true; omega.
  apply zlt_false; omega.
Qed.

Lemma decompose_leu:
  forall xh xl yh yl,
  negb (ltu (ofwords yh yl) (ofwords xh xl)) =
  if Int.eq xh yh then negb (Int.ltu yl xl) else Int.ltu xh yh.
Proof.
  intros. rewrite decompose_ltu. rewrite Int.eq_sym.
  unfold Int.eq. destruct (zeq (Int.unsigned xh) (Int.unsigned yh)).
  auto.
  unfold Int.ltu. destruct (zlt (Int.unsigned xh) (Int.unsigned yh)).
  rewrite zlt_false by omega; auto.
  rewrite zlt_true by omega; auto.
Qed.

Lemma decompose_lt:
  forall xh xl yh yl,
  lt (ofwords xh xl) (ofwords yh yl) = if Int.eq xh yh then Int.ltu xl yl else Int.lt xh yh.
Proof.
  intros. unfold lt. rewrite ! ofwords_add''. rewrite Int.eq_signed.
  destruct (zeq (Int.signed xh) (Int.signed yh)).
  rewrite e. unfold Int.ltu. destruct (zlt (Int.unsigned xl) (Int.unsigned yl)).
  apply zlt_true; omega.
  apply zlt_false; omega.
  change (two_p 32) with Int.modulus.
  generalize (Int.unsigned_range xl) (Int.unsigned_range yl).
  change Int.modulus with 4294967296. intros.
  unfold Int.lt. destruct (zlt (Int.signed xh) (Int.signed yh)).
  apply zlt_true; omega.
  apply zlt_false; omega.
Qed.

Lemma decompose_le:
  forall xh xl yh yl,
  negb (lt (ofwords yh yl) (ofwords xh xl)) =
  if Int.eq xh yh then negb (Int.ltu yl xl) else Int.lt xh yh.
Proof.
  intros. rewrite decompose_lt. rewrite Int.eq_sym.
  rewrite Int.eq_signed. destruct (zeq (Int.signed xh) (Int.signed yh)).
  auto.
  unfold Int.lt. destruct (zlt (Int.signed xh) (Int.signed yh)).
  rewrite zlt_false by omega; auto.
  rewrite zlt_true by omega; auto.
Qed.

(** Utility proofs for mixed 32bit and 64bit arithmetic *)

Remark int_unsigned_range:
  forall x, 0 <= Int.unsigned x <= max_unsigned.
Proof.
  intros.
  unfold max_unsigned. unfold modulus.
  generalize (Int.unsigned_range x).
  unfold Int.modulus in *.
  change (wordsize) with  64%nat in *.
  change (Int.wordsize) with 32%nat in *.
  unfold two_power_nat. simpl.
  omega.
Qed.

Remark int_unsigned_repr:
  forall x, unsigned (repr (Int.unsigned x)) = Int.unsigned x.
Proof.
  intros. rewrite unsigned_repr. auto.
  apply int_unsigned_range.
Qed.

Lemma int_sub_ltu:
  forall x y,
    Int.ltu x y= true ->
    Int.unsigned (Int.sub y x) = unsigned (sub (repr (Int.unsigned y)) (repr (Int.unsigned x))).
Proof.
  intros. generalize (Int.sub_ltu x y H). intros. unfold Int.sub. unfold sub.
  rewrite Int.unsigned_repr. rewrite unsigned_repr.
  rewrite unsigned_repr by apply int_unsigned_range. rewrite int_unsigned_repr. reflexivity.
  rewrite unsigned_repr by apply int_unsigned_range.
  rewrite int_unsigned_repr. generalize (int_unsigned_range y).
  omega.
  generalize (Int.sub_ltu x y H). intros.
  generalize (Int.unsigned_range_2 y). intros. omega.
Qed.

End Int64.

Strategy 0 [Wordsize_64.wordsize].

Notation int64 := Int64.int.

Global Opaque Int.repr Int64.repr Byte.repr.

(** * Specialization to offsets in pointer values *)

Module Wordsize_Ptrofs.
  Definition wordsize := if Archi.ptr64 then 64%nat else 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; destruct Archi.ptr64; congruence. Qed.
End Wordsize_Ptrofs.

Strategy opaque [Wordsize_Ptrofs.wordsize].

Module Ptrofs.

Include Make(Wordsize_Ptrofs).

Definition to_int (x: int): Int.int := Int.repr (unsigned x).

Definition to_int64 (x: int): Int64.int := Int64.repr (unsigned x).

Definition of_int (x: Int.int) : int := repr (Int.unsigned x).

Definition of_intu := of_int.

Definition of_ints (x: Int.int) : int := repr (Int.signed x).

Definition of_int64 (x: Int64.int) : int := repr (Int64.unsigned x).

Definition of_int64u := of_int64.

Definition of_int64s (x: Int64.int) : int := repr (Int64.signed x).

Section AGREE32.

Hypothesis _32: Archi.ptr64 = false.

Lemma modulus_eq32: modulus = Int.modulus.
Proof.
  unfold modulus, wordsize.
  change Wordsize_Ptrofs.wordsize with (if Archi.ptr64 then 64%nat else 32%nat).
  rewrite _32. reflexivity.
Qed.

Lemma eqm32:
  forall x y, Int.eqm x y <-> eqm x y.
Proof.
  intros. unfold Int.eqm, eqm. rewrite modulus_eq32; tauto.
Qed.

Definition agree32 (a: Ptrofs.int) (b: Int.int) : Prop :=
  Ptrofs.unsigned a = Int.unsigned b.

Lemma agree32_repr:
  forall i, agree32 (Ptrofs.repr i) (Int.repr i).
Proof.
  intros; red. rewrite Ptrofs.unsigned_repr_eq, Int.unsigned_repr_eq.
  apply f_equal2. auto. apply modulus_eq32.
Qed.

Lemma agree32_signed:
  forall a b, agree32 a b -> Ptrofs.signed a = Int.signed b.
Proof.
  unfold agree32; intros. unfold signed, Int.signed, half_modulus, Int.half_modulus.
  rewrite modulus_eq32. rewrite H. auto.
Qed.

Lemma agree32_of_int:
  forall b, agree32 (of_int b) b.
Proof.
  unfold of_int; intros. rewrite <- (Int.repr_unsigned b) at 2. apply agree32_repr.
Qed.

Lemma agree32_of_ints:
  forall b, agree32 (of_ints b) b.
Proof.
  unfold of_int; intros. rewrite <- (Int.repr_signed b) at 2. apply agree32_repr.
Qed.

Lemma agree32_of_int_eq:
  forall a b, agree32 a b -> of_int b = a.
Proof.
  unfold agree32, of_int; intros. rewrite <- H. apply repr_unsigned.
Qed.

Lemma agree32_of_ints_eq:
  forall a b, agree32 a b -> of_ints b = a.
Proof.
  unfold of_ints; intros. erewrite <- agree32_signed by eauto. apply repr_signed.
Qed.

Lemma agree32_to_int:
  forall a, agree32 a (to_int a).
Proof.
  unfold agree32, to_int; intros. rewrite <- (agree32_repr (unsigned a)).
  rewrite repr_unsigned; auto.
Qed.

Lemma agree32_to_int_eq:
  forall a b, agree32 a b -> to_int a = b.
Proof.
  unfold agree32, to_int; intros. rewrite H. apply Int.repr_unsigned.
Qed.

Lemma agree32_neg:
  forall a1 b1, agree32 a1 b1 -> agree32 (Ptrofs.neg a1) (Int.neg b1).
Proof.
  unfold agree32, Ptrofs.neg, Int.neg; intros. rewrite H. apply agree32_repr.
Qed.

Lemma agree32_add:
  forall a1 b1 a2 b2,
  agree32 a1 b1 -> agree32 a2 b2 -> agree32 (Ptrofs.add a1 a2) (Int.add b1 b2).
Proof.
  unfold agree32, Ptrofs.add, Int.add; intros. rewrite H, H0. apply agree32_repr.
Qed.

Lemma agree32_sub:
  forall a1 b1 a2 b2,
  agree32 a1 b1 -> agree32 a2 b2 -> agree32 (Ptrofs.sub a1 a2) (Int.sub b1 b2).
Proof.
  unfold agree32, Ptrofs.sub, Int.sub; intros. rewrite H, H0. apply agree32_repr.
Qed.

Lemma agree32_mul:
  forall a1 b1 a2 b2,
  agree32 a1 b1 -> agree32 a2 b2 -> agree32 (Ptrofs.mul a1 a2) (Int.mul b1 b2).
Proof.
  unfold agree32, Ptrofs.mul, Int.mul; intros. rewrite H, H0. apply agree32_repr.
Qed.

Lemma agree32_divs:
  forall a1 b1 a2 b2,
  agree32 a1 b1 -> agree32 a2 b2 -> agree32 (Ptrofs.divs a1 a2) (Int.divs b1 b2).
Proof.
  intros; unfold agree32, Ptrofs.divs, Int.divs.
  erewrite ! agree32_signed by eauto. apply agree32_repr.
Qed.

Lemma of_int_to_int:
  forall n, of_int (to_int n) = n.
Proof.
  intros; unfold of_int, to_int. apply eqm_repr_eq. rewrite <- eqm32.
  apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Lemma to_int_of_int:
  forall n, to_int (of_int n) = n.
Proof.
  intros; unfold of_int, to_int. rewrite unsigned_repr. apply Int.repr_unsigned.
  unfold max_unsigned. rewrite modulus_eq32. destruct (Int.unsigned_range n); omega.
Qed.

End AGREE32.

Section AGREE64.

Hypothesis _64: Archi.ptr64 = true.

Lemma modulus_eq64: modulus = Int64.modulus.
Proof.
  unfold modulus, wordsize.
  change Wordsize_Ptrofs.wordsize with (if Archi.ptr64 then 64%nat else 32%nat).
  rewrite _64. reflexivity.
Qed.

Lemma eqm64:
  forall x y, Int64.eqm x y <-> eqm x y.
Proof.
  intros. unfold Int64.eqm, eqm. rewrite modulus_eq64; tauto.
Qed.

Definition agree64 (a: Ptrofs.int) (b: Int64.int) : Prop :=
  Ptrofs.unsigned a = Int64.unsigned b.

Lemma agree64_repr:
  forall i, agree64 (Ptrofs.repr i) (Int64.repr i).
Proof.
  intros; red. rewrite Ptrofs.unsigned_repr_eq, Int64.unsigned_repr_eq.
  apply f_equal2. auto. apply modulus_eq64.
Qed.

Lemma agree64_signed:
  forall a b, agree64 a b -> Ptrofs.signed a = Int64.signed b.
Proof.
  unfold agree64; intros. unfold signed, Int64.signed, half_modulus, Int64.half_modulus.
  rewrite modulus_eq64. rewrite H. auto.
Qed.

Lemma agree64_of_int:
  forall b, agree64 (of_int64 b) b.
Proof.
  unfold of_int64; intros. rewrite <- (Int64.repr_unsigned b) at 2. apply agree64_repr.
Qed.

Lemma agree64_of_int_eq:
  forall a b, agree64 a b -> of_int64 b = a.
Proof.
  unfold agree64, of_int64; intros. rewrite <- H. apply repr_unsigned.
Qed.

Lemma agree64_to_int:
  forall a, agree64 a (to_int64 a).
Proof.
  unfold agree64, to_int64; intros. rewrite <- (agree64_repr (unsigned a)).
  rewrite repr_unsigned; auto.
Qed.

Lemma agree64_to_int_eq:
  forall a b, agree64 a b -> to_int64 a = b.
Proof.
  unfold agree64, to_int64; intros. rewrite H. apply Int64.repr_unsigned.
Qed.

Lemma agree64_neg:
  forall a1 b1, agree64 a1 b1 -> agree64 (Ptrofs.neg a1) (Int64.neg b1).
Proof.
  unfold agree64, Ptrofs.neg, Int64.neg; intros. rewrite H. apply agree64_repr.
Qed.

Lemma agree64_add:
  forall a1 b1 a2 b2,
  agree64 a1 b1 -> agree64 a2 b2 -> agree64 (Ptrofs.add a1 a2) (Int64.add b1 b2).
Proof.
  unfold agree64, Ptrofs.add, Int.add; intros. rewrite H, H0. apply agree64_repr.
Qed.

Lemma agree64_sub:
  forall a1 b1 a2 b2,
  agree64 a1 b1 -> agree64 a2 b2 -> agree64 (Ptrofs.sub a1 a2) (Int64.sub b1 b2).
Proof.
  unfold agree64, Ptrofs.sub, Int.sub; intros. rewrite H, H0. apply agree64_repr.
Qed.

Lemma agree64_mul:
  forall a1 b1 a2 b2,
  agree64 a1 b1 -> agree64 a2 b2 -> agree64 (Ptrofs.mul a1 a2) (Int64.mul b1 b2).
Proof.
  unfold agree64, Ptrofs.mul, Int.mul; intros. rewrite H, H0. apply agree64_repr.
Qed.

Lemma agree64_divs:
  forall a1 b1 a2 b2,
  agree64 a1 b1 -> agree64 a2 b2 -> agree64 (Ptrofs.divs a1 a2) (Int64.divs b1 b2).
Proof.
  intros; unfold agree64, Ptrofs.divs, Int64.divs.
  erewrite ! agree64_signed by eauto. apply agree64_repr.
Qed.

Lemma of_int64_to_int64:
  forall n, of_int64 (to_int64 n) = n.
Proof.
  intros; unfold of_int64, to_int64. apply eqm_repr_eq. rewrite <- eqm64.
  apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma to_int64_of_int64:
  forall n, to_int64 (of_int64 n) = n.
Proof.
  intros; unfold of_int64, to_int64. rewrite unsigned_repr. apply Int64.repr_unsigned.
  unfold max_unsigned. rewrite  modulus_eq64. destruct (Int64.unsigned_range n); omega.
Qed.

End AGREE64.

Hint Resolve
  agree32_repr agree32_of_int agree32_of_ints agree32_of_int_eq agree32_of_ints_eq
  agree32_to_int agree32_to_int_eq agree32_neg agree32_add agree32_sub agree32_mul agree32_divs
  agree64_repr agree64_of_int agree64_of_int_eq
  agree64_to_int agree64_to_int_eq agree64_neg agree64_add agree64_sub agree64_mul agree64_divs : ptrofs.

End Ptrofs.

Strategy 0 [Wordsize_Ptrofs.wordsize].

Notation ptrofs := Ptrofs.int.

Global Opaque Ptrofs.repr.

Hint Resolve Int.modulus_pos Int.eqm_refl Int.eqm_refl2 Int.eqm_sym Int.eqm_trans
  Int.eqm_small_eq Int.eqm_add Int.eqm_neg Int.eqm_sub Int.eqm_mult
  Int.eqm_unsigned_repr Int.eqm_unsigned_repr_l Int.eqm_unsigned_repr_r
  Int.unsigned_range Int.unsigned_range_2
  Int.repr_unsigned Int.repr_signed Int.unsigned_repr : ints.

Hint Resolve Int64.modulus_pos Int64.eqm_refl Int64.eqm_refl2 Int64.eqm_sym Int64.eqm_trans
  Int64.eqm_small_eq Int64.eqm_add Int64.eqm_neg Int64.eqm_sub Int64.eqm_mult
  Int64.eqm_unsigned_repr Int64.eqm_unsigned_repr_l Int64.eqm_unsigned_repr_r
  Int64.unsigned_range Int64.unsigned_range_2
  Int64.repr_unsigned Int64.repr_signed Int64.unsigned_repr : ints.

Hint Resolve Ptrofs.modulus_pos Ptrofs.eqm_refl Ptrofs.eqm_refl2 Ptrofs.eqm_sym Ptrofs.eqm_trans
  Ptrofs.eqm_small_eq Ptrofs.eqm_add Ptrofs.eqm_neg Ptrofs.eqm_sub Ptrofs.eqm_mult
  Ptrofs.eqm_unsigned_repr Ptrofs.eqm_unsigned_repr_l Ptrofs.eqm_unsigned_repr_r
  Ptrofs.unsigned_range Ptrofs.unsigned_range_2
  Ptrofs.repr_unsigned Ptrofs.repr_signed Ptrofs.unsigned_repr : ints.


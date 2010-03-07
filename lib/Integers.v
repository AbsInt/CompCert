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
  generalize (proof_irrelevance _ Px Py); intro.
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

Definition zero_ext (n: Z) (x: int) : int :=
  repr (Zmod (unsigned x) (two_p n)).
Definition sign_ext (n: Z) (x: int) : int :=
  repr (let p := two_p n in
        let y := Zmod (unsigned x) p in
        if zlt y (two_p (n-1)) then y else y - p).

Definition add (x y: int) : int :=
  repr (unsigned x + unsigned y).
Definition sub (x y: int) : int :=
  repr (unsigned x - unsigned y).
Definition mul (x y: int) : int :=
  repr (unsigned x * unsigned y).

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
  of the number.  The values of characteristic functions for [i] greater
  than 32 are ignored. *)

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

Fixpoint Z_of_bits (n: nat) (f: Z -> bool) {struct n}: Z :=
  match n with
  | O => 0
  | S m => Z_shift_add (f 0) (Z_of_bits m (fun i => f (i + 1)))
  end.

(** Bitwise logical ``and'', ``or'' and ``xor'' operations. *)

Definition bitwise_binop (f: bool -> bool -> bool) (x y: int) :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let fy := bits_of_Z wordsize (unsigned y) in
  repr (Z_of_bits wordsize (fun i => f (fx i) (fy i))).

Definition and (x y: int): int := bitwise_binop andb x y.
Definition or (x y: int): int := bitwise_binop orb x y.
Definition xor (x y: int) : int := bitwise_binop xorb x y.

Definition not (x: int) : int := xor x mone.

(** Shifts and rotates. *)

Definition shl (x y: int): int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let vy := unsigned y in
  repr (Z_of_bits wordsize (fun i => fx (i - vy))).

Definition shru (x y: int): int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let vy := unsigned y in
  repr (Z_of_bits wordsize (fun i => fx (i + vy))).

(** Arithmetic right shift is defined as signed division by a power of two.
  Two such shifts are defined: [shr] rounds towards minus infinity
  (standard behaviour for arithmetic right shift) and
  [shrx] rounds towards zero. *)

Definition shr (x y: int): int :=
  repr (signed x / two_p (unsigned y)).

Definition shrx (x y: int): int :=
  divs x (shl one y).

Definition shr_carry (x y: int) :=
  sub (shrx x y) (shr x y).

Definition rol (x y: int) : int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let vy := unsigned y in
  repr (Z_of_bits wordsize
         (fun i => fx (Zmod (i - vy) (Z_of_nat wordsize)))).

Definition ror (x y: int) : int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let vy := unsigned y in
  repr (Z_of_bits wordsize
         (fun i => fx (Zmod (i + vy) (Z_of_nat wordsize)))).

Definition rolm (x a m: int): int := and (rol x a) m.

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

(** Recognition of integers that are acceptable as immediate operands
  to the [rlwim] PowerPC instruction.  These integers are of the form
  [000011110000] or [111100001111], that is, a run of one bits
  surrounded by zero bits, or conversely.  We recognize these integers by
  running the following automaton on the bits.  The accepting states are
  2, 3, 4, 5, and 6.
<<
               0          1          0
              / \        / \        / \
              \ /        \ /        \ /
        -0--> [1] --1--> [2] --0--> [3]
       /     
     [0]
       \
        -1--> [4] --0--> [5] --1--> [6]
              / \        / \        / \
              \ /        \ /        \ /
               1          0          1
>>
*)

Inductive rlw_state: Type :=
  | RLW_S0 : rlw_state
  | RLW_S1 : rlw_state
  | RLW_S2 : rlw_state
  | RLW_S3 : rlw_state
  | RLW_S4 : rlw_state
  | RLW_S5 : rlw_state
  | RLW_S6 : rlw_state
  | RLW_Sbad : rlw_state.

Definition rlw_transition (s: rlw_state) (b: bool) : rlw_state :=
  match s, b with
  | RLW_S0, false => RLW_S1
  | RLW_S0, true  => RLW_S4
  | RLW_S1, false => RLW_S1
  | RLW_S1, true  => RLW_S2
  | RLW_S2, false => RLW_S3
  | RLW_S2, true  => RLW_S2
  | RLW_S3, false => RLW_S3
  | RLW_S3, true  => RLW_Sbad
  | RLW_S4, false => RLW_S5
  | RLW_S4, true  => RLW_S4
  | RLW_S5, false => RLW_S5
  | RLW_S5, true  => RLW_S6
  | RLW_S6, false => RLW_Sbad
  | RLW_S6, true  => RLW_S6
  | RLW_Sbad, _ => RLW_Sbad
  end.

Definition rlw_accepting (s: rlw_state) : bool :=
  match s with
  | RLW_S0 => false
  | RLW_S1 => false
  | RLW_S2 => true
  | RLW_S3 => true
  | RLW_S4 => true
  | RLW_S5 => true
  | RLW_S6 => true
  | RLW_Sbad => false
  end.

Fixpoint is_rlw_mask_rec (n: nat) (s: rlw_state) (x: Z) {struct n} : bool :=
  match n with
  | O =>
      rlw_accepting s
  | S m =>
      let (b, y) := Z_bin_decomp x in
      is_rlw_mask_rec m (rlw_transition s b) y
  end.

Definition is_rlw_mask (x: int) : bool :=
  is_rlw_mask_rec wordsize RLW_S0 (unsigned x).

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

Lemma eqm_samerepr: forall x y, eqm x y -> repr x = repr y.
Proof.
  intros. unfold repr. apply mkint_eq. 
  apply eqmod_mod_eq. auto with ints. exact H.
Qed.

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

Lemma eqm_unsigned_repr:
  forall z, eqm z (unsigned (repr z)).
Proof.
  unfold eqm, repr, unsigned; intros; simpl.
  apply eqmod_mod. auto with ints.
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
  destruct i; simpl. auto.
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
  apply Zmod_small. auto.
Qed.
Hint Resolve repr_unsigned: ints.

Lemma repr_signed:
  forall i, repr (signed i) = i.
Proof.
  intros. transitivity (repr (unsigned i)). 
  apply eqm_samerepr. apply eqm_signed_unsigned. auto with ints.
Qed.
Hint Resolve repr_signed: ints.

Theorem unsigned_repr:
  forall z, 0 <= z <= max_unsigned -> unsigned (repr z) = z.
Proof.
  intros. unfold repr, unsigned; simpl. 
  apply Zmod_small. unfold max_unsigned in H. omega.
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
  intros; unfold add, zero. change (unsigned (repr 0)) with 0.
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
  unfold neg, zero. compute. apply mkint_eq. auto.
Qed.

Theorem neg_involutive: forall x, neg (neg x) = x.
Proof.
  intros; unfold neg. transitivity (repr (unsigned x)).
  apply eqm_samerepr. apply eqm_trans with (- (- (unsigned x))).
  apply eqm_neg. apply eqm_unsigned_repr_l. apply eqm_refl. 
  apply eqm_refl2. omega. apply repr_unsigned.
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
  intros; unfold sub. change (unsigned zero) with 0.
  replace (unsigned x - 0) with (unsigned x). apply repr_unsigned.
  omega.
Qed.

Theorem sub_zero_r: forall x, sub zero x = neg x.
Proof.
  intros; unfold sub, neg. change (unsigned zero) with 0.
  replace (0 - unsigned x) with (- unsigned x). auto.
  omega.
Qed.

Theorem sub_add_opp: forall x y, sub x y = add x (neg y).
Proof.
  intros; unfold sub, add, neg.
  replace (unsigned x - unsigned y)
     with (unsigned x + (- unsigned y)).
  apply eqm_samerepr. auto with ints. omega.
Qed.

Theorem sub_idem: forall x, sub x x = zero.
Proof.
  intros; unfold sub. replace (unsigned x - unsigned x) with 0.
  reflexivity. omega.
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
  intros; unfold mul. change (unsigned zero) with 0.
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

Lemma Z_shift_add_inj:
  forall b1 x1 b2 x2,
  Z_shift_add b1 x1 = Z_shift_add b2 x2 -> b1 = b2 /\ x1 = x2.
Proof.
  intros until x2.
  unfold Z_shift_add.
  destruct b1; destruct b2; intros;
  ((split; [reflexivity|omega]) || omegaContradiction).
Qed.

Lemma Z_of_bits_exten:
  forall n f1 f2,
  (forall z, 0 <= z < Z_of_nat n -> f1 z = f2 z) ->
  Z_of_bits n f1 = Z_of_bits n f2.
Proof.
  induction n; intros.
  reflexivity.
  simpl. rewrite inj_S in H. decEq. apply H. omega. 
  apply IHn. intros; apply H. omega.
Qed.

Opaque Zmult.

Lemma Z_of_bits_of_Z:
  forall x, eqm (Z_of_bits wordsize (bits_of_Z wordsize x)) x.
Proof.
  assert (forall n x, exists k,
    Z_of_bits n (bits_of_Z n x) = k * two_power_nat n + x).
  induction n; intros.
  rewrite two_power_nat_O. simpl. exists (-x). omega.
  rewrite two_power_nat_S. simpl.
  caseEq (Z_bin_decomp x). intros b y ZBD. simpl. 
  replace (Z_of_bits n (fun i => if zeq (i + 1) 0 then b else bits_of_Z n y (i + 1 - 1)))
     with (Z_of_bits n (bits_of_Z n y)).
  elim (IHn y). intros k1 EQ1. rewrite EQ1.
  rewrite <- (Z_shift_add_bin_decomp x). 
  rewrite ZBD. simpl. 
  exists k1.
  case b; unfold Z_shift_add; ring.
  apply Z_of_bits_exten. intros.
  rewrite zeq_false. decEq. omega. omega. 
  intro. exact (H wordsize x).
Qed.

Lemma bits_of_Z_zero:
  forall n x, bits_of_Z n 0 x = false.
Proof.
  induction n; simpl; intros.
  auto.
  case (zeq x 0); intro. auto. auto.
Qed.

Remark Z_bin_decomp_2xm1:
  forall x, Z_bin_decomp (2 * x - 1) = (true, x - 1).
Proof.
  intros. caseEq (Z_bin_decomp (2 * x - 1)). intros b y EQ.
  generalize (Z_shift_add_bin_decomp (2 * x - 1)).
  rewrite EQ; simpl.
  replace (2 * x - 1) with (Z_shift_add true (x - 1)).
  intro. elim (Z_shift_add_inj _ _ _ _ H); intros.
  congruence. unfold Z_shift_add. omega.
Qed.

Lemma bits_of_Z_mone:
  forall n x,
  0 <= x < Z_of_nat n -> 
  bits_of_Z n (two_power_nat n - 1) x = true.
Proof.
  induction n; intros.
  simpl in H. omegaContradiction.
  unfold bits_of_Z; fold bits_of_Z.
  rewrite two_power_nat_S. rewrite Z_bin_decomp_2xm1.
  rewrite inj_S in H. case (zeq x 0); intro. auto.
  apply IHn. omega. 
Qed.

Lemma Z_bin_decomp_shift_add:
  forall b x, Z_bin_decomp (Z_shift_add b x) = (b, x).
Proof.
  intros. caseEq (Z_bin_decomp (Z_shift_add b x)); intros b' x' EQ.
  generalize (Z_shift_add_bin_decomp (Z_shift_add b x)).
  rewrite EQ; simpl fst; simpl snd. intro.
  elim (Z_shift_add_inj _ _ _ _ H); intros.
  congruence.
Qed.

Lemma bits_of_Z_of_bits:
  forall n f i,
  0 <= i < Z_of_nat n ->
  bits_of_Z n (Z_of_bits n f) i = f i.
Proof.
  induction n; intros; simpl.
  simpl in H. omegaContradiction.
  rewrite Z_bin_decomp_shift_add.
  case (zeq i 0); intro.
  congruence.
  rewrite IHn. decEq. omega. rewrite inj_S in H. omega.
Qed.  

Lemma Z_of_bits_range:
  forall f, 0 <= Z_of_bits wordsize f < modulus.
Proof.
  unfold max_unsigned, modulus.
  generalize wordsize. induction n; simpl; intros.
  rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. generalize (IHn (fun i => f (i + 1))).
  set (x := Z_of_bits n (fun i => f (i + 1))).
  intro. destruct (f 0); unfold Z_shift_add; omega.
Qed.
Hint Resolve Z_of_bits_range: ints.

Lemma Z_of_bits_range_2:
  forall f, 0 <= Z_of_bits wordsize f <= max_unsigned.
Proof.
  intros. unfold max_unsigned.
  generalize (Z_of_bits_range f). omega.
Qed.
Hint Resolve Z_of_bits_range_2: ints.

Lemma bits_of_Z_below:
  forall n x i, i < 0 -> bits_of_Z n x i = false.
Proof.
  induction n; simpl; intros.
  reflexivity.
  destruct (Z_bin_decomp x). rewrite zeq_false. apply IHn.
  omega. omega.
Qed.

Lemma bits_of_Z_above:
  forall n x i, i >= Z_of_nat n -> bits_of_Z n x i = false.
Proof.
  induction n; intros; simpl.
  reflexivity.
  destruct (Z_bin_decomp x). rewrite zeq_false. apply IHn.
  rewrite inj_S in H. omega. rewrite inj_S in H. omega.
Qed.

Lemma bits_of_Z_of_bits':
  forall n f i,
  bits_of_Z n (Z_of_bits n f) i =
  if zlt i 0 then false 
  else if zle (Z_of_nat n) i then false
  else f i.
Proof.
  intros. 
  destruct (zlt i 0). apply bits_of_Z_below; auto.
  destruct (zle (Z_of_nat n) i). apply bits_of_Z_above. omega.
  apply bits_of_Z_of_bits. omega.
Qed. 

Opaque Zmult.

Lemma Z_of_bits_excl:
  forall n f g h,
  (forall i, 0 <= i < Z_of_nat n -> f i && g i = false) ->
  (forall i, 0 <= i < Z_of_nat n -> f i || g i = h i) ->
  Z_of_bits n f + Z_of_bits n g = Z_of_bits n h.
Proof.
  induction n.
  intros; reflexivity.
  intros. simpl. rewrite inj_S in H. rewrite inj_S in H0.
  rewrite <- (IHn (fun i => f(i+1)) (fun i => g(i+1)) (fun i => h(i+1))).
  assert (0 <= 0 < Zsucc(Z_of_nat n)). omega.
  unfold Z_shift_add.
  rewrite <- H0; auto.
  set (F := Z_of_bits n (fun i => f(i + 1))).
  set (G := Z_of_bits n (fun i => g(i + 1))).
  caseEq (f 0); intros; caseEq (g 0); intros; simpl.
  generalize (H 0 H1). rewrite H2; rewrite H3. simpl. intros; discriminate.
  omega. omega. omega.
  intros; apply H. omega.
  intros; apply H0. omega.
Qed.

(** ** Properties of bitwise and, or, xor *)

Lemma bitwise_binop_commut:
  forall f,
  (forall a b, f a b = f b a) ->
  forall x y,
  bitwise_binop f x y = bitwise_binop f y x.
Proof.
  unfold bitwise_binop; intros.
  decEq. apply Z_of_bits_exten; intros. auto.
Qed.

Lemma bitwise_binop_assoc:
  forall f,
  (forall a b c, f a (f b c) = f (f a b) c) ->
  forall x y z,
  bitwise_binop f (bitwise_binop f x y) z =
  bitwise_binop f x (bitwise_binop f y z).
Proof.
  unfold bitwise_binop; intros.
  repeat rewrite unsigned_repr; auto with ints.
  decEq. apply Z_of_bits_exten; intros.
  repeat (rewrite bits_of_Z_of_bits; auto).
Qed.

Lemma bitwise_binop_idem:
  forall f,
  (forall a, f a a = a) ->
  forall x,
  bitwise_binop f x x = x.
Proof.
  unfold bitwise_binop; intros.
  transitivity (repr (Z_of_bits wordsize (bits_of_Z wordsize (unsigned x)))).
  decEq. apply Z_of_bits_exten; intros. auto.
  transitivity (repr (unsigned x)).
  apply eqm_samerepr. apply Z_of_bits_of_Z. apply repr_unsigned.
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
  transitivity (repr(unsigned x)).
  apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_mone. rewrite bits_of_Z_mone. apply andb_b_true. auto.
  apply repr_unsigned.
Qed.

Theorem and_idem: forall x, and x x = x.
Proof.
  assert (forall b, b && b = b).
    destruct b; reflexivity.
  exact (bitwise_binop_idem andb H).
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof (bitwise_binop_commut orb orb_comm).

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof (bitwise_binop_assoc orb orb_assoc).

Theorem or_zero: forall x, or x zero = x.
Proof.
  intros. unfold or, bitwise_binop.
  transitivity (repr(unsigned x)).
  apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_zero. rewrite bits_of_Z_zero. apply orb_b_false.
  apply repr_unsigned.
Qed.

Theorem or_mone: forall x, or x mone = mone.
Proof.
  intros. unfold or, bitwise_binop.
  transitivity (repr(unsigned mone)).
  apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_mone. rewrite bits_of_Z_mone. apply orb_b_true. auto.
  apply repr_unsigned.
Qed.

Theorem or_idem: forall x, or x x = x.
Proof.
  assert (forall b, b || b = b).
    destruct b; reflexivity.
  exact (bitwise_binop_idem orb H).
Qed.

Theorem and_or_distrib:
  forall x y z,
  and x (or y z) = or (and x y) (and x z).
Proof.
  intros; unfold and, or, bitwise_binop.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  apply demorgan1.
Qed.  

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof (bitwise_binop_commut xorb xorb_comm).

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  assert (forall a b c, xorb a (xorb b c) = xorb (xorb a b) c).
  symmetry. apply xorb_assoc.
  exact (bitwise_binop_assoc xorb H).
Qed.

Theorem xor_zero: forall x, xor x zero = x.
Proof.
  intros. unfold xor, bitwise_binop.
  transitivity (repr(unsigned x)).
  apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_zero. rewrite bits_of_Z_zero. apply xorb_false. 
  apply repr_unsigned.
Qed.

Theorem xor_idem: forall x, xor x x = zero.
Proof.
  intros. unfold xor, bitwise_binop.
  transitivity (repr(unsigned zero)).
  apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten. intros. 
  rewrite unsigned_zero. rewrite bits_of_Z_zero. apply xorb_nilpotent. 
  apply repr_unsigned.
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
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  assert (forall a b c, a && (xorb b c) = xorb (a && b) (a && c)).
    destruct a; destruct b; destruct c; reflexivity.
  auto.
Qed.  

Theorem not_involutive:
  forall (x: int), not (not x) = x.
Proof.
  intros. unfold not. rewrite xor_assoc. rewrite xor_idem. apply xor_zero. 
Qed.

(** ** Properties of shifts and rotates *)

Lemma Z_of_bits_shift:
  forall n f,
  exists k,
  Z_of_bits n (fun i => f (i - 1)) =
    k * two_power_nat n + Z_shift_add (f (-1)) (Z_of_bits n f).
Proof.
  induction n; intros.
  simpl. rewrite two_power_nat_O. unfold Z_shift_add.
  exists (if f (-1) then (-1) else 0).
  destruct (f (-1)); omega.
  rewrite two_power_nat_S. simpl. 
  elim (IHn (fun i => f (i + 1))). intros k' EQ.
  replace (Z_of_bits n (fun i => f (i - 1 + 1)))
     with (Z_of_bits n (fun i => f (i + 1 - 1))) in EQ.
  rewrite EQ.
  change (-1 + 1) with 0.
  exists k'.
  unfold Z_shift_add; destruct (f (-1)); destruct (f 0); ring.
  apply Z_of_bits_exten; intros.
  decEq. omega.
Qed.

Lemma Z_of_bits_shifts:
  forall m f,
  0 <= m ->
  (forall i, i < 0 -> f i = false) ->
  eqm (Z_of_bits wordsize (fun i => f (i - m)))
      (two_p m * Z_of_bits wordsize f).
Proof.
  intros. pattern m. apply natlike_ind.
  apply eqm_refl2. transitivity (Z_of_bits wordsize f).
  apply Z_of_bits_exten; intros. decEq. omega.
  simpl two_p. omega.
  intros. rewrite two_p_S; auto.
  set (f' := fun i => f (i - x)).
  apply eqm_trans with (Z_of_bits wordsize (fun i => f' (i - 1))).
  apply eqm_refl2. apply Z_of_bits_exten; intros.
  unfold f'. decEq. omega.
  apply eqm_trans with (Z_shift_add (f' (-1)) (Z_of_bits wordsize f')).
  exact (Z_of_bits_shift wordsize f').
  unfold f'. unfold Z_shift_add. rewrite H0. 
  rewrite <- Zmult_assoc. apply eqm_mult. apply eqm_refl.
  apply H2. omega. assumption.
Qed.

Lemma shl_mul_two_p:
  forall x y,
  shl x y = mul x (repr (two_p (unsigned y))).
Proof.
  intros. unfold shl, mul. 
  apply eqm_samerepr. 
  eapply eqm_trans.
  apply Z_of_bits_shifts.
  generalize (unsigned_range y). omega.
  intros; apply bits_of_Z_below; auto.
  rewrite Zmult_comm. apply eqm_mult.
  apply Z_of_bits_of_Z. apply eqm_unsigned_repr.
Qed.

Theorem shl_zero: forall x, shl x zero = x.
Proof.
  intros. rewrite shl_mul_two_p. 
  change (repr (two_p (unsigned zero))) with one.
  apply mul_one.
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

Lemma ltu_inv:
  forall x y, ltu x y = true -> 0 <= unsigned x < unsigned y.
Proof.
  unfold ltu; intros. destruct (zlt (unsigned x) (unsigned y)).
  split; auto. generalize (unsigned_range x); omega.
  discriminate.
Qed.

Theorem shl_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shl x n = rolm x n (shl mone n).
Proof.
  intros. exploit ltu_inv; eauto. rewrite unsigned_repr_wordsize; intros.
  unfold shl, rolm, rol, and, bitwise_binop.
  decEq. apply Z_of_bits_exten; intros.
  repeat rewrite unsigned_repr; auto with ints.
  repeat rewrite bits_of_Z_of_bits; auto. 
  case (zlt z (unsigned n)); intro LT2.
  assert (z - unsigned n < 0). omega.
  rewrite (bits_of_Z_below wordsize (unsigned x) _ H2).
  rewrite (bits_of_Z_below wordsize (unsigned mone) _ H2).
  symmetry. apply andb_b_false. 
  assert (z - unsigned n < Z_of_nat wordsize).
    generalize (unsigned_range n). omega.
  rewrite unsigned_mone. 
  rewrite bits_of_Z_mone. rewrite andb_b_true. decEq.
  rewrite Zmod_small. auto. omega. omega.
Qed.

Lemma bitwise_binop_shl:
  forall f x y n,
  f false false = false ->
  bitwise_binop f (shl x n) (shl y n) = shl (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, shl.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  case (zlt (z - unsigned n) 0); intro.
  transitivity false. repeat rewrite bits_of_Z_of_bits; auto.
  repeat rewrite bits_of_Z_below; auto.
  rewrite bits_of_Z_below; auto.
  repeat rewrite bits_of_Z_of_bits; auto.
  generalize (unsigned_range n). omega.
Qed.

Theorem and_shl:
  forall x y n,
  and (shl x n) (shl y n) = shl (and x y) n.
Proof.
  unfold and; intros. apply bitwise_binop_shl. reflexivity.
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
  repeat rewrite unsigned_repr.
  decEq. apply Z_of_bits_exten. intros n R.
  rewrite bits_of_Z_of_bits'. 
  destruct (zlt (n - z') 0).
  symmetry. apply bits_of_Z_below. omega.
  destruct (zle (Z_of_nat wordsize) (n - z')).
  symmetry. apply bits_of_Z_below. omega.
  decEq. omega.
  generalize two_wordsize_max_unsigned; omega.
  apply Z_of_bits_range_2.
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
  intros.
  repeat rewrite unsigned_repr.
  decEq. apply Z_of_bits_exten. intros n R.
  rewrite bits_of_Z_of_bits'. 
  destruct (zlt (n + z') 0). omegaContradiction.
  destruct (zle (Z_of_nat wordsize) (n + z')).
  symmetry. apply bits_of_Z_above. omega.
  decEq. omega.
  generalize two_wordsize_max_unsigned; omega.
  apply Z_of_bits_range_2.
Qed.

Theorem shru_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shru x n = rolm x (sub iwordsize n) (shru mone n).
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize. intro. 
  unfold shru, rolm, rol, and, bitwise_binop.
  decEq. apply Z_of_bits_exten; intros.
  repeat rewrite unsigned_repr; auto with ints.
  repeat rewrite bits_of_Z_of_bits; auto. 
  unfold sub. rewrite unsigned_repr_wordsize. 
  rewrite unsigned_repr. 
  case (zlt (z + unsigned n) (Z_of_nat wordsize)); intro LT2.
  rewrite unsigned_mone. rewrite bits_of_Z_mone. rewrite andb_b_true.
  decEq. 
  replace (z - (Z_of_nat wordsize - unsigned n))
     with ((z + unsigned n) + (-1) * Z_of_nat wordsize).
  rewrite Z_mod_plus. symmetry. apply Zmod_small.
  generalize (unsigned_range n). omega. omega. omega. 
  generalize (unsigned_range n). omega. 
  rewrite (bits_of_Z_above wordsize (unsigned x) _ LT2).
  rewrite (bits_of_Z_above wordsize (unsigned mone) _ LT2).
  symmetry. apply andb_b_false.
  split. omega. apply Zle_trans with (Z_of_nat wordsize).
  generalize (unsigned_range n); omega. apply wordsize_max_unsigned.
Qed.

Lemma bitwise_binop_shru:
  forall f x y n,
  f false false = false ->
  bitwise_binop f (shru x n) (shru y n) = shru (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, shru.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  case (zlt (z + unsigned n) (Z_of_nat wordsize)); intro.
  repeat rewrite bits_of_Z_of_bits; auto.
  generalize (unsigned_range n); omega.
  transitivity false. repeat rewrite bits_of_Z_of_bits; auto.
  repeat rewrite bits_of_Z_above; auto.
  rewrite bits_of_Z_above; auto.
Qed.

Lemma and_shru:
  forall x y n,
  and (shru x n) (shru y n) = shru (and x y) n.
Proof.
  unfold and; intros. apply bitwise_binop_shru. reflexivity.
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
  set (x' := signed x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  intros.
  rewrite unsigned_repr.
  rewrite two_p_is_exp. 
  rewrite signed_repr.
  decEq. apply Zdiv_Zdiv. apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
  apply Zdiv_interval_2. unfold x'; apply signed_range.
  generalize min_signed_neg; omega. 
  generalize max_signed_pos; omega.
  apply two_p_gt_ZERO. omega.  omega. omega. 
  generalize two_wordsize_max_unsigned; omega.
Qed.

Theorem rol_zero:
  forall x,
  rol x zero = x.
Proof.
  intros. transitivity (repr (unsigned x)). 
  unfold rol. apply eqm_samerepr. eapply eqm_trans. 2: apply Z_of_bits_of_Z. 
  apply eqm_refl2. apply Z_of_bits_exten; intros. decEq. rewrite unsigned_zero. 
  replace (z - 0) with z by omega. apply Zmod_small. auto.
  apply repr_unsigned.
Qed.

Lemma bitwise_binop_rol:
  forall f x y n,
  bitwise_binop f (rol x n) (rol y n) = rol (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, rol.
  decEq. repeat (rewrite unsigned_repr; auto with ints).
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  apply Z_mod_lt. generalize wordsize_pos; omega. 
Qed.

Theorem rol_and:
  forall x y n,
  rol (and x y) n = and (rol x n) (rol y n).
Proof.
  intros. symmetry. unfold and. apply bitwise_binop_rol.
Qed.

Theorem rol_rol:
  forall x n m,
  Zdivide (Z_of_nat wordsize) modulus ->
  rol (rol x n) m = rol x (modu (add n m) iwordsize).
Proof.
  intros. unfold rol. decEq.
  repeat (rewrite unsigned_repr; auto with ints).
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  decEq. unfold modu, add. 
  set (W := Z_of_nat wordsize).
  set (M := unsigned m); set (N := unsigned n).
  assert (W > 0). unfold W; generalize wordsize_pos; omega.
  assert (forall a, eqmod W a (unsigned (repr a))).
    intros. eapply eqmod_divides. apply eqm_unsigned_repr. assumption.
  apply eqmod_mod_eq. auto.
  replace (unsigned iwordsize) with W.
  apply eqmod_trans with (z - (N + M) mod W).
  apply eqmod_trans with ((z - M) - N).
  apply eqmod_sub. apply eqmod_sym. apply eqmod_mod. auto.
  apply eqmod_refl. 
  replace (z - M - N) with (z - (N + M)).
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

Theorem rol_or:
  forall x y n,
  rol (or x y) n = or (rol x n) (rol y n).
Proof.
  intros. symmetry. unfold or. apply bitwise_binop_rol.
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
  intro. rewrite unsigned_repr.
  decEq. apply Z_of_bits_exten. intros. decEq.
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
  decEq. apply Z_of_bits_exten. intros i iRANGE.
  repeat rewrite unsigned_repr. 
  repeat rewrite bits_of_Z_of_bits; auto.
  assert (y = sub iwordsize z).
    rewrite <- H1. rewrite add_commut. rewrite sub_add_l. rewrite sub_idem. 
    rewrite add_commut. rewrite add_zero. auto.
  assert (unsigned y = Z_of_nat wordsize - unsigned z).
    rewrite H4. unfold sub. rewrite unsigned_repr_wordsize. apply unsigned_repr. 
    generalize wordsize_max_unsigned; omega. 
  destruct (zlt (i + unsigned z) (Z_of_nat wordsize)). 
  rewrite Zmod_small. 
  replace (bits_of_Z wordsize ux (i - unsigned y)) with false.
  auto. 
  symmetry. apply bits_of_Z_below. omega. omega. 
  replace (bits_of_Z wordsize ux (i + unsigned z)) with false.
  rewrite orb_false_r. decEq. 
  replace (i + unsigned z) with (i - unsigned y + 1 * Z_of_nat wordsize) by omega.
  rewrite Z_mod_plus. apply Zmod_small. omega. generalize wordsize_pos; omega. 
  symmetry. apply bits_of_Z_above. auto. 
  apply Z_of_bits_range_2. apply Z_of_bits_range_2.
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
  replace (two_p x) with (2 * two_p (x - 1)). simpl. rewrite Z_bin_decomp_2xm1. 
  destruct (zeq i 0). subst. unfold proj_sumbool. rewrite zlt_true. auto. omega.
  rewrite inj_S in H0. rewrite IHn. unfold proj_sumbool. destruct (zlt i x).
  apply zlt_true. omega.
  apply zlt_false. omega.
  omega. omega. rewrite <- two_p_S. decEq. omega. omega.
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
  decEq. apply Z_of_bits_exten. intros. 
  repeat rewrite unsigned_repr.
  rewrite bits_of_Z_two_p.
  destruct (zlt (z + unsigned y) (Z_of_nat wordsize)).
  rewrite bits_of_Z_of_bits. unfold proj_sumbool. rewrite zlt_true. 
  rewrite andb_true_r. f_equal. omega. 
  omega. omega. 
  rewrite bits_of_Z_above. unfold proj_sumbool. rewrite zlt_false. rewrite andb_false_r; auto. 
  omega. omega. omega. auto. 
  apply two_p_m1_range. omega. 
  apply Z_of_bits_range_2. 
Qed.

(** ** Relation between shifts and powers of 2 *)

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

Theorem mul_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  mul x n = shl x logn.
Proof.
  intros. generalize (is_power2_correct n logn H); intro.
  rewrite shl_mul_two_p. rewrite <- H0. rewrite repr_unsigned.
  auto.
Qed.

Lemma Z_of_bits_shift_rev:
  forall n f,
  (forall i, i >= Z_of_nat n -> f i = false) ->
  Z_of_bits n f = Z_shift_add (f 0) (Z_of_bits n (fun i => f(i + 1))).
Proof.
  induction n; intros.
  simpl. rewrite H. reflexivity. unfold Z_of_nat. omega.
  simpl. rewrite (IHn (fun i => f (i + 1))).
  reflexivity. 
  intros. apply H. rewrite inj_S. omega.
Qed.

Lemma Z_of_bits_shifts_rev:
  forall m f,
  0 <= m ->
  (forall i, i >= Z_of_nat wordsize -> f i = false) ->
  exists k,
  Z_of_bits wordsize f = k + two_p m * Z_of_bits wordsize (fun i => f(i + m))
  /\ 0 <= k < two_p m.
Proof.
  intros. pattern m. apply natlike_ind.
  exists 0. change (two_p 0) with 1. split.
  transitivity (Z_of_bits wordsize (fun i => f (i + 0))).
  apply Z_of_bits_exten. intros. decEq. omega.
  omega. omega.
  intros x POSx [k [EQ1 RANGE1]].
  set (f' := fun i => f (i + x)) in *.
  assert (forall i, i >= Z_of_nat wordsize -> f' i = false).
  intros. unfold f'. apply H0. omega.  
  generalize (Z_of_bits_shift_rev wordsize f' H1). intro.
  rewrite EQ1. rewrite H2. 
  set (z := Z_of_bits wordsize (fun i => f (i + Zsucc x))).
  replace (Z_of_bits wordsize (fun i => f' (i + 1))) with z.
  rewrite two_p_S.
  case (f' 0); unfold Z_shift_add.
  exists (k + two_p x). split. ring. omega. 
  exists k. split. ring. omega.
  auto. 
  unfold z. apply Z_of_bits_exten; intros. unfold f'.
  decEq. omega. 
  auto.
Qed.

Lemma shru_div_two_p:
  forall x y,
  shru x y = repr (unsigned x / two_p (unsigned y)).
Proof.
  intros. unfold shru. 
  set (x' := unsigned x). set (y' := unsigned y).
  elim (Z_of_bits_shifts_rev y' (bits_of_Z wordsize x')).
  intros k [EQ RANGE].
  replace (Z_of_bits wordsize (bits_of_Z wordsize x')) with x' in EQ.
  rewrite Zplus_comm in EQ. rewrite Zmult_comm in EQ.
  generalize (Zdiv_unique _ _ _ _ EQ RANGE). intros.
  rewrite H. auto.
  apply eqm_small_eq. apply eqm_sym. apply Z_of_bits_of_Z. 
  unfold x'. apply unsigned_range. 
  auto with ints.
  generalize (unsigned_range y). unfold y'. omega.
  intros. apply bits_of_Z_above. auto.
Qed.

Theorem shru_zero:
  forall x, shru x zero = x.
Proof.
  intros. rewrite shru_div_two_p. change (two_p (unsigned zero)) with 1.
  transitivity (repr (unsigned x)). decEq. apply Zdiv_unique with 0.
  omega. omega. auto with ints.
Qed.

Theorem shr_zero:
  forall x, shr x zero = x.
Proof.
  intros. unfold shr. change (two_p (unsigned zero)) with 1.
  replace (signed x / 1) with (signed x).
  apply repr_signed.
  symmetry. apply Zdiv_unique with 0. omega. omega. 
Qed.

Theorem divu_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divu x n = shru x logn.
Proof.
  intros. generalize (is_power2_correct n logn H). intro.
  symmetry. unfold divu. rewrite H0. apply shru_div_two_p.
Qed.

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
  intros. unfold shrx, divs, shr. decEq.
  exploit ltu_inv; eauto. rewrite unsigned_repr.   
  set (uy := unsigned y).
  intro RANGE.
  assert (shl one y = repr (two_p uy)).
    transitivity (mul one (repr (two_p uy))).
    symmetry. apply mul_pow2. replace y with (repr uy). 
    apply is_power2_two_p. omega. unfold uy. apply repr_unsigned.
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
  rewrite H6. rewrite signed_repr. decEq. omega.
  generalize (signed_range x). intros.  
  assert (two_p uy - 1 <= max_signed). unfold max_signed. omega.
  omega.
  generalize wordsize_pos wordsize_max_unsigned; omega.
Qed.

Lemma add_and:
  forall x y z,
  and y z = zero ->
  add (and x y) (and x z) = and x (or y z).
Proof.
  intros. unfold add, and, bitwise_binop. 
  decEq.
  repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_excl; intros.
  assert (forall a b c, a && b && (a && c) = a && (b && c)).
    destruct a; destruct b; destruct c; reflexivity.
  rewrite H1. 
  replace (bits_of_Z wordsize (unsigned y) i &&
           bits_of_Z wordsize (unsigned z) i)
     with (bits_of_Z wordsize (unsigned (and y z)) i).
  rewrite H. change (unsigned zero) with 0. 
  rewrite bits_of_Z_zero. apply andb_b_false.
  unfold and, bitwise_binop. 
  rewrite unsigned_repr; auto with ints. rewrite bits_of_Z_of_bits. 
  reflexivity. auto. 
  rewrite <- demorgan1.
  unfold or, bitwise_binop. 
  rewrite unsigned_repr; auto with ints. rewrite bits_of_Z_of_bits; auto.
Qed.

Lemma Z_of_bits_zero:
  forall n f,
  (forall i, i >= 0 -> f i = false) ->
  Z_of_bits n f = 0.
Proof.
  induction n; intros; simpl.
  auto.
  rewrite H. rewrite IHn. auto.  intros. apply H. omega. omega.
Qed.

Lemma Z_of_bits_trunc_1:
  forall n f k,
  (forall i, i >= k -> f i = false) ->
  k >= 0 ->
  0 <= Z_of_bits n f < two_p k.
Proof.
  induction n; intros.
  simpl. assert (two_p k > 0). apply two_p_gt_ZERO; omega. omega.
  destruct (zeq k 0). subst k.
  change (two_p 0) with 1. rewrite Z_of_bits_zero. omega. auto. 
  simpl. replace (two_p k) with (2 * two_p (k - 1)).
  assert (0 <= Z_of_bits n (fun i => f(i+1)) < two_p (k - 1)).
    apply IHn. intros. apply H. omega. omega.
  unfold Z_shift_add. destruct (f 0); omega. 
  rewrite <- two_p_S. decEq. omega. omega. 
Qed.

Lemma Z_of_bits_trunc_2:
  forall n f1 f2 k,
  (forall i, i < k -> f2 i = f1 i) ->
  k >= 0 ->
  exists q, Z_of_bits n f1 = q * two_p k + Z_of_bits n f2.
Proof.
  induction n; intros.
  simpl. exists 0; omega.
  destruct (zeq k 0). subst k.
  exists (Z_of_bits (S n) f1 - Z_of_bits (S n) f2).
  change (two_p 0) with 1. omega. 
  destruct (IHn (fun i => f1 (i + 1)) (fun i => f2 (i + 1)) (k - 1)) as [q EQ].
  intros. apply H. omega. omega.
  exists q. simpl. rewrite H. unfold Z_shift_add. 
  replace (two_p k) with (2 * two_p (k - 1)). rewrite EQ. 
  destruct (f1 0). ring. ring. 
  rewrite <- two_p_S. decEq. omega. omega. omega.
Qed.

Lemma Z_of_bits_trunc_3:
  forall f n k,
  k >= 0 ->
  Zmod (Z_of_bits n f) (two_p k) = Z_of_bits n (fun i => if zlt i k then f i else false).
Proof.
  intros. 
  set (g := fun i : Z => if zlt i k then f i else false).
  destruct (Z_of_bits_trunc_2 n f g k). 
    intros. unfold g. apply zlt_true. auto. 
    auto.
  apply Zmod_unique with x. auto. 
  apply Z_of_bits_trunc_1. intros. unfold g. apply zlt_false. auto. auto.
Qed.

Theorem modu_and:
  forall x n logn,
  is_power2 n = Some logn ->
  modu x n = and x (sub n one).
Proof.
  intros. generalize (is_power2_correct _ _ H); intro.
  generalize (is_power2_rng _ _ H); intro.
  unfold modu, and, bitwise_binop.
  decEq.
  set (ux := unsigned x).
  replace ux with (Z_of_bits wordsize (bits_of_Z wordsize ux)).
  rewrite H0. rewrite Z_of_bits_trunc_3. apply Z_of_bits_exten. intros. 
  rewrite bits_of_Z_of_bits; auto. 
  replace (unsigned (sub n one)) with (two_p (unsigned logn) - 1).
  rewrite bits_of_Z_two_p. unfold proj_sumbool.
  destruct (zlt z (unsigned logn)). rewrite andb_true_r; auto. rewrite andb_false_r; auto. 
  omega. auto. 
  rewrite <- H0. unfold sub. symmetry. rewrite unsigned_one. apply unsigned_repr.
  rewrite H0. 
  assert (two_p (unsigned logn) > 0). apply two_p_gt_ZERO. omega.
  generalize (two_p_range _ H1). omega. 
  omega.
  apply eqm_small_eq. apply Z_of_bits_of_Z. apply Z_of_bits_range. 
  unfold ux. apply unsigned_range.
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

Theorem zero_ext_and:
  forall x, zero_ext n x = and x (repr (two_p n - 1)).
Proof.
  intros; unfold zero_ext.
  assert (is_power2 (repr (two_p n)) = Some (repr n)).
    apply is_power2_two_p. omega.
  generalize (modu_and x _ _ H).
  unfold modu. rewrite unsigned_repr_two_p. intro. rewrite H0. 
  decEq. unfold sub. decEq. rewrite unsigned_repr_two_p.
  rewrite unsigned_one. reflexivity.
Qed.

Theorem zero_ext_idem:
  forall x, zero_ext n (zero_ext n x) = zero_ext n x.
Proof.
  intros. repeat rewrite zero_ext_and. 
  rewrite and_assoc. rewrite and_idem. auto.
Qed.

Lemma eqm_eqmod_two_p:
  forall a b, eqm a b -> eqmod (two_p n) a b.
Proof.
  intros a b [k EQ].
  exists (k * two_p (Z_of_nat wordsize - n)).
  rewrite EQ. decEq. rewrite <- Zmult_assoc. decEq.
  rewrite <- two_p_is_exp. unfold modulus. rewrite two_power_nat_two_p.
  decEq. omega. omega. omega.
Qed.

Lemma sign_ext_charact:
  forall x y,
  -(two_p (n-1)) <= signed y < two_p (n-1) ->
  eqmod (two_p n) (unsigned x) (signed y) ->
  sign_ext n x = y.
Proof.
  intros. unfold sign_ext. set (x' := unsigned x) in *.
  destruct H0 as [k EQ].
  assert (two_p n = 2 * two_p (n - 1)). rewrite <- two_p_S. decEq. omega. omega.
  assert (signed y >= 0 \/ signed y < 0) by omega. destruct H1.
  assert (x' mod two_p n = signed y).
  apply Zmod_unique with k; auto. omega.
  rewrite zlt_true. rewrite H2. apply repr_signed. omega.
  assert (x' mod two_p n = signed y + two_p n).
  apply Zmod_unique with (k-1). rewrite EQ. ring. omega. 
  rewrite zlt_false. replace (x' mod two_p n - two_p n) with (signed y) by omega. apply repr_signed.
  omega.
Qed.

Lemma zero_ext_eqmod_two_p:
  forall x y,
  eqmod (two_p n) (unsigned x) (unsigned y) -> zero_ext n x = zero_ext n y.
Proof.
  intros. unfold zero_ext. decEq. apply eqmod_mod_eq. apply two_p_n_pos. auto.
Qed.

Lemma sign_ext_eqmod_two_p:
  forall x y,
  eqmod (two_p n) (unsigned x) (unsigned y) -> sign_ext n x = sign_ext n y.
Proof.
  intros. unfold sign_ext. 
  assert (unsigned x mod two_p n = unsigned y mod two_p n). 
  apply eqmod_mod_eq. apply two_p_n_pos. auto. 
  rewrite H0. auto.
Qed.

Lemma eqmod_two_p_zero_ext:
  forall x, eqmod (two_p n) (unsigned x) (unsigned (zero_ext n x)).
Proof.
  intros. unfold zero_ext. 
  apply eqmod_trans with (unsigned x mod two_p n).
  apply eqmod_mod. apply two_p_n_pos.
  apply eqm_eqmod_two_p. apply eqm_unsigned_repr. 
Qed.

Lemma eqmod_two_p_sign_ext:
  forall x, eqmod (two_p n) (unsigned x) (unsigned (sign_ext n x)).
Proof.
  intros. unfold sign_ext. destruct (zlt (unsigned x mod two_p n) (two_p (n-1))).
  apply eqmod_trans with (unsigned x mod two_p n).
  apply eqmod_mod. apply two_p_n_pos.
  apply eqm_eqmod_two_p. apply eqm_unsigned_repr. 
  apply eqmod_trans with (unsigned x mod two_p n).
  apply eqmod_mod. apply two_p_n_pos.
  apply eqmod_trans with (unsigned x mod two_p n - 0).
  apply eqmod_refl2. omega.
  apply eqmod_trans with (unsigned x mod two_p n - two_p n).
  apply eqmod_sub. apply eqmod_refl. exists (-1). ring.
  apply eqm_eqmod_two_p. apply eqm_unsigned_repr. 
Qed.

Theorem sign_ext_idem:
  forall x, sign_ext n (sign_ext n x) = sign_ext n x.
Proof.
  intros. apply sign_ext_eqmod_two_p. 
  apply eqmod_sym. apply eqmod_two_p_sign_ext.
Qed.

Theorem sign_ext_zero_ext:
  forall x, sign_ext n (zero_ext n x) = sign_ext n x.
Proof.
  intros. apply sign_ext_eqmod_two_p.
  apply eqmod_sym. apply eqmod_two_p_zero_ext.
Qed.

Theorem zero_ext_sign_ext:
  forall x, zero_ext n (sign_ext n x) = zero_ext n x.
Proof.
  intros. apply zero_ext_eqmod_two_p.
  apply eqmod_sym. apply eqmod_two_p_sign_ext.
Qed.

Theorem sign_ext_equal_if_zero_equal:
  forall x y,
  zero_ext n x = zero_ext n y ->
  sign_ext n x = sign_ext n y.
Proof.
  intros. rewrite <- (sign_ext_zero_ext x).
  rewrite <- (sign_ext_zero_ext y). congruence.
Qed.

Lemma eqmod_mult_div:
  forall n1 n2 x y,
  0 <= n1 -> 0 <= n2 ->
  eqmod (two_p (n1+n2)) (two_p n1 * x) y ->
  eqmod (two_p n2) x (y / two_p n1).
Proof.
  intros. rewrite two_p_is_exp in H1; auto. 
  destruct H1 as [k EQ]. exists k.
  change x with (0 / two_p n1 + x). rewrite <- Z_div_plus.
  replace (0 + x * two_p n1) with (two_p n1 * x) by ring.
  rewrite EQ. 
  replace (k * (two_p n1 * two_p n2) + y) with (y + (k * two_p n2) * two_p n1) by ring.
  rewrite Z_div_plus. ring. 
  apply two_p_gt_ZERO; auto.
  apply two_p_gt_ZERO; auto.
Qed.

Theorem sign_ext_shr_shl:
  forall x, 
  let y := repr (Z_of_nat wordsize - n) in
  sign_ext n x = shr (shl x y) y.
Proof.
  intros.
  assert (unsigned y = Z_of_nat wordsize - n).
    unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. omega.
  apply sign_ext_charact.
  (* inequalities *)
  unfold shr. rewrite H. 
  set (z := signed (shl x y)).
  rewrite signed_repr. 
  apply Zdiv_interval_1.
  assert (two_p (n - 1) > 0). apply two_p_gt_ZERO. omega. omega.
  apply two_p_gt_ZERO. omega.
  apply two_p_gt_ZERO. omega.
  replace ((- two_p (n-1)) * two_p (Z_of_nat wordsize - n))
     with (- (two_p (n-1) * two_p (Z_of_nat wordsize - n))) by ring.
  rewrite <- two_p_is_exp.
  replace (n - 1 + (Z_of_nat wordsize - n)) with (Z_of_nat wordsize - 1) by omega.
  rewrite <- half_modulus_power.
  generalize (signed_range (shl x y)). unfold z, min_signed, max_signed. omega.
  omega. omega. 
  apply Zdiv_interval_2. unfold z. apply signed_range.
  generalize min_signed_neg; omega. generalize max_signed_pos; omega.
  apply two_p_gt_ZERO; omega. 
  (* eqmod *)
  unfold shr. rewrite H. 
  apply eqmod_trans with (signed (shl x y) / two_p (Z_of_nat wordsize - n)).
  apply eqmod_mult_div. omega. omega. 
  replace (Z_of_nat wordsize - n + n) with (Z_of_nat wordsize) by omega.
  rewrite <- two_power_nat_two_p.
  change (eqm (two_p (Z_of_nat wordsize - n) * unsigned x) (signed (shl x y))).
  rewrite shl_mul_two_p. unfold mul. rewrite H. 
  apply eqm_sym. eapply eqm_trans. apply eqm_signed_unsigned. 
  apply eqm_unsigned_repr_l. rewrite (Zmult_comm (unsigned x)). 
  apply eqm_mult. apply eqm_sym. apply eqm_unsigned_repr. apply eqm_refl.
  apply eqm_eqmod_two_p. apply eqm_sym. eapply eqm_trans.
  apply eqm_signed_unsigned. apply eqm_sym. apply eqm_unsigned_repr. 
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

End EXTENSIONS.

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
  simpl. apply one_not_zero. 
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

(** * Specialization to 32-bit integers and to bytes. *)

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

Module Byte := Integers.Make(Wordsize_8).

Notation byte := Byte.int.

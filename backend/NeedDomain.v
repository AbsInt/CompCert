(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract domain for neededness analysis *)

Require Import Coqlib.
Require Import Maps.
Require Import IntvSets.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lattice.
Require Import Registers.
Require Import ValueDomain.
Require Import Op.
Require Import RTL.

(** * Neededness for values *)

Inductive nval : Type :=
  | Nothing              (**r value is entirely unused *)
  | I (m: int)           (**r only need the bits that are 1 in [m] *)
  | All.                 (**r every bit of the value is used *)

Definition eq_nval (x y: nval) : {x=y} + {x<>y}.
Proof.
  decide equality. apply Int.eq_dec.
Defined.

(** ** Agreement between two values relative to a need. *)

Definition iagree (p q mask: int) : Prop :=
  forall i, 0 <= i < Int.zwordsize -> Int.testbit mask i = true ->
            Int.testbit p i = Int.testbit q i.

Fixpoint vagree (v w: val) (x: nval) {struct x}: Prop :=
  match x with
  | Nothing => True
  | I m =>
      match v, w with
      | Vint p, Vint q => iagree p q m
      | Vint p, _ => False
      | _, _ => True
      end
  | All => Val.lessdef v w
  end.

Lemma vagree_same: forall v x, vagree v v x.
Proof.
  intros. destruct x; simpl; auto; destruct v; auto. red; auto.
Qed.

Lemma vagree_lessdef: forall v w x, Val.lessdef v w -> vagree v w x.
Proof.
  intros. inv H. apply vagree_same. destruct x; simpl; auto.
Qed.

Lemma lessdef_vagree: forall v w, vagree v w All -> Val.lessdef v w.
Proof.
  intros. simpl in H. auto.
Qed.

Hint Resolve vagree_same vagree_lessdef lessdef_vagree: na.

Inductive vagree_list: list val -> list val -> list nval -> Prop :=
  | vagree_list_nil: forall nvl,
      vagree_list nil nil nvl
  | vagree_list_default: forall v1 vl1 v2 vl2,
      vagree v1 v2 All -> vagree_list vl1 vl2 nil ->
      vagree_list (v1 :: vl1) (v2 :: vl2) nil
  | vagree_list_cons: forall v1 vl1 v2 vl2 nv1 nvl,
      vagree v1 v2 nv1 -> vagree_list vl1 vl2 nvl ->
      vagree_list (v1 :: vl1) (v2 :: vl2) (nv1 :: nvl).

Lemma lessdef_vagree_list:
  forall vl1 vl2, vagree_list vl1 vl2 nil -> Val.lessdef_list vl1 vl2.
Proof.
  induction vl1; intros; inv H; constructor; auto with na.
Qed.

Lemma vagree_lessdef_list:
  forall vl1 vl2, Val.lessdef_list vl1 vl2 -> forall nvl, vagree_list vl1 vl2 nvl.
Proof.
  induction 1; intros.
  constructor.
  destruct nvl; constructor; auto with na.
Qed.

Hint Resolve lessdef_vagree_list vagree_lessdef_list: na.

(** ** Ordering and least upper bound between value needs *)

Inductive nge: nval -> nval -> Prop :=
  | nge_nothing: forall x, nge All x
  | nge_all: forall x, nge x Nothing
  | nge_int: forall m1 m2,
      (forall i, 0 <= i < Int.zwordsize -> Int.testbit m2 i = true -> Int.testbit m1 i = true) ->
      nge (I m1) (I m2).

Lemma nge_refl: forall x, nge x x.
Proof.
  destruct x; constructor; auto.
Qed.

Hint Constructors nge: na.
Hint Resolve nge_refl: na.

Lemma nge_trans: forall x y, nge x y -> forall z, nge y z -> nge x z.
Proof.
  induction 1; intros w VG; inv VG; eauto with na.
Qed.

Lemma nge_agree:
  forall v w x y, nge x y -> vagree v w x -> vagree v w y.
Proof.
  induction 1; simpl; auto.
- destruct v; auto with na.
- destruct v, w; intuition. red; auto.
Qed.

Definition nlub (x y: nval) : nval :=
  match x, y with
  | Nothing, _ => y
  | _, Nothing => x
  | I m1, I m2 => I (Int.or m1 m2)
  | _, _ => All
  end.

Lemma nge_lub_l:
  forall x y, nge (nlub x y) x.
Proof.
  unfold nlub; destruct x, y; auto with na.
  constructor. intros. autorewrite with ints; auto. rewrite H0; auto.
Qed.

Lemma nge_lub_r:
  forall x y, nge (nlub x y) y.
Proof.
  unfold nlub; destruct x, y; auto with na.
  constructor. intros. autorewrite with ints; auto. rewrite H0. apply orb_true_r; auto.
Qed.

(** ** Properties of agreement between integers *)

Lemma iagree_refl:
  forall p m, iagree p p m.
Proof.
  intros; red; auto.
Qed.

Remark eq_same_bits:
  forall i x y, x = y -> Int.testbit x i = Int.testbit y i.
Proof.
  intros; congruence.
Qed.

Lemma iagree_and_eq:
  forall x y mask,
  iagree x y mask <-> Int.and x mask = Int.and y mask.
Proof.
  intros; split; intros.
- Int.bit_solve. specialize (H i H0).
  destruct (Int.testbit mask i).
  rewrite ! andb_true_r; auto.
  rewrite ! andb_false_r; auto.
- red; intros. exploit (eq_same_bits i); eauto; autorewrite with ints; auto.
  rewrite H1. rewrite ! andb_true_r; auto.
Qed.

Lemma iagree_mone:
  forall p q, iagree p q Int.mone -> p = q.
Proof.
  intros. rewrite iagree_and_eq in H. rewrite ! Int.and_mone in H. auto.
Qed.

Lemma iagree_zero:
  forall p q, iagree p q Int.zero.
Proof.
  intros. rewrite iagree_and_eq. rewrite ! Int.and_zero; auto.
Qed.

Lemma iagree_and:
  forall x y n m,
  iagree x y (Int.and m n) -> iagree (Int.and x n) (Int.and y n) m.
Proof.
  intros. rewrite iagree_and_eq in *. rewrite ! Int.and_assoc.
  rewrite (Int.and_commut n). auto.
Qed.

Lemma iagree_not:
  forall x y m, iagree x y m -> iagree (Int.not x) (Int.not y) m.
Proof.
  intros; red; intros; autorewrite with ints; auto. f_equal; auto.
Qed.

Lemma iagree_not':
  forall x y m, iagree (Int.not x) (Int.not y) m -> iagree x y m.
Proof.
  intros. rewrite <- (Int.not_involutive x). rewrite <- (Int.not_involutive y).
  apply iagree_not; auto.
Qed.

Lemma iagree_or:
  forall x y n m,
  iagree x y (Int.and m (Int.not n)) -> iagree (Int.or x n) (Int.or y n) m.
Proof.
  intros. apply iagree_not'. rewrite ! Int.not_or_and_not. apply iagree_and.
  apply iagree_not; auto.
Qed.

Lemma iagree_bitwise_binop:
  forall sem f,
  (forall x y i, 0 <= i < Int.zwordsize ->
       Int.testbit (f x y) i = sem (Int.testbit x i) (Int.testbit y i)) ->
  forall x1 x2 y1 y2 m,
  iagree x1 y1 m -> iagree x2 y2 m -> iagree (f x1 x2) (f y1 y2) m.
Proof.
  intros; red; intros. rewrite ! H by auto. f_equal; auto.
Qed.

Lemma iagree_shl:
  forall x y m n,
  iagree x y (Int.shru m n) -> iagree (Int.shl x n) (Int.shl y n) m.
Proof.
  intros; red; intros. autorewrite with ints; auto.
  destruct (zlt i (Int.unsigned n)).
- auto.
- generalize (Int.unsigned_range n); intros.
  apply H. omega. rewrite Int.bits_shru by omega.
  replace (i - Int.unsigned n + Int.unsigned n) with i by omega.
  rewrite zlt_true by omega. auto.
Qed.

Lemma iagree_shru:
  forall x y m n,
  iagree x y (Int.shl m n) -> iagree (Int.shru x n) (Int.shru y n) m.
Proof.
  intros; red; intros. autorewrite with ints; auto.
  destruct (zlt (i + Int.unsigned n) Int.zwordsize).
- generalize (Int.unsigned_range n); intros.
  apply H. omega. rewrite Int.bits_shl by omega.
  replace (i + Int.unsigned n - Int.unsigned n) with i by omega.
  rewrite zlt_false by omega. auto.
- auto.
Qed.

Lemma iagree_shr_1:
  forall x y m n,
  Int.shru (Int.shl m n) n = m ->
  iagree x y (Int.shl m n) -> iagree (Int.shr x n) (Int.shr y n) m.
Proof.
  intros; red; intros. rewrite <- H in H2. rewrite Int.bits_shru in H2 by auto.
  rewrite ! Int.bits_shr by auto.
  destruct (zlt (i + Int.unsigned n) Int.zwordsize).
- apply H0; auto. generalize (Int.unsigned_range n); omega.
- discriminate.
Qed.

Lemma iagree_shr:
  forall x y m n,
  iagree x y (Int.or (Int.shl m n) (Int.repr Int.min_signed)) ->
  iagree (Int.shr x n) (Int.shr y n) m.
Proof.
  intros; red; intros. rewrite ! Int.bits_shr by auto.
  generalize (Int.unsigned_range n); intros.
  set (j := if zlt (i + Int.unsigned n) Int.zwordsize
            then i + Int.unsigned n
            else Int.zwordsize - 1).
  assert (0 <= j < Int.zwordsize).
  { unfold j; destruct (zlt (i + Int.unsigned n) Int.zwordsize); omega. }
  apply H; auto. autorewrite with ints; auto. apply orb_true_intro.
  unfold j; destruct (zlt (i + Int.unsigned n) Int.zwordsize).
- left. rewrite zlt_false by omega.
  replace (i + Int.unsigned n - Int.unsigned n) with i by omega.
  auto.
- right. reflexivity.
Qed.

Lemma iagree_rol:
  forall p q m amount,
  iagree p q (Int.ror m amount) ->
  iagree (Int.rol p amount) (Int.rol q amount) m.
Proof.
  intros. assert (Int.zwordsize > 0) by (compute; auto).
  red; intros. rewrite ! Int.bits_rol by auto. apply H.
  apply Z_mod_lt; auto.
  rewrite Int.bits_ror.
  replace (((i - Int.unsigned amount) mod Int.zwordsize + Int.unsigned amount)
   mod Int.zwordsize) with i. auto.
  apply Int.eqmod_small_eq with Int.zwordsize; auto.
  apply Int.eqmod_trans with ((i - Int.unsigned amount) + Int.unsigned amount).
  apply Int.eqmod_refl2; omega.
  eapply Int.eqmod_trans. 2: apply Int.eqmod_mod; auto.
  apply Int.eqmod_add.
  apply Int.eqmod_mod; auto.
  apply Int.eqmod_refl.
  apply Z_mod_lt; auto.
  apply Z_mod_lt; auto.
Qed.

Lemma iagree_ror:
  forall p q m amount,
  iagree p q (Int.rol m amount) ->
  iagree (Int.ror p amount) (Int.ror q amount) m.
Proof.
  intros. rewrite ! Int.ror_rol_neg by apply int_wordsize_divides_modulus.
  apply iagree_rol.
  rewrite Int.ror_rol_neg by apply int_wordsize_divides_modulus.
  rewrite Int.neg_involutive; auto.
Qed.

Lemma eqmod_iagree:
  forall m x y,
  Int.eqmod (two_p (Int.size m)) x y ->
  iagree (Int.repr x) (Int.repr y) m.
Proof.
  intros. set (p := nat_of_Z (Int.size m)).
  generalize (Int.size_range m); intros RANGE.
  assert (EQ: Int.size m = Z.of_nat p). { symmetry; apply nat_of_Z_eq. omega. }
  rewrite EQ in H; rewrite <- two_power_nat_two_p in H.
  red; intros. rewrite ! Int.testbit_repr by auto.
  destruct (zlt i (Int.size m)).
  eapply Int.same_bits_eqmod; eauto. omega.
  assert (Int.testbit m i = false) by (eapply Int.bits_size_2; omega).
  congruence.
Qed.

Definition complete_mask (m: int) := Int.zero_ext (Int.size m) Int.mone.

Lemma iagree_eqmod:
  forall x y m,
  iagree x y (complete_mask m) ->
  Int.eqmod (two_p (Int.size m)) (Int.unsigned x) (Int.unsigned y).
Proof.
  intros. set (p := nat_of_Z (Int.size m)).
  generalize (Int.size_range m); intros RANGE.
  assert (EQ: Int.size m = Z.of_nat p). { symmetry; apply nat_of_Z_eq. omega. }
  rewrite EQ; rewrite <- two_power_nat_two_p.
  apply Int.eqmod_same_bits. intros. apply H. omega.
  unfold complete_mask. rewrite Int.bits_zero_ext by omega.
  rewrite zlt_true by omega. rewrite Int.bits_mone by omega. auto.
Qed.

Lemma complete_mask_idem:
  forall m, complete_mask (complete_mask m) = complete_mask m.
Proof.
  unfold complete_mask; intros. destruct (Int.eq_dec m Int.zero).
+ subst m; reflexivity.
+ assert (Int.unsigned m <> 0).
  { red; intros; elim n. rewrite <- (Int.repr_unsigned m). rewrite H; auto. }
  assert (0 < Int.size m).
  { apply Int.Zsize_pos'. generalize (Int.unsigned_range m); omega. }
  generalize (Int.size_range m); intros.
  f_equal. apply Int.bits_size_4. tauto.
  rewrite Int.bits_zero_ext by omega. rewrite zlt_true by omega.
  apply Int.bits_mone; omega.
  intros. rewrite Int.bits_zero_ext by omega. apply zlt_false; omega.
Qed.

(** ** Abstract operations over value needs. *)

Ltac InvAgree :=
  simpl vagree in *;
  repeat (
  auto || exact Logic.I ||
  match goal with
  | [ H: False |- _ ] => contradiction
  | [ H: match ?v with Vundef => _ | Vint _ => _ | Vlong _ => _ | Vfloat _ => _ | Vsingle _ => _ | Vptr _ _ => _ end |- _ ] => destruct v
  | [ |- context [if Archi.ptr64 then _ else _] ] => destruct Archi.ptr64 eqn:?
  end).

(** And immediate, or immediate *)

Definition andimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.and m n)
  | All => I n
  end.

Lemma andimm_sound:
  forall v w x n,
  vagree v w (andimm x n) ->
  vagree (Val.and v (Vint n)) (Val.and w (Vint n)) x.
Proof.
  unfold andimm; intros; destruct x; simpl in *; unfold Val.and.
- auto.
- InvAgree. apply iagree_and; auto.
- InvAgree. rewrite iagree_and_eq in H. rewrite H; auto.
Qed.

Definition orimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.and m (Int.not n))
  | _ => I (Int.not n)
  end.

Lemma orimm_sound:
  forall v w x n,
  vagree v w (orimm x n) ->
  vagree (Val.or v (Vint n)) (Val.or w (Vint n)) x.
Proof.
  unfold orimm; intros; destruct x; simpl in *.
- auto.
- unfold Val.or; InvAgree. apply iagree_or; auto.
- InvAgree. simpl. apply Val.lessdef_same. f_equal. apply iagree_mone.
  apply iagree_or. rewrite Int.and_commut. rewrite Int.and_mone. auto.
Qed.

(** Bitwise operations: and, or, xor, not *)

Definition bitwise (x: nval) := x.

Remark bitwise_idem: forall nv, bitwise (bitwise nv) = bitwise nv.
Proof. auto. Qed.

Lemma vagree_bitwise_binop:
  forall f,
  (forall p1 p2 q1 q2 m,
     iagree p1 q1 m -> iagree p2 q2 m -> iagree (f p1 p2) (f q1 q2) m) ->
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (bitwise x) -> vagree v2 w2 (bitwise x) ->
  vagree (match v1, v2 with Vint i1, Vint i2 => Vint(f i1 i2) | _, _ => Vundef end)
         (match w1, w2 with Vint i1, Vint i2 => Vint(f i1 i2) | _, _ => Vundef end)
         x.
Proof.
  unfold bitwise; intros. destruct x; simpl in *.
- auto.
- InvAgree.
- inv H0; auto. inv H1; auto. destruct w1; auto.
Qed.

Lemma and_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (bitwise x) -> vagree v2 w2 (bitwise x) ->
  vagree (Val.and v1 v2) (Val.and w1 w2) x.
Proof (vagree_bitwise_binop Int.and (iagree_bitwise_binop andb Int.and Int.bits_and)).

Lemma or_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (bitwise x) -> vagree v2 w2 (bitwise x) ->
  vagree (Val.or v1 v2) (Val.or w1 w2) x.
Proof (vagree_bitwise_binop Int.or (iagree_bitwise_binop orb Int.or Int.bits_or)).

Lemma xor_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (bitwise x) -> vagree v2 w2 (bitwise x) ->
  vagree (Val.xor v1 v2) (Val.xor w1 w2) x.
Proof (vagree_bitwise_binop Int.xor (iagree_bitwise_binop xorb Int.xor Int.bits_xor)).

Lemma notint_sound:
  forall v w x,
  vagree v w (bitwise x) -> vagree (Val.notint v) (Val.notint w) x.
Proof.
  intros. rewrite ! Val.not_xor. apply xor_sound; auto with na.
Qed.

(** Shifts and rotates *)

Definition shlimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.shru m n)
  | All => I (Int.shru Int.mone n)
  end.

Lemma shlimm_sound:
  forall v w x n,
  vagree v w (shlimm x n) ->
  vagree (Val.shl v (Vint n)) (Val.shl w (Vint n)) x.
Proof.
  unfold shlimm; intros. unfold Val.shl.
  destruct (Int.ltu n Int.iwordsize).
  destruct x; simpl in *.
- auto.
- InvAgree. apply iagree_shl; auto.
- InvAgree. apply Val.lessdef_same. f_equal. apply iagree_mone. apply iagree_shl; auto.
- destruct v; auto with na.
Qed.

Definition shruimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.shl m n)
  | All => I (Int.shl Int.mone n)
  end.

Lemma shruimm_sound:
  forall v w x n,
  vagree v w (shruimm x n) ->
  vagree (Val.shru v (Vint n)) (Val.shru w (Vint n)) x.
Proof.
  unfold shruimm; intros. unfold Val.shru.
  destruct (Int.ltu n Int.iwordsize).
  destruct x; simpl in *.
- auto.
- InvAgree. apply iagree_shru; auto.
- InvAgree. apply Val.lessdef_same. f_equal. apply iagree_mone. apply iagree_shru; auto.
- destruct v; auto with na.
Qed.

Definition shrimm (x: nval) (n: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (let m' := Int.shl m n in
              if Int.eq_dec (Int.shru m' n) m
              then m'
              else Int.or m' (Int.repr Int.min_signed))
  | All => I (Int.or (Int.shl Int.mone n) (Int.repr Int.min_signed))
  end.

Lemma shrimm_sound:
  forall v w x n,
  vagree v w (shrimm x n) ->
  vagree (Val.shr v (Vint n)) (Val.shr w (Vint n)) x.
Proof.
  unfold shrimm; intros. unfold Val.shr.
  destruct (Int.ltu n Int.iwordsize).
  destruct x; simpl in *.
- auto.
- InvAgree.
  destruct (Int.eq_dec (Int.shru (Int.shl m n) n) m).
  apply iagree_shr_1; auto.
  apply iagree_shr; auto.
- InvAgree. apply Val.lessdef_same. f_equal. apply iagree_mone. apply iagree_shr. auto.
- destruct v; auto with na.
Qed.

Definition rol (x: nval) (amount: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.ror m amount)
  | All => All
  end.

Lemma rol_sound:
  forall v w x n,
  vagree v w (rol x n) ->
  vagree (Val.rol v (Vint n)) (Val.rol w (Vint n)) x.
Proof.
  unfold rol, Val.rol; intros.
  destruct x; simpl in *.
- auto.
- InvAgree. apply iagree_rol; auto.
- inv H; auto.
Qed.

Definition ror (x: nval) (amount: int) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.rol m amount)
  | All => All
  end.

Lemma ror_sound:
  forall v w x n,
  vagree v w (ror x n) ->
  vagree (Val.ror v (Vint n)) (Val.ror w (Vint n)) x.
Proof.
  unfold ror, Val.ror; intros.
  destruct x; simpl in *.
- auto.
- InvAgree. apply iagree_ror; auto.
- inv H; auto.
Qed.

Definition rolm (x: nval) (amount mask: int) := rol (andimm x mask) amount.

Lemma rolm_sound:
  forall v w x amount mask,
  vagree v w (rolm x amount mask) ->
  vagree (Val.rolm v amount mask) (Val.rolm w amount mask) x.
Proof.
  unfold rolm; intros.
  assert (X: forall u, Val.rolm u amount mask = Val.and (Val.rol u (Vint amount)) (Vint mask)).
  { destruct u; auto. }
  rewrite ! X.
  apply andimm_sound. apply rol_sound. auto.
Qed.

(** Modular arithmetic operations: add, mul, opposite.
    (But not subtraction because of the pointer - pointer case. *)

Definition modarith (x: nval) :=
  match x with
  | Nothing => Nothing
  | I m => I (complete_mask m)
  | All => All
  end.

Lemma add_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (modarith x) -> vagree v2 w2 (modarith x) ->
  vagree (Val.add v1 v2) (Val.add w1 w2) x.
Proof.
  unfold modarith; intros. destruct x; simpl in *.
- auto.
- unfold Val.add; InvAgree.
  apply eqmod_iagree. apply Int.eqmod_add; apply iagree_eqmod; auto.
- inv H; auto. inv H0; auto. destruct w1; auto.
Qed.

Remark modarith_idem: forall nv, modarith (modarith nv) = modarith nv.
Proof.
  destruct nv; simpl; auto. f_equal; apply complete_mask_idem.
Qed.

Lemma mul_sound:
  forall v1 w1 v2 w2 x,
  vagree v1 w1 (modarith x) -> vagree v2 w2 (modarith x) ->
  vagree (Val.mul v1 v2) (Val.mul w1 w2) x.
Proof.
  unfold mul, add; intros. destruct x; simpl in *.
- auto.
- unfold Val.mul; InvAgree. apply eqmod_iagree. apply Int.eqmod_mult; apply iagree_eqmod; auto.
- inv H; auto. inv H0; auto. destruct w1; auto.
Qed.

Lemma neg_sound:
  forall v w x,
  vagree v w (modarith x) ->
  vagree (Val.neg v) (Val.neg w) x.
Proof.
  intros; destruct x; simpl in *.
- auto.
- unfold Val.neg; InvAgree.
  apply eqmod_iagree. apply Int.eqmod_neg. apply iagree_eqmod; auto.
- inv H; simpl; auto.
Qed.

(** Conversions: zero extension, sign extension, single-of-float *)

Definition zero_ext (n: Z) (x: nval) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.zero_ext n m)
  | All => I (Int.zero_ext n Int.mone)
  end.

Lemma zero_ext_sound:
  forall v w x n,
  vagree v w (zero_ext n x) ->
  0 <= n ->
  vagree (Val.zero_ext n v) (Val.zero_ext n w) x.
Proof.
  unfold zero_ext; intros.
  destruct x; simpl in *.
- auto.
- unfold Val.zero_ext; InvAgree.
  red; intros. autorewrite with ints; try omega.
  destruct (zlt i1 n); auto. apply H; auto.
  autorewrite with ints; try omega. rewrite zlt_true; auto.
- unfold Val.zero_ext; InvAgree; auto. apply Val.lessdef_same. f_equal.
  Int.bit_solve; try omega. destruct (zlt i1 n); auto. apply H; auto.
  autorewrite with ints; try omega. apply zlt_true; auto.
Qed.

Definition sign_ext (n: Z) (x: nval) :=
  match x with
  | Nothing => Nothing
  | I m => I (Int.or (Int.zero_ext n m) (Int.shl Int.one (Int.repr (n - 1))))
  | All => I (Int.zero_ext n Int.mone)
  end.

Lemma sign_ext_sound:
  forall v w x n,
  vagree v w (sign_ext n x) ->
  0 < n < Int.zwordsize ->
  vagree (Val.sign_ext n v) (Val.sign_ext n w) x.
Proof.
  unfold sign_ext; intros. destruct x; simpl in *.
- auto.
- unfold Val.sign_ext; InvAgree.
  red; intros. autorewrite with ints; try omega.
  set (j := if zlt i1 n then i1 else n - 1).
  assert (0 <= j < Int.zwordsize).
  { unfold j; destruct (zlt i1 n); omega. }
  apply H; auto.
  autorewrite with ints; try omega. apply orb_true_intro.
  unfold j; destruct (zlt i1 n).
  left. rewrite zlt_true; auto.
  right. rewrite Int.unsigned_repr. rewrite zlt_false by omega.
  replace (n - 1 - (n - 1)) with 0 by omega. reflexivity.
  generalize Int.wordsize_max_unsigned; omega.
- unfold Val.sign_ext; InvAgree; auto. apply Val.lessdef_same. f_equal.
  Int.bit_solve; try omega.
  set (j := if zlt i1 n then i1 else n - 1).
  assert (0 <= j < Int.zwordsize).
  { unfold j; destruct (zlt i1 n); omega. }
  apply H; auto. rewrite Int.bits_zero_ext; try omega.
  rewrite zlt_true. apply Int.bits_mone; auto.
  unfold j. destruct (zlt i1 n); omega.
Qed.

(** The needs of a memory store concerning the value being stored. *)

Definition store_argument (chunk: memory_chunk) :=
  match chunk with
  | Mint8signed | Mint8unsigned => I (Int.repr 255)
  | Mint16signed | Mint16unsigned => I (Int.repr 65535)
  | _ => All
  end.

Lemma store_argument_sound:
  forall chunk v w,
  vagree v w (store_argument chunk) ->
  list_forall2 memval_lessdef (encode_val chunk v) (encode_val chunk w).
Proof.
  intros.
  assert (UNDEF: list_forall2 memval_lessdef
                     (list_repeat (size_chunk_nat chunk) Undef)
                     (encode_val chunk w)).
  {
     rewrite <- (encode_val_length chunk w).
     apply repeat_Undef_inject_any.
  }
  assert (SAME: forall vl1 vl2,
                vl1 = vl2 ->
                list_forall2 memval_lessdef vl1 vl2).
  {
     intros. subst vl2. revert vl1. induction vl1; constructor; auto.
     apply memval_lessdef_refl.
  }

  intros. unfold store_argument in H; destruct chunk.
- InvAgree. apply SAME. simpl; f_equal. apply encode_int_8_mod.
  change 8 with (Int.size (Int.repr 255)). apply iagree_eqmod; auto.
- InvAgree. apply SAME. simpl; f_equal. apply encode_int_8_mod.
  change 8 with (Int.size (Int.repr 255)). apply iagree_eqmod; auto.
- InvAgree. apply SAME. simpl; f_equal. apply encode_int_16_mod.
  change 16 with (Int.size (Int.repr 65535)). apply iagree_eqmod; auto.
- InvAgree. apply SAME. simpl; f_equal. apply encode_int_16_mod.
  change 16 with (Int.size (Int.repr 65535)). apply iagree_eqmod; auto.
- apply encode_val_inject. rewrite val_inject_id; auto.
- apply encode_val_inject. rewrite val_inject_id; auto.
- apply encode_val_inject. rewrite val_inject_id; auto.
- apply encode_val_inject. rewrite val_inject_id; auto.
- apply encode_val_inject. rewrite val_inject_id; auto.
- apply encode_val_inject. rewrite val_inject_id; auto.
Qed.

Lemma store_argument_load_result:
  forall chunk v w,
  vagree v w (store_argument chunk) ->
  Val.lessdef (Val.load_result chunk v) (Val.load_result chunk w).
Proof.
  unfold store_argument; intros; destruct chunk;
  auto using Val.load_result_lessdef; InvAgree; simpl.
- apply sign_ext_sound with (v := Vint i) (w := Vint i0) (x := All) (n := 8).
  auto. compute; auto.
- apply zero_ext_sound with (v := Vint i) (w := Vint i0) (x := All) (n := 8).
  auto. omega.
- apply sign_ext_sound with (v := Vint i) (w := Vint i0) (x := All) (n := 16).
  auto. compute; auto.
- apply zero_ext_sound with (v := Vint i) (w := Vint i0) (x := All) (n := 16).
  auto. omega.
Qed.

(** The needs of a comparison *)

Definition maskzero (n: int) := I n.

Lemma maskzero_sound:
  forall v w n b,
  vagree v w (maskzero n) ->
  Val.maskzero_bool v n = Some b ->
  Val.maskzero_bool w n = Some b.
Proof.
  unfold maskzero; intros.
  unfold Val.maskzero_bool; InvAgree; try discriminate.
  inv H0. rewrite iagree_and_eq in H. rewrite H. auto.
Qed.

(** The default abstraction: if the result is unused, the arguments are
  unused; otherwise, the arguments are needed in full. *)

Definition default (x: nval) :=
  match x with
  | Nothing => Nothing
  | _ => All
  end.

Section DEFAULT.

Variable ge: genv.
Variable sp: block.
Variables m1 m2: mem.
Hypothesis PERM: forall b ofs k p, Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p.

Let valid_pointer_inj:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  unfold inject_id; intros. inv H. rewrite Ptrofs.add_zero.
  rewrite Mem.valid_pointer_nonempty_perm in *. eauto.
Qed.

Let weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  unfold inject_id; intros. inv H. rewrite Ptrofs.add_zero.
  rewrite Mem.weak_valid_pointer_spec in *.
  rewrite ! Mem.valid_pointer_nonempty_perm in *.
  destruct H0; [left|right]; eauto.
Qed.

Let weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  inject_id b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  unfold inject_id; intros. inv H. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
Qed.

Let valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true ->
  inject_id b1 = Some (b1', delta1) ->
  inject_id b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  unfold inject_id; intros. left; congruence.
Qed.

Lemma default_needs_of_condition_sound:
  forall cond args1 b args2,
  eval_condition cond args1 m1 = Some b ->
  vagree_list args1 args2 nil ->
  eval_condition cond args2 m2 = Some b.
Proof.
  intros. apply eval_condition_inj with (f := inject_id) (m1 := m1) (vl1 := args1); auto.
  apply val_inject_list_lessdef. apply lessdef_vagree_list. auto.
Qed.

Lemma default_needs_of_operation_sound:
  forall op args1 v1 args2 nv,
  eval_operation ge (Vptr sp Ptrofs.zero) op args1 m1 = Some v1 ->
  vagree_list args1 args2 nil
  \/ vagree_list args1 args2 (default nv :: nil)
  \/ vagree_list args1 args2 (default nv :: default nv :: nil) ->
  nv <> Nothing ->
  exists v2,
     eval_operation ge (Vptr sp Ptrofs.zero) op args2 m2 = Some v2
  /\ vagree v1 v2 nv.
Proof.
  intros. assert (default nv = All) by (destruct nv; simpl; congruence).
  rewrite H2 in H0.
  assert (Val.lessdef_list args1 args2).
  {
    destruct H0. auto with na.
    destruct H0. inv H0; constructor; auto with na.
    inv H0; constructor; auto with na. inv H8; constructor; auto with na.
  }
  exploit (@eval_operation_inj _ _ _ _ ge ge inject_id).
  eassumption. auto. auto. auto.
  instantiate (1 := op). intros. apply val_inject_lessdef; auto.
  apply val_inject_lessdef. instantiate (1 := Vptr sp Ptrofs.zero). instantiate (1 := Vptr sp Ptrofs.zero). auto.
  apply val_inject_list_lessdef; eauto.
  eauto.
  intros (v2 & A & B). exists v2; split; auto.
  apply vagree_lessdef. apply val_inject_lessdef. auto.
Qed.

End DEFAULT.

(** ** Detecting operations that are redundant and can be turned into a move *)

Definition andimm_redundant (x: nval) (n: int) :=
  match x with
  | Nothing => true
  | I m => Int.eq_dec (Int.and m (Int.not n)) Int.zero
  | _ => false
  end.

Lemma andimm_redundant_sound:
  forall v w x n,
  andimm_redundant x n = true ->
  vagree v w (andimm x n) ->
  vagree (Val.and v (Vint n)) w x.
Proof.
  unfold andimm_redundant; intros. destruct x; try discriminate.
- simpl; auto.
- InvBooleans. simpl in *; unfold Val.and; InvAgree.
  red; intros. exploit (eq_same_bits i1); eauto.
  autorewrite with ints; auto. rewrite H2; simpl; intros.
  destruct (Int.testbit n i1) eqn:N; try discriminate.
  rewrite andb_true_r. apply H0; auto. autorewrite with ints; auto.
  rewrite H2, N; auto.
Qed.

Definition orimm_redundant (x: nval) (n: int) :=
  match x with
  | Nothing => true
  | I m => Int.eq_dec (Int.and m n) Int.zero
  | _ => false
  end.

Lemma orimm_redundant_sound:
  forall v w x n,
  orimm_redundant x n = true ->
  vagree v w (orimm x n) ->
  vagree (Val.or v (Vint n)) w x.
Proof.
  unfold orimm_redundant; intros. destruct x; try discriminate.
- auto.
- InvBooleans. simpl in *; unfold Val.or; InvAgree.
  apply iagree_not'. rewrite Int.not_or_and_not.
  apply (andimm_redundant_sound (Vint (Int.not i)) (Vint (Int.not i0)) (I m) (Int.not n)).
  simpl. rewrite Int.not_involutive. apply proj_sumbool_is_true. auto.
  simpl. apply iagree_not; auto.
Qed.

Definition rolm_redundant (x: nval) (amount mask: int) :=
  Int.eq_dec amount Int.zero && andimm_redundant x mask.

Lemma rolm_redundant_sound:
  forall v w x amount mask,
  rolm_redundant x amount mask = true ->
  vagree v w (rolm x amount mask) ->
  vagree (Val.rolm v amount mask) w x.
Proof.
  unfold rolm_redundant; intros; InvBooleans. subst amount. rewrite Val.rolm_zero.
  apply andimm_redundant_sound; auto.
  assert (forall n, Int.ror n Int.zero = n).
  { intros. rewrite Int.ror_rol_neg by apply int_wordsize_divides_modulus.
    rewrite Int.neg_zero. apply Int.rol_zero. }
  unfold rolm, rol, andimm in *. destruct x; auto.
  rewrite H in H0. auto.
  rewrite H in H0. auto.
Qed.

Definition zero_ext_redundant (n: Z) (x: nval) :=
  match x with
  | Nothing => true
  | I m => Int.eq_dec (Int.zero_ext n m) m
  | _ => false
  end.

Lemma zero_ext_redundant_sound:
  forall v w x n,
  zero_ext_redundant n x = true ->
  vagree v w (zero_ext n x) ->
  0 <= n ->
  vagree (Val.zero_ext n v) w x.
Proof.
  unfold zero_ext_redundant; intros. destruct x; try discriminate.
- auto.
- simpl in *; InvAgree. simpl. InvBooleans. rewrite <- H.
  red; intros; autorewrite with ints; try omega.
  destruct (zlt i1 n). apply H0; auto.
  rewrite Int.bits_zero_ext in H3 by omega. rewrite zlt_false in H3 by auto. discriminate.
Qed.

Definition sign_ext_redundant (n: Z) (x: nval) :=
  match x with
  | Nothing => true
  | I m => Int.eq_dec (Int.zero_ext n m) m
  | _ => false
  end.

Lemma sign_ext_redundant_sound:
  forall v w x n,
  sign_ext_redundant n x = true ->
  vagree v w (sign_ext n x) ->
  0 < n ->
  vagree (Val.sign_ext n v) w x.
Proof.
  unfold sign_ext_redundant; intros. destruct x; try discriminate.
- auto.
- simpl in *; InvAgree. simpl. InvBooleans. rewrite <- H.
  red; intros; autorewrite with ints; try omega.
  destruct (zlt i1 n). apply H0; auto.
  rewrite Int.bits_or; auto. rewrite H3; auto.
  rewrite Int.bits_zero_ext in H3 by omega. rewrite zlt_false in H3 by auto. discriminate.
Qed.

(** * Neededness for register environments *)

Module NVal <: SEMILATTICE.

  Definition t := nval.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
  Definition beq (x y: t) : bool := proj_sumbool (eq_nval x y).
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof. unfold beq; intros. InvBooleans. auto. Qed.
  Definition ge := nge.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof. unfold eq, ge; intros. subst y. apply nge_refl. Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof. unfold ge; intros. eapply nge_trans; eauto. Qed.
  Definition bot : t := Nothing.
  Lemma ge_bot: forall x, ge x bot.
  Proof. intros. constructor. Qed.
  Definition lub := nlub.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof nge_lub_l.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof nge_lub_r.
End NVal.

Module NE := LPMap1(NVal).

Definition nenv := NE.t.

Definition nreg (ne: nenv) (r: reg) := NE.get r ne.

Definition eagree (e1 e2: regset) (ne: nenv) : Prop :=
  forall r, vagree e1#r e2#r (NE.get r ne).

Lemma nreg_agree:
  forall rs1 rs2 ne r, eagree rs1 rs2 ne -> vagree rs1#r rs2#r (nreg ne r).
Proof.
  intros. apply H.
Qed.

Hint Resolve nreg_agree: na.

Lemma eagree_ge:
  forall e1 e2 ne ne',
  eagree e1 e2 ne -> NE.ge ne ne' -> eagree e1 e2 ne'.
Proof.
  intros; red; intros. apply nge_agree with (NE.get r ne); auto. apply H0.
Qed.

Lemma eagree_bot:
  forall e1 e2, eagree e1 e2 NE.bot.
Proof.
  intros; red; intros. rewrite NE.get_bot. exact Logic.I.
Qed.

Lemma eagree_same:
  forall e ne, eagree e e ne.
Proof.
  intros; red; intros. apply vagree_same.
Qed.

Lemma eagree_update_1:
  forall e1 e2 ne v1 v2 nv r,
  eagree e1 e2 ne -> vagree v1 v2 nv -> eagree (e1#r <- v1) (e2#r <- v2) (NE.set r nv ne).
Proof.
  intros; red; intros. rewrite NE.gsspec. rewrite ! PMap.gsspec.
  destruct (peq r0 r); auto.
Qed.

Lemma eagree_update:
  forall e1 e2 ne v1 v2 r,
  vagree v1 v2 (nreg ne r) ->
  eagree e1 e2 (NE.set r Nothing ne) ->
  eagree (e1#r <- v1) (e2#r <- v2) ne.
Proof.
  intros; red; intros. specialize (H0 r0). rewrite NE.gsspec in H0.
  rewrite ! PMap.gsspec. destruct (peq r0 r).
  subst r0. auto.
  auto.
Qed.

Lemma eagree_update_dead:
  forall e1 e2 ne v1 r,
  nreg ne r = Nothing ->
  eagree e1 e2 ne -> eagree (e1#r <- v1) e2 ne.
Proof.
  intros; red; intros. rewrite PMap.gsspec.
  destruct (peq r0 r); auto. subst. unfold nreg in H. rewrite H. red; auto.
Qed.

(** * Neededness for memory locations *)

Inductive nmem : Type :=
  | NMemDead
  | NMem (stk: ISet.t) (gl: PTree.t ISet.t).

(** Interpretation of [nmem]:
- [NMemDead]: all memory locations are unused (dead).  Acts as bottom.
- [NMem stk gl]: all memory locations are used, except:
  - the stack locations whose offset is in the interval [stk]
  - the global locations whose offset is in the corresponding entry of [gl].
*)

Section LOCATIONS.

Variable ge: genv.
Variable sp: block.

Inductive nlive: nmem -> block -> Z -> Prop :=
  | nlive_intro: forall stk gl b ofs
      (STK: b = sp -> ~ISet.In ofs stk)
      (GL: forall id iv,
           Genv.find_symbol ge id = Some b ->
           gl!id = Some iv ->
           ~ISet.In ofs iv),
      nlive (NMem stk gl) b ofs.

(** All locations are live *)

Definition nmem_all := NMem ISet.empty (PTree.empty _).

Lemma nlive_all: forall b ofs, nlive nmem_all b ofs.
Proof.
  intros; constructor; intros.
  apply ISet.In_empty.
  rewrite PTree.gempty in H0; discriminate.
Qed.

(** Add a range of live locations to [nm].  The range starts at
  the abstract pointer [p] and has length [sz]. *)

Definition nmem_add (nm: nmem) (p: aptr) (sz: Z) : nmem :=
  match nm with
  | NMemDead => nmem_all       (**r very conservative, should never happen *)
  | NMem stk gl =>
      match p with
      | Gl id ofs =>
          match gl!id with
          | Some iv => NMem stk (PTree.set id (ISet.remove (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) iv) gl)
          | None => nm
          end
      | Glo id =>
          NMem stk (PTree.remove id gl)
      | Stk ofs =>
          NMem (ISet.remove (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) stk) gl
      | Stack =>
          NMem ISet.empty gl
      | _ => nmem_all
      end
  end.

Lemma nlive_add:
  forall bc b ofs p nm sz i,
  genv_match bc ge ->
  bc sp = BCstack ->
  pmatch bc b ofs p ->
  Ptrofs.unsigned ofs <= i < Ptrofs.unsigned ofs + sz ->
  nlive (nmem_add nm p sz) b i.
Proof.
  intros. unfold nmem_add. destruct nm. apply nlive_all.
  inv H1; try (apply nlive_all).
  - (* Gl id ofs *)
    assert (Genv.find_symbol ge id = Some b) by (eapply H; eauto).
    destruct gl!id as [iv|] eqn:NG.
  + constructor; simpl; intros.
    congruence.
    assert (id0 = id) by (eapply Genv.genv_vars_inj; eauto). subst id0.
    rewrite PTree.gss in H5. inv H5. rewrite ISet.In_remove.
    intros [A B]. elim A; auto.
  + constructor; simpl; intros.
    congruence.
    assert (id0 = id) by (eapply Genv.genv_vars_inj; eauto). subst id0.
    congruence.
  - (* Glo id *)
    assert (Genv.find_symbol ge id = Some b) by (eapply H; eauto).
    constructor; simpl; intros.
    congruence.
    assert (id0 = id) by (eapply Genv.genv_vars_inj; eauto). subst id0.
    rewrite PTree.grs in H5. congruence.
  - (* Stk ofs *)
    constructor; simpl; intros.
    rewrite ISet.In_remove. intros [A B]. elim A; auto.
    assert (bc b = BCglob id) by (eapply H; eauto). congruence.
  - (* Stack *)
    constructor; simpl; intros.
    apply ISet.In_empty.
    assert (bc b = BCglob id) by (eapply H; eauto). congruence.
Qed.

Lemma incl_nmem_add:
  forall nm b i p sz,
  nlive nm b i -> nlive (nmem_add nm p sz) b i.
Proof.
  intros. inversion H; subst. unfold nmem_add; destruct p; try (apply nlive_all).
- (* Gl id ofs *)
  destruct gl!id as [iv|] eqn:NG.
  + split; simpl; intros. auto.
    rewrite PTree.gsspec in H1. destruct (peq id0 id); eauto. inv H1.
    rewrite ISet.In_remove. intros [P Q]. eelim GL; eauto.
  + auto.
- (* Glo id *)
  split; simpl; intros. auto.
  rewrite PTree.grspec in H1. destruct (PTree.elt_eq id0 id). congruence. eauto.
- (* Stk ofs *)
  split; simpl; intros.
  rewrite ISet.In_remove. intros [P Q]. eelim STK; eauto.
  eauto.
- (* Stack *)
  split; simpl; intros.
  apply ISet.In_empty.
  eauto.
Qed.

(** Remove a range of locations from [nm], marking these locations as dead.
  The range starts at the abstract pointer [p] and has length [sz]. *)

Definition nmem_remove (nm: nmem) (p: aptr) (sz: Z) : nmem :=
  match nm with
  | NMemDead => NMemDead
  | NMem stk gl =>
    match p with
    | Gl id ofs =>
        let iv' :=
        match gl!id with
        | Some iv => ISet.add (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) iv
        | None    => ISet.interval (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz)
        end in
        NMem stk (PTree.set id iv' gl)
    | Stk ofs =>
        NMem (ISet.add (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) stk) gl
    | _ => nm
    end
  end.

Lemma nlive_remove:
  forall bc b ofs p nm sz b' i,
  genv_match bc ge ->
  bc sp = BCstack ->
  pmatch bc b ofs p ->
  nlive nm b' i ->
  b' <> b \/ i < Ptrofs.unsigned ofs \/ Ptrofs.unsigned ofs + sz <= i ->
  nlive (nmem_remove nm p sz) b' i.
Proof.
  intros. inversion H2; subst. unfold nmem_remove; inv H1; auto.
- (* Gl id ofs *)
  set (iv' := match gl!id with
                  | Some iv =>
                      ISet.add (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) iv
                  | None =>
                      ISet.interval (Ptrofs.unsigned ofs)
                        (Ptrofs.unsigned ofs + sz)
              end).
  assert (Genv.find_symbol ge id = Some b) by (eapply H; eauto).
  split; simpl; auto; intros.
  rewrite PTree.gsspec in H6. destruct (peq id0 id).
+ inv H6. destruct H3. congruence. destruct gl!id as [iv0|] eqn:NG.
  unfold iv'; rewrite ISet.In_add. intros [P|P]. omega. eelim GL; eauto.
  unfold iv'; rewrite ISet.In_interval. omega.
+ eauto.
- (* Stk ofs *)
  split; simpl; auto; intros. destruct H3.
  elim H3. subst b'. eapply bc_stack; eauto.
  rewrite ISet.In_add. intros [P|P]. omega. eapply STK; eauto.
Qed.

(** Test (conservatively) whether some locations in the range delimited
  by [p] and [sz] can be live in [nm]. *)

Definition nmem_contains (nm: nmem) (p: aptr) (sz: Z) :=
  match nm with
  | NMemDead => false
  | NMem stk gl =>
      match p with
      | Gl id ofs =>
          match gl!id with
          | Some iv => negb (ISet.contains (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) iv)
          | None => true
          end
      | Stk ofs =>
          negb (ISet.contains (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) stk)
      | _ => true  (**r conservative answer *)
      end
  end.

Lemma nlive_contains:
  forall bc b ofs p nm sz i,
  genv_match bc ge ->
  bc sp = BCstack ->
  pmatch bc b ofs p ->
  nmem_contains nm p sz = false ->
  Ptrofs.unsigned ofs <= i < Ptrofs.unsigned ofs + sz ->
  ~(nlive nm b i).
Proof.
  unfold nmem_contains; intros. red; intros L; inv L.
  inv H1; try discriminate.
- (* Gl id ofs *)
  assert (Genv.find_symbol ge id = Some b) by (eapply H; eauto).
  destruct gl!id as [iv|] eqn:HG; inv H2.
  destruct (ISet.contains (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) iv) eqn:IC; try discriminate.
  rewrite ISet.contains_spec in IC. eelim GL; eauto.
- (* Stk ofs *)
  destruct (ISet.contains (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sz) stk) eqn:IC; try discriminate.
  rewrite ISet.contains_spec in IC. eelim STK; eauto. eapply bc_stack; eauto.
Qed.

(** Kill all stack locations between 0 and [sz], and mark everything else
  as live.  This reflects the effect of freeing the stack block at
  a [Ireturn] or [Itailcall] instruction. *)

Definition nmem_dead_stack (sz: Z) :=
  NMem (ISet.interval 0 sz) (PTree.empty _).

Lemma nlive_dead_stack:
  forall sz b' i, b' <> sp \/ ~(0 <= i < sz) -> nlive (nmem_dead_stack sz) b' i.
Proof.
  intros; constructor; simpl; intros.
- rewrite ISet.In_interval. intuition.
- rewrite PTree.gempty in H1; discriminate.
Qed.

(** Least upper bound *)

Definition nmem_lub (nm1 nm2: nmem) : nmem :=
  match nm1, nm2 with
  | NMemDead, _ => nm2
  | _, NMemDead => nm1
  | NMem stk1 gl1, NMem stk2 gl2 =>
      NMem (ISet.inter stk1 stk2)
           (PTree.combine
                (fun o1 o2 =>
                  match o1, o2 with
                  | Some iv1, Some iv2 => Some(ISet.inter iv1 iv2)
                  | _, _ => None
                  end)
                gl1 gl2)
  end.

Lemma nlive_lub_l:
  forall nm1 nm2 b i, nlive nm1 b i -> nlive (nmem_lub nm1 nm2) b i.
Proof.
  intros. inversion H; subst. destruct nm2; simpl. auto.
  constructor; simpl; intros.
- rewrite ISet.In_inter. intros [P Q]. eelim STK; eauto.
- rewrite PTree.gcombine in H1 by auto.
  destruct gl!id as [iv1|] eqn:NG1; try discriminate;
  destruct gl0!id as [iv2|] eqn:NG2; inv H1.
  rewrite ISet.In_inter. intros [P Q]. eelim GL; eauto.
Qed.

Lemma nlive_lub_r:
  forall nm1 nm2 b i, nlive nm2 b i -> nlive (nmem_lub nm1 nm2) b i.
Proof.
  intros. inversion H; subst. destruct nm1; simpl. auto.
  constructor; simpl; intros.
- rewrite ISet.In_inter. intros [P Q]. eelim STK; eauto.
- rewrite PTree.gcombine in H1 by auto.
  destruct gl0!id as [iv1|] eqn:NG1; try discriminate;
  destruct gl!id as [iv2|] eqn:NG2; inv H1.
  rewrite ISet.In_inter. intros [P Q]. eelim GL; eauto.
Qed.

(** Boolean-valued equality test *)

Definition nmem_beq (nm1 nm2: nmem) : bool :=
  match nm1, nm2 with
  | NMemDead, NMemDead => true
  | NMem stk1 gl1, NMem stk2 gl2 => ISet.beq stk1 stk2 && PTree.beq ISet.beq gl1 gl2
  | _, _ => false
  end.

Lemma nmem_beq_sound:
  forall nm1 nm2 b ofs,
  nmem_beq nm1 nm2 = true ->
  (nlive nm1 b ofs <-> nlive nm2 b ofs).
Proof.
  unfold nmem_beq; intros.
  destruct nm1 as [ | stk1 gl1]; destruct nm2 as [ | stk2 gl2]; try discriminate.
- split; intros L; inv L.
- InvBooleans. rewrite ISet.beq_spec in H0. rewrite PTree.beq_correct in H1.
  split; intros L; inv L; constructor; intros.
+ rewrite <- H0. eauto.
+ specialize (H1 id). rewrite H2 in H1. destruct gl1!id as [iv1|] eqn: NG; try contradiction.
  rewrite ISet.beq_spec in H1. rewrite <- H1. eauto.
+ rewrite H0. eauto.
+ specialize (H1 id). rewrite H2 in H1. destruct gl2!id as [iv2|] eqn: NG; try contradiction.
  rewrite ISet.beq_spec in H1. rewrite H1. eauto.
Qed.

End LOCATIONS.


(** * The lattice for dataflow analysis *)

Module NA <: SEMILATTICE.

  Definition t := (nenv * nmem)%type.

  Definition eq (x y: t) :=
    NE.eq (fst x) (fst y) /\
    (forall ge sp b ofs, nlive ge sp (snd x) b ofs <-> nlive ge sp (snd y) b ofs).

  Lemma eq_refl: forall x, eq x x.
  Proof.
    unfold eq; destruct x; simpl; split. apply NE.eq_refl. tauto.
  Qed.
  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq; destruct x, y; simpl. intros [A B].
    split. apply NE.eq_sym; auto.
    intros. rewrite B. tauto.
  Qed.
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq; destruct x, y, z; simpl. intros [A B] [C D]; split.
    eapply NE.eq_trans; eauto.
    intros. rewrite B; auto.
  Qed.

  Definition beq (x y: t) : bool :=
    NE.beq (fst x) (fst y) && nmem_beq (snd x) (snd y).

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq, eq; destruct x, y; simpl; intros. InvBooleans. split.
    apply NE.beq_correct; auto.
    intros. apply nmem_beq_sound; auto.
  Qed.

  Definition ge (x y: t) : Prop :=
    NE.ge (fst x) (fst y) /\
    (forall ge sp b ofs, nlive ge sp (snd y) b ofs -> nlive ge sp (snd x) b ofs).

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge; destruct x, y; simpl. intros [A B]; split.
    apply NE.ge_refl; auto.
    intros. apply B; auto.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; destruct x, y, z; simpl. intros [A B] [C D]; split.
    eapply NE.ge_trans; eauto.
    auto.
  Qed.

  Definition bot : t := (NE.bot, NMemDead).

  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot; destruct x; simpl. split.
    apply NE.ge_bot.
    intros. inv H.
  Qed.

  Definition lub (x y: t) : t :=
    (NE.lub (fst x) (fst y), nmem_lub (snd x) (snd y)).

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold ge; destruct x, y; simpl; split.
    apply NE.ge_lub_left.
    intros; apply nlive_lub_l; auto.
  Qed.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold ge; destruct x, y; simpl; split.
    apply NE.ge_lub_right.
    intros; apply nlive_lub_r; auto.
  Qed.

End NA.


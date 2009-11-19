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

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.

Definition block : Type := Z.
Definition eq_block := zeq.

(** A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
*)

Inductive val: Type :=
  | Vundef: val
  | Vint: int -> val
  | Vfloat: float -> val
  | Vptr: block -> int -> val.

Definition Vzero: val := Vint Int.zero.
Definition Vone: val := Vint Int.one.
Definition Vmone: val := Vint Int.mone.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

Module Val.

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Definition has_type (v: val) (t: typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _, Tint => True
  | Vfloat _, Tfloat => True
  | Vptr _ _, Tint => True
  | _, _ => False
  end.

Fixpoint has_type_list (vl: list val) (tl: list typ) {struct vl} : Prop :=
  match vl, tl with
  | nil, nil => True
  | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
  | _, _ => False
  end.

(** Truth values.  Pointers and non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  [Vundef] and floats are neither true nor false. *)

Definition is_true (v: val) : Prop :=
  match v with
  | Vint n => n <> Int.zero
  | Vptr b ofs => True
  | _ => False
  end.

Definition is_false (v: val) : Prop :=
  match v with
  | Vint n => n = Int.zero
  | _ => False
  end.

Inductive bool_of_val: val -> bool -> Prop :=
  | bool_of_val_int_true:
      forall n, n <> Int.zero -> bool_of_val (Vint n) true
  | bool_of_val_int_false:
      bool_of_val (Vint Int.zero) false
  | bool_of_val_ptr:
      forall b ofs, bool_of_val (Vptr b ofs) true.

Definition neg (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition negf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.neg f)
  | _ => Vundef
  end.

Definition absf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.abs f)
  | _ => Vundef
  end.

Definition intoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vint (Float.intoffloat f)
  | _ => Vundef
  end.

Definition intuoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vint (Float.intuoffloat f)
  | _ => Vundef
  end.

Definition floatofint (v: val) : val :=
  match v with
  | Vint n => Vfloat (Float.floatofint n)
  | _ => Vundef
  end.

Definition floatofintu (v: val) : val :=
  match v with
  | Vint n => Vfloat (Float.floatofintu n)
  | _ => Vundef
  end.

Definition notint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.xor n Int.mone)
  | _ => Vundef
  end.

Definition notbool (v: val) : val :=
  match v with
  | Vint n => of_bool (Int.eq n Int.zero)
  | Vptr b ofs => Vfalse
  | _ => Vundef
  end.

Definition zero_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.zero_ext nbits n)
  | _ => Vundef
  end.

Definition sign_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.sign_ext nbits n)
  | _ => Vundef
  end.

Definition singleoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vfloat(Float.singleoffloat f)
  | _ => Vundef
  end.

Definition add (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.add n1 n2)
  | Vptr b1 ofs1, Vint n2 => Vptr b1 (Int.add ofs1 n2)
  | Vint n1, Vptr b2 ofs2 => Vptr b2 (Int.add ofs2 n1)
  | _, _ => Vundef
  end.

Definition sub (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.sub n1 n2)
  | Vptr b1 ofs1, Vint n2 => Vptr b1 (Int.sub ofs1 n2)
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if zeq b1 b2 then Vint(Int.sub ofs1 ofs2) else Vundef
  | _, _ => Vundef
  end.

Definition mul (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mul n1 n2)
  | _, _ => Vundef
  end.

Definition divs (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then Vundef else Vint(Int.divs n1 n2)
  | _, _ => Vundef
  end.

Definition mods (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then Vundef else Vint(Int.mods n1 n2)
  | _, _ => Vundef
  end.

Definition divu (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then Vundef else Vint(Int.divu n1 n2)
  | _, _ => Vundef
  end.

Definition modu (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then Vundef else Vint(Int.modu n1 n2)
  | _, _ => Vundef
  end.

Definition and (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.and n1 n2)
  | _, _ => Vundef
  end.

Definition or (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.or n1 n2)
  | _, _ => Vundef
  end.

Definition xor (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.xor n1 n2)
  | _, _ => Vundef
  end.

Definition shl (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shl n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr_carry (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr_carry n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrx (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shrx n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shru (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shru n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition rolm (v: val) (amount mask: int): val :=
  match v with
  | Vint n => Vint(Int.rolm n amount mask)
  | _ => Vundef
  end.

Definition ror (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.ror n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition addf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.add f1 f2)
  | _, _ => Vundef
  end.

Definition subf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.div f1 f2)
  | _, _ => Vundef
  end.

Definition cmp_mismatch (c: comparison): val :=
  match c with
  | Ceq => Vfalse
  | Cne => Vtrue
  | _   => Vundef
  end.

Definition cmp (c: comparison) (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => of_bool (Int.cmp c n1 n2)
  | Vint n1, Vptr b2 ofs2 =>
      if Int.eq n1 Int.zero then cmp_mismatch c else Vundef
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if zeq b1 b2
      then of_bool (Int.cmp c ofs1 ofs2)
      else cmp_mismatch c
  | Vptr b1 ofs1, Vint n2 =>
      if Int.eq n2 Int.zero then cmp_mismatch c else Vundef
  | _, _ => Vundef
  end.

Definition cmpu (c: comparison) (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      of_bool (Int.cmpu c n1 n2)
  | Vint n1, Vptr b2 ofs2 =>
      if Int.eq n1 Int.zero then cmp_mismatch c else Vundef
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if zeq b1 b2
      then of_bool (Int.cmpu c ofs1 ofs2)
      else cmp_mismatch c
  | Vptr b1 ofs1, Vint n2 =>
      if Int.eq n2 Int.zero then cmp_mismatch c else Vundef
  | _, _ => Vundef
  end.

Definition cmpf (c: comparison) (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => of_bool (Float.cmp c f1 f2)
  | _, _ => Vundef
  end.

(** [load_result] is used in the memory model (library [Mem])
  to post-process the results of a memory read.  For instance,
  consider storing the integer value [0xFFF] on 1 byte at a
  given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension
  is performed and [0xFFFFFFFF] is returned.   Type mismatches
  (e.g. reading back a float as a [Mint32]) read back as [Vundef]. *)

Definition load_result (chunk: memory_chunk) (v: val) :=
  match chunk, v with
  | Mint8signed, Vint n => Vint (Int.sign_ext 8 n)
  | Mint8unsigned, Vint n => Vint (Int.zero_ext 8 n)
  | Mint16signed, Vint n => Vint (Int.sign_ext 16 n)
  | Mint16unsigned, Vint n => Vint (Int.zero_ext 16 n)
  | Mint32, Vint n => Vint n
  | Mint32, Vptr b ofs => Vptr b ofs
  | Mfloat32, Vfloat f => Vfloat(Float.singleoffloat f)
  | Mfloat64, Vfloat f => Vfloat f
  | _, _ => Vundef
  end.

(** Theorems on arithmetic operations. *)

Theorem cast8unsigned_and:
  forall x, zero_ext 8 x = and x (Vint(Int.repr 255)).
Proof.
  destruct x; simpl; auto. decEq. 
  change 255 with (two_p 8 - 1). apply Int.zero_ext_and. vm_compute; auto.
Qed.

Theorem cast16unsigned_and:
  forall x, zero_ext 16 x = and x (Vint(Int.repr 65535)).
Proof.
  destruct x; simpl; auto. decEq. 
  change 65535 with (two_p 16 - 1). apply Int.zero_ext_and. vm_compute; auto.
Qed.

Theorem istrue_not_isfalse:
  forall v, is_false v -> is_true (notbool v).
Proof.
  destruct v; simpl; try contradiction.
  intros. subst i. simpl. discriminate.
Qed.

Theorem isfalse_not_istrue:
  forall v, is_true v -> is_false (notbool v).
Proof.
  destruct v; simpl; try contradiction.
  intros. generalize (Int.eq_spec i Int.zero).
  case (Int.eq i Int.zero); intro.
  contradiction. simpl. auto.
  auto.
Qed.

Theorem bool_of_true_val:
  forall v, is_true v -> bool_of_val v true.
Proof.
  intro. destruct v; simpl; intros; try contradiction.
  constructor; auto. constructor.
Qed.

Theorem bool_of_true_val2:
  forall v, bool_of_val v true -> is_true v.
Proof.
  intros. inversion H; simpl; auto.
Qed.

Theorem bool_of_true_val_inv:
  forall v b, is_true v -> bool_of_val v b -> b = true.
Proof.
  intros. inversion H0; subst v b; simpl in H; auto. 
Qed.

Theorem bool_of_false_val:
  forall v, is_false v -> bool_of_val v false.
Proof.
  intro. destruct v; simpl; intros; try contradiction.
  subst i;  constructor.
Qed.

Theorem bool_of_false_val2:
  forall v, bool_of_val v false -> is_false v.
Proof.
  intros. inversion H; simpl; auto.
Qed.

Theorem bool_of_false_val_inv:
  forall v b, is_false v -> bool_of_val v b -> b = false.
Proof.
  intros. inversion H0; subst v b; simpl in H.
  congruence. auto. contradiction.
Qed.

Theorem notbool_negb_1:
  forall b, of_bool (negb b) = notbool (of_bool b).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_2:
  forall b, of_bool b = notbool (of_bool (negb b)).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem2:
  forall b, notbool(notbool(of_bool b)) = of_bool b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem3:
  forall x, notbool(notbool(notbool x)) = notbool x.
Proof.
  destruct x; simpl; auto. 
  case (Int.eq i Int.zero); reflexivity.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof.
  destruct x; destruct y; simpl; auto.
  decEq. apply Int.add_commut.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  rewrite Int.add_assoc; auto.
  rewrite Int.add_assoc; auto.
  decEq. decEq. apply Int.add_commut.
  decEq. rewrite Int.add_commut. rewrite <- Int.add_assoc. 
  decEq. apply Int.add_commut.
  decEq. rewrite Int.add_assoc. auto.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut.
Qed.

Theorem add_permut_4:
  forall x y z t, add (add x y) (add z t) = add (add x z) (add y t).
Proof.
  intros. rewrite add_permut. rewrite add_assoc. 
  rewrite add_permut. symmetry. apply add_assoc. 
Qed.

Theorem neg_zero: neg Vzero = Vzero.
Proof.
  reflexivity.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.neg_add_distr.
Qed.

Theorem sub_zero_r: forall x, sub Vzero x = neg x.
Proof.
  destruct x; simpl; auto. 
Qed.

Theorem sub_add_opp: forall x y, sub x (Vint y) = add x (Vint (Int.neg y)).
Proof.
  destruct x; intro y; simpl; auto; rewrite Int.sub_add_opp; auto.
Qed.

Theorem sub_opp_add: forall x y, sub x (Vint (Int.neg y)) = add x (Vint y).
Proof.
  intros. unfold sub, add.
  destruct x; auto; rewrite Int.sub_add_opp; rewrite Int.neg_involutive; auto.
Qed.

Theorem sub_add_l:
  forall v1 v2 i, sub (add v1 (Vint i)) v2 = add (sub v1 v2) (Vint i).
Proof.
  destruct v1; destruct v2; intros; simpl; auto.
  rewrite Int.sub_add_l. auto.
  rewrite Int.sub_add_l. auto.
  case (zeq b b0); intro. rewrite Int.sub_add_l. auto. reflexivity.
Qed.

Theorem sub_add_r:
  forall v1 v2 i, sub v1 (add v2 (Vint i)) = add (sub v1 v2) (Vint (Int.neg i)).
Proof.
  destruct v1; destruct v2; intros; simpl; auto.
  rewrite Int.sub_add_r. auto.
  repeat rewrite Int.sub_add_opp. decEq. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  decEq. repeat rewrite Int.sub_add_opp. 
  rewrite Int.add_assoc. decEq. apply Int.neg_add_distr.
  case (zeq b b0); intro. simpl. decEq. 
  repeat rewrite Int.sub_add_opp. rewrite Int.add_assoc. decEq.
  apply Int.neg_add_distr.
  reflexivity.
Qed.

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.mul_commut.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_assoc.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_add_distr_l.
Qed.


Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_add_distr_r.
Qed.

Theorem mul_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  mul x (Vint n) = shl x (Vint logn).
Proof.
  intros; destruct x; simpl; auto.
  change 32 with (Z_of_nat Int.wordsize).
  rewrite (Int.is_power2_range _ _ H). decEq. apply Int.mul_pow2. auto.
Qed.  

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
Proof.
  destruct x; destruct y; simpl; auto.
  case (Int.eq i0 Int.zero); simpl. auto. decEq. apply Int.mods_divs.
Qed.

Theorem modu_divu:
  forall x y, modu x y = sub x (mul (divu x y) y).
Proof.
  destruct x; destruct y; simpl; auto.
  generalize (Int.eq_spec i0 Int.zero);
  case (Int.eq i0 Int.zero); simpl. auto. 
  intro. decEq. apply Int.modu_divu. auto.
Qed.

Theorem divs_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  divs x (Vint n) = shrx x (Vint logn).
Proof.
  intros; destruct x; simpl; auto.
  change 32 with (Z_of_nat Int.wordsize).
  rewrite (Int.is_power2_range _ _ H). 
  generalize (Int.eq_spec n Int.zero);
  case (Int.eq n Int.zero); intro.
  subst n. compute in H. discriminate.
  decEq. apply Int.divs_pow2. auto.
Qed.

Theorem divu_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  divu x (Vint n) = shru x (Vint logn).
Proof.
  intros; destruct x; simpl; auto.
  change 32 with (Z_of_nat Int.wordsize).
  rewrite (Int.is_power2_range _ _ H). 
  generalize (Int.eq_spec n Int.zero);
  case (Int.eq n Int.zero); intro.
  subst n. compute in H. discriminate.
  decEq. apply Int.divu_pow2. auto.
Qed.

Theorem modu_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  modu x (Vint n) = and x (Vint (Int.sub n Int.one)).
Proof.
  intros; destruct x; simpl; auto.
  generalize (Int.eq_spec n Int.zero);
  case (Int.eq n Int.zero); intro.
  subst n. compute in H. discriminate.
  decEq. eapply Int.modu_and; eauto.
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.and_commut.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.and_assoc.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.or_commut.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.or_assoc.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.xor_commut.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.xor_assoc.
Qed.

Theorem shl_mul: forall x y, Val.mul x (Val.shl Vone y) = Val.shl x y.
Proof.
  destruct x; destruct y; simpl; auto. 
  case (Int.ltu i0 Int.iwordsize); auto.
  decEq. symmetry. apply Int.shl_mul.
Qed.

Theorem shl_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shl x (Vint n) = rolm x n (Int.shl Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shl_rolm. exact H.
Qed.

Theorem shru_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shru x (Vint n) = rolm x (Int.sub Int.iwordsize n) (Int.shru Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shru_rolm. exact H.
Qed.

Theorem shrx_carry:
  forall x y,
  add (shr x y) (shr_carry x y) = shrx x y.
Proof.
  destruct x; destruct y; simpl; auto.
  case (Int.ltu i0 Int.iwordsize); auto.
  simpl. decEq. apply Int.shrx_carry.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or m1 m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq. apply Int.or_rolm.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.modu (Int.add n1 n2) Int.iwordsize)
           (Int.and (Int.rol m1 n2) m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq. 
  apply Int.rolm_rolm. apply int_wordsize_divides_modulus.
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x Int.zero m = and x (Vint m).
Proof.
  intros; destruct x; simpl; auto. decEq. apply Int.rolm_zero.
Qed.

Theorem addf_commut: forall x y, addf x y = addf y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Float.addf_commut.
Qed.

Lemma negate_cmp_mismatch:
  forall c,
  cmp_mismatch (negate_comparison c) = notbool(cmp_mismatch c).
Proof.
  destruct c; reflexivity.
Qed.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
Proof.
  destruct x; destruct y; simpl; auto.
  rewrite Int.negate_cmp. apply notbool_negb_1.
  case (Int.eq i Int.zero). apply negate_cmp_mismatch. reflexivity.
  case (Int.eq i0 Int.zero). apply negate_cmp_mismatch. reflexivity.
  case (zeq b b0); intro.
  rewrite Int.negate_cmp. apply notbool_negb_1.
  apply negate_cmp_mismatch.
Qed.

Theorem negate_cmpu:
  forall c x y,
  cmpu (negate_comparison c) x y = notbool (cmpu c x y).
Proof.
  destruct x; destruct y; simpl; auto.
  rewrite Int.negate_cmpu. apply notbool_negb_1.
  case (Int.eq i Int.zero). apply negate_cmp_mismatch. reflexivity.
  case (Int.eq i0 Int.zero). apply negate_cmp_mismatch. reflexivity.
  case (zeq b b0); intro.
  rewrite Int.negate_cmpu. apply notbool_negb_1.
  apply negate_cmp_mismatch.
Qed.

Lemma swap_cmp_mismatch:
  forall c, cmp_mismatch (swap_comparison c) = cmp_mismatch c.
Proof.
  destruct c; reflexivity.
Qed.
  
Theorem swap_cmp:
  forall c x y,
  cmp (swap_comparison c) x y = cmp c y x.
Proof.
  destruct x; destruct y; simpl; auto.
  rewrite Int.swap_cmp. auto.
  case (Int.eq i Int.zero). apply swap_cmp_mismatch. auto.
  case (Int.eq i0 Int.zero). apply swap_cmp_mismatch. auto.
  case (zeq b b0); intro.
  subst b0. rewrite zeq_true. rewrite Int.swap_cmp. auto.
  rewrite zeq_false. apply swap_cmp_mismatch. auto.
Qed.

Theorem swap_cmpu:
  forall c x y,
  cmpu (swap_comparison c) x y = cmpu c y x.
Proof.
  destruct x; destruct y; simpl; auto.
  rewrite Int.swap_cmpu. auto.
  case (Int.eq i Int.zero). apply swap_cmp_mismatch. auto.
  case (Int.eq i0 Int.zero). apply swap_cmp_mismatch. auto.
  case (zeq b b0); intro.
  subst b0. rewrite zeq_true. rewrite Int.swap_cmpu. auto.
  rewrite zeq_false. apply swap_cmp_mismatch. auto.
Qed.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
Proof.
  destruct v1; destruct v2; simpl; auto.
  rewrite Float.cmp_ne_eq. rewrite notbool_negb_1. 
  apply notbool_idem2.
Qed.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
Proof.
  destruct v1; destruct v2; simpl; auto.
  rewrite Float.cmp_ne_eq. rewrite notbool_negb_1. auto. 
Qed.

Lemma or_of_bool:
  forall b1 b2, or (of_bool b1) (of_bool b2) = of_bool (b1 || b2).
Proof.
  destruct b1; destruct b2; reflexivity.
Qed.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; simpl; auto.
  rewrite or_of_bool. decEq. apply Float.cmp_le_lt_eq.
Qed.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; simpl; auto.
  rewrite or_of_bool. decEq. apply Float.cmp_ge_gt_eq.
Qed.

Definition is_bool (v: val) :=
  v = Vundef \/ v = Vtrue \/ v = Vfalse.

Lemma of_bool_is_bool:
  forall b, is_bool (of_bool b).
Proof.
  destruct b; unfold is_bool; simpl; tauto.
Qed.

Lemma undef_is_bool: is_bool Vundef.
Proof.
  unfold is_bool; tauto.
Qed.

Lemma cmp_mismatch_is_bool:
  forall c, is_bool (cmp_mismatch c).
Proof.
  destruct c; simpl; unfold is_bool; tauto.
Qed.

Lemma cmp_is_bool:
  forall c v1 v2, is_bool (cmp c v1 v2).
Proof.
  destruct v1; destruct v2; simpl; try apply undef_is_bool.
  apply of_bool_is_bool.
  case (Int.eq i Int.zero). apply cmp_mismatch_is_bool. apply undef_is_bool.
  case (Int.eq i0 Int.zero). apply cmp_mismatch_is_bool. apply undef_is_bool.
  case (zeq b b0); intro. apply of_bool_is_bool. apply cmp_mismatch_is_bool.
Qed.

Lemma cmpu_is_bool:
  forall c v1 v2, is_bool (cmpu c v1 v2).
Proof.
  destruct v1; destruct v2; simpl; try apply undef_is_bool.
  apply of_bool_is_bool.
  case (Int.eq i Int.zero). apply cmp_mismatch_is_bool. apply undef_is_bool.
  case (Int.eq i0 Int.zero). apply cmp_mismatch_is_bool. apply undef_is_bool.
  case (zeq b b0); intro. apply of_bool_is_bool. apply cmp_mismatch_is_bool.
Qed.

Lemma cmpf_is_bool:
  forall c v1 v2, is_bool (cmpf c v1 v2).
Proof.
  destruct v1; destruct v2; simpl;
  apply undef_is_bool || apply of_bool_is_bool.
Qed.

Lemma notbool_is_bool:
  forall v, is_bool (notbool v).
Proof.
  destruct v; simpl.
  apply undef_is_bool. apply of_bool_is_bool. 
  apply undef_is_bool. unfold is_bool; tauto.
Qed.

Lemma notbool_xor:
  forall v, is_bool v -> v = xor (notbool v) Vone.
Proof.
  intros. elim H; intro.  
  subst v. reflexivity.
  elim H0; intro; subst v; reflexivity.
Qed.

Lemma rolm_lt_zero:
  forall v, rolm v Int.one Int.one = cmp Clt v (Vint Int.zero).
Proof.
  intros. destruct v; simpl; auto.
  transitivity (Vint (Int.shru i (Int.repr (Z_of_nat Int.wordsize - 1)))).
  decEq. symmetry. rewrite Int.shru_rolm. auto. auto. 
  rewrite Int.shru_lt_zero. destruct (Int.lt i Int.zero); auto. 
Qed.

Lemma rolm_ge_zero:
  forall v,
  xor (rolm v Int.one Int.one) (Vint Int.one) = cmp Cge v (Vint Int.zero).
Proof.
  intros. rewrite rolm_lt_zero. destruct v; simpl; auto.
  destruct (Int.lt i Int.zero); auto.
Qed.

(** The ``is less defined'' relation between values. 
    A value is less defined than itself, and [Vundef] is
    less defined than any value. *)

Inductive lessdef: val -> val -> Prop :=
  | lessdef_refl: forall v, lessdef v v
  | lessdef_undef: forall v, lessdef Vundef v.

Inductive lessdef_list: list val -> list val -> Prop :=
  | lessdef_list_nil:
      lessdef_list nil nil
  | lessdef_list_cons:
      forall v1 v2 vl1 vl2,
      lessdef v1 v2 -> lessdef_list vl1 vl2 ->
      lessdef_list (v1 :: vl1) (v2 :: vl2).

Hint Resolve lessdef_refl lessdef_undef lessdef_list_nil lessdef_list_cons.

Lemma lessdef_list_inv:
  forall vl1 vl2, lessdef_list vl1 vl2 -> vl1 = vl2 \/ In Vundef vl1.
Proof.
  induction 1; simpl.
  tauto.
  inv H. destruct IHlessdef_list. 
  left; congruence. tauto. tauto.
Qed.

Lemma load_result_lessdef:
  forall chunk v1 v2,
  lessdef v1 v2 -> lessdef (load_result chunk v1) (load_result chunk v2).
Proof.
  intros. inv H. auto. destruct chunk; simpl; auto.
Qed.

Lemma zero_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (zero_ext n v1) (zero_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma sign_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (sign_ext n v1) (sign_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma singleoffloat_lessdef:
  forall v1 v2, lessdef v1 v2 -> lessdef (singleoffloat v1) (singleoffloat v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

End Val.

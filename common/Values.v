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

(** * Operations over values *)

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

Module Val.

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

Definition maketotal (ov: option val) : val :=
  match ov with Some v => v | None => Vundef end.

Definition intoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vint (Float.intoffloat f)
  | _ => None
  end.

Definition intuoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vint (Float.intuoffloat f)
  | _ => None
  end.

Definition floatofint (v: val) : option val :=
  match v with
  | Vint n => Some (Vfloat (Float.floatofint n))
  | _ => None
  end.

Definition floatofintu (v: val) : option val :=
  match v with
  | Vint n => Some (Vfloat (Float.floatofintu n))
  | _ => None
  end.

Definition floatofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vfloat (Float.from_words n1 n2)
  | _, _ => Vundef
  end.

Definition negint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition notint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.not n)
  | _ => Vundef
  end.

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Definition boolval (v: val) : val :=
  match v with
  | Vint n => of_bool (negb (Int.eq n Int.zero))
  | Vptr b ofs => Vtrue
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

Definition divs (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint(Int.divs n1 n2))
  | _, _ => None
  end.

Definition mods (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint(Int.mods n1 n2))
  | _, _ => None
  end.

Definition divu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some(Vint(Int.divu n1 n2))
  | _, _ => None
  end.

Definition modu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some(Vint(Int.modu n1 n2))
  | _, _ => None
  end.

Definition add_carry (v1 v2 cin: val): val :=
  match v1, v2, cin with
  | Vint n1, Vint n2, Vint c => Vint(Int.add_carry n1 n2 c)
  | _, _, _ => Vundef
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

Definition shrx (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 31)
     then Some(Vint(Int.shrx n1 n2))
     else None
  | _, _ => None
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

Section COMPARISONS.

Variable valid_ptr: block -> Z -> bool.

Definition cmp_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Int.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmp_different_blocks (c: comparison): option bool :=
  match c with
  | Ceq => Some false
  | Cne => Some true
  | _   => None
  end.

Definition cmpu_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      Some (Int.cmpu c n1 n2)
  | Vint n1, Vptr b2 ofs2 =>
      if Int.eq n1 Int.zero then cmp_different_blocks c else None
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if valid_ptr b1 (Int.unsigned ofs1) && valid_ptr b2 (Int.unsigned ofs2) then
        if zeq b1 b2
        then Some (Int.cmpu c ofs1 ofs2)
        else cmp_different_blocks c
      else None
  | Vptr b1 ofs1, Vint n2 =>
      if Int.eq n2 Int.zero then cmp_different_blocks c else None
  | _, _ => None
  end.

Definition cmpf_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Some (Float.cmp c f1 f2)
  | _, _ => None
  end.

Definition of_optbool (ob: option bool): val :=
  match ob with Some true => Vtrue | Some false => Vfalse | None => Vundef end.

Definition cmp (c: comparison) (v1 v2: val): val :=
  of_optbool (cmp_bool c v1 v2).

Definition cmpu (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpu_bool c v1 v2).

Definition cmpf (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpf_bool c v1 v2).

End COMPARISONS.

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
  | (Mfloat64 | Mfloat64al32), Vfloat f => Vfloat f
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

Theorem notbool_negb_3:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto.
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

Theorem notbool_idem4:
  forall ob, notbool (notbool (of_optbool ob)) = of_optbool ob.
Proof.
  destruct ob; auto. destruct b; auto.
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
  forall x y z,
  mods x y = Some z -> exists v, divs x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int.eq i0 Int.zero
        || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H.
  exists (Vint (Int.divs i i0)); split; auto. 
  simpl. rewrite Int.mods_divs. auto.
Qed.

Theorem modu_divu:
  forall x y z,
  modu x y = Some z -> exists v, divu x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int.eq i0 Int.zero) as []_eqn; inv H. 
  exists (Vint (Int.divu i i0)); split; auto. 
  simpl. rewrite Int.modu_divu. auto.
  generalize (Int.eq_spec i0 Int.zero). rewrite Heqb; auto. 
Qed.

Theorem divs_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn -> Int.ltu logn (Int.repr 31) = true ->
  divs x (Vint n) = Some y ->
  shrx x (Vint logn) = Some y.
Proof.
  intros; destruct x; simpl in H1; inv H1.
  destruct (Int.eq n Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq n Int.mone); inv H3.
  simpl. rewrite H0. decEq. decEq. symmetry. apply Int.divs_pow2. auto.
Qed.

Theorem divu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  divu x (Vint n) = Some y ->
  shru x (Vint logn) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int.eq n Int.zero); inv H2. 
  simpl. 
  rewrite (Int.is_power2_range _ _ H).
  decEq. symmetry. apply Int.divu_pow2. auto.
Qed.

Theorem modu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  modu x (Vint n) = Some y ->
  and x (Vint (Int.sub n Int.one)) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int.eq n Int.zero); inv H2. 
  simpl. decEq. symmetry. eapply Int.modu_and; eauto.
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

Theorem not_xor: forall x, notint x = xor x (Vint Int.mone).
Proof.
  destruct x; simpl; auto. 
Qed.

Theorem shl_mul: forall x y, mul x (shl Vone y) = shl x y.
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
  forall x y z,
  shrx x y = Some z ->
  add (shr x y) (shr_carry x y) = z.
Proof.
  intros. destruct x; destruct y; simpl in H; inv H. 
  destruct (Int.ltu i0 (Int.repr 31)) as []_eqn; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true). 
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega. 
  simpl. rewrite H0. simpl. decEq. rewrite Int.shrx_carry; auto.
Qed.

Theorem shrx_shr:
  forall x y z,
  shrx x y = Some z ->
  exists p, exists q,
    x = Vint p /\ y = Vint q /\
    z = shr (if Int.lt p Int.zero then add x (Vint (Int.sub (Int.shl Int.one q) Int.one)) else x) (Vint q).
Proof.
  intros. destruct x; destruct y; simpl in H; inv H. 
  destruct (Int.ltu i0 (Int.repr 31)) as []_eqn; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true). 
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega. 
  exists i; exists i0; intuition. 
  rewrite Int.shrx_shr; auto. destruct (Int.lt i Int.zero); simpl; rewrite H0; auto.
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

Theorem negate_cmp_bool:
  forall c x y, cmp_bool (negate_comparison c) x y = option_map negb (cmp_bool c x y).
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int.negate_cmp. auto.
Qed.

Theorem negate_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmpu_bool valid_ptr c x y).
Proof.
  assert (forall c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c)).
  destruct c; auto. 
  destruct x; destruct y; simpl; auto.
  rewrite Int.negate_cmpu. auto.
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i0 Int.zero); auto.
  destruct (valid_ptr b (Int.unsigned i) && valid_ptr b0 (Int.unsigned i0)); auto.
  destruct (zeq b b0); auto. rewrite Int.negate_cmpu. auto.
Qed.

Lemma not_of_optbool:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto. 
Qed.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
Proof.
  intros. unfold cmp. rewrite negate_cmp_bool. apply not_of_optbool.
Qed.

Theorem negate_cmpu:
  forall valid_ptr c x y,
  cmpu valid_ptr (negate_comparison c) x y = notbool (cmpu valid_ptr c x y).
Proof.
  intros. unfold cmpu. rewrite negate_cmpu_bool. apply not_of_optbool.
Qed.

Theorem swap_cmp_bool:
  forall c x y,
  cmp_bool (swap_comparison c) x y = cmp_bool c y x.
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int.swap_cmp. auto.
Qed.

Theorem swap_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (swap_comparison c) x y = cmpu_bool valid_ptr c y x.
Proof.
  assert (forall c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c).
    destruct c; auto.
  destruct x; destruct y; simpl; auto.
  rewrite Int.swap_cmpu. auto.
  case (Int.eq i Int.zero); auto.
  case (Int.eq i0 Int.zero); auto.
  destruct (valid_ptr b (Int.unsigned i)); destruct (valid_ptr b0 (Int.unsigned i0)); auto.
  simpl. destruct (zeq b b0); subst. 
  rewrite zeq_true. rewrite Int.swap_cmpu. auto.
  rewrite zeq_false; auto.
Qed.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_le_lt_eq.
  destruct (Float.cmp Clt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ge_gt_eq.
  destruct (Float.cmp Cgt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Lemma zero_ext_and:
  forall n v, 
  0 < n < Z_of_nat Int.wordsize ->
  Val.zero_ext n v = Val.and v (Vint (Int.repr (two_p n - 1))).
Proof.
  intros. destruct v; simpl; auto. decEq. apply Int.zero_ext_and; auto.
Qed.

Lemma rolm_lt_zero:
  forall v, rolm v Int.one Int.one = cmp Clt v (Vint Int.zero).
Proof.
  intros. unfold cmp, cmp_bool; destruct v; simpl; auto.
  transitivity (Vint (Int.shru i (Int.repr (Z_of_nat Int.wordsize - 1)))).
  decEq. symmetry. rewrite Int.shru_rolm. auto. auto. 
  rewrite Int.shru_lt_zero. destruct (Int.lt i Int.zero); auto. 
Qed.

Lemma rolm_ge_zero:
  forall v,
  xor (rolm v Int.one Int.one) (Vint Int.one) = cmp Cge v (Vint Int.zero).
Proof.
  intros. rewrite rolm_lt_zero. destruct v; simpl; auto.
  unfold cmp; simpl. destruct (Int.lt i Int.zero); auto.
Qed.

(** The ``is less defined'' relation between values. 
    A value is less defined than itself, and [Vundef] is
    less defined than any value. *)

Inductive lessdef: val -> val -> Prop :=
  | lessdef_refl: forall v, lessdef v v
  | lessdef_undef: forall v, lessdef Vundef v.

Lemma lessdef_trans:
  forall v1 v2 v3, lessdef v1 v2 -> lessdef v2 v3 -> lessdef v1 v3.
Proof.
  intros. inv H. auto. constructor.
Qed.

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

(** Compatibility of operations with the [lessdef] relation. *)

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

Lemma add_lessdef:
  forall v1 v1' v2 v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (add v1 v2) (add v1' v2').
Proof.
  intros. inv H. inv H0. auto. destruct v1'; simpl; auto. simpl; auto.
Qed.

Lemma cmpu_bool_lessdef:
  forall valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (forall b ofs, valid_ptr b ofs = true -> valid_ptr' b ofs = true) ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  cmpu_bool valid_ptr c v1 v2 = Some b ->
  cmpu_bool valid_ptr' c v1' v2' = Some b.
Proof.
  intros. 
  destruct v1; simpl in H2; try discriminate;
  destruct v2; simpl in H2; try discriminate;
  inv H0; inv H1; simpl; auto.
  destruct (valid_ptr b0 (Int.unsigned i)) as []_eqn; try discriminate.
  destruct (valid_ptr b1 (Int.unsigned i0)) as []_eqn; try discriminate.
  rewrite (H _ _ Heqb2). rewrite (H _ _ Heqb0). auto.
Qed.

Lemma of_optbool_lessdef:
  forall ob ob',
  (forall b, ob = Some b -> ob' = Some b) ->
  lessdef (of_optbool ob) (of_optbool ob').
Proof.
  intros. destruct ob; simpl; auto. rewrite (H b); auto. 
Qed.

End Val.

(** * Values and memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
*)

Definition meminj : Type := block -> option (block * Z).

(** A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection.  Moreover, [Vundef] values
  inject into any other value. *)

Inductive val_inject (mi: meminj): val -> val -> Prop :=
  | val_inject_int:
      forall i, val_inject mi (Vint i) (Vint i)
  | val_inject_float:
      forall f, val_inject mi (Vfloat f) (Vfloat f)
  | val_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta,
      mi b1 = Some (b2, delta) ->
      ofs2 = Int.add ofs1 (Int.repr delta) ->
      val_inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_undef: forall v,
      val_inject mi Vundef v.

Hint Resolve val_inject_int val_inject_float val_inject_ptr 
             val_inject_undef.

Inductive val_list_inject (mi: meminj): list val -> list val-> Prop:= 
  | val_nil_inject :
      val_list_inject mi nil nil
  | val_cons_inject : forall v v' vl vl' , 
      val_inject mi v v' -> val_list_inject mi vl vl'->
      val_list_inject mi (v :: vl) (v' :: vl').  

Hint Resolve val_nil_inject val_cons_inject.

Lemma val_load_result_inject:
  forall f chunk v1 v2,
  val_inject f v1 v2 ->
  val_inject f (Val.load_result chunk v1) (Val.load_result chunk v2).
Proof.
  intros. inv H; destruct chunk; simpl; econstructor; eauto.
Qed.

(** Monotone evolution of a memory injection. *)

Definition inject_incr (f1 f2: meminj) : Prop :=
  forall b b' delta, f1 b = Some(b', delta) -> f2 b = Some(b', delta).

Lemma inject_incr_refl :
   forall f , inject_incr f f .
Proof. unfold inject_incr. auto. Qed.

Lemma inject_incr_trans :
  forall f1 f2 f3, 
  inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 .
Proof .
  unfold inject_incr; intros. eauto. 
Qed.

Lemma val_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  val_inject f1 v v' ->
  val_inject f2 v v'.
Proof.
  intros. inv H0; eauto.
Qed.

Lemma val_list_inject_incr:
  forall f1 f2 vl vl' ,
  inject_incr f1 f2 -> val_list_inject f1 vl vl' ->
  val_list_inject f2 vl vl'.
Proof.
  induction vl; intros; inv H0. auto.
  constructor. eapply val_inject_incr; eauto. auto.
Qed.

Hint Resolve inject_incr_refl val_inject_incr val_list_inject_incr.

Lemma val_inject_lessdef:
  forall v1 v2, Val.lessdef v1 v2 <-> val_inject (fun b => Some(b, 0)) v1 v2.
Proof.
  intros; split; intros.
  inv H; auto. destruct v2; econstructor; eauto. rewrite Int.add_zero; auto. 
  inv H; auto. inv H0. rewrite Int.add_zero; auto.
Qed.

Lemma val_list_inject_lessdef:
  forall vl1 vl2, Val.lessdef_list vl1 vl2 <-> val_list_inject (fun b => Some(b, 0)) vl1 vl2.
Proof.
  intros; split.
  induction 1; constructor; auto. apply val_inject_lessdef; auto.
  induction 1; constructor; auto. apply val_inject_lessdef; auto.
Qed.

(** The identity injection gives rise to the "less defined than" relation. *)

Definition inject_id : meminj := fun b => Some(b, 0).

Lemma val_inject_id:
  forall v1 v2,
  val_inject inject_id v1 v2 <-> Val.lessdef v1 v2.
Proof.
  intros; split; intros.
  inv H. constructor. constructor.
  unfold inject_id in H0. inv H0. rewrite Int.add_zero. constructor.
  constructor.
  inv H. destruct v2; econstructor. unfold inject_id; reflexivity. rewrite Int.add_zero; auto.
  constructor.
Qed.

(** Composing two memory injections *)

Definition compose_meminj (f f': meminj) : meminj :=
  fun b =>
    match f b with
    | None => None
    | Some(b', delta) =>
        match f' b' with
        | None => None
        | Some(b'', delta') => Some(b'', delta + delta')
        end
    end.

Lemma val_inject_compose:
  forall f f' v1 v2 v3,
  val_inject f v1 v2 -> val_inject f' v2 v3 ->
  val_inject (compose_meminj f f') v1 v3.
Proof.
  intros. inv H; auto; inv H0; auto. econstructor.
  unfold compose_meminj; rewrite H1; rewrite H3; eauto. 
  rewrite Int.add_assoc. decEq. unfold Int.add. apply Int.eqm_samerepr. auto with ints.
Qed. 


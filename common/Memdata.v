(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** In-memory representation of values. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

(** * Properties of memory chunks *)

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 8
  | Mfloat64al32 => 8
  end.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros. destruct chunk; simpl; omega.
Qed.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  nat_of_Z(size_chunk chunk).

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z_of_nat (size_chunk_nat chunk).
Proof.
  intros. destruct chunk; reflexivity.
Qed.

Lemma size_chunk_nat_pos:
  forall chunk, exists n, size_chunk_nat chunk = S n.
Proof.
  intros. 
  generalize (size_chunk_pos chunk). rewrite size_chunk_conv. 
  destruct (size_chunk_nat chunk).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following 
  [align_chunk] function.  Some target architectures
  (e.g. PowerPC and x86) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC, ARM and x86. *)

Definition align_chunk (chunk: memory_chunk) : Z := 
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 8
  | Mfloat64al32 => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; omega.
Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try apply Zdivide_refl; exists 2; auto. 
Qed.

Lemma align_le_divides:
  forall chunk1 chunk2,
  align_chunk chunk1 <= align_chunk chunk2 -> (align_chunk chunk1 | align_chunk chunk2).
Proof.
  intros. destruct chunk1; destruct chunk2; simpl in *;
  solve [ omegaContradiction
        | apply Zdivide_refl
        | exists 2; reflexivity
        | exists 4; reflexivity
        | exists 8; reflexivity ].
Qed.

(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque pointer;
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Undef: memval
  | Byte: byte -> memval
  | Pointer: block -> int -> nat -> memval.

(** * Encoding and decoding integers *)

(** We define functions to convert between integers and lists of bytes
  of a given length *)

Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Byte.repr x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
  end.

Parameter big_endian: bool.

Definition rev_if_be (l: list byte) : list byte :=
  if big_endian then List.rev l else l.

Definition encode_int (sz: nat) (x: Z) : list byte :=
  rev_if_be (bytes_of_int sz x).

Definition decode_int (b: list byte) : Z :=
  int_of_bytes (rev_if_be b).

(** Length properties *)

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

Lemma rev_if_be_length:
  forall l, length (rev_if_be l) = length l.
Proof.
  intros; unfold rev_if_be; destruct big_endian.
  apply List.rev_length.
  auto.
Qed.

Lemma encode_int_length:
  forall sz x, length(encode_int sz x) = sz.
Proof.
  intros. unfold encode_int. rewrite rev_if_be_length. apply length_bytes_of_int.
Qed.

(** Decoding after encoding *)

Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z_of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
Opaque Byte.wordsize.
  rewrite inj_S. simpl.
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  rewrite Zmod_recombine. rewrite IHn. rewrite Zplus_comm. 
  change (Byte.unsigned (Byte.repr x)) with (Byte.Z_mod_modulus x). 
  rewrite Byte.Z_mod_modulus_eq. reflexivity. 
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.

Lemma rev_if_be_involutive:
  forall l, rev_if_be (rev_if_be l) = l.
Proof.
  intros; unfold rev_if_be; destruct big_endian. 
  apply List.rev_involutive. 
  auto.
Qed.

Lemma decode_encode_int:
  forall n x, decode_int (encode_int n x) = x mod (two_p (Z_of_nat n * 8)).
Proof.
  unfold decode_int, encode_int; intros. rewrite rev_if_be_involutive. 
  apply int_of_bytes_of_int.
Qed.

Lemma decode_encode_int_1:
  forall x, Int.repr (decode_int (encode_int 1 (Int.unsigned x))) = Int.zero_ext 8 x.
Proof.
  intros. rewrite decode_encode_int. 
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  decEq. symmetry. apply Int.zero_ext_mod. compute. intuition congruence. 
Qed.

Lemma decode_encode_int_2:
  forall x, Int.repr (decode_int (encode_int 2 (Int.unsigned x))) = Int.zero_ext 16 x.
Proof.
  intros. rewrite decode_encode_int. 
  rewrite <- (Int.repr_unsigned (Int.zero_ext 16 x)).
  decEq. symmetry. apply Int.zero_ext_mod. compute; intuition congruence.
Qed.

Lemma decode_encode_int_4:
  forall x, Int.repr (decode_int (encode_int 4 (Int.unsigned x))) = x.
Proof.
  intros. rewrite decode_encode_int. transitivity (Int.repr (Int.unsigned x)).
  decEq. apply Zmod_small. apply Int.unsigned_range. apply Int.repr_unsigned.
Qed.

Lemma decode_encode_int_8:
  forall x, Int64.repr (decode_int (encode_int 8 (Int64.unsigned x))) = x.
Proof.
  intros. rewrite decode_encode_int. transitivity (Int64.repr (Int64.unsigned x)).
  decEq. apply Zmod_small. apply Int64.unsigned_range. apply Int64.repr_unsigned.
Qed.

(** A length-[n] encoding depends only on the low [8*n] bits of the integer. *)

Lemma bytes_of_int_mod:
  forall n x y,
  Int.eqmod (two_p (Z_of_nat n * 8)) x y ->
  bytes_of_int n x = bytes_of_int n y.
Proof.
  induction n.
  intros; simpl; auto.
  intros until y.
  rewrite inj_S. 
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  intro EQM.
  simpl; decEq. 
  apply Byte.eqm_samerepr. red. 
  eapply Int.eqmod_divides; eauto. apply Zdivide_factor_l.
  apply IHn.
  destruct EQM as [k EQ]. exists k. rewrite EQ. 
  rewrite <- Z_div_plus_full_l. decEq. change (two_p 8) with 256. ring. omega.
Qed.

Lemma encode_int_8_mod:
  forall x y,
  Int.eqmod (two_p 8) x y ->
  encode_int 1%nat x = encode_int 1%nat y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

Lemma encode_int_16_mod:
  forall x y,
  Int.eqmod (two_p 16) x y ->
  encode_int 2%nat x = encode_int 2%nat y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

(** * Encoding and decoding values *)

Definition inj_bytes (bl: list byte) : list memval :=
  List.map Byte bl.

Fixpoint proj_bytes (vl: list memval) : option (list byte) :=
  match vl with
  | nil => Some nil
  | Byte b :: vl' =>
      match proj_bytes vl' with None => None | Some bl => Some(b :: bl) end
  | _ => None
  end.

Remark length_inj_bytes:
  forall bl, length (inj_bytes bl) = length bl.
Proof.
  intros. apply List.map_length. 
Qed.

Remark proj_inj_bytes:
  forall bl, proj_bytes (inj_bytes bl) = Some bl.
Proof.
  induction bl; simpl. auto. rewrite IHbl. auto.
Qed.

Lemma inj_proj_bytes:
  forall cl bl, proj_bytes cl = Some bl -> cl = inj_bytes bl.
Proof.
  induction cl; simpl; intros. 
  inv H; auto.
  destruct a; try congruence. destruct (proj_bytes cl); inv H.
  simpl. decEq. auto.
Qed.

Fixpoint inj_pointer (n: nat) (b: block) (ofs: int) {struct n}: list memval :=
  match n with
  | O => nil
  | S m => Pointer b ofs m :: inj_pointer m b ofs
  end.

Fixpoint check_pointer (n: nat) (b: block) (ofs: int) (vl: list memval) 
                       {struct n} : bool :=
  match n, vl with
  | O, nil => true
  | S m, Pointer b' ofs' m' :: vl' =>
      eq_block b b' && Int.eq_dec ofs ofs' && beq_nat m m' && check_pointer m b ofs vl'
  | _, _ => false
  end.

Definition proj_pointer (vl: list memval) : val :=
  match vl with
  | Pointer b ofs n :: vl' =>
      if check_pointer 4%nat b ofs vl then Vptr b ofs else Vundef
  | _ => Vundef
  end.

Definition encode_val (chunk: memory_chunk) (v: val) : list memval :=
  match v, chunk with
  | Vint n, (Mint8signed | Mint8unsigned) => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Vint n, (Mint16signed | Mint16unsigned) => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Vint n, Mint32 => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Vptr b ofs, Mint32 => inj_pointer 4%nat b ofs
  | Vlong n, Mint64 => inj_bytes (encode_int 8%nat (Int64.unsigned n))
  | Vfloat n, Mfloat32 => inj_bytes (encode_int 4%nat (Int.unsigned (Float.bits_of_single n)))
  | Vfloat n, (Mfloat64 | Mfloat64al32) => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.bits_of_double n)))
  | _, _ => list_repeat (size_chunk_nat chunk) Undef
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : val :=
  match proj_bytes vl with
  | Some bl =>
      match chunk with
      | Mint8signed => Vint(Int.sign_ext 8 (Int.repr (decode_int bl)))
      | Mint8unsigned => Vint(Int.zero_ext 8 (Int.repr (decode_int bl)))
      | Mint16signed => Vint(Int.sign_ext 16 (Int.repr (decode_int bl)))
      | Mint16unsigned => Vint(Int.zero_ext 16 (Int.repr (decode_int bl)))
      | Mint32 => Vint(Int.repr(decode_int bl))
      | Mint64 => Vlong(Int64.repr(decode_int bl))
      | Mfloat32 => Vfloat(Float.single_of_bits (Int.repr (decode_int bl)))
      | Mfloat64 | Mfloat64al32 => Vfloat(Float.double_of_bits (Int64.repr (decode_int bl)))
      end
  | None =>
      match chunk with
      | Mint32 => proj_pointer vl
      | _ => Vundef
      end
  end.

Lemma encode_val_length:
  forall chunk v, length(encode_val chunk v) = size_chunk_nat chunk.
Proof.
  intros. destruct v; simpl; destruct chunk; 
  solve [ reflexivity
        | apply length_list_repeat
        | rewrite length_inj_bytes; apply encode_int_length ].
Qed.

Lemma check_inj_pointer:
  forall b ofs n, check_pointer n b ofs (inj_pointer n b ofs) = true.
Proof.
  induction n; simpl. auto. 
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true.  
  rewrite <- beq_nat_refl. simpl; auto.
Qed.

Definition decode_encode_val (v1: val) (chunk1 chunk2: memory_chunk) (v2: val) : Prop :=
  match v1, chunk1, chunk2 with
  | Vundef, _, _ => v2 = Vundef
  | Vint n, Mint8signed, Mint8signed => v2 = Vint(Int.sign_ext 8 n)
  | Vint n, Mint8unsigned, Mint8signed => v2 = Vint(Int.sign_ext 8 n)
  | Vint n, Mint8signed, Mint8unsigned => v2 = Vint(Int.zero_ext 8 n)
  | Vint n, Mint8unsigned, Mint8unsigned => v2 = Vint(Int.zero_ext 8 n)
  | Vint n, Mint16signed, Mint16signed => v2 = Vint(Int.sign_ext 16 n)
  | Vint n, Mint16unsigned, Mint16signed => v2 = Vint(Int.sign_ext 16 n)
  | Vint n, Mint16signed, Mint16unsigned => v2 = Vint(Int.zero_ext 16 n)
  | Vint n, Mint16unsigned, Mint16unsigned => v2 = Vint(Int.zero_ext 16 n)
  | Vint n, Mint32, Mint32 => v2 = Vint n
  | Vint n, Mint32, Mfloat32 => v2 = Vfloat(Float.single_of_bits n)
  | Vint n, (Mint64 | Mfloat32 | Mfloat64 | Mfloat64al32), _ => v2 = Vundef
  | Vint n, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vptr b ofs, Mint32, Mint32 => v2 = Vptr b ofs
  | Vptr b ofs, _, _ => v2 = Vundef
  | Vlong n, Mint64, Mint64 => v2 = Vlong n
  | Vlong n, Mint64, (Mfloat64 | Mfloat64al32) => v2 = Vfloat(Float.double_of_bits n)
  | Vlong n, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mfloat32|Mfloat64|Mfloat64al32), _ => v2 = Vundef
  | Vlong n, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vfloat f, Mfloat32, Mfloat32 => v2 = Vfloat(Float.singleoffloat f)
  | Vfloat f, Mfloat32, Mint32 => v2 = Vint(Float.bits_of_single f)
  | Vfloat f, (Mfloat64 | Mfloat64al32), (Mfloat64 | Mfloat64al32) => v2 = Vfloat f
  | Vfloat f, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mint64), _ => v2 = Vundef
  | Vfloat f, (Mfloat64 | Mfloat64al32), Mint64 => v2 = Vlong(Float.bits_of_double f)
  | Vfloat f, _, _ => True   (* nothing interesting to say about v2 *)
  end.

Remark decode_val_undef:
  forall bl chunk, decode_val chunk (Undef :: bl) = Vundef.
Proof.
  intros. unfold decode_val. simpl. destruct chunk; auto.
Qed.

Lemma decode_encode_val_general:
  forall v chunk1 chunk2,
  decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)).
Proof.
Opaque inj_pointer.
  intros.
  destruct v; destruct chunk1; simpl; try (apply decode_val_undef);
  destruct chunk2; unfold decode_val; auto; try (rewrite proj_inj_bytes).
  rewrite decode_encode_int_1. decEq. apply Int.sign_ext_zero_ext. omega.
  rewrite decode_encode_int_1. decEq. apply Int.zero_ext_idem. omega.
  rewrite decode_encode_int_1. decEq. apply Int.sign_ext_zero_ext. omega.
  rewrite decode_encode_int_1. decEq. apply Int.zero_ext_idem. omega.
  rewrite decode_encode_int_2. decEq. apply Int.sign_ext_zero_ext. omega.
  rewrite decode_encode_int_2. decEq. apply Int.zero_ext_idem. omega.
  rewrite decode_encode_int_2. decEq. apply Int.sign_ext_zero_ext. omega.
  rewrite decode_encode_int_2. decEq. apply Int.zero_ext_idem. omega.
  rewrite decode_encode_int_4. auto.
  rewrite decode_encode_int_4. auto.
  rewrite decode_encode_int_8. auto.
  rewrite decode_encode_int_8. auto.
  rewrite decode_encode_int_8. auto.
  rewrite decode_encode_int_4. auto.
  rewrite decode_encode_int_4. decEq. apply Float.single_of_bits_of_single.
  rewrite decode_encode_int_8. auto.
  rewrite decode_encode_int_8. decEq. apply Float.double_of_bits_of_double.
  rewrite decode_encode_int_8. decEq. apply Float.double_of_bits_of_double.
  rewrite decode_encode_int_8. auto.
  rewrite decode_encode_int_8. decEq. apply Float.double_of_bits_of_double.
  rewrite decode_encode_int_8. decEq. apply Float.double_of_bits_of_double.
  change (proj_bytes (inj_pointer 4 b i)) with (@None (list byte)). simpl. 
  unfold proj_pointer. generalize (check_inj_pointer b i 4%nat).
Transparent inj_pointer. 
  simpl. intros EQ; rewrite EQ; auto.
Qed.

Lemma decode_encode_val_similar:
  forall v1 chunk1 chunk2 v2,
  type_of_chunk chunk1 = type_of_chunk chunk2 ->
  size_chunk chunk1 = size_chunk chunk2 ->
  decode_encode_val v1 chunk1 chunk2 v2 ->
  v2 = Val.load_result chunk2 v1.
Proof.
  intros until v2; intros TY SZ DE. 
  destruct chunk1; destruct chunk2; simpl in TY; try discriminate; simpl in SZ; try omegaContradiction;
  destruct v1; auto.
Qed.

Lemma decode_val_type:
  forall chunk cl,
  Val.has_type (decode_val chunk cl) (type_of_chunk chunk).
Proof.
  intros. unfold decode_val. 
  destruct (proj_bytes cl). 
  destruct chunk; simpl; auto. apply Float.single_of_bits_is_single.
  destruct chunk; simpl; auto.
  unfold proj_pointer. destruct cl; try (exact I).
  destruct m; try (exact I).
  destruct (check_pointer 4%nat b i (Pointer b i n :: cl));
  exact I.
Qed.

Lemma encode_val_int8_signed_unsigned:
  forall v, encode_val Mint8signed v = encode_val Mint8unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.

Lemma encode_val_int16_signed_unsigned:
  forall v, encode_val Mint16signed v = encode_val Mint16unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.

Lemma encode_val_int8_zero_ext:
  forall n, encode_val Mint8unsigned (Vint (Int.zero_ext 8 n)) = encode_val Mint8unsigned (Vint n).
Proof.
  intros; unfold encode_val. decEq. apply encode_int_8_mod. apply Int.eqmod_zero_ext. 
  compute; intuition congruence.
Qed.

Lemma encode_val_int8_sign_ext:
  forall n, encode_val Mint8signed (Vint (Int.sign_ext 8 n)) = encode_val Mint8signed (Vint n).
Proof.
  intros; unfold encode_val. decEq. apply encode_int_8_mod. apply Int.eqmod_sign_ext'. compute; auto.
Qed.

Lemma encode_val_int16_zero_ext:
  forall n, encode_val Mint16unsigned (Vint (Int.zero_ext 16 n)) = encode_val Mint16unsigned (Vint n).
Proof.
  intros; unfold encode_val. decEq. apply encode_int_16_mod. apply Int.eqmod_zero_ext. compute; intuition congruence.
Qed.

Lemma encode_val_int16_sign_ext:
  forall n, encode_val Mint16signed (Vint (Int.sign_ext 16 n)) = encode_val Mint16signed (Vint n).
Proof.
  intros; unfold encode_val. decEq. apply encode_int_16_mod. apply Int.eqmod_sign_ext'. compute; auto.
Qed.

Lemma decode_val_cast:
  forall chunk l,
  let v := decode_val chunk l in
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | Mfloat32 => v = Val.singleoffloat v
  | _ => True
  end.
Proof.
  unfold decode_val; intros; destruct chunk; auto; destruct (proj_bytes l); auto.
  unfold Val.sign_ext. rewrite Int.sign_ext_idem; auto. omega.
  unfold Val.zero_ext. rewrite Int.zero_ext_idem; auto. omega. 
  unfold Val.sign_ext. rewrite Int.sign_ext_idem; auto. omega.
  unfold Val.zero_ext. rewrite Int.zero_ext_idem; auto. omega.
  simpl. rewrite Float.singleoffloat_of_bits. auto.
Qed.

(** Pointers cannot be forged. *)

Definition memval_valid_first (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n = 3%nat
  | _ => True
  end.

Definition memval_valid_cont (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n <> 3%nat
  | _ => True
  end.

Inductive encoding_shape: list memval -> Prop :=
  | encoding_shape_intro: forall mv1 mvl,
      memval_valid_first mv1 ->
      (forall mv, In mv mvl -> memval_valid_cont mv) ->
      encoding_shape (mv1 :: mvl).

Lemma encode_val_shape:
  forall chunk v, encoding_shape (encode_val chunk v).
Proof.
  intros. 
  destruct (size_chunk_nat_pos chunk) as [sz1 EQ].
  assert (A: encoding_shape (list_repeat (size_chunk_nat chunk) Undef)).
    rewrite EQ; simpl; constructor. exact I. 
    intros. replace mv with Undef. exact I. symmetry; eapply in_list_repeat; eauto.
  assert (B: forall bl, length bl = size_chunk_nat chunk ->
          encoding_shape (inj_bytes bl)).
    intros. destruct bl; simpl in *. congruence. 
    constructor. exact I. unfold inj_bytes. intros.
    exploit list_in_map_inv; eauto. intros [x [C D]]. subst mv. exact I.
  destruct v; auto; destruct chunk; simpl; auto; try (apply B; apply encode_int_length).
  constructor. red. auto.
  simpl; intros. intuition; subst mv; red; simpl; congruence.
Qed.

Lemma check_pointer_inv:
  forall b ofs n mv,
  check_pointer n b ofs mv = true -> mv = inj_pointer n b ofs.
Proof.
  induction n; destruct mv; simpl. 
  auto.
  congruence.
  congruence.
  destruct m; try congruence. intro. 
  destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0). 
  destruct (andb_prop _ _ H2).
  decEq. decEq. symmetry; eapply proj_sumbool_true; eauto.
  symmetry; eapply proj_sumbool_true; eauto.
  symmetry; apply beq_nat_true; auto.
  auto.
Qed.

Inductive decoding_shape: list memval -> Prop :=
  | decoding_shape_intro: forall mv1 mvl,
      memval_valid_first mv1 -> mv1 <> Undef ->
      (forall mv, In mv mvl -> memval_valid_cont mv /\ mv <> Undef) ->
      decoding_shape (mv1 :: mvl).

Lemma decode_val_shape:
  forall chunk mvl,
  List.length mvl = size_chunk_nat chunk ->
  decode_val chunk mvl = Vundef \/ decoding_shape mvl.
Proof.
  intros. destruct (size_chunk_nat_pos chunk) as [sz EQ]. 
  unfold decode_val. 
  caseEq (proj_bytes mvl).
  intros bl PROJ. right. exploit inj_proj_bytes; eauto. intros. subst mvl.
  destruct bl; simpl in H. congruence. simpl. constructor. 
  red; auto. congruence.
  unfold inj_bytes; intros. exploit list_in_map_inv; eauto. intros [b [A B]]. 
  subst mv. split. red; auto. congruence.
  intros. destruct chunk; auto. unfold proj_pointer.
  destruct mvl; auto. destruct m; auto. 
  caseEq (check_pointer 4%nat b i (Pointer b i n :: mvl)); auto.
  intros. right. exploit check_pointer_inv; eauto. simpl; intros; inv H2.
  constructor. red. auto. congruence. 
  simpl; intros. intuition; subst mv; simpl; congruence.
Qed.

Lemma encode_val_pointer_inv:
  forall chunk v b ofs n mvl,
  encode_val chunk v = Pointer b ofs n :: mvl ->
  chunk = Mint32 /\ v = Vptr b ofs /\ mvl = inj_pointer 3%nat b ofs.
Proof.
  intros until mvl.
  assert (A: list_repeat (size_chunk_nat chunk) Undef = Pointer b ofs n :: mvl ->
            chunk = Mint32 /\ v = Vptr b ofs /\ mvl = inj_pointer 3 b ofs).
    intros. destruct (size_chunk_nat_pos chunk) as [sz SZ]. rewrite SZ in H. simpl in H. discriminate.
  assert (B: forall bl, length bl <> 0%nat -> inj_bytes bl = Pointer b ofs n :: mvl ->
            chunk = Mint32 /\ v = Vptr b ofs /\ mvl = inj_pointer 3 b ofs).
    intros. destruct bl; simpl in *; congruence.
  unfold encode_val; destruct v; destruct chunk;
  (apply A; assumption) ||
  (apply B; rewrite encode_int_length; congruence) || idtac.
  simpl. intros EQ; inv EQ; auto. 
Qed.

Lemma decode_val_pointer_inv:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ mvl = inj_pointer 4%nat b ofs.
Proof.
  intros until ofs; unfold decode_val.
  destruct (proj_bytes mvl). 
  destruct chunk; congruence.
  destruct chunk; try congruence.
  unfold proj_pointer. destruct mvl. congruence. destruct m; try congruence.
  case_eq (check_pointer 4%nat b0 i (Pointer b0 i n :: mvl)); intros.
  inv H0. split; auto. apply check_pointer_inv; auto. 
  congruence.
Qed.

Inductive pointer_encoding_shape: list memval -> Prop :=
  | pointer_encoding_shape_intro: forall mv1 mvl,
      ~memval_valid_cont mv1 ->
      (forall mv, In mv mvl -> ~memval_valid_first mv) ->
      pointer_encoding_shape (mv1 :: mvl).

Lemma encode_pointer_shape:
  forall b ofs, pointer_encoding_shape (encode_val Mint32 (Vptr b ofs)).
Proof.
  intros. simpl. constructor.
  unfold memval_valid_cont. red; intro. elim H. auto. 
  unfold memval_valid_first. simpl; intros; intuition; subst mv; congruence.
Qed.

Lemma decode_pointer_shape:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ pointer_encoding_shape mvl.
Proof.
  intros. exploit decode_val_pointer_inv; eauto. intros [A B].
  split; auto. subst mvl. apply encode_pointer_shape. 
Qed.

(** * Compatibility with memory injections *)

(** Relating two memory values according to a memory injection. *)

Inductive memval_inject (f: meminj): memval -> memval -> Prop :=
  | memval_inject_byte:
      forall n, memval_inject f (Byte n) (Byte n)
  | memval_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta n,
      f b1 = Some (b2, delta) ->
      ofs2 = Int.add ofs1 (Int.repr delta) ->
      memval_inject f (Pointer b1 ofs1 n) (Pointer b2 ofs2 n)
  | memval_inject_undef:
      forall mv, memval_inject f Undef mv.

Lemma memval_inject_incr:
  forall f f' v1 v2, memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2.
Proof.
  intros. inv H; econstructor. rewrite (H0 _ _ _ H1). reflexivity. auto.
Qed.

(** [decode_val], applied to lists of memory values that are pairwise
  related by [memval_inject], returns values that are related by [val_inject]. *)

Lemma proj_bytes_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall bl,
  proj_bytes vl = Some bl ->
  proj_bytes vl' = Some bl.
Proof.
  induction 1; simpl. congruence.
  inv H; try congruence.
  destruct (proj_bytes al); intros. 
  inv H. rewrite (IHlist_forall2 l); auto. 
  congruence.
Qed.

Lemma check_pointer_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n b ofs b' delta,
  check_pointer n b ofs vl = true ->
  f b = Some(b', delta) ->
  check_pointer n b' (Int.add ofs (Int.repr delta)) vl' = true.
Proof.
  induction 1; intros; destruct n; simpl in *; auto. 
  inv H; auto.
  destruct (andb_prop _ _ H1). destruct (andb_prop _ _ H). 
  destruct (andb_prop _ _ H5). 
  assert (n = n0) by (apply beq_nat_true; auto).
  assert (b = b0) by (eapply proj_sumbool_true; eauto). 
  assert (ofs = ofs1) by (eapply proj_sumbool_true; eauto).
  subst. rewrite H3 in H2; inv H2. 
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true. 
  rewrite <- beq_nat_refl. simpl. eauto. 
  congruence.
Qed.

Lemma proj_pointer_inject:
  forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (proj_pointer vl1) (proj_pointer vl2).
Proof.
  intros. unfold proj_pointer.
  inversion H; subst. auto. inversion H0; subst; auto.
  case_eq (check_pointer 4%nat b0 ofs1 (Pointer b0 ofs1 n :: al)); intros.
  exploit check_pointer_inject. eexact H. eauto. eauto. 
  intro. rewrite H4. econstructor; eauto. 
  constructor.
Qed.

Lemma proj_bytes_not_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  proj_bytes vl = None -> proj_bytes vl' <> None -> In Undef vl.
Proof.
  induction 1; simpl; intros.
  congruence.
  inv H; try congruence. 
  right. apply IHlist_forall2.
  destruct (proj_bytes al); congruence.
  destruct (proj_bytes bl); congruence.
  auto.
Qed.

Lemma check_pointer_undef:
  forall n b ofs vl,
  In Undef vl -> check_pointer n b ofs vl = false.
Proof.
  induction n; intros; simpl. 
  destruct vl. elim H. auto.
  destruct vl. auto.
  destruct m; auto. simpl in H; destruct H. congruence.
  rewrite IHn; auto. apply andb_false_r. 
Qed.

Lemma proj_pointer_undef:
  forall vl, In Undef vl -> proj_pointer vl = Vundef.
Proof.
  intros; unfold proj_pointer.
  destruct vl; auto. destruct m; auto. 
  rewrite check_pointer_undef. auto. auto.
Qed.

Theorem decode_val_inject:
  forall f vl1 vl2 chunk,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (decode_val chunk vl1) (decode_val chunk vl2).
Proof.
  intros. unfold decode_val. 
  case_eq (proj_bytes vl1); intros. 
  exploit proj_bytes_inject; eauto. intros. rewrite H1. 
  destruct chunk; constructor.
  destruct chunk; auto.
  case_eq (proj_bytes vl2); intros.
  rewrite proj_pointer_undef. auto. eapply proj_bytes_not_inject; eauto. congruence.
  apply proj_pointer_inject; auto.
Qed.

(** Symmetrically, [encode_val], applied to values related by [val_inject],
  returns lists of memory values that are pairwise
  related by [memval_inject]. *)

Lemma inj_bytes_inject:
  forall f bl, list_forall2 (memval_inject f) (inj_bytes bl) (inj_bytes bl).
Proof.
  induction bl; constructor; auto. constructor.
Qed.

Lemma repeat_Undef_inject_any:
  forall f vl,
  list_forall2 (memval_inject f) (list_repeat (length vl) Undef) vl.
Proof.
  induction vl; simpl; constructor; auto. constructor. 
Qed.  

Lemma repeat_Undef_inject_self:
  forall f n,
  list_forall2 (memval_inject f) (list_repeat n Undef) (list_repeat n Undef).
Proof.
  induction n; simpl; constructor; auto. constructor.
Qed.  

Theorem encode_val_inject:
  forall f v1 v2 chunk,
  val_inject f v1 v2 ->
  list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2).
Proof.
  intros. inv H; simpl.
  destruct chunk; apply inj_bytes_inject || apply repeat_Undef_inject_self.
  destruct chunk; apply inj_bytes_inject || apply repeat_Undef_inject_self.
  destruct chunk; apply inj_bytes_inject || apply repeat_Undef_inject_self.
  destruct chunk; try (apply repeat_Undef_inject_self). 
  repeat econstructor; eauto. 
  replace (size_chunk_nat chunk) with (length (encode_val chunk v2)).
  apply repeat_Undef_inject_any. apply encode_val_length. 
Qed.

Definition memval_lessdef: memval -> memval -> Prop := memval_inject inject_id.

Lemma memval_lessdef_refl:
  forall mv, memval_lessdef mv mv.
Proof.
  red. destruct mv; econstructor.
  unfold inject_id; reflexivity. rewrite Int.add_zero; auto. 
Qed.

(** [memval_inject] and compositions *)

Lemma memval_inject_compose:
  forall f f' v1 v2 v3,
  memval_inject f v1 v2 -> memval_inject f' v2 v3 ->
  memval_inject (compose_meminj f f') v1 v3.
Proof.
  intros. inv H.
  inv H0. constructor.
  inv H0. econstructor. 
  unfold compose_meminj; rewrite H1; rewrite H5; eauto. 
  rewrite Int.add_assoc. decEq. unfold Int.add. apply Int.eqm_samerepr. auto with ints.
  constructor.
Qed. 

(** * Breaking 64-bit memory accesses into two 32-bit accesses *)

Lemma int_of_bytes_append:
  forall l2 l1, 
  int_of_bytes (l1 ++ l2) = int_of_bytes l1 + int_of_bytes l2 * two_p (Z_of_nat (length l1) * 8).
Proof.
  induction l1; simpl int_of_bytes; intros.
  simpl. ring.
  simpl length. rewrite inj_S. 
  replace (Z.succ (Z.of_nat (length l1)) * 8) with (Z_of_nat (length l1) * 8 + 8) by omega.
  rewrite two_p_is_exp. change (two_p 8) with 256. rewrite IHl1. ring.
  omega. omega.
Qed.

Lemma int_of_bytes_range:
  forall l, 0 <= int_of_bytes l < two_p (Z_of_nat (length l) * 8).
Proof.
  induction l; intros. 
  simpl. omega.
  simpl length. rewrite inj_S. 
  replace (Z.succ (Z.of_nat (length l)) * 8) with (Z.of_nat (length l) * 8 + 8) by omega.
  rewrite two_p_is_exp. change (two_p 8) with 256. 
  simpl int_of_bytes. generalize (Byte.unsigned_range a). 
  change Byte.modulus with 256. omega. 
  omega. omega. 
Qed.

Lemma length_proj_bytes:
  forall l b, proj_bytes l = Some b -> length b = length l.
Proof.
  induction l; simpl; intros. 
  inv H; auto.
  destruct a; try discriminate. 
  destruct (proj_bytes l) eqn:E; inv H. 
  simpl. f_equal. auto.
Qed.

Lemma proj_bytes_append:
  forall l2 l1,
  proj_bytes (l1 ++ l2) =
  match proj_bytes l1, proj_bytes l2 with
  | Some b1, Some b2 => Some (b1 ++ b2)
  | _, _ => None
  end.
Proof.
  induction l1; simpl.
  destruct (proj_bytes l2); auto.
  destruct a; auto. rewrite IHl1. 
  destruct (proj_bytes l1); auto. destruct (proj_bytes l2); auto. 
Qed.

Lemma decode_val_int64:
  forall l1 l2,
  length l1 = 4%nat -> length l2 = 4%nat ->
  decode_val Mint64 (l1 ++ l2) =
  Val.longofwords (decode_val Mint32 (if big_endian then l1 else l2))
                  (decode_val Mint32 (if big_endian then l2 else l1)).
Proof.
  intros. unfold decode_val.
  assert (PP: forall vl, match proj_pointer vl with Vundef => True | Vptr _ _ => True | _ => False end).
    intros. unfold proj_pointer. destruct vl; auto. destruct m; auto. 
    destruct (check_pointer 4 b i (Pointer b i n :: vl)); auto. 
  assert (PP1: forall vl v2, Val.longofwords (proj_pointer vl) v2 = Vundef).
    intros. generalize (PP vl). destruct (proj_pointer vl); reflexivity || contradiction.
  assert (PP2: forall v1 vl, Val.longofwords v1 (proj_pointer vl) = Vundef).
    intros. destruct v1; simpl; auto. 
    generalize (PP vl). destruct (proj_pointer vl); reflexivity || contradiction.
  rewrite proj_bytes_append. 
  destruct (proj_bytes l1) as [b1|] eqn:B1; destruct (proj_bytes l2) as [b2|] eqn:B2.
- exploit length_proj_bytes. eexact B1. rewrite H; intro L1.
  exploit length_proj_bytes. eexact B2. rewrite H0; intro L2.
  assert (UR: forall l, length l = 4%nat -> Int.unsigned (Int.repr (int_of_bytes l)) = int_of_bytes l).
    intros. apply Int.unsigned_repr. 
    generalize (int_of_bytes_range l). rewrite H1. 
    change (two_p (Z.of_nat 4 * 8)) with (Int.max_unsigned + 1). 
    omega.
  unfold decode_int, rev_if_be. destruct big_endian; rewrite B1; rewrite B2.
  + rewrite <- (rev_length b1) in L1. 
    rewrite <- (rev_length b2) in L2.
    rewrite rev_app_distr.
    set (b1' := rev b1) in *; set (b2' := rev b2) in *.
    unfold Val.longofwords. f_equal. rewrite Int64.ofwords_add. f_equal.
    rewrite !UR by auto. rewrite int_of_bytes_append. 
    rewrite L2. change (Z.of_nat 4 * 8) with 32. ring.
  + unfold Val.longofwords. f_equal. rewrite Int64.ofwords_add. f_equal.
    rewrite !UR by auto. rewrite int_of_bytes_append. 
    rewrite L1. change (Z.of_nat 4 * 8) with 32. ring.
- destruct big_endian; rewrite B1; rewrite B2; auto.
- destruct big_endian; rewrite B1; rewrite B2; auto.
- destruct big_endian; rewrite B1; rewrite B2; auto.
Qed.

Lemma bytes_of_int_append:
  forall n2 x2 n1 x1,
  0 <= x1 < two_p (Z_of_nat n1 * 8) ->
  bytes_of_int (n1 + n2) (x1 + x2 * two_p (Z_of_nat n1 * 8)) =
  bytes_of_int n1 x1 ++ bytes_of_int n2 x2.
Proof.
  induction n1; intros.
- simpl in *. f_equal. omega. 
- assert (E: two_p (Z.of_nat (S n1) * 8) = two_p (Z.of_nat n1 * 8) * 256).
  {
    rewrite inj_S. change 256 with (two_p 8). rewrite <- two_p_is_exp. 
    f_equal. omega. omega. omega. 
  }
  rewrite E in *. simpl. f_equal.
  apply Byte.eqm_samerepr. exists (x2 * two_p (Z.of_nat n1 * 8)). 
  change Byte.modulus with 256. ring.
  rewrite Zmult_assoc. rewrite Z_div_plus. apply IHn1.
  apply Zdiv_interval_1. omega. apply two_p_gt_ZERO; omega. omega. 
  assumption. omega.
Qed.

Lemma bytes_of_int64:
  forall i,
  bytes_of_int 8 (Int64.unsigned i) =
  bytes_of_int 4 (Int.unsigned (Int64.loword i)) ++ bytes_of_int 4 (Int.unsigned (Int64.hiword i)).
Proof.
  intros. transitivity (bytes_of_int (4 + 4) (Int64.unsigned (Int64.ofwords (Int64.hiword i) (Int64.loword i)))).
  f_equal. f_equal. rewrite Int64.ofwords_recompose. auto.
  rewrite Int64.ofwords_add'.
  change 32 with (Z_of_nat 4 * 8). 
  rewrite Zplus_comm. apply bytes_of_int_append. apply Int.unsigned_range. 
Qed.

Lemma encode_val_int64:
  forall v,
  encode_val Mint64 v =
     encode_val Mint32 (if big_endian then Val.hiword v else Val.loword v)
  ++ encode_val Mint32 (if big_endian then Val.loword v else Val.hiword v).
Proof.
  intros. destruct v; destruct big_endian eqn:BI; try reflexivity;
  unfold Val.loword, Val.hiword, encode_val.
  unfold inj_bytes. rewrite <- map_app. f_equal. 
  unfold encode_int, rev_if_be. rewrite BI. rewrite <- rev_app_distr. f_equal.
  apply bytes_of_int64. 
  unfold inj_bytes. rewrite <- map_app. f_equal. 
  unfold encode_int, rev_if_be. rewrite BI.
  apply bytes_of_int64.
Qed.

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
  | Mfloat32 => 4
  | Mfloat64 => 8
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
  (e.g. the PowerPC) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC and ARM. *)

Definition align_chunk (chunk: memory_chunk) : Z := 
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | _ => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; omega.
Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try apply Zdivide_refl. exists 2; auto. 
Qed.

Lemma align_chunk_compat:
  forall chunk1 chunk2,
  size_chunk chunk1 = size_chunk chunk2 -> align_chunk chunk1 = align_chunk chunk2.
Proof.
  intros chunk1 chunk2. 
  destruct chunk1; destruct chunk2; simpl; congruence.
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
  according to a given memory chunk. *)

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

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

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
  rewrite Zmod_recombine. rewrite IHn. rewrite Zplus_comm. reflexivity. 
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.

Lemma int_of_bytes_of_int_2:
  forall n x,
  (n = 1 \/ n = 2)%nat ->
  Int.repr (int_of_bytes (bytes_of_int n (Int.unsigned x))) = Int.zero_ext (Z_of_nat n * 8) x.
Proof.
  intros. rewrite int_of_bytes_of_int. 
  rewrite <- (Int.repr_unsigned (Int.zero_ext (Z_of_nat n * 8) x)). 
  decEq. symmetry. apply Int.zero_ext_mod.
  destruct H; subst n; compute; auto.
Qed.

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

Parameter big_endian: bool.

Definition rev_if_be (l: list byte) : list byte :=
  if big_endian then List.rev l else l.

Lemma rev_if_be_involutive:
  forall l, rev_if_be (rev_if_be l) = l.
Proof.
  intros; unfold rev_if_be; destruct big_endian. 
  apply List.rev_involutive. 
  auto.
Qed.

Lemma rev_if_be_length:
  forall l, length (rev_if_be l) = length l.
Proof.
  intros; unfold rev_if_be; destruct big_endian.
  apply List.rev_length.
  auto.
Qed.

Definition encode_int (c: memory_chunk) (x: int) : list byte :=
  let n := Int.unsigned x in
  rev_if_be (match c with
  | Mint8signed | Mint8unsigned => bytes_of_int 1%nat n
  | Mint16signed | Mint16unsigned => bytes_of_int 2%nat n
  | Mint32 => bytes_of_int 4%nat n
  | Mfloat32 => bytes_of_int 4%nat 0
  | Mfloat64 => bytes_of_int 8%nat 0
  end).

Definition decode_int (c: memory_chunk) (b: list byte) : int :=
  let b' := rev_if_be b in
  match c with
  | Mint8signed => Int.sign_ext 8 (Int.repr (int_of_bytes b'))
  | Mint8unsigned => Int.zero_ext 8 (Int.repr (int_of_bytes b'))
  | Mint16signed => Int.sign_ext 16 (Int.repr (int_of_bytes b'))
  | Mint16unsigned => Int.zero_ext 16 (Int.repr (int_of_bytes b'))
  | Mint32 => Int.repr (int_of_bytes b')
  | Mfloat32 => Int.zero
  | Mfloat64 => Int.zero
  end.

Lemma encode_int_length:
  forall chunk n, length(encode_int chunk n) = size_chunk_nat chunk.
Proof.
  intros. unfold encode_int. rewrite rev_if_be_length.
  destruct chunk; rewrite length_bytes_of_int; reflexivity.
Qed.

Lemma decode_encode_int:
  forall c x,
  decode_int c (encode_int c x) =
  match c with
  | Mint8signed => Int.sign_ext 8 x
  | Mint8unsigned => Int.zero_ext 8 x
  | Mint16signed => Int.sign_ext 16 x
  | Mint16unsigned => Int.zero_ext 16 x
  | Mint32 => x
  | Mfloat32 => Int.zero
  | Mfloat64 => Int.zero
  end.
Proof.
  intros. unfold decode_int, encode_int; destruct c; auto;
  rewrite rev_if_be_involutive.
  rewrite int_of_bytes_of_int_2; auto.
  apply Int.sign_ext_zero_ext. compute; auto.
  rewrite int_of_bytes_of_int_2; auto.
  apply Int.zero_ext_idem. compute; auto.
  rewrite int_of_bytes_of_int_2; auto.
  apply Int.sign_ext_zero_ext. compute; auto.
  rewrite int_of_bytes_of_int_2; auto.
  apply Int.zero_ext_idem. compute; auto.
  rewrite int_of_bytes_of_int. 
  transitivity (Int.repr (Int.unsigned x)). 
  apply Int.eqm_samerepr. apply Int.eqm_sym. apply Int.eqmod_mod. apply two_p_gt_ZERO. omega. 
  apply Int.repr_unsigned.
Qed.

Lemma encode_int8_signed_unsigned: forall n,
  encode_int Mint8signed n = encode_int Mint8unsigned n.
Proof.
  intros; reflexivity.
Qed.

Remark encode_8_mod:
  forall x y,
  Int.eqmod (two_p 8) (Int.unsigned x) (Int.unsigned y) ->
  encode_int Mint8unsigned x = encode_int Mint8unsigned y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

Lemma encode_int8_zero_ext:
  forall x,
  encode_int Mint8unsigned (Int.zero_ext 8 x) = encode_int Mint8unsigned x.
Proof.
  intros. apply encode_8_mod. apply Int.eqmod_zero_ext. compute; auto.
Qed.

Lemma encode_int8_sign_ext:
  forall x,
  encode_int Mint8signed (Int.sign_ext 8 x) = encode_int Mint8signed x.
Proof.
  intros. repeat rewrite encode_int8_signed_unsigned. 
  apply encode_8_mod. eapply Int.eqmod_trans.
  apply Int.eqm_eqmod_two_p. compute; auto. 
  apply Int.eqm_sym. apply Int.eqm_signed_unsigned.
  apply Int.eqmod_sign_ext. compute; auto.
Qed.

Lemma encode_int16_signed_unsigned: forall n,
  encode_int Mint16signed n = encode_int Mint16unsigned n.
Proof.
  intros; reflexivity.
Qed.

Remark encode_16_mod:
  forall x y,
  Int.eqmod (two_p 16) (Int.unsigned x) (Int.unsigned y) ->
  encode_int Mint16unsigned x = encode_int Mint16unsigned y.
Proof.
  intros. unfold encode_int. decEq. apply bytes_of_int_mod. auto.
Qed.

Lemma encode_int16_zero_ext:
  forall x,
  encode_int Mint16unsigned (Int.zero_ext 16 x) = encode_int Mint16unsigned x.
Proof.
  intros. apply encode_16_mod. apply Int.eqmod_zero_ext. compute; auto.
Qed.

Lemma encode_int16_sign_ext:
  forall x,
  encode_int Mint16signed (Int.sign_ext 16 x) = encode_int Mint16signed x.
Proof.
  intros. repeat rewrite encode_int16_signed_unsigned. 
  apply encode_16_mod. eapply Int.eqmod_trans.
  apply Int.eqm_eqmod_two_p. compute; auto. 
  apply Int.eqm_sym. apply Int.eqm_signed_unsigned.
  apply Int.eqmod_sign_ext. compute; auto.
Qed.

Lemma decode_int8_zero_ext:
  forall l,
  Int.zero_ext 8 (decode_int Mint8unsigned l) = decode_int Mint8unsigned l.
Proof.
  intros; simpl. apply Int.zero_ext_idem. vm_compute; auto.
Qed.

Lemma decode_int8_sign_ext:
  forall l,
  Int.sign_ext 8 (decode_int Mint8signed l) = decode_int Mint8signed l.
Proof.
  intros; simpl. apply Int.sign_ext_idem. vm_compute; auto.
Qed.

Lemma decode_int16_zero_ext:
  forall l,
  Int.zero_ext 16 (decode_int Mint16unsigned l) = decode_int Mint16unsigned l.
Proof.
  intros; simpl. apply Int.zero_ext_idem. vm_compute; auto.
Qed.

Lemma decode_int16_sign_ext:
  forall l,
  Int.sign_ext 16 (decode_int Mint16signed l) = decode_int Mint16signed l.
Proof.
  intros; simpl. apply Int.sign_ext_idem. vm_compute; auto.
Qed.

Lemma decode_int8_signed_unsigned:
  forall l,
  decode_int Mint8signed l = Int.sign_ext 8 (decode_int Mint8unsigned l).
Proof.
  intros; simpl. rewrite Int.sign_ext_zero_ext; auto. vm_compute; auto.
Qed.

Lemma decode_int16_signed_unsigned:
  forall l,
  decode_int Mint16signed l = Int.sign_ext 16 (decode_int Mint16unsigned l).
Proof.
  intros; simpl. rewrite Int.sign_ext_zero_ext; auto. vm_compute; auto.
Qed.

(** * Encoding and decoding floats *)

Definition encode_float (c: memory_chunk) (f: float) : list byte :=
  rev_if_be (match c with
  | Mint8signed | Mint8unsigned => bytes_of_int 1%nat 0
  | Mint16signed | Mint16unsigned => bytes_of_int 2%nat 0
  | Mint32 => bytes_of_int 4%nat 0
  | Mfloat32 => bytes_of_int 4%nat (Int.unsigned (Float.bits_of_single f))
  | Mfloat64 => bytes_of_int 8%nat (Int64.unsigned (Float.bits_of_double f))
  end).

Definition decode_float (c: memory_chunk) (b: list byte) : float :=
  let b' := rev_if_be b in
  match c with
  | Mfloat32 => Float.single_of_bits (Int.repr (int_of_bytes b'))
  | Mfloat64 => Float.double_of_bits (Int64.repr (int_of_bytes b'))
  | _ => Float.zero
  end.

Lemma encode_float_length:
  forall chunk n, length(encode_float chunk n) = size_chunk_nat chunk.
Proof.
  unfold encode_float; intros. 
  rewrite rev_if_be_length. 
  destruct chunk; apply length_bytes_of_int. 
Qed.

Lemma decode_encode_float32: forall n,
  decode_float Mfloat32 (encode_float Mfloat32 n) = Float.singleoffloat n.
Proof.
  intros; unfold decode_float, encode_float. 
  rewrite rev_if_be_involutive. 
  rewrite int_of_bytes_of_int. rewrite <- Float.single_of_bits_of_single. 
  decEq. 
  transitivity (Int.repr (Int.unsigned (Float.bits_of_single n))). 
  apply Int.eqm_samerepr. apply Int.eqm_sym. apply Int.eqmod_mod. apply two_p_gt_ZERO. omega. 
  apply Int.repr_unsigned.
Qed.

Lemma decode_encode_float64: forall n,
  decode_float Mfloat64 (encode_float Mfloat64 n) = n.
Proof.
  intros; unfold decode_float, encode_float. 
  rewrite rev_if_be_involutive. 
  rewrite int_of_bytes_of_int.
  set (x := Float.bits_of_double n).
  transitivity (Float.double_of_bits(Int64.repr (Int64.unsigned x))).
  decEq. 
  apply Int64.eqm_samerepr. apply Int64.eqm_sym. apply Int64.eqmod_mod. apply two_p_gt_ZERO. omega. 
  rewrite Int64.repr_unsigned. apply Float.double_of_bits_of_double.
Qed.

Lemma encode_float8_signed_unsigned: forall n,
  encode_float Mint8signed n = encode_float Mint8unsigned n.
Proof.
  intros. reflexivity. 
Qed.

Lemma encode_float16_signed_unsigned: forall n,
  encode_float Mint16signed n = encode_float Mint16unsigned n.
Proof.
  intros. reflexivity.
Qed.

Lemma encode_float32_cast:
  forall f,
  encode_float Mfloat32 (Float.singleoffloat f) = encode_float Mfloat32 f.
Proof.
  intros; unfold encode_float. decEq. decEq. decEq. 
  apply Float.bits_of_singleoffloat.
Qed.

Lemma decode_float32_cast:
  forall l,
  Float.singleoffloat (decode_float Mfloat32 l) = decode_float Mfloat32 l.
Proof.
  intros; unfold decode_float. rewrite Float.singleoffloat_of_bits. auto.
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
      if check_pointer (size_chunk_nat Mint32) b ofs vl
      then Vptr b ofs
      else Vundef
  | _ => Vundef
  end.

Definition encode_val (chunk: memory_chunk) (v: val) : list memval :=
  match v, chunk with
  | Vptr b ofs, Mint32 => inj_pointer (size_chunk_nat Mint32) b ofs
  | Vint n, _ => inj_bytes (encode_int chunk n)
  | Vfloat f, _ => inj_bytes (encode_float chunk f)
  | _, _ => list_repeat (size_chunk_nat chunk) Undef
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : val :=
  match proj_bytes vl with
  | Some bl =>
      match chunk with
      | Mint8signed | Mint8unsigned
      | Mint16signed | Mint16unsigned | Mint32 =>
          Vint(decode_int chunk bl)
      | Mfloat32 | Mfloat64 =>
          Vfloat(decode_float chunk bl)
      end
  | None =>
      match chunk with
      | Mint32 => proj_pointer vl
      | _ => Vundef
      end
  end.

(*
Lemma inj_pointer_length:
  forall b ofs n, List.length(inj_pointer n b ofs) = n.
Proof.
  induction n; simpl; congruence.
Qed.
*)

Lemma encode_val_length:
  forall chunk v, length(encode_val chunk v) = size_chunk_nat chunk.
Proof.
  intros. destruct v; simpl. 
  apply length_list_repeat.
  rewrite length_inj_bytes. apply encode_int_length.
  rewrite length_inj_bytes. apply encode_float_length.
  destruct chunk; try (apply length_list_repeat). reflexivity.
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
  | Vint n, Mint32, Mfloat32 => v2 = Vfloat(decode_float Mfloat32 (encode_int Mint32 n))
  | Vint n, _, _ => True   (* nothing interesting to say about v2 *)
  | Vptr b ofs, Mint32, Mint32 => v2 = Vptr b ofs
  | Vptr b ofs, _, _ => v2 = Vundef
  | Vfloat f, Mfloat32, Mfloat32 => v2 = Vfloat(Float.singleoffloat f)
  | Vfloat f, Mfloat32, Mint32 => v2 = Vint(decode_int Mint32 (encode_float Mfloat32 f))
  | Vfloat f, Mfloat64, Mfloat64 => v2 = Vfloat f
  | Vfloat f, _, _ => True   (* nothing interesting to say about v2 *)
  end.

Lemma decode_encode_val_general:
  forall v chunk1 chunk2,
  decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)).
Proof.
  intros. destruct v.
(* Vundef *)
  simpl. destruct (size_chunk_nat_pos chunk1) as [psz EQ]. 
  rewrite EQ. simpl.
  unfold decode_val. simpl. destruct chunk2; auto.
(* Vint *)
  simpl.
  destruct chunk1; auto; destruct chunk2; auto; unfold decode_val;
  rewrite proj_inj_bytes.
  rewrite decode_encode_int. auto.
  rewrite encode_int8_signed_unsigned. rewrite decode_encode_int. auto.
  rewrite <- encode_int8_signed_unsigned.  rewrite decode_encode_int. auto.
  rewrite decode_encode_int. auto.
  rewrite decode_encode_int. auto.
  rewrite encode_int16_signed_unsigned. rewrite decode_encode_int. auto.
  rewrite <- encode_int16_signed_unsigned.  rewrite decode_encode_int. auto.
  rewrite decode_encode_int. auto.
  rewrite decode_encode_int. auto.
  reflexivity. 
(* Vfloat *)
  unfold decode_val, encode_val, decode_encode_val;
  destruct chunk1; auto; destruct chunk2; auto; unfold decode_val;
  rewrite proj_inj_bytes.
  auto.
  rewrite decode_encode_float32. auto.
  rewrite decode_encode_float64. auto.
(* Vptr *)
  unfold decode_val, encode_val, decode_encode_val;
  destruct chunk1; auto; destruct chunk2; auto.
  simpl. generalize (check_inj_pointer b i (size_chunk_nat Mint32)).
  simpl. intro. rewrite H. auto.
Qed.

Lemma decode_encode_val_similar:
  forall v1 chunk1 chunk2 v2,
  type_of_chunk chunk1 = type_of_chunk chunk2 ->
  size_chunk chunk1 = size_chunk chunk2 ->
  Val.has_type v1 (type_of_chunk chunk1) ->
  decode_encode_val v1 chunk1 chunk2 v2 ->
  v2 = Val.load_result chunk2 v1.
Proof.
  intros. 
  destruct v1.
  simpl in *. destruct chunk2; simpl; auto. 
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
Qed.

Lemma decode_val_type:
  forall chunk cl,
  Val.has_type (decode_val chunk cl) (type_of_chunk chunk).
Proof.
  intros. unfold decode_val. 
  destruct (proj_bytes cl). 
  destruct chunk; simpl; auto. 
  destruct chunk; simpl; auto.
  unfold proj_pointer. destruct cl; try (exact I).
  destruct m; try (exact I).
  destruct (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n :: cl));
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
  intros; unfold encode_val. rewrite encode_int8_zero_ext. auto.
Qed.

Lemma encode_val_int8_sign_ext:
  forall n, encode_val Mint8signed (Vint (Int.sign_ext 8 n)) = encode_val Mint8signed (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int8_sign_ext. auto.
Qed.

Lemma encode_val_int16_zero_ext:
  forall n, encode_val Mint16unsigned (Vint (Int.zero_ext 16 n)) = encode_val Mint16unsigned (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int16_zero_ext. auto.
Qed.

Lemma encode_val_int16_sign_ext:
  forall n, encode_val Mint16signed (Vint (Int.sign_ext 16 n)) = encode_val Mint16signed (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int16_sign_ext. auto.
Qed.

Lemma decode_val_int_inv:
  forall chunk cl n,
  decode_val chunk cl = Vint n ->
  type_of_chunk chunk = Tint /\
  exists bytes, proj_bytes cl = Some bytes /\ n = decode_int chunk bytes.
Proof.
  intros until n. unfold decode_val. destruct (proj_bytes cl). 
Opaque decode_int.
  destruct chunk; intro EQ; inv EQ; split; auto; exists l; auto. 
  destruct chunk; try congruence. unfold proj_pointer. 
  destruct cl; try congruence. destruct m; try congruence. 
  destruct (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n0 :: cl));
  congruence.
Qed.

Lemma decode_val_float_inv:
  forall chunk cl f,
  decode_val chunk cl = Vfloat f ->
  type_of_chunk chunk = Tfloat /\
  exists bytes, proj_bytes cl = Some bytes /\ f = decode_float chunk bytes.
Proof.
  intros until f. unfold decode_val. destruct (proj_bytes cl). 
  destruct chunk; intro EQ; inv EQ; split; auto; exists l; auto. 
  destruct chunk; try congruence. unfold proj_pointer. 
  destruct cl; try congruence. destruct m; try congruence.
  destruct (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n :: cl));
  congruence.
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
  unfold Val.sign_ext. decEq. symmetry. apply decode_int8_sign_ext.
  unfold Val.zero_ext. decEq. symmetry. apply decode_int8_zero_ext.
  unfold Val.sign_ext. decEq. symmetry. apply decode_int16_sign_ext.
  unfold Val.zero_ext. decEq. symmetry. apply decode_int16_zero_ext.
  unfold Val.singleoffloat. decEq. symmetry. apply decode_float32_cast. 
Qed.

(** Pointers cannot be forged. *)

Definition memval_valid_first (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n = pred (size_chunk_nat Mint32)
  | _ => True
  end.

Definition memval_valid_cont (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n <> pred (size_chunk_nat Mint32)
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
  assert (encoding_shape (list_repeat (size_chunk_nat chunk) Undef)).
    rewrite EQ; simpl; constructor. exact I. 
    intros. replace mv with Undef. exact I. symmetry; eapply in_list_repeat; eauto.
  assert (forall bl, length bl = size_chunk_nat chunk ->
          encoding_shape (inj_bytes bl)).
    intros. destruct bl; simpl in *. congruence. 
    constructor. exact I. unfold inj_bytes. intros.
    exploit list_in_map_inv; eauto. intros [x [A B]]. subst mv. exact I.
  destruct v; simpl. 
  auto.
  apply H0. apply encode_int_length. 
  apply H0. apply encode_float_length.
  destruct chunk; auto. 
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
  caseEq (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n :: mvl)); auto.
  intros. right. exploit check_pointer_inv; eauto. simpl; intros; inv H2.
  constructor. red. auto. congruence. 
  simpl; intros. intuition; subst mv; simpl; congruence.
Qed.

Lemma encode_val_pointer_inv:
  forall chunk v b ofs n mvl,
  encode_val chunk v = Pointer b ofs n :: mvl ->
  chunk = Mint32 /\ v = Vptr b ofs /\ mvl = inj_pointer (pred (size_chunk_nat Mint32)) b ofs.
Proof.
  intros until mvl. 
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  unfold encode_val. rewrite SZ. destruct v.
  simpl. congruence. 
  generalize (encode_int_length chunk i). destruct (encode_int chunk i); simpl; congruence.
  generalize (encode_float_length chunk f). destruct (encode_float chunk f); simpl; congruence.
  destruct chunk; try (simpl; congruence). 
  simpl. intuition congruence. 
Qed.

Lemma decode_val_pointer_inv:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ mvl = inj_pointer (size_chunk_nat Mint32) b ofs.
Proof.
  intros until ofs; unfold decode_val.
  destruct (proj_bytes mvl). 
  destruct chunk; congruence.
  destruct chunk; try congruence.
  unfold proj_pointer. destruct mvl. congruence. destruct m; try congruence.
  case_eq (check_pointer (size_chunk_nat Mint32) b0 i (Pointer b0 i n :: mvl)); intros.
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
  case_eq (check_pointer (size_chunk_nat Mint32) b0 ofs1 (Pointer b0 ofs1 n :: al)); intros.
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
  apply inj_bytes_inject.
  apply inj_bytes_inject.
  destruct chunk; try apply repeat_Undef_inject_self. 
  unfold inj_pointer; simpl; repeat econstructor; auto. 
  replace (size_chunk_nat chunk) with (length (encode_val chunk v2)).
  apply repeat_Undef_inject_any. apply encode_val_length. 
Qed.

(** The identity injection has interesting properties. *)

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

Lemma memval_inject_id:
  forall mv, memval_inject inject_id mv mv.
Proof.
  destruct mv; econstructor. unfold inject_id; reflexivity. rewrite Int.add_zero; auto. 
Qed.
 

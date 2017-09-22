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
Require Archi.
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
  | Many32 => 4
  | Many64 => 8
  end.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros. destruct chunk; simpl; omega.
Qed.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  nat_of_Z(size_chunk chunk).

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z.of_nat (size_chunk_nat chunk).
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

Lemma size_chunk_Mptr: size_chunk Mptr = if Archi.ptr64 then 8 else 4.
Proof.
  unfold Mptr; destruct Archi.ptr64; auto.
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
  | Mfloat64 => 4
  | Many32 => 4
  | Many64 => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; omega.
Qed.

Lemma align_chunk_Mptr: align_chunk Mptr = if Archi.ptr64 then 8 else 4.
Proof.
  unfold Mptr; destruct Archi.ptr64; auto.
Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try apply Z.divide_refl; exists 2; auto.
Qed.

Lemma align_le_divides:
  forall chunk1 chunk2,
  align_chunk chunk1 <= align_chunk chunk2 -> (align_chunk chunk1 | align_chunk chunk2).
Proof.
  intros. destruct chunk1; destruct chunk2; simpl in *;
  solve [ omegaContradiction
        | apply Z.divide_refl
        | exists 2; reflexivity
        | exists 4; reflexivity
        | exists 8; reflexivity ].
Qed.

Inductive quantity : Type := Q32 | Q64.

Definition quantity_eq (q1 q2: quantity) : {q1 = q2} + {q1 <> q2}.
Proof. decide equality. Defined.
Global Opaque quantity_eq.

Definition size_quantity_nat (q: quantity) :=
  match q with Q32 => 4%nat | Q64 => 8%nat end.

Lemma size_quantity_nat_pos:
  forall q, exists n, size_quantity_nat q = S n.
Proof.
  intros. destruct q; [exists 3%nat | exists 7%nat]; auto.
Qed.

(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque value;
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Undef: memval
  | Byte: byte -> memval
  | Fragment: val -> quantity -> nat -> memval.

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

Definition rev_if_be (l: list byte) : list byte :=
  if Archi.big_endian then List.rev l else l.

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
  intros; unfold rev_if_be; destruct Archi.big_endian.
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
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z.of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
Opaque Byte.wordsize.
  rewrite Nat2Z.inj_succ. simpl.
  replace (Z.succ (Z.of_nat n) * 8) with (Z.of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega.
  rewrite Zmod_recombine. rewrite IHn. rewrite Z.add_comm.
  change (Byte.unsigned (Byte.repr x)) with (Byte.Z_mod_modulus x).
  rewrite Byte.Z_mod_modulus_eq. reflexivity.
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.

Lemma rev_if_be_involutive:
  forall l, rev_if_be (rev_if_be l) = l.
Proof.
  intros; unfold rev_if_be; destruct Archi.big_endian.
  apply List.rev_involutive.
  auto.
Qed.

Lemma decode_encode_int:
  forall n x, decode_int (encode_int n x) = x mod (two_p (Z.of_nat n * 8)).
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
  Int.eqmod (two_p (Z.of_nat n * 8)) x y ->
  bytes_of_int n x = bytes_of_int n y.
Proof.
  induction n.
  intros; simpl; auto.
  intros until y.
  rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat n) * 8) with (Z.of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega.
  intro EQM.
  simpl; decEq.
  apply Byte.eqm_samerepr. red.
  eapply Int.eqmod_divides; eauto. apply Z.divide_factor_r.
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

Fixpoint inj_value_rec (n: nat) (v: val) (q: quantity) {struct n}: list memval :=
  match n with
  | O => nil
  | S m => Fragment v q m :: inj_value_rec m v q
  end.

Definition inj_value (q: quantity) (v: val): list memval :=
  inj_value_rec (size_quantity_nat q) v q.

Fixpoint check_value (n: nat) (v: val) (q: quantity) (vl: list memval)
                       {struct n} : bool :=
  match n, vl with
  | O, nil => true
  | S m, Fragment v' q' m' :: vl' =>
      Val.eq v v' && quantity_eq q q' && Nat.eqb m m' && check_value m v q vl'
  | _, _ => false
  end.

Definition proj_value (q: quantity) (vl: list memval) : val :=
  match vl with
  | Fragment v q' n :: vl' =>
      if check_value (size_quantity_nat q) v q vl then v else Vundef
  | _ => Vundef
  end.

Definition encode_val (chunk: memory_chunk) (v: val) : list memval :=
  match v, chunk with
  | Vint n, (Mint8signed | Mint8unsigned) => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Vint n, (Mint16signed | Mint16unsigned) => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Vint n, Mint32 => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Vptr b ofs, Mint32 => if Archi.ptr64 then list_repeat 4%nat Undef else inj_value Q32 v
  | Vlong n, Mint64 => inj_bytes (encode_int 8%nat (Int64.unsigned n))
  | Vptr b ofs, Mint64 => if Archi.ptr64 then inj_value Q64 v else list_repeat 8%nat Undef
  | Vsingle n, Mfloat32 => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n)))
  | Vfloat n, Mfloat64 => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n)))
  | _, Many32 => inj_value Q32 v
  | _, Many64 => inj_value Q64 v
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
      | Mfloat32 => Vsingle(Float32.of_bits (Int.repr (decode_int bl)))
      | Mfloat64 => Vfloat(Float.of_bits (Int64.repr (decode_int bl)))
      | Many32 => Vundef
      | Many64 => Vundef
      end
  | None =>
      match chunk with
      | Mint32 => if Archi.ptr64 then Vundef else Val.load_result chunk (proj_value Q32 vl)
      | Many32 => Val.load_result chunk (proj_value Q32 vl)
      | Mint64 => if Archi.ptr64 then Val.load_result chunk (proj_value Q64 vl) else Vundef
      | Many64 => Val.load_result chunk (proj_value Q64 vl)
      | _ => Vundef
      end
  end.

Ltac solve_encode_val_length :=
  match goal with
  | [ |- length (inj_bytes _) = _ ] => rewrite length_inj_bytes; solve_encode_val_length
  | [ |- length (encode_int _ _) = _ ] => apply encode_int_length
  | [ |- length (if ?x then _ else _) = _ ] => destruct x eqn:?; solve_encode_val_length
  | _ => reflexivity
  end.

Lemma encode_val_length:
  forall chunk v, length(encode_val chunk v) = size_chunk_nat chunk.
Proof.
  intros. destruct v; simpl; destruct chunk; solve_encode_val_length.
Qed.

Lemma check_inj_value:
  forall v q n, check_value n v q (inj_value_rec n v q) = true.
Proof.
  induction n; simpl. auto.
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true.
  rewrite <- beq_nat_refl. simpl; auto.
Qed.

Lemma proj_inj_value:
  forall q v, proj_value q (inj_value q v) = v.
Proof.
  intros. unfold proj_value, inj_value. destruct (size_quantity_nat_pos q) as [n EQ].
  rewrite EQ at 1. simpl. rewrite check_inj_value. auto.
Qed.

Remark in_inj_value:
  forall mv v q, In mv (inj_value q v) -> exists n, mv = Fragment v q n.
Proof.
Local Transparent inj_value.
  unfold inj_value; intros until q. generalize (size_quantity_nat q). induction n; simpl; intros.
  contradiction.
  destruct H. exists n; auto. eauto.
Qed.

Lemma proj_inj_value_mismatch:
  forall q1 q2 v, q1 <> q2 -> proj_value q1 (inj_value q2 v) = Vundef.
Proof.
  intros. unfold proj_value. destruct (inj_value q2 v) eqn:V. auto. destruct m; auto.
  destruct (in_inj_value (Fragment v0 q n) v q2) as [n' EQ].
  rewrite V; auto with coqlib. inv EQ.
  destruct (size_quantity_nat_pos q1) as [p EQ1]; rewrite EQ1; simpl.
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_false by congruence. auto.
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
  | Vint n, Many32, Many32 => v2 = Vint n
  | Vint n, Mint32, Mfloat32 => v2 = Vsingle(Float32.of_bits n)
  | Vint n, Many64, Many64 => v2 = Vint n
  | Vint n, (Mint64 | Mfloat32 | Mfloat64 | Many64), _ => v2 = Vundef
  | Vint n, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vptr b ofs, (Mint32 | Many32), (Mint32 | Many32) => v2 = if Archi.ptr64 then Vundef else Vptr b ofs
  | Vptr b ofs, Mint64, (Mint64 | Many64) => v2 = if Archi.ptr64 then Vptr b ofs else Vundef
  | Vptr b ofs, Many64, Many64 => v2 = Vptr b ofs
  | Vptr b ofs, Many64, Mint64 => v2 = if Archi.ptr64 then Vptr b ofs else Vundef
  | Vptr b ofs, _, _ => v2 = Vundef
  | Vlong n, Mint64, Mint64 => v2 = Vlong n
  | Vlong n, Mint64, Mfloat64 => v2 = Vfloat(Float.of_bits n)
  | Vlong n, Many64, Many64 => v2 = Vlong n
  | Vlong n, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mfloat32|Mfloat64|Many32), _ => v2 = Vundef
  | Vlong n, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vfloat f, Mfloat64, Mfloat64 => v2 = Vfloat f
  | Vfloat f, Mfloat64, Mint64 => v2 = Vlong(Float.to_bits f)
  | Vfloat f, Many64, Many64 => v2 = Vfloat f
  | Vfloat f, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mfloat32|Mint64|Many32), _ => v2 = Vundef
  | Vfloat f, _, _ => True   (* nothing interesting to say about v2 *)
  | Vsingle f, Mfloat32, Mfloat32 => v2 = Vsingle f
  | Vsingle f, Mfloat32, Mint32 => v2 = Vint(Float32.to_bits f)
  | Vsingle f, Many32, Many32 => v2 = Vsingle f
  | Vsingle f, Many64, Many64 => v2 = Vsingle f
  | Vsingle f, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mint64|Mfloat64|Many64), _ => v2 = Vundef
  | Vsingle f, _, _ => True (* nothing interesting to say about v2 *)
  end.

Remark decode_val_undef:
  forall bl chunk, decode_val chunk (Undef :: bl) = Vundef.
Proof.
  intros. unfold decode_val. simpl. destruct chunk, Archi.ptr64; auto.
Qed.

Remark proj_bytes_inj_value:
  forall q v, proj_bytes (inj_value q v) = None.
Proof.
  intros. destruct q; reflexivity.
Qed.

Ltac solve_decode_encode_val_general :=
  exact I || reflexivity ||
  match goal with
  | |- context [ if Archi.ptr64 then _ else _ ] => destruct Archi.ptr64 eqn:?
  | |- context [ proj_bytes (inj_bytes _) ] => rewrite proj_inj_bytes
  | |- context [ proj_bytes (inj_value _ _) ] => rewrite proj_bytes_inj_value
  | |- context [ proj_value _ (inj_value _ _) ] => rewrite ?proj_inj_value, ?proj_inj_value_mismatch by congruence
  | |- context [ Int.repr(decode_int (encode_int 1 (Int.unsigned _))) ] => rewrite decode_encode_int_1
  | |- context [ Int.repr(decode_int (encode_int 2 (Int.unsigned _))) ] => rewrite decode_encode_int_2
  | |- context [ Int.repr(decode_int (encode_int 4 (Int.unsigned _))) ] => rewrite decode_encode_int_4
  | |- context [ Int64.repr(decode_int (encode_int 8 (Int64.unsigned _))) ] => rewrite decode_encode_int_8
  | |- Vint (Int.sign_ext _ (Int.sign_ext _ _)) = Vint _ => f_equal; apply Int.sign_ext_idem; omega
  | |- Vint (Int.zero_ext _ (Int.zero_ext _ _)) = Vint _ => f_equal; apply Int.zero_ext_idem; omega
  | |- Vint (Int.sign_ext _ (Int.zero_ext _ _)) = Vint _ => f_equal; apply Int.sign_ext_zero_ext; omega
  end.

Lemma decode_encode_val_general:
  forall v chunk1 chunk2,
  decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)).
Proof.
Opaque inj_value.
  intros.
  destruct v; destruct chunk1 eqn:C1; try (apply decode_val_undef);
  destruct chunk2 eqn:C2; unfold decode_encode_val, decode_val, encode_val, Val.load_result;
  repeat solve_decode_encode_val_general.
- rewrite Float.of_to_bits; auto.
- rewrite Float32.of_to_bits; auto.
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
  destruct chunk; simpl; auto.
Local Opaque Val.load_result.
  destruct chunk; simpl;
  (exact I || apply Val.load_result_type || destruct Archi.ptr64; (exact I || apply Val.load_result_type)).
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
  | _ => True
  end.
Proof.
  unfold decode_val; intros; destruct chunk; auto; destruct (proj_bytes l); auto.
  unfold Val.sign_ext. rewrite Int.sign_ext_idem; auto. omega.
  unfold Val.zero_ext. rewrite Int.zero_ext_idem; auto. omega.
  unfold Val.sign_ext. rewrite Int.sign_ext_idem; auto. omega.
  unfold Val.zero_ext. rewrite Int.zero_ext_idem; auto. omega.
Qed.

(** Pointers cannot be forged. *)

Definition quantity_chunk (chunk: memory_chunk) :=
  match chunk with
  | Mint64 | Mfloat64 | Many64 => Q64
  | _ => Q32
  end.

Inductive shape_encoding (chunk: memory_chunk) (v: val): list memval -> Prop :=
  | shape_encoding_f: forall q i mvl,
      (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64) ->
      q = quantity_chunk chunk ->
      S i = size_quantity_nat q ->
      (forall mv, In mv mvl -> exists j, mv = Fragment v q j /\ S j <> size_quantity_nat q) ->
      shape_encoding chunk v (Fragment v q i :: mvl)
  | shape_encoding_b: forall b mvl,
      match v with Vint _ => True | Vlong _ => True | Vfloat _ => True | Vsingle _ => True | _ => False end ->
      (forall mv, In mv mvl -> exists b', mv = Byte b') ->
      shape_encoding chunk v (Byte b :: mvl)
  | shape_encoding_u: forall mvl,
      (forall mv, In mv mvl -> mv = Undef) ->
      shape_encoding chunk v (Undef :: mvl).

Lemma encode_val_shape: forall chunk v, shape_encoding chunk v (encode_val chunk v).
Proof.
  intros.
  destruct (size_chunk_nat_pos chunk) as [sz EQ].
  assert (A: forall mv q n,
             (n < size_quantity_nat q)%nat ->
             In mv (inj_value_rec n v q) ->
             exists j, mv = Fragment v q j /\ S j <> size_quantity_nat q).
  {
    induction n; simpl; intros. contradiction. destruct H0.
    exists n; split; auto. omega. apply IHn; auto. omega.
  }
  assert (B: forall q,
             q = quantity_chunk chunk ->
             (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64) ->
             shape_encoding chunk v (inj_value q v)).
  {
Local Transparent inj_value.
    intros. unfold inj_value. destruct (size_quantity_nat_pos q) as [sz' EQ'].
    rewrite EQ'. simpl. constructor; auto.
    intros; eapply A; eauto. omega.
  }
  assert (C: forall bl,
             match v with Vint _ => True | Vlong _ => True | Vfloat _ => True | Vsingle _ => True | _ => False end ->
             length (inj_bytes bl) = size_chunk_nat chunk ->
             shape_encoding chunk v (inj_bytes bl)).
  {
    intros. destruct bl as [|b1 bl]. simpl in H0; congruence. simpl.
    constructor; auto. unfold inj_bytes; intros. exploit list_in_map_inv; eauto.
    intros (b & P & Q); exists b; auto.
  }
  assert (D: shape_encoding chunk v (list_repeat (size_chunk_nat chunk) Undef)).
  {
    intros. rewrite EQ; simpl; constructor; auto.
    intros. eapply in_list_repeat; eauto.
  }
  generalize (encode_val_length chunk v). intros LEN.
  unfold encode_val; unfold encode_val in LEN;
  destruct v; destruct chunk;
  (apply B || apply C || apply D || (destruct Archi.ptr64; (apply B || apply D)));
  auto.
Qed.

Inductive shape_decoding (chunk: memory_chunk): list memval -> val -> Prop :=
  | shape_decoding_f: forall v q i mvl,
      (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64) ->
      q = quantity_chunk chunk ->
      S i = size_quantity_nat q ->
      (forall mv, In mv mvl -> exists j, mv = Fragment v q j /\ S j <> size_quantity_nat q) ->
      shape_decoding chunk (Fragment v q i :: mvl) (Val.load_result chunk v)
  | shape_decoding_b: forall b mvl v,
      match v with Vint _ => True | Vlong _ => True | Vfloat _ => True | Vsingle _ => True |  _ => False end ->
      (forall mv, In mv mvl -> exists b', mv = Byte b') ->
      shape_decoding chunk (Byte b :: mvl) v
  | shape_decoding_u: forall mvl,
      shape_decoding chunk mvl Vundef.

Lemma decode_val_shape: forall chunk mv1 mvl,
  shape_decoding chunk (mv1 :: mvl) (decode_val chunk (mv1 :: mvl)).
Proof.
  intros.
  assert (A: forall mv mvs bs, proj_bytes mvs = Some bs -> In mv mvs ->
                               exists b, mv = Byte b).
  {
    induction mvs; simpl; intros.
    contradiction.
    destruct a; try discriminate. destruct H0. exists i; auto.
    destruct (proj_bytes mvs); try discriminate. eauto.
  }
  assert (B: forall v q mv n mvs,
             check_value n v q mvs = true -> In mv mvs -> (n < size_quantity_nat q)%nat ->
             exists j, mv = Fragment v q j /\ S j <> size_quantity_nat q).
  {
    induction n; destruct mvs; simpl; intros; try discriminate.
    contradiction.
    destruct m; try discriminate. InvBooleans. apply beq_nat_true in H4. subst.
    destruct H0. subst mv. exists n0; split; auto. omega.
    eapply IHn; eauto. omega.
  }
  assert (U: forall mvs, shape_decoding chunk mvs (Val.load_result chunk Vundef)).
  {
    intros. replace (Val.load_result chunk Vundef) with Vundef. constructor.
    destruct chunk; auto.
  }
  assert (C: forall q, size_quantity_nat q = size_chunk_nat chunk ->
             (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64) ->
             shape_decoding chunk (mv1 :: mvl) (Val.load_result chunk (proj_value q (mv1 :: mvl)))).
  {
    intros. unfold proj_value. destruct mv1; auto.
    destruct (size_quantity_nat_pos q) as [sz EQ]. rewrite EQ.
    simpl. unfold proj_sumbool. rewrite dec_eq_true.
    destruct (quantity_eq q q0); auto.
    destruct (Nat.eqb sz n) eqn:EQN; auto.
    destruct (check_value sz v q mvl) eqn:CHECK; auto.
    simpl. apply beq_nat_true in EQN. subst n q0. constructor. auto.
    destruct H0 as [E|[E|[E|E]]]; subst chunk; destruct q; auto || discriminate.
    congruence.
    intros. eapply B; eauto. omega.
  }
  unfold decode_val.
  destruct (proj_bytes (mv1 :: mvl)) as [bl|] eqn:PB.
  exploit (A mv1); eauto with coqlib. intros [b1 EQ1]; subst mv1.
  destruct chunk; (apply shape_decoding_u || apply shape_decoding_b); eauto with coqlib.
  destruct chunk, Archi.ptr64; (apply shape_decoding_u || apply C); auto.
Qed.

(** * Compatibility with memory injections *)

(** Relating two memory values according to a memory injection. *)

Inductive memval_inject (f: meminj): memval -> memval -> Prop :=
  | memval_inject_byte:
      forall n, memval_inject f (Byte n) (Byte n)
  | memval_inject_frag:
      forall v1 v2 q n,
      Val.inject f v1 v2 ->
      memval_inject f (Fragment v1 q n) (Fragment v2 q n)
  | memval_inject_undef:
      forall mv, memval_inject f Undef mv.

Lemma memval_inject_incr:
  forall f f' v1 v2, memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2.
Proof.
  intros. inv H; econstructor. eapply val_inject_incr; eauto.
Qed.

(** [decode_val], applied to lists of memory values that are pairwise
  related by [memval_inject], returns values that are related by [Val.inject]. *)

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

Lemma check_value_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall v v' q n,
  check_value n v q vl = true ->
  Val.inject f v v' -> v <> Vundef ->
  check_value n v' q vl' = true.
Proof.
  induction 1; intros; destruct n; simpl in *; auto.
  inv H; auto.
  InvBooleans. assert (n = n0) by (apply beq_nat_true; auto). subst v1 q0 n0.
  replace v2 with v'.
  unfold proj_sumbool; rewrite ! dec_eq_true. rewrite <- beq_nat_refl. simpl; eauto.
  inv H2; try discriminate; inv H4; congruence.
  discriminate.
Qed.

Lemma proj_value_inject:
  forall f q vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  Val.inject f (proj_value q vl1) (proj_value q vl2).
Proof.
  intros. unfold proj_value.
  inversion H; subst. auto. inversion H0; subst; auto.
  destruct (check_value (size_quantity_nat q) v1 q (Fragment v1 q0 n :: al)) eqn:B; auto.
  destruct (Val.eq v1 Vundef). subst; auto.
  erewrite check_value_inject by eauto. auto.
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

Lemma check_value_undef:
  forall n q v vl,
  In Undef vl -> check_value n v q vl = false.
Proof.
  induction n; intros; simpl.
  destruct vl. elim H. auto.
  destruct vl. auto.
  destruct m; auto. simpl in H; destruct H. congruence.
  rewrite IHn; auto. apply andb_false_r.
Qed.

Lemma proj_value_undef:
  forall q vl, In Undef vl -> proj_value q vl = Vundef.
Proof.
  intros; unfold proj_value.
  destruct vl; auto. destruct m; auto.
  rewrite check_value_undef. auto. auto.
Qed.

Theorem decode_val_inject:
  forall f vl1 vl2 chunk,
  list_forall2 (memval_inject f) vl1 vl2 ->
  Val.inject f (decode_val chunk vl1) (decode_val chunk vl2).
Proof.
  intros. unfold decode_val.
  destruct (proj_bytes vl1) as [bl1|] eqn:PB1.
  exploit proj_bytes_inject; eauto. intros PB2. rewrite PB2.
  destruct chunk; constructor.
  assert (A: forall q fn,
     Val.inject f (Val.load_result chunk (proj_value q vl1))
                  (match proj_bytes vl2 with
                   | Some bl => fn bl
                   | None => Val.load_result chunk (proj_value q vl2)
                   end)).
  { intros. destruct (proj_bytes vl2) as [bl2|] eqn:PB2.
    rewrite proj_value_undef. destruct chunk; auto. eapply proj_bytes_not_inject; eauto. congruence.
    apply Val.load_result_inject. apply proj_value_inject; auto.
  }
  destruct chunk; destruct Archi.ptr64; auto.
Qed.

(** Symmetrically, [encode_val], applied to values related by [Val.inject],
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

Lemma repeat_Undef_inject_encode_val:
  forall f chunk v,
  list_forall2 (memval_inject f) (list_repeat (size_chunk_nat chunk) Undef) (encode_val chunk v).
Proof.
  intros. rewrite <- (encode_val_length chunk v). apply repeat_Undef_inject_any.
Qed.

Lemma repeat_Undef_inject_self:
  forall f n,
  list_forall2 (memval_inject f) (list_repeat n Undef) (list_repeat n Undef).
Proof.
  induction n; simpl; constructor; auto. constructor.
Qed.

Lemma inj_value_inject:
  forall f v1 v2 q, Val.inject f v1 v2 -> list_forall2 (memval_inject f) (inj_value q v1) (inj_value q v2).
Proof.
  intros.
Local Transparent inj_value.
  unfold inj_value. generalize (size_quantity_nat q). induction n; simpl; constructor; auto.
  constructor; auto.
Qed.

Theorem encode_val_inject:
  forall f v1 v2 chunk,
  Val.inject f v1 v2 ->
  list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2).
Proof.
Local Opaque list_repeat.
  intros. inversion H; subst; simpl; destruct chunk;
  auto using inj_bytes_inject, inj_value_inject, repeat_Undef_inject_self, repeat_Undef_inject_encode_val.
- destruct Archi.ptr64; auto using inj_value_inject, repeat_Undef_inject_self.
- destruct Archi.ptr64; auto using inj_value_inject, repeat_Undef_inject_self.
- unfold encode_val. destruct v2; apply inj_value_inject; auto.
- unfold encode_val. destruct v2; apply inj_value_inject; auto.
Qed.

Definition memval_lessdef: memval -> memval -> Prop := memval_inject inject_id.

Lemma memval_lessdef_refl:
  forall mv, memval_lessdef mv mv.
Proof.
  red. destruct mv; econstructor. apply val_inject_id. auto.
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
  eapply val_inject_compose; eauto.
  constructor.
Qed.

(** * Breaking 64-bit memory accesses into two 32-bit accesses *)

Lemma int_of_bytes_append:
  forall l2 l1,
  int_of_bytes (l1 ++ l2) = int_of_bytes l1 + int_of_bytes l2 * two_p (Z.of_nat (length l1) * 8).
Proof.
  induction l1; simpl int_of_bytes; intros.
  simpl. ring.
  simpl length. rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat (length l1)) * 8) with (Z.of_nat (length l1) * 8 + 8) by omega.
  rewrite two_p_is_exp. change (two_p 8) with 256. rewrite IHl1. ring.
  omega. omega.
Qed.

Lemma int_of_bytes_range:
  forall l, 0 <= int_of_bytes l < two_p (Z.of_nat (length l) * 8).
Proof.
  induction l; intros.
  simpl. omega.
  simpl length. rewrite Nat2Z.inj_succ.
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
  length l1 = 4%nat -> length l2 = 4%nat -> Archi.ptr64 = false ->
  Val.lessdef
    (decode_val Mint64 (l1 ++ l2))
    (Val.longofwords (decode_val Mint32 (if Archi.big_endian then l1 else l2))
                     (decode_val Mint32 (if Archi.big_endian then l2 else l1))).
Proof.
  intros. unfold decode_val. rewrite H1.
  rewrite proj_bytes_append.
  destruct (proj_bytes l1) as [b1|] eqn:B1; destruct (proj_bytes l2) as [b2|] eqn:B2; auto.
  exploit length_proj_bytes. eexact B1. rewrite H; intro L1.
  exploit length_proj_bytes. eexact B2. rewrite H0; intro L2.
  assert (UR: forall l, length l = 4%nat -> Int.unsigned (Int.repr (int_of_bytes l)) = int_of_bytes l).
    intros. apply Int.unsigned_repr.
    generalize (int_of_bytes_range l). rewrite H2.
    change (two_p (Z.of_nat 4 * 8)) with (Int.max_unsigned + 1).
    omega.
  apply Val.lessdef_same.
  unfold decode_int, rev_if_be. destruct Archi.big_endian; rewrite B1; rewrite B2.
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
Qed.

Lemma bytes_of_int_append:
  forall n2 x2 n1 x1,
  0 <= x1 < two_p (Z.of_nat n1 * 8) ->
  bytes_of_int (n1 + n2) (x1 + x2 * two_p (Z.of_nat n1 * 8)) =
  bytes_of_int n1 x1 ++ bytes_of_int n2 x2.
Proof.
  induction n1; intros.
- simpl in *. f_equal. omega.
- assert (E: two_p (Z.of_nat (S n1) * 8) = two_p (Z.of_nat n1 * 8) * 256).
  {
    rewrite Nat2Z.inj_succ. change 256 with (two_p 8). rewrite <- two_p_is_exp.
    f_equal. omega. omega. omega.
  }
  rewrite E in *. simpl. f_equal.
  apply Byte.eqm_samerepr. exists (x2 * two_p (Z.of_nat n1 * 8)).
  change Byte.modulus with 256. ring.
  rewrite Z.mul_assoc. rewrite Z_div_plus. apply IHn1.
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
  change 32 with (Z.of_nat 4 * 8).
  rewrite Z.add_comm. apply bytes_of_int_append. apply Int.unsigned_range.
Qed.

Lemma encode_val_int64:
  forall v,
  Archi.ptr64 = false ->
  encode_val Mint64 v =
     encode_val Mint32 (if Archi.big_endian then Val.hiword v else Val.loword v)
  ++ encode_val Mint32 (if Archi.big_endian then Val.loword v else Val.hiword v).
Proof.
  intros. unfold encode_val. rewrite H.
  destruct v; destruct Archi.big_endian eqn:BI; try reflexivity;
  unfold Val.loword, Val.hiword, encode_val.
  unfold inj_bytes. rewrite <- map_app. f_equal.
  unfold encode_int, rev_if_be. rewrite BI. rewrite <- rev_app_distr. f_equal.
  apply bytes_of_int64.
  unfold inj_bytes. rewrite <- map_app. f_equal.
  unfold encode_int, rev_if_be. rewrite BI.
  apply bytes_of_int64.
Qed.

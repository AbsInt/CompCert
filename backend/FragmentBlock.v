(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Gergö Barany, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import OrderedType.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import Ordered.
Require Import AST.
Require Import Values.
Require Import Memdata.
Require Import Memory.
Require Export Machregs.

Open Scope Z_scope.

(** * Memory-like blocks storing value fragments *)

(** The register file and the stack are represented as instances of the module
  below, which is a basis for defining mappings from locations to values. This
  basic module implements a word-addressed memory block that can be read in
  words or doublewords (that is, as Q32 or Q64 quantities). Accesses use a word
  offset into the block, which is internally scaled to byte addresses. *)

Module FragBlock.

  Definition t := ZMap.t memval.

  Definition init := ZMap.init Undef.

  (* A register's address: The index of its first byte. *)
  Definition addr (ofs: Z) : Z := ofs * 4.

  (* The size of a quantity in bytes. *)
  Definition quantity_size (q: quantity) : Z := Z.of_nat (size_quantity_nat q).

  (* The address one byte past the end of a value at [ofs] of kind [q]. The next
    nonoverlapping value may start here. *)
  Definition next_addr (ofs: Z) (q: quantity) : Z := addr ofs + quantity_size q.

  Definition get_bytes (ofs: Z) (q: quantity) (fb: t) : list memval :=
    Mem.getN (size_quantity_nat q) (addr ofs) fb.

  Definition get (ofs: Z) (q: quantity) (fb: t) : val :=
    decode_val (chunk_of_quantity q) (get_bytes ofs q fb).

  Definition set_bytes (ofs: Z) (q: quantity) (bytes: list memval) (fb: t) : t :=
    Mem.setN (firstn (size_quantity_nat q) bytes) (addr ofs) fb.

  Definition set (ofs: Z) (q: quantity) (v: val) (fb: t) : t :=
    set_bytes ofs q (encode_val (chunk_of_quantity q) v) fb.

  (* Update the [old] block with copies of the fragments from [new] at the
    locations in [locs] specified as pairs of an offset and a quantity. *)
  Fixpoint override (locs: list (Z * quantity)) (new old: t) : t :=
    match locs with
    | nil => old
    | (ofs, q) :: locs' => set_bytes ofs q (get_bytes ofs q new) (override locs' new old)
    end.

  Fixpoint undef_locs (locs: list (Z * quantity)) (fb: t) : t :=
    match locs with
    | nil => fb
    | (ofs, q) :: locs' => set ofs q Vundef (undef_locs locs' fb)
    end.

  Lemma quantity_size_lt:
    forall q q', quantity_size q < quantity_size q' -> q = Q32 /\ q' = Q64.
  Proof.
    intros. destruct q, q'; try inv H. auto.
  Qed.

  Lemma gss_bytes:
    forall ofs q bs fb,
    length bs = size_quantity_nat q ->
    get_bytes ofs q (set_bytes ofs q bs fb) = bs.
  Proof.
    intros. unfold get_bytes, set_bytes.
    rewrite <- H, firstn_all, Mem.getN_setN_same. reflexivity.
  Qed.

  Lemma gss:
    forall ofs q v fb,
    get ofs q (set ofs q v fb) = Val.load_result (chunk_of_quantity q) v.
  Proof.
    intros. unfold get, set.
    rewrite gss_bytes; auto using encode_val_quantity_size.
    apply decode_encode_val_q.
  Qed.

  Lemma gso_bytes:
    forall ofs q ofs' q' bs fb,
    next_addr ofs q <= addr ofs' \/ next_addr ofs' q' <= addr ofs ->
    length bs = size_quantity_nat q' ->
    get_bytes ofs q (set_bytes ofs' q' bs fb) = get_bytes ofs q fb.
  Proof.
    intros until fb. intros H LEN. unfold get_bytes, set_bytes.
    rewrite Mem.getN_setN_outside; auto.
    unfold next_addr, addr, quantity_size in *.
    destruct H.
    - left; omega.
    - right. rewrite <- LEN, firstn_all. omega.
  Qed.

  Lemma gso:
    forall ofs q ofs' q' v fb,
    next_addr ofs q <= addr ofs' \/ next_addr ofs' q' <= addr ofs ->
    get ofs q (set ofs' q' v fb) = get ofs q fb.
  Proof.
    intros. unfold get, set.
    rewrite gso_bytes; auto using encode_val_quantity_size.
  Qed.

  Lemma gu_set_inside:
    forall ofs q ofs' q' v fb,
    addr ofs <= addr ofs' /\ addr ofs' < next_addr ofs q ->
    quantity_size q' < quantity_size q ->
    get ofs q (set ofs' q' v fb) = Vundef.
  Proof.
    intros until fb. intros (LB & UB) QLT.
    exploit quantity_size_lt; eauto; intros [Q' Q]; subst.

    assert (OFS: ofs = ofs' \/ ofs + 1 = ofs').
    { destruct (Zle_lt_or_eq _ _ LB).
      - right. unfold next_addr, addr, quantity_size in *.
        simpl in *; omega.
      - left. unfold addr in H. omega. }

    unfold get, set, get_bytes, set_bytes.
    simpl size_quantity_nat.
    change 8%nat with (4 + 4)%nat.
    rewrite Mem.getN_concat.
    replace 4%nat with (length (encode_val Many32 v)) by apply encode_val_length.
    rewrite firstn_all.
    simpl chunk_of_quantity. rewrite encode_val_any32.

    destruct OFS as [EQ | LT].
    - subst ofs.

      rewrite Mem.getN_setN_same. unfold inj_value.
      destruct (Val.eq v Vundef). simpl; auto.
      destruct (fits_quantity_dec v Q32). simpl.
      erewrite decode_val_diff_q with (q := Q32); simpl; eauto. congruence.
      simpl. auto.

    - subst ofs'.
      assert (A: addr ofs + Z.of_nat (length (inj_value Q32 v)) = addr (ofs + 1)).
      { rewrite inj_value_length. unfold addr. simpl. omega. }
      rewrite A, Mem.getN_setN_same.
      unfold inj_value.
      destruct (Val.eq v Vundef).
      rewrite decode_val_undef. auto. apply in_app. right. simpl; auto.
      destruct (fits_quantity_dec v Q32).
      erewrite decode_val_diff_q with (q := Q32); simpl; eauto. congruence.
      intuition eauto.
      rewrite decode_val_undef. auto. apply in_app. right. simpl; auto.
  Qed.

  Lemma gu_partial_overlap:
    forall ofs q ofs' q' v fb,
    addr ofs < addr ofs' /\ addr ofs' < next_addr ofs q ->
    get ofs q (set ofs' q' v fb) = Vundef.
  Proof.
    intros until fb. intros (LB & UB).

    assert (AUX: q = Q64 /\ ofs + 1 = ofs').
    { unfold next_addr, addr, quantity_size in *.
      destruct q; simpl in *; split; auto; omega. }
    destruct AUX as [Q OFS]. subst q. subst ofs'.

    destruct q'.
    rewrite gu_set_inside. auto. omega. unfold quantity_size. simpl. omega.

    unfold get, set, get_bytes, set_bytes.
    simpl size_quantity_nat. rewrite encode_val_any64.
    change 8%nat with (4 + 4)%nat.
    rewrite Mem.getN_concat.
    rewrite Mem.getN_setN_outside by (left; unfold addr; simpl; omega).
    replace (4 + 4)%nat with (length (inj_value Q64 v)) by apply inj_value_length.
    rewrite firstn_all.

    assert (A: addr ofs + Z.of_nat 4 = addr (ofs + 1)).
    { unfold addr. simpl. omega. }
    rewrite A, Mem.getN_setN_prefix.

    simpl chunk_of_quantity. unfold decode_val.
    unfold inj_value.
    destruct (Val.eq v Vundef).

    rewrite proj_bytes_undef, proj_value_undef; simpl; intuition auto using in_app.
    rewrite pred_dec_true by apply any_fits_quantity_Q64.
    erewrite proj_bytes_fragment by (simpl; intuition auto).
    erewrite proj_value_misaligned with (n := 4%nat); simpl; eauto.
    rewrite inj_value_length; simpl; auto.
  Qed.

  Lemma proj_bytes_firstn_inj_value_mismatch:
    forall n q v,
    n <> 0%nat ->
    proj_bytes (firstn n (inj_value q v)) = None.
  Proof.
    intros.
    unfold inj_value.
    destruct (Val.eq v Vundef), (fits_quantity_dec v q), q, n; simpl; congruence.
  Qed.

  Lemma proj_value_firstn_inj_value_mismatch:
    forall q q' v,
    q <> q' ->
    proj_value q (firstn (size_quantity_nat q) (inj_value q' v)) = Vundef.
  Proof.
    intros. destruct q, q'; try contradiction.
    - simpl size_quantity_nat.
      unfold inj_value.
      destruct (Val.eq v Vundef); auto.
      rewrite pred_dec_true by apply any_fits_quantity_Q64.
      erewrite proj_value_diff_q; simpl; eauto.
    - simpl size_quantity_nat.
      unfold inj_value.
      destruct (Val.eq v Vundef); auto.
      destruct (fits_quantity_dec v Q32).
      + erewrite proj_value_diff_q; simpl; eauto.
      + simpl; auto.
  Qed.

  Lemma gu_overlap:
    forall ofs q ofs' q' v fb,
    (ofs, q) <> (ofs', q') ->
    next_addr ofs q > addr ofs' ->
    next_addr ofs' q' > addr ofs ->
    get ofs q (set ofs' q' v fb) = Vundef.
  Proof.
    intros until fb. intros DIFF H H'.

    unfold next_addr, addr, quantity_size in *.

    destruct (Z.eq_dec ofs ofs').
    - subst ofs.
      destruct (quantity_eq q q').
      + subst q. contradiction.
      + unfold get, set, get_bytes, set_bytes.
        rewrite encode_val_q, firstn_inj_value.
        destruct q, q'; try contradiction.
        * rewrite Mem.getN_setN_prefix.
          simpl chunk_of_quantity. unfold decode_val.
          rewrite proj_bytes_firstn_inj_value_mismatch by (simpl; auto).
          rewrite proj_value_firstn_inj_value_mismatch; auto.
          rewrite inj_value_length; simpl; auto.
        * simpl size_quantity_nat.
          replace 8%nat with (4 + 4)%nat.
          rewrite Mem.getN_concat.
          unfold inj_value.
          destruct (Val.eq v Vundef).
            erewrite decode_val_undef; auto.
            change 4%nat with (length (list_repeat (size_quantity_nat Q32) Undef)).
            rewrite Mem.getN_setN_same; simpl; auto.
          destruct (fits_quantity_dec v Q32).
            erewrite decode_val_diff_q; eauto.
            change 4%nat with (length (inj_value_rec (size_quantity_nat Q32) v Q32)).
            rewrite Mem.getN_setN_same; simpl; auto.
            erewrite decode_val_undef; auto.
            change 4%nat with (length (list_repeat (size_quantity_nat Q32) Undef)).
            rewrite Mem.getN_setN_same; simpl; auto.
            simpl; auto.
    - destruct (zlt (addr ofs) (addr ofs')).
      + apply gu_partial_overlap.
        unfold next_addr, addr, quantity_size in *.
        omega.
      + unfold get, set, get_bytes, set_bytes.
        rewrite encode_val_q, firstn_inj_value.
        assert (q' = Q64).
        { destruct q'; auto. simpl in H'. unfold addr in g. omega. }
        subst q'.
        assert (ofs = ofs' + 1).
        { simpl in H'. unfold addr in g. omega. }
        subst ofs. unfold addr.
        destruct q.
        * simpl size_quantity_nat.
          replace ((ofs' + 1) * 4) with (ofs' * 4 + Z.of_nat 4) by (simpl; omega).
          rewrite Mem.getN_setN_suffix.
          unfold inj_value.
          destruct (Val.eq v Vundef); auto.
          rewrite pred_dec_true by apply any_fits_quantity_Q64.
          erewrite decode_val_diff_q; simpl; eauto. congruence.
          rewrite inj_value_length; simpl; auto.
        * simpl size_quantity_nat.
          replace ((ofs' + 1) * 4) with (ofs' * 4 + Z.of_nat 4) by (simpl; omega).
          unfold inj_value.
          destruct (Val.eq v Vundef).
          ** erewrite decode_val_undef; auto.
             simpl. left.
             replace (ofs' * 4 + 1 + 1 + 1 + 1) with (ofs' * 4 + 4) by omega.
             rewrite 3! ZMap.gso by (apply Z.lt_neq; omega).
             rewrite ZMap.gss; auto.
          ** rewrite pred_dec_true by apply any_fits_quantity_Q64.
             simpl chunk_of_quantity; unfold decode_val.
             erewrite proj_bytes_fragment.
             erewrite proj_value_misaligned with (n := 0%nat). auto.
             simpl.
             replace (ofs' * 4 + 1 + 1 + 1 + 1) with (ofs' * 4 + 4) by omega.
             rewrite 3! ZMap.gso by (apply Z.lt_neq; omega).
             rewrite ZMap.gss; auto.
             simpl. auto.
             simpl.
             replace (ofs' * 4 + 1 + 1 + 1 + 1) with (ofs' * 4 + 4) by omega.
             rewrite 3! ZMap.gso by (apply Z.lt_neq; omega).
             rewrite ZMap.gss; auto.
  Qed.

  Lemma gi:
    forall ofs q, get ofs q init = Vundef.
  Proof.
    intros. unfold init, get, get_bytes.
    destruct q; simpl; rewrite ZMap.gi; apply decode_val_hd_undef.
  Qed.

  Lemma get_has_type:
    forall ofs q fb, Val.has_type (get ofs q fb) (typ_of_quantity q).
  Proof.
    intros. unfold get.
    generalize (decode_val_type (chunk_of_quantity q)); intro.
    destruct q; auto.
  Qed.

  Lemma get_fits_quantity:
    forall ofs q fb, fits_quantity (get ofs q fb) q.
  Proof.
    intros.
    generalize (get_has_type ofs q fb); intro.
    apply has_type_fits_quantity in H.
    destruct q; auto.
  Qed.

End FragBlock.

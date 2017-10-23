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
Require Import Maps.
Require Import Ordered.
Require Import AST.
Require Import Values.
Require Import Memdata.
Require Import Memory.
Require Export Machregs.

Open Scope Z_scope.

(** * Representation of the register file *)

(** The [Regfile] module defines mappings from registers to values. The register
  file is represented as a kind of memory block containing bytes addressed using
  register numbers.
  The register numbers are taken from [IndexedMreg], interpreted as words and
  scaled internally to bytes. The indices of adjacent 64-bit registers must
  therefore differ by at least 2. *)

Module Regfile.

  Definition t := ZMap.t memval.

  Definition init := ZMap.init Undef.

  (* A register's address: The index of its first byte. *)
  Definition addr (r: mreg) : Z := Zpos (IndexedMreg.index r) * 4.

  Remark addr_pos: forall r, addr r > 0.
  Proof.
    intros. unfold addr. xomega.
  Qed.

  (* The address one byte past the end of register [r]. The next nonoverlapping
     register may start here. *)
  Definition next_addr (r: mreg) : Z := addr r + AST.typesize (mreg_type r).

  Lemma outside_interval_diff:
    forall r s, next_addr r <= addr s \/ next_addr s <= addr r -> r <> s.
  Proof.
    intros. destruct H; unfold next_addr in H.
    generalize (AST.typesize_pos (mreg_type r)); intros. contradict H. subst. omega.
    generalize (AST.typesize_pos (mreg_type s)); intros. contradict H. subst. omega.
  Qed.

  Lemma address_lt:
    forall r s,
    r <> s ->
    addr r < addr s ->
    next_addr r <= addr s.
  Proof.
    intros. unfold addr in H0.
    apply IndexedMreg.scaled_index_with_size; omega.
  Qed.

  Lemma diff_outside_interval:
    forall r s, r <> s -> next_addr r <= addr s \/ next_addr s <= addr r.
  Proof.
    intros.
    assert (Neq: addr r <> addr s).
    { unfold addr. contradict H. apply IndexedMreg.index_inj. xomega. }
    assert (Cases: addr r < addr s \/ addr s < addr r) by omega.
    destruct Cases.
    - left. apply address_lt; auto.
    - right. apply address_lt; auto.
  Qed.

  Definition chunk_of_mreg (r: mreg) : memory_chunk :=
    chunk_of_type (mreg_type r).

  Lemma chunk_length:
    forall r v,
    Z.to_nat (AST.typesize (mreg_type r)) = length (encode_val (chunk_of_mreg r) v).
  Proof.
    intros. rewrite encode_val_length.
    unfold chunk_of_mreg. destruct (mreg_type r); auto.
  Qed.

  Definition get_bytes (r: mreg) (rf: t) : list memval :=
    Mem.getN (Z.to_nat (AST.typesize (mreg_type r))) (addr r) rf.

  Definition get (r: mreg) (rf: t) : val :=
    decode_val (chunk_of_mreg r) (get_bytes r rf).

  Definition set_bytes (r: mreg) (bytes: list memval) (rf: t) : t :=
    Mem.setN bytes (addr r) rf.

  Definition set (r: mreg) (v: val) (rf: t) : t :=
    set_bytes r (encode_val (chunk_of_mreg r) v) rf.

  (* Update the [old] register file by choosing the values for the registers in
     [rs] from [new]. *)
  Fixpoint override (rs: list mreg) (new old: t) : t :=
    match rs with
    | nil => old
    | r :: rs' => set r (get r new) (override rs' new old)
    end.

  Fixpoint undef_regs (rs: list mreg) (rf: t) : t :=
    match rs with
    | nil => rf
    | r :: rs => set r Vundef (undef_regs rs rf)
    end.

  Lemma gss:
    forall r v rf,
    get r (set r v rf) = Val.load_result (chunk_of_mreg r) v.
  Proof.
    intros. unfold get, set, get_bytes, set_bytes.
    erewrite chunk_length. rewrite Mem.getN_setN_same.
    erewrite <- decode_encode_val_similar; eauto.
    eapply decode_encode_val_general.
  Qed.

  Lemma gso:
    forall r s v rf,
    r <> s ->
    get r (set s v rf) = get r rf.
  Proof.
    intros. unfold get, set, get_bytes, set_bytes.
    rewrite Mem.getN_setN_outside; auto.
    rewrite <- chunk_length.
    generalize (AST.typesize_pos (mreg_type s)), (AST.typesize_pos (mreg_type r)); intros.
    apply diff_outside_interval in H. unfold next_addr in H.
    rewrite !Z2Nat.id; omega.
  Qed.

  Lemma override_in:
    forall rs r new old,
    In r rs -> get r (override rs new old) = get r new.
  Proof.
    intros. induction rs; try contradiction.
    destruct (mreg_eq r a).
    - subst; simpl; rewrite gss.
      unfold chunk_of_mreg. rewrite Val.load_result_same; auto.
      unfold get. rewrite <- type_of_chunk_of_type.
      apply decode_val_type.
    - inversion H; try congruence.
      simpl; rewrite gso; auto.
  Qed.

  Lemma override_notin:
    forall r rs new old,
    ~ In r rs -> get r (override rs new old) = get r old.
  Proof.
    intros. induction rs; auto.
    apply not_in_cons in H. simpl. rewrite gso; intuition auto.
  Qed.

  Lemma undef_regs_in:
    forall r rs rf,
    In r rs -> get r (undef_regs rs rf) = Vundef.
  Proof.
    induction rs; simpl; intros. contradiction.
    destruct (mreg_eq r a).
    - subst; simpl; rewrite gss.
      destruct (chunk_of_mreg a); auto.
    - inversion H; try congruence.
      simpl; rewrite gso; auto.
  Qed.

  Lemma undef_regs_notin:
    forall r rs rf,
    ~ In r rs -> get r (undef_regs rs rf) = get r rf.
  Proof.
    induction rs; auto; intros.
    apply not_in_cons in H. simpl. rewrite gso; intuition auto.
  Qed.

End Regfile.

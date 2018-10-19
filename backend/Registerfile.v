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
Require Import FragmentBlock.
Require Export Machregs.

Open Scope Z_scope.

(** * Auxiliary definitions *)

Definition quantity_of_mreg (r: mreg) : quantity :=
  quantity_of_typ (mreg_type r).

Definition chunk_of_mreg (r: mreg) : memory_chunk :=
  chunk_of_type (mreg_type r).

Definition typesize ty :=
  match ty with
  | Tint | Tsingle | Tany32 => 1
  | Tlong | Tfloat | Tany64 => 2
  end.

Lemma typesize_pos:
  forall ty, typesize ty > 0.
Proof.
  destruct ty; simpl; omega.
Qed.

(** * Definition of a general register model *)

(** We will be using slightly different models of the target CPU's register
  architecture: [mreg] models data registers only, with no separation of
  different kinds of registers, while [preg] models integer and floating-point
  registers differently and includes condition code registers and the program
  counter as well.

  We will want to use the same basic representation of the register file for
  both of these register models, so we capture their commonalities in this
  module type. *)

Module Type REGISTER_MODEL.

  Parameter reg: Set.
  Axiom eq_dec: forall r s: reg, {r = s} + {r <> s}.

  Parameter type: reg -> typ.
  Parameter quantity_of: reg -> quantity.
  Parameter chunk_of: reg -> memory_chunk.

  Axiom type_cases:
    forall r, type r = Tany32 \/ type r = Tany64.

  Parameter ofs: reg -> Z.
  Parameter addr: reg -> Z.
  Parameter next_addr: reg -> Z.

  Axiom addr_pos: forall r, addr r > 0.

  Axiom addr_compat: forall r, FragBlock.addr (ofs r) = addr r.
  Axiom next_addr_compat: forall r, FragBlock.next_addr (ofs r) (quantity_of r) = next_addr r.

  Axiom size_compat:
    forall r,
    AST.typesize (type r) = FragBlock.quantity_size (quantity_of r).

  Axiom quantity_of_compat:
    forall r,
    quantity_of r = quantity_of_typ (type r).

  Axiom chunk_of_reg_compat:
    forall r,
    chunk_of r = chunk_of_quantity (quantity_of r).

  Axiom chunk_of_reg_type:
    forall r,
    chunk_of r = chunk_of_type (type r).

  Axiom diff_outside_interval:
    forall r s, r <> s -> next_addr r <= addr s \/ next_addr s <= addr r.

End REGISTER_MODEL.

Module Mreg <: REGISTER_MODEL.

  Definition reg := mreg.
  Definition eq_dec := mreg_eq.

  Definition type := mreg_type.
  Definition quantity_of := quantity_of_mreg.
  Definition chunk_of := chunk_of_mreg.

  Definition type_cases := mreg_type_cases.

  (* A register's offset, in words, from an arbitrary starting point. *)
  Definition ofs (r: mreg) : Z :=
    Zpos (IndexedMreg.index r).

  (* A register's address: The index of its first byte. *)
  Definition addr (r: mreg) : Z := Zpos (IndexedMreg.index r) * 4.

  Remark addr_pos: forall r, addr r > 0.
  Proof.
    intros. unfold addr. xomega.
  Qed.

  (* The address one byte past the end of register [r]. The next nonoverlapping
     register may start here. *)
  Definition next_addr (r: mreg) : Z := addr r + AST.typesize (mreg_type r).

  (* Our notions of offset and address are compatible with FragBlock's addresses. *)
  Lemma addr_compat: forall r, FragBlock.addr (ofs r) = addr r.
  Proof.
    unfold addr, ofs, FragBlock.addr; intros. auto.
  Qed.

  Lemma size_compat:
    forall r,
    AST.typesize (mreg_type r) = FragBlock.quantity_size (quantity_of_mreg r).
  Proof.
    intros. unfold quantity_of_mreg. destruct (mreg_type r); simpl; auto.
  Qed.

  Lemma quantity_of_compat:
    forall r,
    quantity_of r = quantity_of_typ (type r).
  Proof.
    reflexivity.
  Qed.

  Lemma chunk_of_reg_type:
    forall r,
    chunk_of r = chunk_of_type (type r).
  Proof.
    reflexivity.
  Qed.

  Lemma chunk_of_reg_compat:
    forall r,
    chunk_of r = chunk_of_quantity (quantity_of_mreg r).
  Proof.
    intros.
    rewrite quantity_of_compat, chunk_of_quantity_of_typ, chunk_of_reg_type; auto.
    apply type_cases.
  Qed.

  Lemma next_addr_compat: forall r, FragBlock.next_addr (ofs r) (quantity_of_mreg r) = next_addr r.
  Proof.
    unfold next_addr, addr, ofs, FragBlock.next_addr, FragBlock.addr; intros.
    rewrite size_compat. auto.
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

  Lemma outside_interval_diff:
    forall r s, next_addr r <= addr s \/ next_addr s <= addr r -> r <> s.
  Proof.
    intros. destruct H; unfold next_addr in H.
    generalize (AST.typesize_pos (mreg_type r)); intros. contradict H. subst. omega.
    generalize (AST.typesize_pos (mreg_type s)); intros. contradict H. subst. omega.
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

End Mreg.

(** * Representation of the register file *)

(** The [Regfile] module defines mappings from registers to values. The register
  file is represented as a kind of memory block containing bytes addressed using
  register numbers.

  The register offset numbers are interpreted as words and scaled internally to
  bytes. The indices of adjacent 64-bit registers must therefore differ by at
  least 2. *)

Module Regfile(M: REGISTER_MODEL).

  Definition t := FragBlock.t.

  Definition init := FragBlock.init.

  (* The offset just past the end of register [r]. The next nonoverlapping
    register may start here. *)
  Definition next_ofs (r: M.reg) : Z := M.ofs r + typesize (M.type r).

  Lemma chunk_length:
    forall r v,
    Z.to_nat (AST.typesize (mreg_type r)) = length (encode_val (chunk_of_mreg r) v).
  Proof.
    intros. rewrite encode_val_length.
    unfold chunk_of_mreg. destruct (mreg_type r); auto.
  Qed.

  Definition get_bytes (r: M.reg) (rf: t) : list memval :=
    FragBlock.get_bytes (M.ofs r) (M.quantity_of r) rf.

  Definition get (r: M.reg) (rf: t) : val :=
    FragBlock.get (M.ofs r) (M.quantity_of r) rf.

  Definition set_bytes (r: M.reg) (bytes: list memval) (rf: t) : t :=
    FragBlock.set_bytes (M.ofs r) (M.quantity_of r) bytes rf.

  Definition set (r: M.reg) (v: val) (rf: t) : t :=
    FragBlock.set (M.ofs r) (M.quantity_of r) v rf.

  (* Update the [old] register file by choosing the values for the registers in
     [rs] from [new]. *)
  Fixpoint override (rs: list M.reg) (new old: t) : t :=
    match rs with
    | nil => old
    | r :: rs' => set r (get r new) (override rs' new old)
    end.

  Fixpoint undef_regs (rs: list M.reg) (rf: t) : t :=
    match rs with
    | nil => rf
    | r :: rs => set r Vundef (undef_regs rs rf)
    end.

  Lemma gss:
    forall r v rf,
    get r (set r v rf) = Val.load_result (M.chunk_of r) v.
  Proof.
    intros. unfold get, set.
    rewrite FragBlock.gss, M.chunk_of_reg_compat; auto.
  Qed.

  Lemma gso:
    forall r s v rf,
    r <> s ->
    get r (set s v rf) = get r rf.
  Proof.
    intros. unfold get, set.
    rewrite FragBlock.gso; auto.
    rewrite !M.next_addr_compat, !M.addr_compat.
    apply M.diff_outside_interval; auto.
  Qed.

  Lemma get_has_type:
    forall r rf, Val.has_type (get r rf) (M.type r).
  Proof.
    intros. unfold get.
    unfold quantity_of_mreg.
    rewrite M.quantity_of_compat.
    destruct (M.type_cases r) as [T | T]; rewrite T; apply FragBlock.get_has_type.
  Qed.

  Lemma get_load_result:
    forall r rf, Val.load_result (M.chunk_of r) (get r rf) = get r rf.
  Proof.
    intros. rewrite M.chunk_of_reg_type, Val.load_result_same; auto using get_has_type.
  Qed.

  Lemma get_bytes_compat:
    forall r rf, get r rf = decode_val (M.chunk_of r) (get_bytes r rf).
  Proof.
    intros. unfold get, FragBlock.get. rewrite M.chunk_of_reg_compat. reflexivity.
  Qed.

  Lemma set_bytes_compat:
    forall r v rf, set r v rf = set_bytes r (encode_val (M.chunk_of r) v) rf.
  Proof.
    intros. unfold set, FragBlock.set. rewrite M.chunk_of_reg_compat. reflexivity.
  Qed.

  Lemma override_in:
    forall rs r new old,
    In r rs -> get r (override rs new old) = get r new.
  Proof.
    intros. induction rs; try contradiction.
    destruct (M.eq_dec r a).
    - subst; simpl; rewrite gss.
      rewrite M.chunk_of_reg_type, Val.load_result_same; auto.
      apply get_has_type.
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
    destruct (M.eq_dec r a).
    - subst; simpl; rewrite gss.
      destruct (M.chunk_of a); auto.
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

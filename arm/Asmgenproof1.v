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

(** Correctness proof for ARM code generation: auxiliary results. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Compopts.
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.
Require Import Asmgenproof0.

Local Transparent Archi.ptr64.

(** Useful properties of the R14 registers. *)

Lemma ireg_of_not_R14:
  forall m r, ireg_of m = OK r -> IR r <> IR IR14.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.
Hint Resolve ireg_of_not_R14: asmgen.

Lemma ireg_of_not_R14':
  forall m r, ireg_of m = OK r -> r <> IR14.
Proof.
  intros. generalize (ireg_of_not_R14 _ _ H). congruence.
Qed.
Hint Resolve ireg_of_not_R14': asmgen.

(** [undef_flags] and [nextinstr_nf] *)

Lemma nextinstr_nf_pc:
  forall rs, (nextinstr_nf rs)#PC = Val.offset_ptr rs#PC Ptrofs.one.
Proof.
  intros. reflexivity.
Qed.

Definition if_preg (r: preg) : bool :=
  match r with
  | IR _ => true
  | FR _ => true
  | CR _ => false
  | PC   => false
  end.

Lemma data_if_preg: forall r, data_preg r = true -> if_preg r = true.
Proof.
  intros. destruct r; reflexivity || discriminate.
Qed.

Lemma if_preg_not_PC: forall r, if_preg r = true -> r <> PC.
Proof.
  intros; red; intros; subst; discriminate.
Qed.

Hint Resolve data_if_preg if_preg_not_PC: asmgen.

Lemma nextinstr_nf_inv:
  forall r rs, if_preg r = true -> (nextinstr_nf rs)#r = rs#r.
Proof.
  intros. destruct r; reflexivity || discriminate.
Qed.

Lemma nextinstr_nf_inv1:
  forall r rs, data_preg r = true -> (nextinstr_nf rs)#r = rs#r.
Proof.
  intros. destruct r; reflexivity || discriminate.
Qed.

(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite nextinstr_nf_inv by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite nextinstr_nf_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of ARM constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Decomposition of an integer constant *)

Lemma decompose_int_arm_or:
  forall N n p x, List.fold_left Int.or (decompose_int_arm N n p) x = Int.or x n.
Proof.
  induction N; intros; simpl.
  predSpec Int.eq Int.eq_spec n Int.zero; simpl.
  subst n. rewrite Int.or_zero. auto.
  auto.
  predSpec Int.eq Int.eq_spec (Int.and n (Int.shl (Int.repr 3) p)) Int.zero.
  auto.
  simpl. rewrite IHN. rewrite Int.or_assoc. decEq. rewrite <- Int.and_or_distrib.
  rewrite Int.or_not_self. apply Int.and_mone.
Qed.

Lemma decompose_int_arm_xor:
  forall N n p x, List.fold_left Int.xor (decompose_int_arm N n p) x = Int.xor x n.
Proof.
  induction N; intros; simpl.
  predSpec Int.eq Int.eq_spec n Int.zero; simpl.
  subst n. rewrite Int.xor_zero. auto.
  auto.
  predSpec Int.eq Int.eq_spec (Int.and n (Int.shl (Int.repr 3) p)) Int.zero.
  auto.
  simpl. rewrite IHN. rewrite Int.xor_assoc. decEq. rewrite <- Int.and_xor_distrib.
  rewrite Int.xor_not_self. apply Int.and_mone.
Qed.

Lemma decompose_int_arm_add:
  forall N n p x, List.fold_left Int.add (decompose_int_arm N n p) x = Int.add x n.
Proof.
  induction N; intros; simpl.
  predSpec Int.eq Int.eq_spec n Int.zero; simpl.
  subst n. rewrite Int.add_zero. auto.
  auto.
  predSpec Int.eq Int.eq_spec (Int.and n (Int.shl (Int.repr 3) p)) Int.zero.
  auto.
  simpl. rewrite IHN. rewrite Int.add_assoc. decEq. rewrite Int.add_and.
  rewrite Int.or_not_self. apply Int.and_mone. apply Int.and_not_self.
Qed.

Remark decompose_int_arm_nil:
  forall N n p, decompose_int_arm N n p = nil -> n = Int.zero.
Proof.
  intros. generalize (decompose_int_arm_or N n p Int.zero). rewrite H. simpl.
  rewrite Int.or_commut; rewrite Int.or_zero; auto.
Qed.

Lemma decompose_int_thumb_or:
  forall N n p x, List.fold_left Int.or (decompose_int_thumb N n p) x = Int.or x n.
Proof.
  induction N; intros; simpl.
  predSpec Int.eq Int.eq_spec n Int.zero; simpl.
  subst n. rewrite Int.or_zero. auto.
  auto.
  predSpec Int.eq Int.eq_spec (Int.and n (Int.shl Int.one p)) Int.zero.
  auto.
  simpl. rewrite IHN. rewrite Int.or_assoc. decEq. rewrite <- Int.and_or_distrib.
  rewrite Int.or_not_self. apply Int.and_mone.
Qed.

Lemma decompose_int_thumb_xor:
  forall N n p x, List.fold_left Int.xor (decompose_int_thumb N n p) x = Int.xor x n.
Proof.
  induction N; intros; simpl.
  predSpec Int.eq Int.eq_spec n Int.zero; simpl.
  subst n. rewrite Int.xor_zero. auto.
  auto.
  predSpec Int.eq Int.eq_spec (Int.and n (Int.shl Int.one p)) Int.zero.
  auto.
  simpl. rewrite IHN. rewrite Int.xor_assoc. decEq. rewrite <- Int.and_xor_distrib.
  rewrite Int.xor_not_self. apply Int.and_mone.
Qed.

Lemma decompose_int_thumb_add:
  forall N n p x, List.fold_left Int.add (decompose_int_thumb N n p) x = Int.add x n.
Proof.
  induction N; intros; simpl.
  predSpec Int.eq Int.eq_spec n Int.zero; simpl.
  subst n. rewrite Int.add_zero. auto.
  auto.
  predSpec Int.eq Int.eq_spec (Int.and n (Int.shl Int.one p)) Int.zero.
  auto.
  simpl. rewrite IHN. rewrite Int.add_assoc. decEq. rewrite Int.add_and.
  rewrite Int.or_not_self. apply Int.and_mone. apply Int.and_not_self.
Qed.

Remark decompose_int_thumb_nil:
  forall N n p, decompose_int_thumb N n p = nil -> n = Int.zero.
Proof.
  intros. generalize (decompose_int_thumb_or N n p Int.zero). rewrite H. simpl.
  rewrite Int.or_commut; rewrite Int.or_zero; auto.
Qed.

Lemma decompose_int_general:
  forall (f: val -> int -> val) (g: int -> int -> int),
  (forall v1 n2 n3, f (f v1 n2) n3 = f v1 (g n2 n3)) ->
  (forall n1 n2 n3, g (g n1 n2) n3 = g n1 (g n2 n3)) ->
  (forall n, g Int.zero n = n) ->
  (forall N n p x, List.fold_left g (decompose_int_arm N n p) x = g x n) ->
  (forall N n p x, List.fold_left g (decompose_int_thumb N n p) x = g x n) ->
  forall n v,
  List.fold_left f (decompose_int n) v = f v n.
Proof.
  intros f g DISTR ASSOC ZERO DECOMP1 DECOMP2.
  assert (A: forall l x y, g x (fold_left g l y) = fold_left g l (g x y)).
    induction l; intros; simpl. auto. rewrite IHl. decEq. rewrite ASSOC; auto.
  assert (B: forall l v n, fold_left f l (f v n) = f v (fold_left g l n)).
    induction l; intros; simpl.
    auto.
    rewrite IHl. rewrite DISTR. decEq. decEq. auto.
  intros. unfold decompose_int, decompose_int_base.
  destruct (thumb tt); [destruct (is_immed_arith_thumb_special n)|].
- reflexivity.
- destruct (decompose_int_thumb 24%nat n Int.zero) eqn:DB.
  + simpl. exploit decompose_int_thumb_nil; eauto. congruence.
  + simpl. rewrite B. decEq.
    generalize (DECOMP2 24%nat n Int.zero Int.zero).
    rewrite DB; simpl. rewrite ! ZERO. auto.
- destruct (decompose_int_arm 12%nat n Int.zero) eqn:DB.
  + simpl. exploit decompose_int_arm_nil; eauto. congruence.
  + simpl. rewrite B. decEq.
    generalize (DECOMP1 12%nat n Int.zero Int.zero).
    rewrite DB; simpl. rewrite ! ZERO. auto.
Qed.

Lemma decompose_int_or:
  forall n v,
  List.fold_left (fun v i => Val.or v (Vint i)) (decompose_int n) v = Val.or v (Vint n).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.or v (Vint n)) (g := Int.or).
  intros. rewrite Val.or_assoc. auto.
  apply Int.or_assoc.
  intros. rewrite Int.or_commut. apply Int.or_zero.
  apply decompose_int_arm_or. apply decompose_int_thumb_or.
Qed.

Lemma decompose_int_bic:
  forall n v,
  List.fold_left (fun v i => Val.and v (Vint (Int.not i))) (decompose_int n) v = Val.and v (Vint (Int.not n)).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.and v (Vint (Int.not n))) (g := Int.or).
  intros. rewrite Val.and_assoc. simpl. decEq. decEq. rewrite Int.not_or_and_not. auto.
  apply Int.or_assoc.
  intros. rewrite Int.or_commut. apply Int.or_zero.
  apply decompose_int_arm_or. apply decompose_int_thumb_or.
Qed.

Lemma decompose_int_xor:
  forall n v,
  List.fold_left (fun v i => Val.xor v (Vint i)) (decompose_int n) v = Val.xor v (Vint n).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.xor v (Vint n)) (g := Int.xor).
  intros. rewrite Val.xor_assoc. auto.
  apply Int.xor_assoc.
  intros. rewrite Int.xor_commut. apply Int.xor_zero.
  apply decompose_int_arm_xor. apply decompose_int_thumb_xor.
Qed.

Lemma decompose_int_add:
  forall n v,
  List.fold_left (fun v i => Val.add v (Vint i)) (decompose_int n) v = Val.add v (Vint n).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.add v (Vint n)) (g := Int.add).
  intros. rewrite Val.add_assoc. auto.
  apply Int.add_assoc.
  intros. rewrite Int.add_commut. apply Int.add_zero.
  apply decompose_int_arm_add. apply decompose_int_thumb_add.
Qed.

Lemma decompose_int_sub:
  forall n v,
  List.fold_left (fun v i => Val.sub v (Vint i)) (decompose_int n) v = Val.sub v (Vint n).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.sub v (Vint n)) (g := Int.add).
  intros. repeat rewrite Val.sub_add_opp. rewrite Val.add_assoc. decEq. simpl. decEq.
  rewrite Int.neg_add_distr; auto.
  apply Int.add_assoc.
  intros. rewrite Int.add_commut. apply Int.add_zero.
  apply decompose_int_arm_add. apply decompose_int_thumb_add.
Qed.

Lemma iterate_op_correct:
  forall op1 op2 (f: val -> int -> val) (rs: regset) (r: ireg) m v0 n k,
  (forall (rs:regset) n,
    exec_instr ge fn (op2 (SOimm n)) rs m =
    Next (nextinstr_nf (rs#r <- (f (rs#r) n))) m) ->
  (forall n,
    exec_instr ge fn (op1 (SOimm n)) rs m =
    Next (nextinstr_nf (rs#r <- (f v0 n))) m) ->
  exists rs',
     exec_straight ge fn (iterate_op op1 op2 (decompose_int n) k) rs m  k rs' m
  /\ rs'#r = List.fold_left f (decompose_int n) v0
  /\ forall r': preg, r' <> r -> if_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros until k; intros SEM2 SEM1.
  unfold iterate_op.
  destruct (decompose_int n) as [ | i tl] eqn:DI.
  unfold decompose_int in DI. destruct (decompose_int_base n); congruence.
  revert k. pattern tl. apply List.rev_ind.
  (* base case *)
  intros; simpl. econstructor.
  split. apply exec_straight_one. rewrite SEM1. reflexivity. reflexivity.
  intuition Simpl.
  (* inductive case *)
  intros.
  rewrite List.map_app. simpl. rewrite app_ass. simpl.
  destruct (H (op2 (SOimm x) :: k)) as [rs' [A [B C]]].
  econstructor.
  split. eapply exec_straight_trans. eexact A. apply exec_straight_one.
  rewrite SEM2. reflexivity. reflexivity.
  split. rewrite fold_left_app; simpl. Simpl. rewrite B. auto.
  intros; Simpl.
Qed.

(** Loading a constant. *)

Lemma loadimm_correct:
  forall r n k rs m,
  exists rs',
     exec_straight ge fn (loadimm r n k) rs m  k rs' m
  /\ rs'#r = Vint n
  /\ forall r': preg, r' <> r -> if_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm.
  set (l1 := length (decompose_int n)).
  set (l2 := length (decompose_int (Int.not n))).
  destruct (Nat.leb l1 1%nat).
{ (* single mov *)
  econstructor; split. apply exec_straight_one. simpl; reflexivity. auto.
  split; intros; Simpl. }
  destruct (Nat.leb l2 1%nat).
{ (* single movn *)
  econstructor; split. apply exec_straight_one.
  simpl. rewrite Int.not_involutive. reflexivity. auto.
  split; intros; Simpl. }
  destruct Archi.thumb2_support.
{ (* movw / movt *)
  unfold loadimm_word. destruct (Int.eq (Int.shru n (Int.repr 16)) Int.zero).
  econstructor; split.
  apply exec_straight_one. simpl; eauto. auto. split; intros; Simpl.
  econstructor; split.
  eapply exec_straight_two. simpl; reflexivity. simpl; reflexivity. auto. auto.
  split; intros; Simpl. simpl. f_equal. rewrite Int.zero_ext_and by omega.
  rewrite Int.and_assoc. change 65535 with (two_p 16 - 1). rewrite Int.and_idem.
  apply Int.same_bits_eq; intros.
  rewrite Int.bits_or, Int.bits_and, Int.bits_shl, Int.testbit_repr by auto.
  rewrite Int.Ztestbit_two_p_m1 by omega. change (Int.unsigned (Int.repr 16)) with 16.
  destruct (zlt i 16).
  rewrite andb_true_r, orb_false_r; auto.
  rewrite andb_false_r; simpl. rewrite Int.bits_shru by omega.
  change (Int.unsigned (Int.repr 16)) with 16. rewrite zlt_true by omega. f_equal; omega.
}
  destruct (Nat.leb l1 l2).
{ (* mov - orr* *)
  replace (Vint n) with (List.fold_left (fun v i => Val.or v (Vint i)) (decompose_int n) Vzero).
  apply iterate_op_correct.
  auto.
  intros; simpl. rewrite Int.or_commut; rewrite Int.or_zero; auto.
  rewrite decompose_int_or. simpl. rewrite Int.or_commut; rewrite Int.or_zero; auto.
}
{ (* mvn - bic* *)
  replace (Vint n) with (List.fold_left (fun v i => Val.and v (Vint (Int.not i))) (decompose_int (Int.not n)) (Vint Int.mone)).
  apply iterate_op_correct.
  auto.
  intros. simpl. rewrite Int.and_commut; rewrite Int.and_mone; auto.
  rewrite decompose_int_bic. simpl. rewrite Int.not_involutive. rewrite Int.and_commut. rewrite Int.and_mone; auto.
}
Qed.

(** Add integer immediate. *)

Lemma addimm_correct:
  forall r1 r2 n k rs m,
  exists rs',
     exec_straight ge fn (addimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> if_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm.
  destruct (Int.ltu (Int.repr (-256)) n).
  (* sub *)
  econstructor; split. apply exec_straight_one; simpl; auto.
  split; intros; Simpl. apply Val.sub_opp_add.
  destruct (Nat.leb (length (decompose_int n)) (length (decompose_int (Int.neg n)))).
  (* add - add* *)
  replace (Val.add (rs r2) (Vint n))
     with (List.fold_left (fun v i => Val.add v (Vint i)) (decompose_int n) (rs r2)).
  apply iterate_op_correct.
  auto.
  auto.
  apply decompose_int_add.
  (* sub - sub* *)
  replace (Val.add (rs r2) (Vint n))
     with (List.fold_left (fun v i => Val.sub v (Vint i)) (decompose_int (Int.neg n)) (rs r2)).
  apply iterate_op_correct.
  auto.
  auto.
  rewrite decompose_int_sub. apply Val.sub_opp_add.
Qed.

(* And integer immediate *)

Lemma andimm_correct:
  forall r1 r2 n k rs m,
  exists rs',
     exec_straight ge fn (andimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.and rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> if_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm. destruct (is_immed_arith n).
  (* andi *)
  exists (nextinstr_nf (rs#r1 <- (Val.and rs#r2 (Vint n)))).
  split. apply exec_straight_one; auto. split; intros; Simpl.
  (* bic - bic* *)
  replace (Val.and (rs r2) (Vint n))
     with (List.fold_left (fun v i => Val.and v (Vint (Int.not i))) (decompose_int (Int.not n)) (rs r2)).
  apply iterate_op_correct.
  auto. auto.
  rewrite decompose_int_bic. rewrite Int.not_involutive. auto.
Qed.

(** Reverse sub immediate *)

Lemma rsubimm_correct:
  forall r1 r2 n k rs m,
  exists rs',
     exec_straight ge fn (rsubimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.sub (Vint n) rs#r2
  /\ forall r': preg, r' <> r1 -> if_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros. unfold rsubimm.
  (* rsb - add* *)
  replace (Val.sub (Vint n) (rs r2))
     with (List.fold_left (fun v i => Val.add v (Vint i)) (decompose_int n) (Val.neg (rs r2))).
  apply iterate_op_correct.
  auto.
  intros. simpl. destruct (rs r2); auto. simpl. rewrite Int.sub_add_opp.
  rewrite Int.add_commut; auto.
  rewrite decompose_int_add.
  destruct (rs r2); simpl; auto. rewrite Int.sub_add_opp. rewrite Int.add_commut; auto.
Qed.

(** Or immediate *)

Lemma orimm_correct:
  forall r1 r2 n k rs m,
  exists rs',
     exec_straight ge fn (orimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.or rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> if_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros. unfold orimm.
  (* ori - ori* *)
  replace (Val.or (rs r2) (Vint n))
     with (List.fold_left (fun v i => Val.or v (Vint i)) (decompose_int n) (rs r2)).
  apply iterate_op_correct.
  auto.
  auto.
  apply decompose_int_or.
Qed.

(** Xor immediate *)

Lemma xorimm_correct:
  forall r1 r2 n k rs m,
  exists rs',
     exec_straight ge fn (xorimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.xor rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> if_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros. unfold xorimm.
  (* xori - xori* *)
  replace (Val.xor (rs r2) (Vint n))
     with (List.fold_left (fun v i => Val.xor v (Vint i)) (decompose_int n) (rs r2)).
  apply iterate_op_correct.
  auto.
  auto.
  apply decompose_int_xor.
Qed.

(** Indexed memory loads. *)

Lemma indexed_memory_access_correct:
  forall (P: regset -> Prop) (mk_instr: ireg -> int -> instruction)
         (mk_immed: int -> int) (base: ireg) n k (rs: regset) m m',
  (forall (r1: ireg) (rs1: regset) n1 k,
    Val.add rs1#r1 (Vint n1) = Val.add rs#base (Vint n) ->
    (forall (r: preg), if_preg r = true -> r <> IR14 -> rs1 r = rs r) ->
    exists rs',
    exec_straight ge fn (mk_instr r1 n1 :: k) rs1 m k rs' m' /\ P rs') ->
  exists rs',
     exec_straight ge fn
        (indexed_memory_access mk_instr mk_immed base n k) rs m
        k rs' m'
  /\ P rs'.
Proof.
  intros until m'; intros SEM.
  unfold indexed_memory_access.
  destruct (Int.eq n (mk_immed n)).
- apply SEM; auto.
- destruct (addimm_correct IR14 base (Int.sub n (mk_immed n)) (mk_instr IR14 (mk_immed n) :: k) rs m)
  as (rs1 & A & B & C).
  destruct (SEM IR14 rs1 (mk_immed n) k) as (rs2 & D & E).
  rewrite B. rewrite Val.add_assoc. f_equal. simpl.
  rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg (mk_immed n))).
  rewrite Int.add_neg_zero. rewrite Int.add_zero. auto.
  auto with asmgen.
  exists rs2; split; auto. eapply exec_straight_trans; eauto.
Qed.

Lemma loadind_int_correct:
  forall (base: ireg) ofs dst (rs: regset) m v k,
  Mem.loadv Mint32 m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn (loadind_int base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, if_preg r = true -> r <> IR14 -> r <> dst -> rs'#r = rs#r.
Proof.
  intros; unfold loadind_int.
  assert (Val.offset_ptr (rs base) ofs = Val.add (rs base) (Vint (Ptrofs.to_int ofs))).
  { destruct (rs base); try discriminate. simpl. f_equal; f_equal. symmetry; auto with ptrofs. }
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_load. rewrite H1, <- H0, H. eauto. auto.
  split; intros; Simpl.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, if_preg r = true -> r <> IR14 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  unfold loadind; intros.
  assert (Val.offset_ptr (rs base) ofs = Val.add (rs base) (Vint (Ptrofs.to_int ofs))).
  { destruct (rs base); try discriminate. simpl. f_equal; f_equal. symmetry; auto with ptrofs. }
  destruct ty; destruct (preg_of dst); inv H; simpl in H0.
- (* int *)
  apply loadind_int_correct; auto.
- (* float *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_load. rewrite H, <- H1, H0. eauto. auto.
  split; intros; Simpl.
- (* single *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_load. rewrite H, <- H1, H0. eauto. auto.
  split; intros; Simpl.
- (* any32 *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_load. rewrite H, <- H1, H0. eauto. auto.
  split; intros; Simpl.
- (* any64 *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_load. rewrite H, <- H1, H0. eauto. auto.
  split; intros; Simpl.
Qed.

(** Indexed memory stores. *)

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) (rs#(preg_of src)) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, if_preg r = true -> r <> IR14 -> rs'#r = rs#r.
Proof.
  unfold storeind; intros.
  assert (DATA: data_preg (preg_of src) = true) by eauto with asmgen.
  assert (Val.offset_ptr (rs base) ofs = Val.add (rs base) (Vint (Ptrofs.to_int ofs))).
  { destruct (rs base); try discriminate. simpl. f_equal; f_equal. symmetry; auto with ptrofs. }
  destruct ty; destruct (preg_of src); inv H; simpl in H0.
- (* int *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H, <- H1, H2, H0 by auto with asmgen; eauto. auto.
  intros; Simpl.
- (* float *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H, <- H1, H2, H0 by auto with asmgen; eauto. auto.
  intros; Simpl.
- (* single *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H, <- H1, H2, H0 by auto with asmgen; eauto. auto.
  intros; Simpl.
- (* any32 *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H, <- H1, H2, H0 by auto with asmgen; eauto. auto.
  intros; Simpl.
- (* any64 *)
  apply indexed_memory_access_correct; intros.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H, <- H1, H2, H0 by auto with asmgen; eauto. auto.
  intros; Simpl.
Qed.

(** Saving the link register *)

Lemma save_lr_correct:
  forall ofs k (rs: regset) m m',
  Mem.storev Mint32 m (Val.offset_ptr rs#IR13 ofs) (rs#IR14) = Some m' ->
  exists rs',
     exec_straight ge fn (save_lr ofs k) rs m k rs' m'
  /\ (forall r, if_preg r = true -> r <> IR12 -> rs'#r = rs#r)
  /\ (save_lr_preserves_R12 ofs = true -> rs'#IR12 = rs#IR12).
Proof.
  intros; unfold save_lr, save_lr_preserves_R12.
  set (n := Ptrofs.to_int ofs). set (n1 := mk_immed_mem_word n).
  assert (EQ: Val.offset_ptr rs#IR13 ofs = Val.add rs#IR13 (Vint n)).
  { destruct rs#IR13; try discriminate. simpl. f_equal; f_equal. unfold n; symmetry; auto with ptrofs. }
  destruct (Int.eq n n1).
- econstructor; split. apply exec_straight_one. simpl; unfold exec_store. rewrite <- EQ, H; reflexivity. auto.
  split. intros; Simpl. intros; Simpl.
- destruct (addimm_correct IR12 IR13 (Int.sub n n1) (Pstr IR14 IR12 (SOimm n1) :: k) rs m)
  as (rs1 & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. 
  apply exec_straight_one. simpl; unfold exec_store.
  rewrite B. rewrite Val.add_assoc. simpl.
  rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg n1)).
  rewrite Int.add_neg_zero. rewrite Int.add_zero. 
  rewrite <- EQ. rewrite C by eauto with asmgen. rewrite H. reflexivity.
  auto.
  split. intros; Simpl. congruence.
Qed.
  
(** Translation of shift immediates *)

Lemma transl_shift_correct:
  forall s (r: ireg) (rs: regset),
  eval_shift_op (transl_shift s r) rs = eval_shift s (rs#r).
Proof.
  intros. destruct s; simpl; auto.
Qed.

(** Translation of conditions *)

Lemma compare_int_spec:
  forall rs v1 v2 m,
  let rs1 := nextinstr (compare_int rs v1 v2 m) in
     rs1#CN = Val.negative (Val.sub v1 v2)
  /\ rs1#CZ = Val.cmpu (Mem.valid_pointer m) Ceq v1 v2
  /\ rs1#CC = Val.cmpu (Mem.valid_pointer m) Cge v1 v2
  /\ rs1#CV = Val.sub_overflow v1 v2.
Proof.
  intros. unfold rs1. intuition.
Qed.

Lemma compare_int_inv:
  forall rs v1 v2 m,
  let rs1 := nextinstr (compare_int rs v1 v2 m) in
  forall r', data_preg r' = true -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1, compare_int.
  repeat Simplif.
Qed.

Lemma int_signed_eq:
  forall x y, Int.eq x y = zeq (Int.signed x) (Int.signed y).
Proof.
  intros. unfold Int.eq. unfold proj_sumbool.
  destruct (zeq (Int.unsigned x) (Int.unsigned y));
  destruct (zeq (Int.signed x) (Int.signed y)); auto.
  elim n. unfold Int.signed. rewrite e; auto.
  elim n. apply Int.eqm_small_eq; auto with ints.
  eapply Int.eqm_trans. apply Int.eqm_sym. apply Int.eqm_signed_unsigned.
  rewrite e. apply Int.eqm_signed_unsigned.
Qed.

Lemma int_not_lt:
  forall x y, negb (Int.lt y x) = (Int.lt x y || Int.eq x y).
Proof.
  intros. unfold Int.lt. rewrite int_signed_eq. unfold proj_sumbool.
  destruct (zlt (Int.signed y) (Int.signed x)).
  rewrite zlt_false. rewrite zeq_false. auto. omega. omega.
  destruct (zeq (Int.signed x) (Int.signed y)).
  rewrite zlt_false. auto. omega.
  rewrite zlt_true. auto. omega.
Qed.

Lemma int_lt_not:
  forall x y, Int.lt y x = negb (Int.lt x y) && negb (Int.eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- int_not_lt. rewrite negb_involutive. auto.
Qed.

Lemma int_not_ltu:
  forall x y, negb (Int.ltu y x) = (Int.ltu x y || Int.eq x y).
Proof.
  intros. unfold Int.ltu, Int.eq.
  destruct (zlt (Int.unsigned y) (Int.unsigned x)).
  rewrite zlt_false. rewrite zeq_false. auto. omega. omega.
  destruct (zeq (Int.unsigned x) (Int.unsigned y)).
  rewrite zlt_false. auto. omega.
  rewrite zlt_true. auto. omega.
Qed.

Lemma int_ltu_not:
  forall x y, Int.ltu y x = negb (Int.ltu x y) && negb (Int.eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- int_not_ltu. rewrite negb_involutive. auto.
Qed.

Lemma cond_for_signed_cmp_correct:
  forall c v1 v2 rs m b,
  Val.cmp_bool c v1 v2 = Some b ->
  eval_testcond (cond_for_signed_cmp c)
                (nextinstr (compare_int rs v1 v2 m)) = Some b.
Proof.
  intros. generalize (compare_int_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_int rs v1 v2 m)).
  intros [A [B [C D]]].
  destruct v1; destruct v2; simpl in H; inv H.
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  simpl. unfold Val.cmp, Val.cmpu.
  rewrite Int.lt_sub_overflow.
  destruct c; simpl.
  destruct (Int.eq i i0); auto.
  destruct (Int.eq i i0); auto.
  destruct (Int.lt i i0); auto.
  rewrite int_not_lt. destruct (Int.lt i i0); simpl; destruct (Int.eq i i0); auto.
  rewrite (int_lt_not i i0). destruct (Int.lt i i0); destruct (Int.eq i i0); reflexivity.
  destruct (Int.lt i i0); reflexivity.
Qed.

Lemma cond_for_unsigned_cmp_correct:
  forall c v1 v2 rs m b,
  Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
  eval_testcond (cond_for_unsigned_cmp c)
                (nextinstr (compare_int rs v1 v2 m)) = Some b.
Proof.
  intros. generalize (compare_int_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_int rs v1 v2 m)).
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite B; rewrite C. unfold Val.cmpu, Val.cmp.
  destruct v1; destruct v2; simpl in H; inv H.
(* int int *)
  destruct c; simpl; auto.
  destruct (Int.eq i i0); reflexivity.
  destruct (Int.eq i i0); auto.
  destruct (Int.ltu i i0); auto.
  rewrite (int_not_ltu i i0).  destruct (Int.ltu i i0); destruct (Int.eq i i0); auto.
  rewrite (int_ltu_not i i0). destruct (Int.ltu i i0); destruct (Int.eq i i0); reflexivity.
  destruct (Int.ltu i i0); reflexivity.
(* int ptr *)
  destruct (Int.eq i Int.zero &&
    (Mem.valid_pointer m b0 (Ptrofs.unsigned i0) || Mem.valid_pointer m b0 (Ptrofs.unsigned i0 - 1))) eqn:?; try discriminate.
  destruct c; simpl in *; inv H1.
  rewrite Heqb1; reflexivity.
  rewrite Heqb1; reflexivity.
(* ptr int *)
  destruct (Int.eq i0 Int.zero &&
    (Mem.valid_pointer m b0 (Ptrofs.unsigned i) || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1))) eqn:?; try discriminate.
  destruct c; simpl in *; inv H1.
  rewrite Heqb1; reflexivity.
  rewrite Heqb1; reflexivity.
(* ptr ptr *)
  simpl.
  fold (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i)) in *.
  fold (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)) in *.
  destruct (eq_block b0 b1).
  destruct (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i) &&
            Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)); inversion H1.
  destruct c; simpl; auto.
  destruct (Ptrofs.eq i i0); reflexivity.
  destruct (Ptrofs.eq i i0); auto.
  destruct (Ptrofs.ltu i i0); auto.
  rewrite (Ptrofs.not_ltu i i0). destruct (Ptrofs.ltu i i0); simpl; destruct (Ptrofs.eq i i0); auto.
  rewrite (Ptrofs.ltu_not i i0). destruct (Ptrofs.ltu i i0); destruct (Ptrofs.eq i i0); reflexivity.
  destruct (Ptrofs.ltu i i0); reflexivity.
  destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned i) &&
            Mem.valid_pointer m b1 (Ptrofs.unsigned i0)); try discriminate.
  destruct c; simpl in *; inv H1; reflexivity.
Qed.

Lemma compare_float_spec:
  forall rs f1 f2,
  let rs1 := nextinstr (compare_float rs (Vfloat f1) (Vfloat f2)) in
     rs1#CN = Val.of_bool (Float.cmp Clt f1 f2)
  /\ rs1#CZ = Val.of_bool (Float.cmp Ceq f1 f2)
  /\ rs1#CC = Val.of_bool (negb (Float.cmp Clt f1 f2))
  /\ rs1#CV = Val.of_bool (negb (Float.cmp Ceq f1 f2 || Float.cmp Clt f1 f2 || Float.cmp Cgt f1 f2)).
Proof.
  intros. intuition.
Qed.

Lemma compare_float_inv:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_float rs v1 v2) in
  forall r', data_preg r' = true -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1, compare_float.
  assert (nextinstr (rs#CN <- Vundef #CZ <- Vundef #CC <- Vundef #CV <- Vundef) r' = rs r').
  { repeat Simplif. }
  destruct v1; destruct v2; auto.
  repeat Simplif.
Qed.

Lemma compare_float_nextpc:
  forall rs v1 v2,
  nextinstr (compare_float rs v1 v2) PC = Val.offset_ptr (rs PC) Ptrofs.one.
Proof.
  intros. unfold compare_float. destruct v1; destruct v2; reflexivity.
Qed.

Lemma cond_for_float_cmp_correct:
  forall c n1 n2 rs,
  eval_testcond (cond_for_float_cmp c)
                (nextinstr (compare_float rs (Vfloat n1) (Vfloat n2))) =
  Some(Float.cmp c n1 n2).
Proof.
  intros.
  generalize (compare_float_spec rs n1 n2).
  set (rs' := nextinstr (compare_float rs (Vfloat n1) (Vfloat n2))).
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  destruct c; simpl.
(* eq *)
  destruct (Float.cmp Ceq n1 n2); auto.
(* ne *)
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq n1 n2); auto.
(* lt *)
  destruct (Float.cmp Clt n1 n2); auto.
(* le *)
  rewrite Float.cmp_le_lt_eq.
  destruct (Float.cmp Clt n1 n2); destruct (Float.cmp Ceq n1 n2); auto.
(* gt *)
  destruct (Float.cmp Ceq n1 n2) eqn:EQ;
  destruct (Float.cmp Clt n1 n2) eqn:LT;
  destruct (Float.cmp Cgt n1 n2) eqn:GT; auto.
  exfalso; eapply Float.cmp_lt_gt_false; eauto.
  exfalso; eapply Float.cmp_gt_eq_false; eauto.
  exfalso; eapply Float.cmp_lt_gt_false; eauto.
(* ge *)
  rewrite Float.cmp_ge_gt_eq.
  destruct (Float.cmp Ceq n1 n2) eqn:EQ;
  destruct (Float.cmp Clt n1 n2) eqn:LT;
  destruct (Float.cmp Cgt n1 n2) eqn:GT; auto.
  exfalso; eapply Float.cmp_lt_eq_false; eauto.
  exfalso; eapply Float.cmp_lt_eq_false; eauto.
  exfalso; eapply Float.cmp_lt_gt_false; eauto.
Qed.

Lemma cond_for_float_not_cmp_correct:
  forall c n1 n2 rs,
  eval_testcond (cond_for_float_not_cmp c)
                (nextinstr (compare_float rs (Vfloat n1) (Vfloat n2)))=
  Some(negb(Float.cmp c n1 n2)).
Proof.
  intros.
  generalize (compare_float_spec rs n1 n2).
  set (rs' := nextinstr (compare_float rs (Vfloat n1) (Vfloat n2))).
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  destruct c; simpl.
(* eq *)
  destruct (Float.cmp Ceq n1 n2); auto.
(* ne *)
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq n1 n2); auto.
(* lt *)
  destruct (Float.cmp Clt n1 n2); auto.
(* le *)
  rewrite Float.cmp_le_lt_eq.
  destruct (Float.cmp Clt n1 n2) eqn:LT; destruct (Float.cmp Ceq n1 n2) eqn:EQ; auto.
(* gt *)
  destruct (Float.cmp Ceq n1 n2) eqn:EQ;
  destruct (Float.cmp Clt n1 n2) eqn:LT;
  destruct (Float.cmp Cgt n1 n2) eqn:GT; auto.
  exfalso; eapply Float.cmp_lt_gt_false; eauto.
  exfalso; eapply Float.cmp_gt_eq_false; eauto.
  exfalso; eapply Float.cmp_lt_gt_false; eauto.
(* ge *)
  rewrite Float.cmp_ge_gt_eq.
  destruct (Float.cmp Ceq n1 n2) eqn:EQ;
  destruct (Float.cmp Clt n1 n2) eqn:LT;
  destruct (Float.cmp Cgt n1 n2) eqn:GT; auto.
  exfalso; eapply Float.cmp_lt_eq_false; eauto.
  exfalso; eapply Float.cmp_lt_eq_false; eauto.
  exfalso; eapply Float.cmp_lt_gt_false; eauto.
Qed.

Lemma compare_float32_spec:
  forall rs f1 f2,
  let rs1 := nextinstr (compare_float32 rs (Vsingle f1) (Vsingle f2)) in
     rs1#CN = Val.of_bool (Float32.cmp Clt f1 f2)
  /\ rs1#CZ = Val.of_bool (Float32.cmp Ceq f1 f2)
  /\ rs1#CC = Val.of_bool (negb (Float32.cmp Clt f1 f2))
  /\ rs1#CV = Val.of_bool (negb (Float32.cmp Ceq f1 f2 || Float32.cmp Clt f1 f2 || Float32.cmp Cgt f1 f2)).
Proof.
  intros. intuition.
Qed.

Lemma compare_float32_inv:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_float32 rs v1 v2) in
  forall r', data_preg r' = true -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1, compare_float32.
  assert (nextinstr (rs#CN <- Vundef #CZ <- Vundef #CC <- Vundef #CV <- Vundef) r' = rs r').
  { repeat Simplif. }
  destruct v1; destruct v2; auto.
  repeat Simplif.
Qed.

Lemma compare_float32_nextpc:
  forall rs v1 v2,
  nextinstr (compare_float32 rs v1 v2) PC = Val.offset_ptr (rs PC) Ptrofs.one.
Proof.
  intros. unfold compare_float32. destruct v1; destruct v2; reflexivity.
Qed.

Lemma cond_for_float32_cmp_correct:
  forall c n1 n2 rs,
  eval_testcond (cond_for_float_cmp c)
                (nextinstr (compare_float32 rs (Vsingle n1) (Vsingle n2))) =
  Some(Float32.cmp c n1 n2).
Proof.
  intros.
  generalize (compare_float32_spec rs n1 n2).
  set (rs' := nextinstr (compare_float32 rs (Vsingle n1) (Vsingle n2))).
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  destruct c; simpl.
(* eq *)
  destruct (Float32.cmp Ceq n1 n2); auto.
(* ne *)
  rewrite Float32.cmp_ne_eq. destruct (Float32.cmp Ceq n1 n2); auto.
(* lt *)
  destruct (Float32.cmp Clt n1 n2); auto.
(* le *)
  rewrite Float32.cmp_le_lt_eq.
  destruct (Float32.cmp Clt n1 n2); destruct (Float32.cmp Ceq n1 n2); auto.
(* gt *)
  destruct (Float32.cmp Ceq n1 n2) eqn:EQ;
  destruct (Float32.cmp Clt n1 n2) eqn:LT;
  destruct (Float32.cmp Cgt n1 n2) eqn:GT; auto.
  exfalso; eapply Float32.cmp_lt_gt_false; eauto.
  exfalso; eapply Float32.cmp_gt_eq_false; eauto.
  exfalso; eapply Float32.cmp_lt_gt_false; eauto.
(* ge *)
  rewrite Float32.cmp_ge_gt_eq.
  destruct (Float32.cmp Ceq n1 n2) eqn:EQ;
  destruct (Float32.cmp Clt n1 n2) eqn:LT;
  destruct (Float32.cmp Cgt n1 n2) eqn:GT; auto.
  exfalso; eapply Float32.cmp_lt_eq_false; eauto.
  exfalso; eapply Float32.cmp_lt_eq_false; eauto.
  exfalso; eapply Float32.cmp_lt_gt_false; eauto.
Qed.

Lemma cond_for_float32_not_cmp_correct:
  forall c n1 n2 rs,
  eval_testcond (cond_for_float_not_cmp c)
                (nextinstr (compare_float32 rs (Vsingle n1) (Vsingle n2)))=
  Some(negb(Float32.cmp c n1 n2)).
Proof.
  intros.
  generalize (compare_float32_spec rs n1 n2).
  set (rs' := nextinstr (compare_float32 rs (Vsingle n1) (Vsingle n2))).
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  destruct c; simpl.
(* eq *)
  destruct (Float32.cmp Ceq n1 n2); auto.
(* ne *)
  rewrite Float32.cmp_ne_eq. destruct (Float32.cmp Ceq n1 n2); auto.
(* lt *)
  destruct (Float32.cmp Clt n1 n2); auto.
(* le *)
  rewrite Float32.cmp_le_lt_eq.
  destruct (Float32.cmp Clt n1 n2) eqn:LT; destruct (Float32.cmp Ceq n1 n2) eqn:EQ; auto.
(* gt *)
  destruct (Float32.cmp Ceq n1 n2) eqn:EQ;
  destruct (Float32.cmp Clt n1 n2) eqn:LT;
  destruct (Float32.cmp Cgt n1 n2) eqn:GT; auto.
  exfalso; eapply Float32.cmp_lt_gt_false; eauto.
  exfalso; eapply Float32.cmp_gt_eq_false; eauto.
  exfalso; eapply Float32.cmp_lt_gt_false; eauto.
(* ge *)
  rewrite Float32.cmp_ge_gt_eq.
  destruct (Float32.cmp Ceq n1 n2) eqn:EQ;
  destruct (Float32.cmp Clt n1 n2) eqn:LT;
  destruct (Float32.cmp Cgt n1 n2) eqn:GT; auto.
  exfalso; eapply Float32.cmp_lt_eq_false; eauto.
  exfalso; eapply Float32.cmp_lt_eq_false; eauto.
  exfalso; eapply Float32.cmp_lt_gt_false; eauto.
Qed.

Ltac ArgsInv :=
  repeat (match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H
  end);
  subst;
  repeat (match goal with
  | [ H: ireg_of ?x = OK ?y |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *
  | [ H: freg_of ?x = OK ?y |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *
  end).

Lemma transl_cond_correct:
  forall cond args k rs m c,
  transl_cond cond args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ match eval_condition cond (map rs (map preg_of args)) m with
     | Some b => eval_testcond (cond_for_cond cond) rs' = Some b
                 /\ eval_testcond (cond_for_cond (negate_condition cond)) rs' = Some (negb b)
     | None => True
     end
  /\ forall r, data_preg r = true -> rs'#r = rs r.
Proof.
  intros until c; intros TR.
  unfold transl_cond in TR; destruct cond; ArgsInv.
- (* Ccomp *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmp_bool c0 (rs x) (rs x0)) eqn:CMP; auto.
  split; apply cond_for_signed_cmp_correct; auto. rewrite Val.negate_cmp_bool, CMP; auto.
  apply compare_int_inv.
- (* Ccompu *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs x) (rs x0)) eqn:CMP; auto.
  split; apply cond_for_unsigned_cmp_correct; auto. rewrite Val.negate_cmpu_bool, CMP; auto.
  apply compare_int_inv.
- (* Ccompshift *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite transl_shift_correct.
  destruct (Val.cmp_bool c0 (rs x) (eval_shift s (rs x0))) eqn:CMP; auto.
  split; apply cond_for_signed_cmp_correct; auto. rewrite Val.negate_cmp_bool, CMP; auto.
  apply compare_int_inv.
- (* Ccompushift *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite transl_shift_correct.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs x) (eval_shift s (rs x0))) eqn:CMP; auto.
  split; apply cond_for_unsigned_cmp_correct; auto. rewrite Val.negate_cmpu_bool, CMP; auto.
  apply compare_int_inv.
- (* Ccompimm *)
  destruct (is_immed_arith i).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmp_bool c0 (rs x) (Vint i)) eqn:CMP; auto.
  split; apply cond_for_signed_cmp_correct; auto. rewrite Val.negate_cmp_bool, CMP; auto.
  apply compare_int_inv.
  destruct (is_immed_arith (Int.neg i)).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmp_bool c0 (rs x) (Vint i)) eqn:CMP; auto.
  split; apply cond_for_signed_cmp_correct; rewrite Int.neg_involutive; auto.
  rewrite Val.negate_cmp_bool, CMP; auto.
  apply compare_int_inv.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  econstructor.
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite R; eauto with asmgen. auto.
  split. rewrite <- R by (eauto with asmgen).
  destruct (Val.cmp_bool c0 (rs' x) (Vint i)) eqn:CMP; auto.
  split; apply cond_for_signed_cmp_correct; auto. rewrite Val.negate_cmp_bool, CMP; auto.
  intros. rewrite compare_int_inv by auto. auto with asmgen.
- (* Ccompuimm *)
  destruct (is_immed_arith i).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs x) (Vint i)) eqn:CMP; auto.
  split; apply cond_for_unsigned_cmp_correct; auto. rewrite Val.negate_cmpu_bool, CMP; auto.
  apply compare_int_inv.
  destruct (is_immed_arith (Int.neg i)).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs x) (Vint i)) eqn:CMP; auto.
  split; apply cond_for_unsigned_cmp_correct; rewrite Int.neg_involutive; auto.
  rewrite Val.negate_cmpu_bool, CMP; auto.
  apply compare_int_inv.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  econstructor.
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite R; eauto with asmgen. auto.
  split. rewrite <- R by (eauto with asmgen).
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs' x) (Vint i)) eqn:CMP; auto.
  split; apply cond_for_unsigned_cmp_correct; auto. rewrite Val.negate_cmpu_bool, CMP; auto.
  intros. rewrite compare_int_inv by auto. auto with asmgen.
- (* Ccompf *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. apply compare_float_nextpc.
  split. destruct (Val.cmpf_bool c0 (rs x) (rs x0)) eqn:CMP; auto.
  destruct (rs x); try discriminate. destruct (rs x0); try discriminate.
  simpl in CMP. inv CMP.
  split. apply cond_for_float_cmp_correct. apply cond_for_float_not_cmp_correct.
  apply compare_float_inv.
- (* Cnotcompf *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. apply compare_float_nextpc.
  split. destruct (Val.cmpf_bool c0 (rs x) (rs x0)) eqn:CMP; auto.
  destruct (rs x); try discriminate. destruct (rs x0); try discriminate.
  simpl in CMP. inv CMP.
Local Opaque compare_float. simpl.
  split. apply cond_for_float_not_cmp_correct. rewrite negb_involutive. apply cond_for_float_cmp_correct.
  exact I.
  apply compare_float_inv.
- (* Ccompfzero *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. apply compare_float_nextpc.
  split. destruct (Val.cmpf_bool c0 (rs x) (Vfloat Float.zero)) eqn:CMP; auto.
  destruct (rs x); try discriminate.
  simpl in CMP. inv CMP.
  split. apply cond_for_float_cmp_correct. apply cond_for_float_not_cmp_correct.
  apply compare_float_inv.
- (* Cnotcompfzero *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. apply compare_float_nextpc.
  split. destruct (Val.cmpf_bool c0 (rs x) (Vfloat Float.zero)) eqn:CMP; auto.
  destruct (rs x); try discriminate. simpl in CMP. inv CMP.
Local Opaque compare_float. simpl.
  split. apply cond_for_float_not_cmp_correct. rewrite negb_involutive. apply cond_for_float_cmp_correct.
  exact I.
  apply compare_float_inv.
- (* Ccompfs *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. apply compare_float32_nextpc.
  split. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) eqn:CMP; auto.
  destruct (rs x); try discriminate. destruct (rs x0); try discriminate.
  simpl in CMP. inv CMP.
  split. apply cond_for_float32_cmp_correct. apply cond_for_float32_not_cmp_correct.
  apply compare_float32_inv.
- (* Cnotcompfs *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. apply compare_float32_nextpc.
  split. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) eqn:CMP; auto.
  destruct (rs x); try discriminate. destruct (rs x0); try discriminate.
  simpl in CMP. inv CMP.
Local Opaque compare_float32. simpl.
  split. apply cond_for_float32_not_cmp_correct. rewrite negb_involutive. apply cond_for_float32_cmp_correct.
  exact I.
  apply compare_float32_inv.
- (* Ccompfszero *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. apply compare_float32_nextpc.
  split. destruct (Val.cmpfs_bool c0 (rs x) (Vsingle Float32.zero)) eqn:CMP; auto.
  destruct (rs x); try discriminate.
  simpl in CMP. inv CMP.
  split. apply cond_for_float32_cmp_correct. apply cond_for_float32_not_cmp_correct.
  apply compare_float32_inv.
- (* Cnotcompfzero *)
  econstructor.
  split. apply exec_straight_one. simpl. eauto. apply compare_float32_nextpc.
  split. destruct (Val.cmpfs_bool c0 (rs x) (Vsingle Float32.zero)) eqn:CMP; auto.
  destruct (rs x); try discriminate. simpl in CMP. inv CMP.
  simpl. split. apply cond_for_float32_not_cmp_correct. rewrite negb_involutive. apply cond_for_float32_cmp_correct.
  exact I.
  apply compare_float32_inv.
Qed.

(** Translation of arithmetic operations. *)

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity ]
  | split; [try rewrite transl_shift_correct; repeat Simpl | intros; repeat Simpl] ].

Lemma transl_op_correct_same:
  forall op args res k c (rs: regset) m v,
  transl_op op args res k = OK c ->
  eval_operation ge rs#IR13 op (map rs (map preg_of args)) m = Some v ->
  match op with Ocmp _ => False | Oaddrstack _ => False | _ => True end ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV NOCMP.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; inv EV; try (TranslOpSimpl; fail).
  (* Omove *)
  destruct (preg_of res) eqn:RES; try discriminate;
  destruct (preg_of m0) eqn:ARG; inv TR.
  econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  (* Ointconst *)
  generalize (loadimm_correct x i k rs m). intros [rs' [A [B C]]].
  exists rs'; auto with asmgen.
  (* Oaddrstack *)
  contradiction.
  (* Ocast8signed *)
  destruct Archi.thumb2_support.
  econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  destruct (rs x0); auto; simpl. rewrite Int.shru_zero. reflexivity.
  set (rs1 := nextinstr_nf (rs#x <- (Val.shl rs#x0 (Vint (Int.repr 24))))).
  set (rs2 := nextinstr_nf (rs1#x <- (Val.shr rs1#x (Vint (Int.repr 24))))).
  exists rs2.
  split. apply exec_straight_two with rs1 m; auto.
  split. unfold rs2; Simpl. unfold rs1; Simpl.
  unfold Val.shr, Val.shl; destruct (rs x0); auto.
  change (Int.ltu (Int.repr 24) Int.iwordsize) with true; simpl.
  f_equal. symmetry. apply (Int.sign_ext_shr_shl 8). compute; auto.
  intros. unfold rs2, rs1; Simpl.
  (* Ocast16signed *)
  destruct Archi.thumb2_support.
  econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  destruct (rs x0); auto; simpl. rewrite Int.shru_zero. reflexivity.
  set (rs1 := nextinstr_nf (rs#x <- (Val.shl rs#x0 (Vint (Int.repr 16))))).
  set (rs2 := nextinstr_nf (rs1#x <- (Val.shr rs1#x (Vint (Int.repr 16))))).
  exists rs2.
  split. apply exec_straight_two with rs1 m; auto.
  split. unfold rs2; Simpl. unfold rs1; Simpl.
  unfold Val.shr, Val.shl; destruct (rs x0); auto.
  change (Int.ltu (Int.repr 16) Int.iwordsize) with true; simpl.
  f_equal. symmetry. apply (Int.sign_ext_shr_shl 16). compute; auto.
  intros. unfold rs2, rs1; Simpl.
  (* Oaddimm *)
  generalize (addimm_correct x x0 i k rs m).
  intros [rs' [A [B C]]].
  exists rs'; auto with asmgen.
  (* Orsbimm *)
  generalize (rsubimm_correct x x0 i k rs m).
  intros [rs' [A [B C]]].
  exists rs'; auto with asmgen.
  (* divs *)
Local Transparent destroyed_by_op.
  econstructor. split. apply exec_straight_one. simpl. rewrite H0. reflexivity. auto.
  split. Simpl. simpl; intros. intuition Simpl.
  (* divu *)
  econstructor. split. apply exec_straight_one. simpl. rewrite H0. reflexivity. auto.
  split. Simpl. simpl; intros. intuition Simpl.
  (* Oandimm *)
  generalize (andimm_correct x x0 i k rs m).
  intros [rs' [A [B C]]].
  exists rs'; auto with asmgen.
  (* Oorimm *)
  generalize (orimm_correct x x0 i k rs m).
  intros [rs' [A [B C]]].
  exists rs'; auto with asmgen.
  (* Oxorimm *)
  generalize (xorimm_correct x x0 i k rs m).
  intros [rs' [A [B C]]].
  exists rs'; auto with asmgen.
  (* Oshrximm *)
  destruct (rs x0) eqn: X0; simpl in H0; try discriminate.
  destruct (Int.ltu i (Int.repr 31)) eqn: LTU; inv H0.
  revert EQ2. predSpec Int.eq Int.eq_spec i Int.zero; intros EQ2.
  (* i = 0 *)
  inv EQ2. econstructor.
  split. apply exec_straight_one. simpl. reflexivity. auto.
  split. Simpl. unfold Int.shrx. rewrite Int.shl_zero. unfold Int.divs.
  change (Int.signed Int.one) with 1. rewrite Z.quot_1_r. rewrite Int.repr_signed. auto.
  intros. Simpl.
  (* i <> 0 *)
  inv EQ2.
  assert (LTU': Int.ltu (Int.sub Int.iwordsize i) Int.iwordsize = true).
  {
    generalize (Int.ltu_inv _ _ LTU). intros.
    unfold Int.sub, Int.ltu. rewrite Int.unsigned_repr_wordsize.
    rewrite Int.unsigned_repr. apply zlt_true.
    assert (Int.unsigned i <> 0).
    { red; intros; elim H. rewrite <- (Int.repr_unsigned i). rewrite H1; reflexivity. }
    omega.
    change (Int.unsigned (Int.repr 31)) with (Int.zwordsize - 1) in H0.
    generalize Int.wordsize_max_unsigned; omega.
  }
  assert (LTU'': Int.ltu i Int.iwordsize = true).
  {
    generalize (Int.ltu_inv _ _ LTU). intros.
    unfold Int.ltu. rewrite Int.unsigned_repr_wordsize. apply zlt_true.
    change (Int.unsigned (Int.repr 31)) with (Int.zwordsize - 1) in H0.
    omega.
  }
  set (j := Int.sub Int.iwordsize i) in *.
  set (rs1 := nextinstr_nf (rs#IR14 <- (Val.shr (Vint i0) (Vint (Int.repr 31))))).
  set (rs2 := nextinstr_nf (rs1#IR14 <- (Val.add (Vint i0) (Val.shru rs1#IR14 (Vint j))))).
  set (rs3 := nextinstr_nf (rs2#x <- (Val.shr rs2#IR14 (Vint i)))).
  exists rs3; split.
  apply exec_straight_three with rs1 m rs2 m.
  simpl. rewrite X0; reflexivity.
  simpl. f_equal. Simpl. replace (rs1 x0) with (rs x0). rewrite X0; reflexivity.
  unfold rs1; Simpl.
  reflexivity.
  auto. auto. auto.
  split. unfold rs3; Simpl. unfold rs2; Simpl. unfold rs1; Simpl.
  simpl. change (Int.ltu (Int.repr 31) Int.iwordsize) with true. simpl.
  rewrite LTU'; simpl. rewrite LTU''; simpl.
  f_equal. symmetry. apply Int.shrx_shr_2. assumption.
  intros. unfold rs3; Simpl. unfold rs2; Simpl. unfold rs1; Simpl.
  (* intoffloat *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
Transparent destroyed_by_op.
  simpl. intuition Simpl.
  (* intuoffloat *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  simpl. intuition Simpl.
  (* floatofint *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  intuition Simpl.
  (* floatofintu *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  intuition Simpl.
  (* intofsingle *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  simpl. intuition Simpl.
  (* intuofsingle *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  simpl. intuition Simpl.
  (* singleofint *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  intuition Simpl.
  (* singleofintu *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  intuition Simpl.
  (* Ocmp *)
  contradiction.
Qed.

Lemma transl_op_correct:
  forall op args res k c (rs: regset) m v,
  transl_op op args res k = OK c ->
  eval_operation ge rs#IR13 op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs'#r = rs#r.
Proof.
  intros.
  assert (SAME:
      (exists rs', exec_straight ge fn c rs m k rs' m
           /\ rs'#(preg_of res) = v
           /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs'#r = rs#r) ->
       exists rs', exec_straight ge fn c rs m k rs' m
           /\ Val.lessdef v rs'#(preg_of res)
           /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs'#r = rs#r).
  { intros (rs' & A & B & C). subst v; exists rs'; auto. }
  destruct op; try (apply SAME; eapply transl_op_correct_same; eauto; fail).
- (* Oaddrstack *)
  clear SAME; simpl in *; ArgsInv.
  destruct (addimm_correct x IR13 (Ptrofs.to_int i) k rs m) as [rs' [EX [RES OTH]]].
  exists rs'; split. auto. split.
  rewrite RES; inv H0. destruct (rs IR13); simpl; auto. rewrite Ptrofs.of_int_to_int; auto.
  intros; apply OTH; eauto with asmgen.
- (* Ocmp *)
  clear SAME. simpl in H. monadInv H. simpl in H0. inv H0.
  rewrite (ireg_of_eq _ _ EQ).
  exploit transl_cond_correct; eauto. instantiate (1 := rs). instantiate (1 := m). intros [rs1 [A [B C]]].
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl.
  destruct (eval_condition c0 rs ## (preg_of ## args) m) as [b|]; simpl; auto.
  destruct B as [B1 B2]; rewrite B1. destruct b; auto.
Qed.

(** Translation of loads and stores. *)

Remark val_add_add_zero:
  forall v1 v2, Val.add v1 v2 = Val.add (Val.add v1 v2) (Vint Int.zero).
Proof.
  intros. destruct v1; destruct v2; simpl; auto.
  rewrite Int.add_zero; auto.
  rewrite Ptrofs.add_zero; auto.
  rewrite Ptrofs.add_zero; auto.
Qed.

Lemma transl_memory_access_correct:
  forall (P: regset -> Prop) (mk_instr_imm: ireg -> int -> instruction)
         (mk_instr_gen: option (ireg -> shift_op -> instruction))
         (mk_immed: int -> int)
         addr args k c (rs: regset) a m m',
  transl_memory_access mk_instr_imm mk_instr_gen mk_immed addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  match a with Vptr _ _ => True | _ => False end ->
  (forall (r1: ireg) (rs1: regset) n k,
    Val.add rs1#r1 (Vint n) = a ->
    (forall (r: preg), if_preg r = true -> r <> IR14 -> rs1 r = rs r) ->
    exists rs',
    exec_straight ge fn (mk_instr_imm r1 n :: k) rs1 m k rs' m' /\ P rs') ->
  match mk_instr_gen with
  | None => True
  | Some mk =>
      (forall (r1: ireg) (sa: shift_op) k,
      Val.add rs#r1 (eval_shift_op sa rs) = a ->
       exists rs',
      exec_straight ge fn (mk r1 sa :: k) rs m k rs' m' /\ P rs')
  end ->
  exists rs',
    exec_straight ge fn c rs m k rs' m' /\ P rs'.
Proof.
  intros until m'; intros TR EA ADDR MK1 MK2.
  unfold transl_memory_access in TR; destruct addr; ArgsInv; simpl in EA; inv EA.
  (* Aindexed *)
  apply indexed_memory_access_correct. exact MK1.
  (* Aindexed2 *)
  destruct mk_instr_gen as [mk | ]; monadInv TR. apply MK2.
  simpl. erewrite ! ireg_of_eq; eauto.
  (* Aindexed2shift *)
  destruct mk_instr_gen as [mk | ]; monadInv TR. apply MK2.
  erewrite ! ireg_of_eq; eauto. rewrite transl_shift_correct. auto.
  (* Ainstack *)
  inv TR. apply indexed_memory_access_correct. intros. eapply MK1; eauto.
  rewrite H. destruct (rs IR13); try contradiction. simpl. f_equal; f_equal. auto with ptrofs.
Qed.

Lemma transl_load_int_correct:
  forall mk_instr is_immed dst addr args k c (rs: regset) a chunk m v,
  transl_memory_access_int mk_instr is_immed dst addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  (forall (r1 r2: ireg) (sa: shift_op) (rs1: regset),
    exec_instr ge fn (mk_instr r1 r2 sa) rs1 m =
    exec_load chunk (Val.add rs1#r2 (eval_shift_op sa rs1)) r1 rs1 m) ->
  exists rs',
      exec_straight ge fn c rs m k rs' m
   /\ rs'#(preg_of dst) = v
   /\ forall r, data_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros. monadInv H. erewrite ireg_of_eq by eauto.
  eapply transl_memory_access_correct; eauto.
  destruct a; discriminate || trivial.
  intros; simpl. econstructor; split. apply exec_straight_one.
  rewrite H2. unfold exec_load. simpl eval_shift_op. rewrite H. rewrite H1. eauto. auto.
  split. Simpl. intros; Simpl.
  simpl; intros.
  econstructor; split. apply exec_straight_one.
  rewrite H2. unfold exec_load. rewrite H. rewrite H1. eauto. auto.
  split. Simpl. intros; Simpl.
Qed.

Lemma transl_load_float_correct:
  forall mk_instr is_immed dst addr args k c (rs: regset) a chunk m v,
  transl_memory_access_float mk_instr is_immed dst addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  (forall (r1: freg) (r2: ireg) (n: int) (rs1: regset),
    exec_instr ge fn (mk_instr r1 r2 n) rs1 m =
    exec_load chunk (Val.add rs1#r2 (Vint n)) r1 rs1 m) ->
  exists rs',
      exec_straight ge fn c rs m k rs' m
   /\ rs'#(preg_of dst) = v
   /\ forall r, data_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros. monadInv H. erewrite freg_of_eq by eauto.
  eapply transl_memory_access_correct; eauto.
  destruct a; discriminate || trivial.
  intros; simpl. econstructor; split. apply exec_straight_one.
  rewrite H2. unfold exec_load. rewrite H. rewrite H1. eauto. auto.
  split. Simpl. intros; Simpl.
  simpl; auto.
Qed.

Lemma transl_store_int_correct:
  forall mr mk_instr is_immed src addr args k c (rs: regset) a chunk m m',
  transl_memory_access_int mk_instr is_immed src addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  (forall (r1 r2: ireg) (sa: shift_op) (rs1: regset),
    exec_instr ge fn (mk_instr r1 r2 sa) rs1 m =
    exec_store chunk (Val.add rs1#r2 (eval_shift_op sa rs1)) r1 rs1 m) ->
  exists rs',
      exec_straight ge fn c rs m k rs' m'
   /\ forall r, data_preg r = true -> preg_notin r mr -> rs'#r = rs#r.
Proof.
  intros. assert (DR: data_preg (preg_of src) = true) by eauto with asmgen.
  monadInv H. erewrite ireg_of_eq in * by eauto.
  eapply transl_memory_access_correct; eauto.
  destruct a; discriminate || trivial.
  intros; simpl. econstructor; split. apply exec_straight_one.
  rewrite H2. unfold exec_store. simpl eval_shift_op. rewrite H. rewrite H3; eauto with asmgen.
  rewrite H1. eauto. auto.
  intros; Simpl.
  simpl; intros.
  econstructor; split. apply exec_straight_one.
  rewrite H2. unfold exec_store. rewrite H. rewrite H1. eauto. auto.
  intros; Simpl.
Qed.

Lemma transl_store_float_correct:
  forall mr mk_instr is_immed src addr args k c (rs: regset) a chunk m m',
  transl_memory_access_float mk_instr is_immed src addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  (forall (r1: freg) (r2: ireg) (n: int) (rs1: regset),
    exec_instr ge fn (mk_instr r1 r2 n) rs1 m =
    exec_store chunk (Val.add rs1#r2 (Vint n)) r1 rs1 m) ->
  exists rs',
      exec_straight ge fn c rs m k rs' m'
   /\ forall r, data_preg r = true -> preg_notin r mr -> rs'#r = rs#r.
Proof.
  intros. assert (DR: data_preg (preg_of src) = true) by eauto with asmgen.
  monadInv H. erewrite freg_of_eq in * by eauto.
  eapply transl_memory_access_correct; eauto.
  destruct a; discriminate || trivial.
  intros; simpl. econstructor; split. apply exec_straight_one.
  rewrite H2. unfold exec_store. rewrite H. rewrite H3; auto with asmgen. rewrite H1. eauto. auto.
  intros; Simpl.
  simpl; auto.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) a m v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
      exec_straight ge fn c rs m k rs' m
   /\ rs'#(preg_of dst) = v
   /\ forall r, data_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros. destruct chunk; simpl in H.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_int_correct; eauto.
  discriminate.
  eapply transl_load_float_correct; eauto.
  eapply transl_load_float_correct; eauto.
  discriminate.
  discriminate.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) a m m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
      exec_straight ge fn c rs m k rs' m'
   /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_store chunk addr) -> rs'#r = rs#r.
Proof.
  intros. destruct chunk; simpl in H.
- assert (Mem.storev Mint8unsigned m a (rs (preg_of src)) = Some m').
    rewrite <- H1. destruct a; simpl; auto. symmetry. apply Mem.store_signed_unsigned_8.
  clear H1. eapply transl_store_int_correct; eauto.
- eapply transl_store_int_correct; eauto.
- assert (Mem.storev Mint16unsigned m a (rs (preg_of src)) = Some m').
    rewrite <- H1. destruct a; simpl; auto. symmetry. apply Mem.store_signed_unsigned_16.
  clear H1. eapply transl_store_int_correct; eauto.
- eapply transl_store_int_correct; eauto.
- eapply transl_store_int_correct; eauto.
- discriminate.
- eapply transl_store_float_correct; eauto.
- eapply transl_store_float_correct; eauto.
- discriminate.
- discriminate.
Qed.

End CONSTRUCTORS.

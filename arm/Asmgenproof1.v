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
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.
Require Import Asmgenproof0.

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

(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of ARM constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Decomposition of an integer constant *)

Lemma decompose_int_rec_or:
  forall N n p x, List.fold_left Int.or (decompose_int_rec N n p) x = Int.or x n.
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

Lemma decompose_int_rec_xor:
  forall N n p x, List.fold_left Int.xor (decompose_int_rec N n p) x = Int.xor x n.
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

Lemma decompose_int_rec_add:
  forall N n p x, List.fold_left Int.add (decompose_int_rec N n p) x = Int.add x n.
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

Remark decompose_int_rec_nil:
  forall N n p, decompose_int_rec N n p = nil -> n = Int.zero.
Proof.
  intros. generalize (decompose_int_rec_or N n p Int.zero). rewrite H. simpl. 
  rewrite Int.or_commut; rewrite Int.or_zero; auto.
Qed.

Lemma decompose_int_general:
  forall (f: val -> int -> val) (g: int -> int -> int),
  (forall v1 n2 n3, f (f v1 n2) n3 = f v1 (g n2 n3)) ->
  (forall n1 n2 n3, g (g n1 n2) n3 = g n1 (g n2 n3)) ->
  (forall n, g Int.zero n = n) ->
  (forall N n p x, List.fold_left g (decompose_int_rec N n p) x = g x n) ->
  forall n v,
  List.fold_left f (decompose_int n) v = f v n.
Proof.
  intros f g DISTR ASSOC ZERO DECOMP.
  assert (A: forall l x y, g x (fold_left g l y) = fold_left g l (g x y)).
    induction l; intros; simpl. auto. rewrite IHl. decEq. rewrite ASSOC; auto.
  assert (B: forall l v n, fold_left f l (f v n) = f v (fold_left g l n)).
    induction l; intros; simpl.
    auto.
    rewrite IHl. rewrite DISTR. decEq. decEq. auto.
  intros. unfold decompose_int. 
  destruct (decompose_int_rec 12 n Int.zero) eqn:?. 
  simpl. exploit decompose_int_rec_nil; eauto. congruence.
  simpl. rewrite B. decEq.  
  generalize (DECOMP 12%nat n Int.zero Int.zero).
  rewrite Heql. simpl. repeat rewrite ZERO. auto.
Qed.

Lemma decompose_int_or:
  forall n v,
  List.fold_left (fun v i => Val.or v (Vint i)) (decompose_int n) v = Val.or v (Vint n).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.or v (Vint n)) (g := Int.or).
  intros. rewrite Val.or_assoc. auto.
  apply Int.or_assoc.
  intros. rewrite Int.or_commut. apply Int.or_zero.
  apply decompose_int_rec_or.
Qed.

Lemma decompose_int_bic:
  forall n v,
  List.fold_left (fun v i => Val.and v (Vint (Int.not i))) (decompose_int n) v = Val.and v (Vint (Int.not n)).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.and v (Vint (Int.not n))) (g := Int.or).
  intros. rewrite Val.and_assoc. simpl. decEq. decEq. rewrite Int.not_or_and_not. auto.
  apply Int.or_assoc.
  intros. rewrite Int.or_commut. apply Int.or_zero.
  apply decompose_int_rec_or.
Qed.

Lemma decompose_int_xor:
  forall n v,
  List.fold_left (fun v i => Val.xor v (Vint i)) (decompose_int n) v = Val.xor v (Vint n).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.xor v (Vint n)) (g := Int.xor).
  intros. rewrite Val.xor_assoc. auto. 
  apply Int.xor_assoc.
  intros. rewrite Int.xor_commut. apply Int.xor_zero.
  apply decompose_int_rec_xor.
Qed.

Lemma decompose_int_add:
  forall n v,
  List.fold_left (fun v i => Val.add v (Vint i)) (decompose_int n) v = Val.add v (Vint n).
Proof.
  intros. apply decompose_int_general with (f := fun v n => Val.add v (Vint n)) (g := Int.add).
  intros. rewrite Val.add_assoc. auto. 
  apply Int.add_assoc.
  intros. rewrite Int.add_commut. apply Int.add_zero.
  apply decompose_int_rec_add.
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
  apply decompose_int_rec_add.
Qed.

Lemma iterate_op_correct:
  forall op1 op2 (f: val -> int -> val) (rs: regset) (r: ireg) m v0 n k,
  (forall (rs:regset) n,
    exec_instr ge fn (op2 (SOimm n)) rs m =
    Next (nextinstr (rs#r <- (f (rs#r) n))) m) ->
  (forall n,
    exec_instr ge fn (op1 (SOimm n)) rs m =
    Next (nextinstr (rs#r <- (f v0 n))) m) ->
  exists rs',
     exec_straight ge fn (iterate_op op1 op2 (decompose_int n) k) rs m  k rs' m
  /\ rs'#r = List.fold_left f (decompose_int n) v0
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros until k; intros SEM2 SEM1.
  unfold iterate_op.
  destruct (decompose_int n) as [ | i tl] eqn:?.
  unfold decompose_int in Heql. destruct (decompose_int_rec 12%nat n Int.zero); congruence.
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
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm.
  destruct (NPeano.leb (length (decompose_int n)) (length (decompose_int (Int.not n)))).
  (* mov - orr* *)
  replace (Vint n) with (List.fold_left (fun v i => Val.or v (Vint i)) (decompose_int n) Vzero).
  apply iterate_op_correct.
  auto.
  intros; simpl. rewrite Int.or_commut; rewrite Int.or_zero; auto.
  rewrite decompose_int_or. simpl. rewrite Int.or_commut; rewrite Int.or_zero; auto.
  (* mvn - bic* *)
  replace (Vint n) with (List.fold_left (fun v i => Val.and v (Vint (Int.not i))) (decompose_int (Int.not n)) (Vint Int.mone)).
  apply iterate_op_correct.
  auto.
  intros. simpl. rewrite Int.and_commut; rewrite Int.and_mone; auto.
  rewrite decompose_int_bic. simpl. rewrite Int.not_involutive. rewrite Int.and_commut. rewrite Int.and_mone; auto.
Qed.

(** Add integer immediate. *)

Lemma addimm_correct:
  forall r1 r2 n k rs m,
  exists rs',
     exec_straight ge fn (addimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm.
  destruct (NPeano.leb (length (decompose_int n)) (length (decompose_int (Int.neg n)))).
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
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm.
  (* andi *)
  case (is_immed_arith n).
  exists (nextinstr (rs#r1 <- (Val.and rs#r2 (Vint n)))).
  split. apply exec_straight_one; auto.
  split. rewrite nextinstr_inv; auto with asmgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* bic - bic* *)
  replace (Val.and (rs r2) (Vint n))
     with (List.fold_left (fun v i => Val.and v (Vint (Int.not i))) (decompose_int (Int.not n)) (rs r2)).
  apply iterate_op_correct.
  auto.
  auto.
  rewrite decompose_int_bic. rewrite Int.not_involutive. auto.
Qed.

(** Reverse sub immediate *)

Lemma rsubimm_correct:
  forall r1 r2 n k rs m,
  exists rs',
     exec_straight ge fn (rsubimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.sub (Vint n) rs#r2
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
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
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
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
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
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
    (forall (r: preg), r <> PC -> r <> IR14 -> rs1 r = rs r) ->
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
  Mem.loadv Mint32 m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight ge fn (loadind_int base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> IR14 -> r <> dst -> rs'#r = rs#r.
Proof.
  intros; unfold loadind_int. apply indexed_memory_access_correct; intros.
  econstructor; split. 
  apply exec_straight_one. simpl. unfold exec_load. rewrite H0; rewrite H; eauto. auto.
  split. Simpl. intros; Simpl.
Qed.

Lemma loadind_float_correct:
  forall (base: ireg) ofs dst (rs: regset) m v k,
  Mem.loadv Mfloat64al32 m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight ge fn (loadind_float base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> IR14 -> r <> dst -> rs'#r = rs#r.
Proof.
  intros; unfold loadind_float. apply indexed_memory_access_correct; intros.
  econstructor; split. 
  apply exec_straight_one. simpl. unfold exec_load. rewrite H0; rewrite H; eauto. auto.
  split. Simpl. intros; Simpl.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> IR14 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  unfold loadind; intros.
  destruct ty; monadInv H.
  erewrite ireg_of_eq by eauto. apply loadind_int_correct; auto. 
  erewrite freg_of_eq by eauto. apply loadind_float_correct; auto. 
Qed.

(** Indexed memory stores. *)

Lemma storeind_int_correct:
  forall (base: ireg) ofs (src: ireg) (rs: regset) m m' k,
  Mem.storev Mint32 m (Val.add rs#base (Vint ofs)) (rs#src) = Some m' ->
  src <> IR14 ->
  exists rs',
     exec_straight ge fn (storeind_int src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> IR14 -> rs'#r = rs#r.
Proof.
  intros; unfold storeind_int. apply indexed_memory_access_correct; intros.
  econstructor; split. 
  apply exec_straight_one. simpl. unfold exec_store. 
  rewrite H1. rewrite H2; auto with asmgen. rewrite H; eauto. auto.
  intros; Simpl.
Qed.

Lemma storeind_float_correct:
  forall (base: ireg) ofs (src: freg) (rs: regset) m m' k,
  Mem.storev Mfloat64al32 m (Val.add rs#base (Vint ofs)) (rs#src) = Some m' ->
  exists rs',
     exec_straight ge fn (storeind_float src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> IR14 -> rs'#r = rs#r.
Proof.
  intros; unfold storeind_float. apply indexed_memory_access_correct; intros.
  econstructor; split. 
  apply exec_straight_one. simpl. unfold exec_store. 
  rewrite H0. rewrite H1; auto with asmgen. rewrite H; eauto. auto.
  intros; Simpl.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> IR14 -> rs'#r = rs#r.
Proof.
  unfold storeind; intros.
  destruct ty; monadInv H.
  erewrite ireg_of_eq  in H0 by eauto. apply storeind_int_correct; auto.
  assert (IR x <> IR IR14) by eauto with asmgen. congruence.
  erewrite freg_of_eq in H0 by eauto. apply storeind_float_correct; auto. 
Qed.

(** Translation of shift immediates *)

Lemma transl_shift_correct:
  forall s (r: ireg) (rs: regset),
  eval_shift_op (transl_shift s r) rs = eval_shift s (rs#r).
Proof.
  intros. destruct s; simpl; auto.
Qed.

Lemma transl_shift_addr_correct:
  forall s (r: ireg) (rs: regset),
  eval_shift_addr (transl_shift_addr s r) rs = eval_shift s (rs#r).
Proof.
  intros. destruct s; simpl; auto.
Qed.

(** Translation of conditions *)

Lemma compare_int_spec:
  forall rs v1 v2 m,
  let rs1 := nextinstr (compare_int rs v1 v2 m) in
     rs1#CReq = (Val.cmpu (Mem.valid_pointer m) Ceq v1 v2)
  /\ rs1#CRne = (Val.cmpu (Mem.valid_pointer m) Cne v1 v2)
  /\ rs1#CRhs = (Val.cmpu (Mem.valid_pointer m) Cge v1 v2)
  /\ rs1#CRlo = (Val.cmpu (Mem.valid_pointer m) Clt v1 v2)
  /\ rs1#CRhi = (Val.cmpu (Mem.valid_pointer m) Cgt v1 v2)
  /\ rs1#CRls = (Val.cmpu (Mem.valid_pointer m) Cle v1 v2)
  /\ rs1#CRge = (Val.cmp Cge v1 v2)
  /\ rs1#CRlt = (Val.cmp Clt v1 v2)
  /\ rs1#CRgt = (Val.cmp Cgt v1 v2)
  /\ rs1#CRle = (Val.cmp Cle v1 v2)
  /\ forall r', data_preg r' = true -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1. intuition; try reflexivity.
  unfold compare_int. Simpl. 
Qed.

Lemma compare_float_spec:
  forall rs v1 v2,
  let rs' := nextinstr (compare_float rs v1 v2) in
     rs'#CReq = (Val.cmpf Ceq v1 v2)
  /\ rs'#CRne = (Val.cmpf Cne v1 v2)
  /\ rs'#CRmi = (Val.cmpf Clt v1 v2)              
  /\ rs'#CRpl = (Val.notbool (Val.cmpf Clt v1 v2))
  /\ rs'#CRhi = (Val.notbool (Val.cmpf Cle v1 v2))
  /\ rs'#CRls = (Val.cmpf Cle v1 v2)              
  /\ rs'#CRge = (Val.cmpf Cge v1 v2)              
  /\ rs'#CRlt = (Val.notbool (Val.cmpf Cge v1 v2))
  /\ rs'#CRgt = (Val.cmpf Cgt v1 v2)               
  /\ rs'#CRle = (Val.notbool (Val.cmpf Cgt v1 v2))
  /\ forall r', data_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros. unfold rs'. intuition; try reflexivity.
  unfold compare_float. Simpl. 
Qed.

Ltac ArgsInv :=
  repeat (match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H
  | [ H: assertion _ = OK _ |- _ ] => monadInv H
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
     | Some b => rs'#(CR (crbit_for_cond cond)) = Val.of_bool b
     | None => True
     end
  /\ forall r, data_preg r = true -> rs'#r = rs r.
Proof.
  intros until c; intros TR. 
  assert (MATCH: forall v ob,
           v = Val.of_optbool ob ->
           match ob with Some b => v = Val.of_bool b | None => True end).
    intros. subst v. destruct ob; auto.  
  assert (MATCH2: forall cmp v1 v2 v,
           v = Val.cmpu (Mem.valid_pointer m) cmp v1 v2 ->
           cmp = Ceq \/ cmp = Cne ->
           match Val.cmp_bool cmp v1 v2 with
           | Some b => v = Val.of_bool b
           | None => True
           end).
     intros. destruct v1; simpl; auto; destruct v2; simpl; auto.
     unfold Val.cmpu, Val.cmpu_bool in H. subst v. destruct H0; subst cmp; auto.

  unfold transl_cond in TR; destruct cond; ArgsInv.
- (* Ccomp *)
  generalize (compare_int_spec rs (rs x) (rs x0) m).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct c0; (apply MATCH; assumption) || (apply MATCH2; auto).
  auto.
- (* Ccompu *)
  generalize (compare_int_spec rs (rs x) (rs x0) m).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct c0; (apply MATCH; assumption) || (apply MATCH2; auto).
  auto.
- (* Ccompshift *)
  generalize (compare_int_spec rs (rs x) (eval_shift s (rs x0)) m).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  rewrite transl_shift_correct. 
  split. destruct c0; (apply MATCH; assumption) || (apply MATCH2; auto).
  auto.
- (* Ccompushift *)
  generalize (compare_int_spec rs (rs x) (eval_shift s (rs x0)) m).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  rewrite transl_shift_correct. 
  split. destruct c0; (apply MATCH; assumption) || (apply MATCH2; auto).
  auto.
- (* Ccompimm *)
  destruct (is_immed_arith i).
  generalize (compare_int_spec rs (rs x) (Vint i) m).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto. 
  split. destruct c0; (apply MATCH; assumption) || (apply MATCH2; auto).
  auto.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  generalize (compare_int_spec rs' (rs x) (Vint i) m).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite R; eauto with asmgen. auto.
  split. destruct c0; (apply MATCH; assumption) || (apply MATCH2; auto).
  intros. rewrite C; auto with asmgen.
- (* Ccompuimm *)
  destruct (is_immed_arith i).
  generalize (compare_int_spec rs (rs x) (Vint i) m).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto. 
  split. destruct c0; (apply MATCH; assumption) || (apply MATCH2; auto).
  auto.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  generalize (compare_int_spec rs' (rs x) (Vint i) m).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite R; eauto with asmgen. auto.
  split. destruct c0; (apply MATCH; assumption) || (apply MATCH2; auto).
  intros. rewrite C; auto with asmgen.
- (* Ccompf *)
  generalize (compare_float_spec rs (rs x) (rs x0)).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. case c0; apply MATCH; assumption.
  auto.
- (* Cnotcompf *)
  generalize (compare_float_spec rs (rs x) (rs x0)).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite <- Val.negate_cmpf_ne in C2. rewrite <- Val.negate_cmpf_eq in C1.  
  destruct c0; apply MATCH; simpl; rewrite Val.notbool_negb_3; auto.
  auto.
- (* Ccompfzero *)
  generalize (compare_float_spec rs (rs x) (Vfloat Float.zero)).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. case c0; apply MATCH; assumption.
  auto.
- (* Cnotcompf *)
  generalize (compare_float_spec rs (rs x) (Vfloat Float.zero)).
  intros (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C).
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite <- Val.negate_cmpf_ne in C2. rewrite <- Val.negate_cmpf_eq in C1.  
  destruct c0; apply MATCH; simpl; rewrite Val.notbool_negb_3; auto.
  auto.
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
  match op with Ocmp _ => False | _ => True end ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r, data_preg r = true -> r <> preg_of res -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV NOCMP. 
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; inv EV; try (TranslOpSimpl; fail).
  (* Omove *)
  exists (nextinstr (rs#(preg_of res) <- (rs#(preg_of m0)))).
  split.
  destruct (preg_of res) eqn:RES; try discriminate;
  destruct (preg_of m0) eqn:ARG; inv TR.
  apply exec_straight_one; auto.
  apply exec_straight_one; auto.
  intuition Simpl.
  (* Ointconst *)
  generalize (loadimm_correct x i k rs m). intros [rs' [A [B C]]]. 
  exists rs'; auto with asmgen. 
  (* Oaddrstack *)
  generalize (addimm_correct x IR13 i k rs m). 
  intros [rs' [EX [RES OTH]]].
  exists rs'; auto with asmgen. 
  (* Oaddimm *)
  generalize (addimm_correct x x0 i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'; auto with asmgen.
  (* Orsbimm *)
  generalize (rsubimm_correct x x0 i k rs m).
  intros [rs' [A [B C]]].
  exists rs'; auto with asmgen.
  (* Omul *)
  destruct (ireg_eq x x0 || ireg_eq x x1).
  econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto.
  intuition Simpl.
  TranslOpSimpl.
  (* divs *)
  econstructor. split. apply exec_straight_one. simpl. rewrite H0. reflexivity. auto. 
  intuition Simpl.
  (* divu *)
  econstructor. split. apply exec_straight_one. simpl. rewrite H0. reflexivity. auto.
  intuition Simpl.
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
  exploit Val.shrx_shr; eauto. intros [n [i' [ARG1 [ARG2 RES]]]].
  injection ARG2; intro ARG2'; subst i'; clear ARG2.
  set (islt := Int.lt n Int.zero) in *.
  set (rs1 := nextinstr (compare_int rs (Vint n) (Vint Int.zero) m)).
  assert (OTH1: forall r', data_preg r' = true -> rs1#r' = rs#r').
    generalize (compare_int_spec rs (Vint n) (Vint Int.zero) m).
    fold rs1. intros [A B]. intuition.
  exploit (addimm_correct IR14 x0 (Int.sub (Int.shl Int.one i) Int.one)).
  intros [rs2 [EXEC2 [RES2 OTH2]]].
  set (rs3 := nextinstr (if islt then rs2 else rs2#IR14 <- (Vint n))).
  set (rs4 := nextinstr (rs3#x <- (Val.shr rs3#IR14 (Vint i)))).
  exists rs4; split.
  apply exec_straight_step with rs1 m.
  simpl. rewrite ARG1. auto. auto.
  eapply exec_straight_trans. eexact EXEC2.
  apply exec_straight_two with rs3 m.
  simpl. rewrite OTH2; eauto with asmgen.
    change (rs1 CRge) with (Val.cmp Cge (Vint n) (Vint Int.zero)).
    unfold Val.cmp, Val.cmp_bool. change (Int.cmp Cge n Int.zero) with (negb islt).
    rewrite OTH2; eauto with asmgen. rewrite OTH1. rewrite ARG1. 
    unfold rs3. case islt; reflexivity.
    rewrite <- (ireg_of_eq _ _ EQ1). auto with asmgen.
    auto.
    unfold rs3. destruct islt; auto. auto. 
    split. unfold rs4; Simpl. unfold rs3. destruct islt. 
    Simpl. rewrite RES2. unfold rs1. Simpl.
    Simpl. congruence.
    intros. unfold rs4, rs3; Simpl. destruct islt; Simpl; rewrite OTH2; auto with asmgen. 
  (* intoffloat *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  intuition Simpl.
  (* intuoffloat *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  intuition Simpl.
  (* floatofint *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H0; simpl. eauto. auto.
  intuition Simpl.
  (* floatofintu *)
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
  /\ forall r, data_preg r = true -> r <> preg_of res -> rs'#r = rs#r.
Proof.
  intros. 
  assert (EITHER: match op with Ocmp _ => False | _ => True end \/ exists cmp, op = Ocmp cmp).
    destruct op; auto. right; exists c0; auto.
  destruct EITHER as [A | [cmp A]]. 
  exploit transl_op_correct_same; eauto. intros [rs' [P [Q R]]].
  subst v. exists rs'; eauto. 
  (* Ocmp *)
  subst op. simpl in H. monadInv H. simpl in H0. inv H0. 
  rewrite (ireg_of_eq _ _ EQ).
  exploit transl_cond_correct; eauto. instantiate (1 := rs). instantiate (1 := m). intros [rs1 [A [B C]]].
  set (rs2 := nextinstr (rs1#x <- (Vint Int.zero))).
  set (rs3 := nextinstr (match rs2#(crbit_for_cond cmp) with
             | Vint n => if Int.eq n Int.zero then rs2 else rs2#x <- Vone
             | _      => rs2#x <- Vundef
             end)).
  exists rs3; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_two with rs2 m.
  auto.
  simpl. unfold rs3. destruct (rs2 (crbit_for_cond cmp)); auto. destruct (Int.eq i Int.zero); auto.
  auto. unfold rs3.  destruct (rs2 (crbit_for_cond cmp)); auto. destruct (Int.eq i Int.zero); auto.
  split. unfold rs3. Simpl. 
  replace (rs2 (crbit_for_cond cmp)) with (rs1 (crbit_for_cond cmp)).
  destruct (eval_condition cmp rs##(preg_of##args) m) as [[]|]; simpl in *.
  rewrite B. simpl. rewrite Int.eq_false. Simpl. apply Int.one_not_zero.  
  rewrite B. simpl. rewrite Int.eq_true. unfold rs2. Simpl.
  auto.
  destruct cmp; reflexivity. 
  intros. transitivity (rs2 r). 
  unfold rs3. destruct (rs2 (crbit_for_cond cmp)); Simpl. destruct (Int.eq i Int.zero); auto; Simpl.
  unfold rs2. Simpl.
Qed.

(** Translation of loads and stores. *)

Remark val_add_add_zero:
  forall v1 v2, Val.add v1 v2 = Val.add (Val.add v1 v2) (Vint Int.zero).
Proof.
  intros. destruct v1; destruct v2; simpl; auto; rewrite Int.add_zero; auto.
Qed.

Lemma transl_memory_access_correct:
  forall (P: regset -> Prop) (mk_instr_imm: ireg -> int -> instruction)
         (mk_instr_gen: option (ireg -> shift_addr -> instruction))
         (mk_immed: int -> int)
         addr args k c (rs: regset) a m m',
  transl_memory_access mk_instr_imm mk_instr_gen mk_immed addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  (forall (r1: ireg) (rs1: regset) n k,
    Val.add rs1#r1 (Vint n) = a ->
    (forall (r: preg), r <> PC -> r <> IR14 -> rs1 r = rs r) ->
    exists rs',
    exec_straight ge fn (mk_instr_imm r1 n :: k) rs1 m k rs' m' /\ P rs') ->
  match mk_instr_gen with
  | None => True
  | Some mk =>
      (forall (r1: ireg) (sa: shift_addr) k,
      Val.add rs#r1 (eval_shift_addr sa rs) = a ->
       exists rs',
      exec_straight ge fn (mk r1 sa :: k) rs m k rs' m' /\ P rs')
  end ->
  exists rs',
    exec_straight ge fn c rs m k rs' m' /\ P rs'.
Proof.
  intros until m'; intros TR EA MK1 MK2.
  unfold transl_memory_access in TR; destruct addr; ArgsInv; simpl in EA; inv EA.
  (* Aindexed *)
  apply indexed_memory_access_correct. exact MK1.
  (* Aindexed2 *)
  destruct mk_instr_gen as [mk | ]; monadInv TR. apply MK2.
  simpl. erewrite ! ireg_of_eq; eauto.
  (* Aindexed2shift *)
  destruct mk_instr_gen as [mk | ]; monadInv TR. apply MK2.
  erewrite ! ireg_of_eq; eauto. rewrite transl_shift_addr_correct. auto. 
  (* Ainstack *)
  inv TR. apply indexed_memory_access_correct. exact MK1.
Qed.

Lemma transl_load_int_correct:
  forall mk_instr is_immed dst addr args k c (rs: regset) a chunk m v,
  transl_memory_access_int mk_instr is_immed dst addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  (forall (r1 r2: ireg) (sa: shift_addr) (rs1: regset),
    exec_instr ge fn (mk_instr r1 r2 sa) rs1 m =
    exec_load chunk (Val.add rs1#r2 (eval_shift_addr sa rs1)) r1 rs1 m) ->
  exists rs',
      exec_straight ge fn c rs m k rs' m
   /\ rs'#(preg_of dst) = v
   /\ forall r, nontemp_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros. monadInv H. erewrite ireg_of_eq by eauto.  
  eapply transl_memory_access_correct; eauto.
  intros; simpl. econstructor; split. apply exec_straight_one. 
  rewrite H2. unfold exec_load. simpl eval_shift_addr. rewrite H. rewrite H1. eauto. auto.
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
   /\ forall r, nontemp_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros. monadInv H. erewrite freg_of_eq by eauto.  
  eapply transl_memory_access_correct; eauto.
  intros; simpl. econstructor; split. apply exec_straight_one. 
  rewrite H2. unfold exec_load. rewrite H. rewrite H1. eauto. auto.
  split. Simpl. intros; Simpl.
  simpl; auto.
Qed.

Lemma transl_store_int_correct:
  forall mk_instr is_immed src addr args k c (rs: regset) a chunk m m',
  transl_memory_access_int mk_instr is_immed src addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  (forall (r1 r2: ireg) (sa: shift_addr) (rs1: regset),
    exec_instr ge fn (mk_instr r1 r2 sa) rs1 m =
    exec_store chunk (Val.add rs1#r2 (eval_shift_addr sa rs1)) r1 rs1 m) ->
  exists rs',
      exec_straight ge fn c rs m k rs' m'
   /\ forall r, nontemp_preg r = true -> rs'#r = rs#r.
Proof.
  intros. monadInv H. erewrite ireg_of_eq in * by eauto.  
  eapply transl_memory_access_correct; eauto.
  intros; simpl. econstructor; split. apply exec_straight_one. 
  rewrite H2. unfold exec_store. simpl eval_shift_addr. rewrite H. rewrite H3; eauto with asmgen. 
  rewrite H1. eauto. auto.
  intros; Simpl.
  simpl; intros. 
  econstructor; split. apply exec_straight_one. 
  rewrite H2. unfold exec_store. rewrite H. rewrite H1. eauto. auto.
  intros; Simpl.
Qed.

Lemma transl_store_float_correct:
  forall mk_instr is_immed src addr args k c (rs: regset) a chunk m m',
  transl_memory_access_float mk_instr is_immed src addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  (forall (r1: freg) (r2: ireg) (n: int) (rs1: regset),
    exec_instr ge fn (mk_instr r1 r2 n) rs1 m =
    exec_store chunk (Val.add rs1#r2 (Vint n)) r1 rs1 m) ->
  exists rs',
      exec_straight ge fn c rs m k rs' m'
   /\ forall r, nontemp_preg r = true -> rs'#r = rs#r.
Proof.
  intros. monadInv H. erewrite freg_of_eq in * by eauto.  
  eapply transl_memory_access_correct; eauto.
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
   /\ forall r, nontemp_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros. destruct chunk; simpl in H.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_int_correct; eauto.
  eapply transl_load_float_correct; eauto.
  apply Mem.loadv_float64al32 in H1. eapply transl_load_float_correct; eauto.
  eapply transl_load_float_correct; eauto.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) a m m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
      exec_straight ge fn c rs m k rs' m'
   /\ forall r, nontemp_preg r = true -> rs'#r = rs#r.
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
- unfold transl_memory_access_float in H. monadInv H. rewrite (freg_of_eq _ _ EQ) in *. 
  eapply transl_memory_access_correct; eauto. 
  intros. econstructor; split. apply exec_straight_one.
  simpl. unfold exec_store. rewrite H. rewrite H2; eauto with asmgen. 
  rewrite H1. eauto. auto. intros. Simpl. 
  simpl; auto.
- apply Mem.storev_float64al32 in H1. eapply transl_store_float_correct; eauto.
- eapply transl_store_float_correct; eauto.
Qed.

End CONSTRUCTORS.



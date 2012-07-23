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

Require Import Axioms.
Require Import Coqlib.
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
Require Import Machsem.
Require Import Machtyping.
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.

(** * Correspondence between Mach registers and PPC registers *)

Hint Extern 2 (_ <> _) => discriminate: ppcgen.

(** Mapping from Mach registers to PPC registers. *)

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

Lemma ireg_of_not_IR13:
  forall r, ireg_of r <> IR13.
Proof.
  destruct r; simpl; congruence.
Qed.

Lemma ireg_of_not_IR14:
  forall r, ireg_of r <> IR14.
Proof.
  destruct r; simpl; congruence.
Qed.

Lemma preg_of_not_IR13:
  forall r, preg_of r <> IR13.
Proof.
  unfold preg_of; intros. destruct (mreg_type r).
  generalize (ireg_of_not_IR13 r); congruence.
  congruence.
Qed.

Lemma preg_of_not_IR14:
  forall r, preg_of r <> IR14.
Proof.
  unfold preg_of; intros. destruct (mreg_type r).
  generalize (ireg_of_not_IR14 r); congruence.
  congruence.
Qed.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  intros. unfold preg_of. destruct (mreg_type r); congruence.
Qed.

Lemma ireg_diff:
  forall r1 r2, r1 <> r2 -> IR r1 <> IR r2.
Proof. intros; congruence. Qed.

Hint Resolve ireg_of_not_IR13 ireg_of_not_IR14
             preg_of_not_IR13 preg_of_not_IR14
             preg_of_not_PC ireg_diff: ppcgen.

(** Agreement between Mach register sets and ARM register sets. *)

Record agree (ms: Mach.regset) (sp: val) (rs: Asm.regset) : Prop := mkagree {
  agree_sp: rs#IR13 = sp;
  agree_sp_def: sp <> Vundef;
  agree_mregs: forall r: mreg, Val.lessdef (ms r) (rs#(preg_of r))
}.

Lemma preg_val:
  forall ms sp rs r,
  agree ms sp rs -> Val.lessdef (ms r) rs#(preg_of r).
Proof.
  intros. destruct H. auto.
Qed.

Lemma preg_vals:
  forall ms sp rs, agree ms sp rs ->
  forall l, Val.lessdef_list (map ms l) (map rs (map preg_of l)).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_val; eauto. auto.
Qed.

Lemma ireg_val:
  forall ms sp rs r,
  agree ms sp rs ->
  mreg_type r = Tint ->
  Val.lessdef (ms r) rs#(ireg_of r).
Proof.
  intros. generalize (preg_val _ _ _ r H). unfold preg_of. rewrite H0. auto.
Qed.

Lemma freg_val:
  forall ms sp rs r,
  agree ms sp rs ->
  mreg_type r = Tfloat ->
  Val.lessdef (ms r) rs#(freg_of r).
Proof.
  intros. generalize (preg_val _ _ _ r H). unfold preg_of. rewrite H0. auto.
Qed.

Lemma sp_val:
  forall ms sp rs,
  agree ms sp rs ->
  sp = rs#IR13.
Proof.
  intros. destruct H; auto.
Qed.

Hint Resolve preg_val ireg_val freg_val sp_val: ppcgen.

Definition important_preg (r: preg) : bool :=
  match r with
  | IR IR14 => false
  | IR _ => true
  | FR _ => true
  | CR _ => false
  | PC => false
  end.

Lemma preg_of_important:
  forall r, important_preg (preg_of r) = true.
Proof.
  intros. destruct r; reflexivity.
Qed.

Lemma important_diff:
  forall r r',
  important_preg r = true -> important_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Hint Resolve important_diff: ppcgen.

Lemma agree_exten:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, important_preg r = true -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. destruct H. split. 
  rewrite H0; auto. auto.
  intros. rewrite H0; auto. apply preg_of_important.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', important_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. destruct H. split.
  rewrite H1; auto. apply sym_not_equal. apply preg_of_not_IR13.
  auto.
  intros. unfold Regmap.set. destruct (RegEq.eq r0 r). congruence. 
  rewrite H1. auto. apply preg_of_important.
  red; intros; elim n. eapply preg_of_injective; eauto.
Qed.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  important_preg r = false ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten with rs. auto.
  intros. apply Pregmap.gso. congruence.
Qed.

Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_set_other. auto. auto.
Qed.

Definition nontemp_preg (r: preg) : bool :=
  match r with
  | IR IR14 => false
  | IR IR10 => false
  | IR IR12 => false
  | IR _ => true
  | FR FR6 => false
  | FR FR7 => false
  | FR _ => true
  | CR _ => false
  | PC => false
  end.

Lemma nontemp_diff:
  forall r r',
  nontemp_preg r = true -> nontemp_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.

Hint Resolve nontemp_diff: ppcgen.

Lemma nontemp_important:
  forall r, nontemp_preg r = true -> important_preg r = true.
Proof.
  unfold nontemp_preg, important_preg; destruct r; auto. destruct i; auto.
Qed.

Hint Resolve nontemp_important: ppcgen.

Remark undef_regs_1:
  forall l ms r, ms r = Vundef -> Mach.undef_regs l ms r = Vundef.
Proof.
  induction l; simpl; intros. auto. apply IHl. unfold Regmap.set.
  destruct (RegEq.eq r a); congruence.
Qed.

Remark undef_regs_2:
  forall l ms r, In r l -> Mach.undef_regs l ms r = Vundef.
Proof.
  induction l; simpl; intros. contradiction. 
  destruct H. subst. apply undef_regs_1. apply Regmap.gss.
  auto.
Qed.

Remark undef_regs_3:
  forall l ms r, ~In r l -> Mach.undef_regs l ms r = ms r.
Proof.
  induction l; simpl; intros. auto.
  rewrite IHl. apply Regmap.gso. intuition. intuition.
Qed.

Lemma agree_exten_temps:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, nontemp_preg r = true -> rs'#r = rs#r) ->
  agree (undef_temps ms) sp rs'.
Proof.
  intros. destruct H. split. 
  rewrite H0; auto. auto. 
  intros. unfold undef_temps. 
  destruct (In_dec mreg_eq r (int_temporaries ++ float_temporaries)).
  rewrite undef_regs_2; auto. 
  rewrite undef_regs_3; auto. rewrite H0; auto.
  simpl in n. destruct r; auto; intuition.
Qed.

Lemma agree_set_undef_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', nontemp_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v (undef_temps ms)) sp rs'.
Proof.
  intros. apply agree_set_mreg with (rs'#(preg_of r) <- (rs#(preg_of r))); auto.
  eapply agree_exten_temps; eauto. 
  intros. unfold Pregmap.set. destruct (PregEq.eq r0 (preg_of r)). 
  congruence. auto. 
  intros. rewrite Pregmap.gso; auto. 
Qed.

Lemma agree_undef_temps:
  forall ms sp rs,
  agree ms sp rs ->
  agree (undef_temps ms) sp rs.
Proof.
  intros. eapply agree_exten_temps; eauto.
Qed.

(** Useful properties of the PC register. *)

Lemma nextinstr_inv:
  forall r rs,
  r <> PC ->
  (nextinstr rs)#r = rs#r.
Proof.
  intros. unfold nextinstr. apply Pregmap.gso. red; intro; subst. auto.
Qed.

Lemma nextinstr_inv2:
  forall r rs,
  nontemp_preg r = true ->
  (nextinstr rs)#r = rs#r.
Proof.
  intros. apply nextinstr_inv. red; intro; subst; discriminate.
Qed.

Lemma nextinstr_set_preg:
  forall rs m v,
  (nextinstr (rs#(preg_of m) <- v))#PC = Val.add rs#PC Vone.
Proof.
  intros. unfold nextinstr. rewrite Pregmap.gss. 
  rewrite Pregmap.gso. auto. apply sym_not_eq. apply preg_of_not_PC. 
Qed.

(** Connection between Mach and Asm calling conventions for external
    functions. *)

Lemma extcall_arg_match:
  forall ms sp rs m m' l v,
  agree ms sp rs ->
  Machsem.extcall_arg ms m sp l v ->
  Mem.extends m m' ->
  exists v', Asm.extcall_arg rs m' l v' /\ Val.lessdef v v'.
Proof.
  intros. inv H0.
  exists (rs#(preg_of r)); split. constructor. eauto with ppcgen.
  unfold load_stack in H2. 
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ H) in A. 
  exists v'; split; auto. destruct ty; econstructor; eauto.
Qed.

Lemma extcall_args_match:
  forall ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall ll vl,
  list_forall2 (Machsem.extcall_arg ms m sp) ll vl ->
  exists vl', list_forall2 (Asm.extcall_arg rs m') ll vl' /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros. 
  exists (@nil val); split. constructor. constructor.
  exploit extcall_arg_match; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma extcall_arguments_match:
  forall ms m sp rs sg args m',
  agree ms sp rs ->
  Machsem.extcall_arguments ms m sp sg args ->
  Mem.extends m m' ->
  exists args', Asm.extcall_arguments rs m' sg args' /\ Val.lessdef_list args args'.
Proof.
  unfold Machsem.extcall_arguments, Asm.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
Qed.

(** Translation of arguments to annotations. *)

Lemma annot_arg_match:
  forall ms sp rs m m' p v,
  agree ms sp rs ->
  Mem.extends m m' ->
  Machsem.annot_arg ms m sp p v ->
  exists v', Asm.annot_arg rs m' (transl_annot_param p) v' /\ Val.lessdef v v'.
Proof.
  intros. inv H1; simpl.
(* reg *)
  exists (rs (preg_of r)); split. constructor. eapply preg_val; eauto.
(* stack *)
  exploit Mem.load_extends; eauto. intros [v' [A B]].
  exists v'; split; auto. 
  inv H. econstructor; eauto. 
Qed.

Lemma annot_arguments_match:
  forall ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall pl vl,
  Machsem.annot_arguments ms m sp pl vl ->
  exists vl', Asm.annot_arguments rs m' (map transl_annot_param pl) vl'
           /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros. 
  exists (@nil val); split. constructor. constructor.
  exploit annot_arg_match; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** * Execution of straight-line code *)

Section STRAIGHTLINE.

Variable ge: genv.
Variable fn: code.

(** Straight-line code is composed of PPC instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

Inductive exec_straight: code -> regset -> mem -> 
                         code -> regset -> mem -> Prop :=
  | exec_straight_one:
      forall i1 c rs1 m1 rs2 m2,
      exec_instr ge fn i1 rs1 m1 = OK rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      exec_straight (i1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step:
      forall i c rs1 m1 rs2 m2 c' rs3 m3,
      exec_instr ge fn i rs1 m1 = OK rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      exec_straight c rs2 m2 c' rs3 m3 ->
      exec_straight (i :: c) rs1 m1 c' rs3 m3.

Lemma exec_straight_trans:
  forall c1 rs1 m1 c2 rs2 m2 c3 rs3 m3,
  exec_straight c1 rs1 m1 c2 rs2 m2 ->
  exec_straight c2 rs2 m2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 c3 rs3 m3.
Proof.
  induction 1; intros.
  apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_step with rs2 m2; auto.
Qed.

Lemma exec_straight_two:
  forall i1 i2 c rs1 m1 rs2 m2 rs3 m3,
  exec_instr ge fn i1 rs1 m1 = OK rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = OK rs3 m3 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  exec_straight (i1 :: i2 :: c) rs1 m1 c rs3 m3.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4,
  exec_instr ge fn i1 rs1 m1 = OK rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = OK rs3 m3 ->
  exec_instr ge fn i3 rs3 m3 = OK rs4 m4 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  rs4#PC = Val.add rs3#PC Vone ->
  exec_straight (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_two; eauto.
Qed.

Lemma exec_straight_four:
  forall i1 i2 i3 i4 c rs1 m1 rs2 m2 rs3 m3 rs4 m4 rs5 m5,
  exec_instr ge fn i1 rs1 m1 = OK rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = OK rs3 m3 ->
  exec_instr ge fn i3 rs3 m3 = OK rs4 m4 ->
  exec_instr ge fn i4 rs4 m4 = OK rs5 m5 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  rs4#PC = Val.add rs3#PC Vone ->
  rs5#PC = Val.add rs4#PC Vone ->
  exec_straight (i1 :: i2 :: i3 :: i4 :: c) rs1 m1 c rs5 m5.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_three; eauto.
Qed.

(** * Correctness of ARM constructor functions *)

(** Decomposition of an integer constant *)

Lemma decompose_int_rec_or:
  forall N n p x, List.fold_left Int.or (decompose_int_rec N n p) x = Int.or x n.
Proof.
  induction N; intros; simpl.
  destruct (Int.eq_dec n Int.zero); simpl. 
  subst n. rewrite Int.or_zero. auto.
  auto.
  destruct (Int.eq_dec (Int.and n (Int.shl (Int.repr 3) p)) Int.zero).
  auto.
  simpl. rewrite IHN. rewrite Int.or_assoc. decEq. rewrite <- Int.and_or_distrib.
  rewrite Int.or_not_self. apply Int.and_mone.
Qed.

Lemma decompose_int_rec_xor:
  forall N n p x, List.fold_left Int.xor (decompose_int_rec N n p) x = Int.xor x n.
Proof.
  induction N; intros; simpl.
  destruct (Int.eq_dec n Int.zero); simpl. 
  subst n. rewrite Int.xor_zero. auto.
  auto.
  destruct (Int.eq_dec (Int.and n (Int.shl (Int.repr 3) p)) Int.zero).
  auto.
  simpl. rewrite IHN. rewrite Int.xor_assoc. decEq. rewrite <- Int.and_xor_distrib.
  rewrite Int.xor_not_self. apply Int.and_mone.
Qed.

Lemma decompose_int_rec_add:
  forall N n p x, List.fold_left Int.add (decompose_int_rec N n p) x = Int.add x n.
Proof.
  induction N; intros; simpl.
  destruct (Int.eq_dec n Int.zero); simpl. 
  subst n. rewrite Int.add_zero. auto.
  auto.
  destruct (Int.eq_dec (Int.and n (Int.shl (Int.repr 3) p)) Int.zero).
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
  destruct (decompose_int_rec 12 n Int.zero) as []_eqn. 
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
    OK (nextinstr (rs#r <- (f (rs#r) n))) m) ->
  (forall n,
    exec_instr ge fn (op1 (SOimm n)) rs m =
    OK (nextinstr (rs#r <- (f v0 n))) m) ->
  exists rs',
     exec_straight (iterate_op op1 op2 (decompose_int n) k) rs m  k rs' m
  /\ rs'#r = List.fold_left f (decompose_int n) v0
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros until k; intros SEM2 SEM1.
  unfold iterate_op.
  destruct (decompose_int n) as [ | i tl] _eqn.
  unfold decompose_int in Heql. destruct (decompose_int_rec 12%nat n Int.zero); congruence.
  revert k. pattern tl. apply List.rev_ind.
  (* base case *)
  intros; simpl. econstructor.
  split. apply exec_straight_one. rewrite SEM1. reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. auto.
  intros. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gso; auto with ppcgen.
  (* inductive case *)
  intros. 
  rewrite List.map_app. simpl. rewrite app_ass. simpl. 
  destruct (H (op2 (SOimm x) :: k)) as [rs' [A [B C]]].
  econstructor.
  split. eapply exec_straight_trans. eexact A. apply exec_straight_one.
  rewrite SEM2. reflexivity. reflexivity.
  split. rewrite fold_left_app; simpl. rewrite nextinstr_inv; auto with ppcgen.
  rewrite Pregmap.gss. rewrite B. auto.
  intros. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gso; auto with ppcgen.
Qed.
  
(** Loading a constant. *)

Lemma loadimm_correct:
  forall r n k rs m,
  exists rs',
     exec_straight (loadimm r n k) rs m  k rs' m
  /\ rs'#r = Vint n
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm.
  destruct (le_dec (length (decompose_int n)) (length (decompose_int (Int.not n)))).
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
     exec_straight (addimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm.
  destruct (le_dec (length (decompose_int n)) (length (decompose_int (Int.neg n)))).
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
  r2 <> IR14 ->
  exists rs',
     exec_straight (andimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.and rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm.
  (* andi *)
  case (is_immed_arith n).
  exists (nextinstr (rs#r1 <- (Val.and rs#r2 (Vint n)))).
  split. apply exec_straight_one; auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
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
     exec_straight (rsubimm r1 r2 n k) rs m  k rs' m
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
     exec_straight (orimm r1 r2 n k) rs m  k rs' m
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
     exec_straight (xorimm r1 r2 n k) rs m  k rs' m
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

Lemma loadind_int_correct:
  forall (base: ireg) ofs dst (rs: regset) m v k,
  Mem.loadv Mint32 m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight (loadind_int base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> IR14 -> r <> dst -> rs'#r = rs#r.
Proof.
  intros; unfold loadind_int. destruct (is_immed_mem_word ofs).
  exists (nextinstr (rs#dst <- v)).
  split. apply exec_straight_one. simpl. 
    unfold exec_load. rewrite H. auto. auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  exploit addimm_correct. intros [rs' [A [B C]]].
  exists (nextinstr (rs'#dst <- v)).
  split. eapply exec_straight_trans. eauto. apply exec_straight_one.
    simpl. unfold exec_load. rewrite B.
    rewrite Val.add_assoc. simpl. rewrite Int.add_zero.
    rewrite H. auto. auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

Lemma loadind_float_correct:
  forall (base: ireg) ofs dst (rs: regset) m v k,
  Mem.loadv Mfloat64al32 m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight (loadind_float base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> IR14 -> r <> dst -> rs'#r = rs#r.
Proof.
  intros; unfold loadind_float. destruct (is_immed_mem_float ofs).
  exists (nextinstr (rs#dst <- v)).
  split. apply exec_straight_one. simpl. 
    unfold exec_load. rewrite H. auto. auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  exploit addimm_correct. eauto. intros [rs' [A [B C]]].
  exists (nextinstr (rs'#dst <- v)).
  split. eapply exec_straight_trans. eauto. apply exec_straight_one.
    simpl. unfold exec_load. rewrite B.
    rewrite Val.add_assoc. simpl. 
    rewrite Int.add_zero. rewrite H. auto. auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) m v,
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  mreg_type dst = ty ->
  exists rs',
     exec_straight (loadind base ofs ty dst k) rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> IR14 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros. unfold loadind. 
  assert (preg_of dst <> PC).
    unfold preg_of. case (mreg_type dst); discriminate.
  unfold preg_of. rewrite H0. destruct ty.
  apply loadind_int_correct; auto.
  apply loadind_float_correct; auto.
Qed.

(** Indexed memory stores. *)

Lemma storeind_int_correct:
  forall (base: ireg) ofs (src: ireg) (rs: regset) m m' k,
  Mem.storev Mint32 m (Val.add rs#base (Vint ofs)) (rs#src) = Some m' ->
  src <> IR14 ->
  exists rs',
     exec_straight (storeind_int src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> IR14 -> rs'#r = rs#r.
Proof.
  intros; unfold storeind_int. destruct (is_immed_mem_word ofs).
  exists (nextinstr rs).
  split. apply exec_straight_one. simpl. 
    unfold exec_store. rewrite H. auto. auto.
  intros. rewrite nextinstr_inv; auto.
  exploit addimm_correct. eauto. intros [rs' [A [B C]]].
  exists (nextinstr rs').
  split. eapply exec_straight_trans. eauto. apply exec_straight_one.
    simpl. unfold exec_store. rewrite B.
    rewrite C. rewrite Val.add_assoc. simpl. rewrite Int.add_zero. 
    rewrite H. auto. 
    congruence. auto with ppcgen. auto.
  intros. rewrite nextinstr_inv; auto.
Qed.

Lemma storeind_float_correct:
  forall (base: ireg) ofs (src: freg) (rs: regset) m m' k,
  Mem.storev Mfloat64al32 m (Val.add rs#base (Vint ofs)) (rs#src) = Some m' ->
  base <> IR14 ->
  exists rs',
     exec_straight (storeind_float src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> IR14 -> rs'#r = rs#r.
Proof.
  intros; unfold storeind_float. destruct (is_immed_mem_float ofs).
  exists (nextinstr rs).
  split. apply exec_straight_one. simpl. 
    unfold exec_store. rewrite H. auto. auto.
  intros. rewrite nextinstr_inv; auto.
  exploit addimm_correct. eauto. intros [rs' [A [B C]]].
  exists (nextinstr rs').
  split. eapply exec_straight_trans. eauto. apply exec_straight_one.
    simpl. unfold exec_store. rewrite B. 
    rewrite C. rewrite Val.add_assoc. simpl. rewrite Int.add_zero. 
    rewrite H. auto.
    congruence. congruence. 
    auto with ppcgen. 
  intros. rewrite nextinstr_inv; auto.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) m m',
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  mreg_type src = ty ->
  base <> IR14 ->
  exists rs',
     exec_straight (storeind src base ofs ty k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> IR14 -> rs'#r = rs#r.
Proof.
  intros. unfold storeind. unfold preg_of in H. rewrite H0 in H. destruct ty.
  apply storeind_int_correct. auto. auto. auto with ppcgen.
  apply storeind_float_correct. auto. auto.
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
  /\ forall r', important_preg r' = true -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1. intuition; try reflexivity. 
  rewrite nextinstr_inv; auto with ppcgen.
  unfold compare_int. repeat rewrite Pregmap.gso; auto with ppcgen.
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
  /\ forall r', important_preg r' = true -> rs'#r' = rs#r'.
Proof.
  intros. unfold rs'. intuition; try reflexivity. 
  rewrite nextinstr_inv; auto with ppcgen.
  unfold compare_float. repeat rewrite Pregmap.gso; auto with ppcgen.
Qed.

Ltac TypeInv1 :=
  match goal with
  | H: (List.map ?f ?x = nil) |- _ =>
      destruct x; inv H; TypeInv1
  | H: (List.map ?f ?x = ?hd :: ?tl) |- _ =>
      destruct x; simpl in H; simplify_eq H; clear H; intros; TypeInv1
  | _ => idtac
  end.

Ltac TypeInv2 :=
  match goal with
  | H: (mreg_type _ = Tint) |- _ => try (rewrite H in *); clear H; TypeInv2
  | H: (mreg_type _ = Tfloat) |- _ => try (rewrite H in *); clear H; TypeInv2
  | _ => idtac
  end.

Ltac TypeInv := TypeInv1; simpl in *; unfold preg_of in *; TypeInv2.

Lemma transl_cond_correct:
  forall cond args k rs m,
  map mreg_type args = type_of_condition cond ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ match eval_condition cond (map rs (map preg_of args)) m with
     | Some b => rs'#(CR (crbit_for_cond cond)) = Val.of_bool b
     | None => True
     end
  /\ forall r, important_preg r = true -> rs'#r = rs r.
Proof.
  intros until m; intros TY.
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

   destruct cond; simpl in TY; TypeInv; simpl.
  (* Ccomp *)
  generalize (compare_int_spec rs (rs (ireg_of m0)) (rs (ireg_of m1)) m).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct c; (apply MATCH; assumption) || (apply MATCH2; auto).
  auto.
  (* Ccompu *)
  generalize (compare_int_spec rs (rs (ireg_of m0)) (rs (ireg_of m1)) m).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct c; apply MATCH; assumption.
  auto.
  (* Ccompshift *)
  generalize (compare_int_spec rs (rs (ireg_of m0)) (eval_shift s (rs (ireg_of m1))) m).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite transl_shift_correct. destruct c; (apply MATCH; assumption) || (apply MATCH2; auto).
  rewrite transl_shift_correct. auto.
  (* Ccompushift *)
  generalize (compare_int_spec rs (rs (ireg_of m0)) (eval_shift s (rs (ireg_of m1))) m).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite transl_shift_correct. destruct c; apply MATCH; assumption.
  rewrite transl_shift_correct. auto.
  (* Ccompimm *)
  destruct (is_immed_arith i).
  generalize (compare_int_spec rs (rs (ireg_of m0)) (Vint i) m).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto. 
  split. destruct c; (apply MATCH; assumption) || (apply MATCH2; auto).
  auto.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  generalize (compare_int_spec rs' (rs (ireg_of m0)) (Vint i) m).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite R; eauto with ppcgen. auto.
  split. destruct c; (apply MATCH; assumption) || (apply MATCH2; auto).
  intros. rewrite K; auto with ppcgen.
  (* Ccompuimm *)
  destruct (is_immed_arith i).
  generalize (compare_int_spec rs (rs (ireg_of m0)) (Vint i) m).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto. 
  split. destruct c; apply MATCH; assumption.
  auto.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  generalize (compare_int_spec rs' (rs (ireg_of m0)) (Vint i) m).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite R; eauto with ppcgen. auto.
  split. destruct c; apply MATCH; assumption.
  intros. rewrite K; auto with ppcgen.
  (* Ccompf *)
  generalize (compare_float_spec rs (rs (freg_of m0)) (rs (freg_of m1))).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. case c; apply MATCH; assumption.
  auto.
  (* Cnotcompf *)
  generalize (compare_float_spec rs (rs (freg_of m0)) (rs (freg_of m1))).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite <- Val.negate_cmpf_ne in B. rewrite <- Val.negate_cmpf_eq in A.  
  destruct c; apply MATCH; simpl; rewrite Val.notbool_negb_3; auto.
  auto.
  (* Ccompfzero *)
  generalize (compare_float_spec rs (rs (freg_of m0)) (Vfloat Float.zero)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. case c; apply MATCH; assumption.
  auto.
  (* Cnotcompf *)
  generalize (compare_float_spec rs (rs (freg_of m0)) (Vfloat Float.zero)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite <- Val.negate_cmpf_ne in B. rewrite <- Val.negate_cmpf_eq in A.  
  destruct c; apply MATCH; simpl; rewrite Val.notbool_negb_3; auto.
  auto.
Qed.

(** Translation of arithmetic operations. *)

Ltac Simpl :=
  match goal with
  | [ |- context[nextinstr _ _] ] => rewrite nextinstr_inv; [auto | auto with ppcgen]
  | [ |- context[Pregmap.get ?x (Pregmap.set ?x _ _)] ] => rewrite Pregmap.gss; auto
  | [ |- context[Pregmap.set ?x _ _ ?x] ] => rewrite Pregmap.gss; auto
  | [ |- context[Pregmap.get _ (Pregmap.set _ _ _)] ] => rewrite Pregmap.gso; [auto | auto with ppcgen]
  | [ |- context[Pregmap.set _ _ _ _] ] => rewrite Pregmap.gso; [auto | auto with ppcgen]
  end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity ]
  | split; [try rewrite transl_shift_correct; repeat Simpl | intros; repeat Simpl] ].

Lemma transl_op_correct_same:
  forall op args res k (rs: regset) m v,
  wt_instr (Mop op args res) ->
  eval_operation ge rs#IR13 op (map rs (map preg_of args)) m = Some v ->
  match op with Ocmp _ => False | _ => True end ->
  exists rs',
     exec_straight (transl_op op args res k) rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r, important_preg r = true -> r <> preg_of res -> rs'#r = rs#r.
Proof.
  intros. inv H. 
  (* Omove *)
  simpl in *. inv H0.
  exists (nextinstr (rs#(preg_of res) <- (rs#(preg_of r1)))).
  split. unfold preg_of; rewrite <- H3.
  destruct (mreg_type r1); apply exec_straight_one; auto.
  split. Simpl. Simpl.
  intros. Simpl. Simpl.
  (* Other instructions *)
  destruct op; simpl in H6; inv H6; TypeInv; simpl in H0; inv H0; try (TranslOpSimpl; fail).
  (* Ointconst *)
  generalize (loadimm_correct (ireg_of res) i k rs m). intros [rs' [A [B C]]]. 
  exists rs'. split. auto. split. rewrite B; auto. intros. auto with ppcgen.
  (* Oaddrstack *)
  generalize (addimm_correct (ireg_of res) IR13 i k rs m). 
  intros [rs' [EX [RES OTH]]].
  exists rs'. split. auto. split. auto. auto with ppcgen.
  (* Oaddimm *)
  generalize (addimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. split. auto. auto with ppcgen.
  (* Orsbimm *)
  generalize (rsubimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]].
  exists rs'.
  split. eauto. split. rewrite B. auto. 
  auto with ppcgen. 
  (* Omul *)
  destruct (ireg_eq (ireg_of res) (ireg_of m0) || ireg_eq (ireg_of res) (ireg_of m1)).
  econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto.
  split. repeat Simpl.
  intros. repeat Simpl.
  TranslOpSimpl.
  (* divs *)
  econstructor. split. apply exec_straight_one. simpl. rewrite H2. reflexivity. auto. 
  split. repeat Simpl. intros. repeat Simpl.
  (* divu *)
  econstructor. split. apply exec_straight_one. simpl. rewrite H2. reflexivity. auto. 
  split. repeat Simpl. intros. repeat Simpl.
  (* Oandimm *)
  generalize (andimm_correct (ireg_of res) (ireg_of m0) i k rs m
                            (ireg_of_not_IR14 m0)).
  intros [rs' [A [B C]]]. 
  exists rs'; auto with ppcgen.
  (* Oorimm *)
  generalize (orimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'; auto with ppcgen.
  (* Oxorimm *)
  generalize (xorimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'; auto with ppcgen.
  (* Oshrximm *)
  exploit Val.shrx_shr; eauto. intros [n [i' [ARG1 [ARG2 RES]]]].
  injection ARG2; intro ARG2'; subst i'; clear ARG2.
  set (islt := Int.lt n Int.zero) in *.
  set (rs1 := nextinstr (compare_int rs (Vint n) (Vint Int.zero) m)).
  assert (OTH1: forall r', important_preg r' = true -> rs1#r' = rs#r').
    generalize (compare_int_spec rs (Vint n) (Vint Int.zero) m).
    fold rs1. intros [A B]. intuition.
  exploit (addimm_correct IR14 (ireg_of m0) (Int.sub (Int.shl Int.one i) Int.one)).
  intros [rs2 [EXEC2 [RES2 OTH2]]].
  set (rs3 := nextinstr (if islt then rs2 else rs2#IR14 <- (Vint n))).
  set (rs4 := nextinstr (rs3#(ireg_of res) <- (Val.shr rs3#IR14 (Vint i)))).
  exists rs4; split.
  apply exec_straight_step with rs1 m.
  simpl. rewrite ARG1. auto. auto.
  eapply exec_straight_trans. eexact EXEC2.
  apply exec_straight_two with rs3 m.
  simpl. rewrite OTH2. change (rs1 CRge) with (Val.cmp Cge (Vint n) (Vint Int.zero)).
    unfold Val.cmp, Val.cmp_bool. change (Int.cmp Cge n Int.zero) with (negb islt).
    rewrite OTH2. rewrite OTH1. rewrite ARG1. 
    unfold rs3. case islt; reflexivity.
    destruct m0; reflexivity. auto with ppcgen. auto with ppcgen. discriminate. discriminate.
  simpl. auto. 
  auto. unfold rs3. case islt; auto. auto.
  split. unfold rs4. repeat Simpl. unfold rs3. Simpl. destruct islt.
  rewrite RES2. change (rs1 (IR (ireg_of m0))) with (rs (IR (ireg_of m0))). auto.
  Simpl. rewrite <- ARG1; auto.
  intros. unfold rs4; repeat Simpl. unfold rs3; repeat Simpl. 
  transitivity (rs2 r). destruct islt; auto. Simpl. 
  rewrite OTH2; auto with ppcgen.
  (* intoffloat *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H2; simpl. eauto. auto.
  split; intros; repeat Simpl.
  (* intuoffloat *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H2; simpl. eauto. auto.
  split; intros; repeat Simpl.
  (* floatofint *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H2; simpl. eauto. auto.
  split; intros; repeat Simpl.
  (* floatofintu *)
  econstructor; split. apply exec_straight_one; simpl. rewrite H2; simpl. eauto. auto.
  split; intros; repeat Simpl.
  (* Ocmp *)
  contradiction.
Qed.

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v,
  wt_instr (Mop op args res) ->
  eval_operation ge rs#IR13 op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight (transl_op op args res k) rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, important_preg r = true -> r <> preg_of res -> rs'#r = rs#r.
Proof.
  intros. 
  assert (EITHER: match op with Ocmp _ => False | _ => True end \/ exists cmp, op = Ocmp cmp).
    destruct op; auto. right; exists c; auto.
  destruct EITHER as [A | [c A]]. 
  exploit transl_op_correct_same; eauto. intros [rs' [P [Q R]]].
  subst v. exists rs'; eauto. 
  (* Ocmp *)
  subst op. inv H. simpl in H5. inv H5. simpl in H0. inv H0.
  destruct (transl_cond_correct c args 
             (Pmov (ireg_of res) (SOimm Int.zero)
              :: Pmovc (crbit_for_cond c) (ireg_of res) (SOimm Int.one) :: k)
             rs m H1)
  as [rs1 [A [B C]]].
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (Vint Int.zero))).
  set (v := match rs2#(crbit_for_cond c) with
             | Vint n => if Int.eq n Int.zero then Vint Int.zero else Vint Int.one
             | _ => Vundef
           end).
  set (rs3 := nextinstr (rs2#(ireg_of res) <- v)).
  exists rs3; split.
  eapply exec_straight_trans. eauto. 
  apply exec_straight_two with rs2 m; auto.
  simpl. unfold rs3, v. 
  destruct (rs2 (crbit_for_cond c)) as []_eqn; auto.
  destruct (Int.eq i Int.zero); auto. 
  decEq. decEq. apply extensionality; intros. unfold Pregmap.set.
  destruct (PregEq.eq x (ireg_of res)); auto. subst. 
  unfold rs2. Simpl. Simpl.
  replace (preg_of res) with (IR (ireg_of res)).
  split. unfold rs3. Simpl. Simpl. 
  destruct (eval_condition c rs ## (preg_of ## args) m); simpl; auto.
  unfold v. unfold rs2. Simpl. Simpl. rewrite B. 
  destruct b; simpl; auto.
  intros. unfold rs3. repeat Simpl. unfold rs2. repeat Simpl.
  unfold preg_of; rewrite H2; auto.
Qed.

Remark val_add_add_zero:
  forall v1 v2, Val.add v1 v2 = Val.add (Val.add v1 v2) (Vint Int.zero).
Proof.
  intros. destruct v1; destruct v2; simpl; auto; rewrite Int.add_zero; auto.
Qed.

Lemma transl_load_store_correct:
  forall (mk_instr_imm: ireg -> int -> instruction)
         (mk_instr_gen: option (ireg -> shift_addr -> instruction))
         (is_immed: int -> bool)
         addr args k ms sp rs m ms' m',
  (forall (r1: ireg) (rs1: regset) n k,
    eval_addressing ge sp addr (map rs (map preg_of args)) = Some(Val.add rs1#r1 (Vint n)) ->
    (forall (r: preg), r <> PC -> r <> IR14 -> rs1 r = rs r) ->
    exists rs',
    exec_straight (mk_instr_imm r1 n :: k) rs1 m k rs' m' /\
    agree ms' sp rs') ->
  match mk_instr_gen with
  | None => True
  | Some mk =>
      (forall (r1: ireg) (sa: shift_addr) (rs1: regset) k,
      eval_addressing ge sp addr (map rs (map preg_of args)) = Some(Val.add rs1#r1 (eval_shift_addr sa rs1)) ->
      (forall (r: preg), r <> PC -> r <> IR14 -> rs1 r = rs r) ->
      exists rs',
      exec_straight (mk r1 sa :: k) rs1 m k rs' m' /\
      agree ms' sp rs')
  end ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  exists rs',
    exec_straight (transl_load_store mk_instr_imm mk_instr_gen is_immed addr args k) rs m
                        k rs' m'
  /\ agree ms' sp rs'.
Proof.
  intros. destruct addr; simpl in H2; TypeInv; simpl.
  (* Aindexed *)
  case (is_immed i).
  (* Aindexed, small displacement *)
  apply H; auto.
  (* Aindexed, large displacement *)
  destruct (addimm_correct IR14 (ireg_of m0) i (mk_instr_imm IR14 Int.zero :: k) rs m)
  as [rs' [A [B C]]].
  exploit (H IR14 rs' Int.zero); eauto. 
  rewrite B. rewrite Val.add_assoc. simpl Val.add. rewrite Int.add_zero. reflexivity.
  intros [rs'' [D E]].
  exists rs''; split.
  eapply exec_straight_trans. eexact A. eexact D. auto.
  (* Aindexed2 *)
  destruct mk_instr_gen as [mk | ]. 
  (* binary form available *)
  apply H0; auto.
  (* binary form not available *)
  set (rs' := nextinstr (rs#IR14 <- (Val.add (rs (ireg_of m0)) (rs (ireg_of m1))))).
  exploit (H IR14 rs' Int.zero); eauto.
  unfold rs'. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  decEq. apply val_add_add_zero. 
  unfold rs'. intros. repeat Simpl. 
  intros [rs'' [A B]].
  exists rs''; split.
  eapply exec_straight_step with (rs2 := rs'); eauto.
  simpl. auto. auto.
  (* Aindexed2shift *)
  destruct mk_instr_gen as [mk | ]. 
  (* binary form available *)
  apply H0; auto. rewrite transl_shift_addr_correct. auto.
  (* binary form not available *)
  set (rs' := nextinstr (rs#IR14 <- (Val.add (rs (ireg_of m0)) (eval_shift s (rs (ireg_of m1)))))).
  exploit (H IR14 rs' Int.zero); eauto.
  unfold rs'. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  decEq. apply val_add_add_zero.
  unfold rs'; intros; repeat Simpl.
  intros [rs'' [A B]].
  exists rs''; split.
  eapply exec_straight_step with (rs2 := rs'); eauto.
  simpl. rewrite transl_shift_correct. auto. 
  auto.
  (* Ainstack *)
  destruct (is_immed i).
  (* Ainstack, short displacement *)
  apply H; auto. rewrite (sp_val _ _ _ H1). auto.
  (* Ainstack, large displacement *)
  destruct (addimm_correct IR14 IR13 i (mk_instr_imm IR14 Int.zero :: k) rs m)
  as [rs' [A [B C]]].
  exploit (H IR14 rs' Int.zero); eauto.
  rewrite (sp_val _ _ _ H1). rewrite B. rewrite Val.add_assoc. simpl Val.add. rewrite Int.add_zero. auto.
  intros [rs'' [D E]].
  exists rs''; split.
  eapply exec_straight_trans. eexact A. eexact D. auto.
Qed.

Lemma transl_load_int_correct:
  forall (mk_instr: ireg -> ireg -> shift_addr -> instruction)
         (is_immed: int -> bool)
         (rd: mreg) addr args k ms sp rs m m' chunk a v,
  (forall (c: code) (r1 r2: ireg) (sa: shift_addr) (rs1: regset),
    exec_instr ge c (mk_instr r1 r2 sa) rs1 m' =
    exec_load chunk (Val.add rs1#r2 (eval_shift_addr sa rs1)) r1 rs1 m') ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  mreg_type rd = Tint ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.loadv chunk m a = Some v ->
  Mem.extends m m' ->
  exists rs',
    exec_straight (transl_load_store_int mk_instr is_immed rd addr args k) rs m'
                        k rs' m'
  /\ agree (Regmap.set rd v (undef_temps ms)) sp rs'.
Proof.
  intros. unfold transl_load_store_int.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eauto. 
  intros [a' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]]. 
  apply transl_load_store_correct with ms; auto.
  intros.
  assert (Val.add (rs1 r1) (Vint n) = a') by congruence.
  exists (nextinstr (rs1#(ireg_of rd) <- v')); split.
  apply exec_straight_one. rewrite H. unfold exec_load. 
  simpl. rewrite H8. rewrite C. auto. auto.
  apply agree_nextinstr. eapply agree_set_undef_mreg; eauto. 
  unfold preg_of. rewrite H2. rewrite Pregmap.gss. auto. 
  unfold preg_of. rewrite H2. intros. rewrite Pregmap.gso; auto. apply H7; auto with ppcgen.
  intros.
  assert (Val.add (rs1 r1) (eval_shift_addr sa rs1) = a') by congruence.
  exists (nextinstr (rs1#(ireg_of rd) <- v')); split.
  apply exec_straight_one. rewrite H. unfold exec_load. 
  simpl. rewrite H8. rewrite C. auto. auto.
  apply agree_nextinstr. eapply agree_set_undef_mreg; eauto. 
  unfold preg_of. rewrite H2. rewrite Pregmap.gss. auto. 
  unfold preg_of. rewrite H2. intros. rewrite Pregmap.gso; auto. apply H7; auto with ppcgen.
Qed.

Lemma transl_load_float_correct:
  forall (mk_instr: freg -> ireg -> int -> instruction)
         (is_immed: int -> bool)
         (rd: mreg) addr args k ms sp rs m m' chunk a v,
  (forall (c: code) (r1: freg) (r2: ireg) (n: int) (rs1: regset),
    exec_instr ge c (mk_instr r1 r2 n) rs1 m' =
    exec_load chunk (Val.add rs1#r2 (Vint n)) r1 rs1 m') ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  mreg_type rd = Tfloat ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.loadv chunk m a = Some v ->
  Mem.extends m m' ->
  exists rs',
    exec_straight (transl_load_store_float mk_instr is_immed rd addr args k) rs m'
                        k rs' m'
  /\ agree (Regmap.set rd v (undef_temps ms)) sp rs'.
Proof.
  intros. unfold transl_load_store_int.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eauto. 
  intros [a' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]]. 
  apply transl_load_store_correct with ms; auto.
  intros.
  assert (Val.add (rs1 r1) (Vint n) = a') by congruence.
  exists (nextinstr (rs1#(freg_of rd) <- v')); split.
  apply exec_straight_one. rewrite H. unfold exec_load. 
  simpl. rewrite H8. rewrite C. auto. auto.
  apply agree_nextinstr. eapply agree_set_undef_mreg; eauto. 
  unfold preg_of. rewrite H2. rewrite Pregmap.gss. auto. 
  unfold preg_of. rewrite H2. intros. rewrite Pregmap.gso; auto. apply H7; auto with ppcgen.
Qed.

Lemma transl_store_int_correct:
  forall (mk_instr: ireg -> ireg -> shift_addr -> instruction)
         (is_immed: int -> bool)
         (rd: mreg) addr args k ms sp rs m1 chunk a m2 m1',
  (forall (c: code) (r1 r2: ireg) (sa: shift_addr) (rs1: regset),
    exec_instr ge c (mk_instr r1 r2 sa) rs1 m1' =
    exec_store chunk (Val.add rs1#r2 (eval_shift_addr sa rs1)) r1 rs1 m1') ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  mreg_type rd = Tint ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.storev chunk m1 a (ms rd) = Some m2 ->
  Mem.extends m1 m1' ->
  exists m2',
    Mem.extends m2 m2' /\
    exists rs',
    exec_straight (transl_load_store_int mk_instr is_immed rd addr args k) rs m1'
                        k rs' m2'
    /\ agree (undef_temps ms) sp rs'.
Proof.
  intros. unfold transl_load_store_int.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eauto. 
  intros [a' [A B]].
  exploit preg_val; eauto. instantiate (1 := rd). intros C.
  exploit Mem.storev_extends; eauto. unfold preg_of; rewrite H2. intros [m2' [D E]].
  exists m2'; split; auto.
  apply transl_load_store_correct with ms; auto.
  intros.
  assert (Val.add (rs1 r1) (Vint n) = a') by congruence.
  exists (nextinstr rs1); split.
  apply exec_straight_one. rewrite H. simpl. rewrite H8. 
  unfold exec_store. rewrite H7; auto with ppcgen. rewrite D. auto. auto.
  apply agree_nextinstr. apply agree_exten_temps with rs; auto with ppcgen.
  intros.
  assert (Val.add (rs1 r1) (eval_shift_addr sa rs1) = a') by congruence.
  exists (nextinstr rs1); split.
  apply exec_straight_one. rewrite H. simpl. rewrite H8. 
  unfold exec_store. rewrite H7; auto with ppcgen. rewrite D. auto. auto.
  apply agree_nextinstr. apply agree_exten_temps with rs; auto with ppcgen.
Qed.

Lemma transl_store_float_correct:
  forall (mk_instr: freg -> ireg -> int -> instruction)
         (is_immed: int -> bool)
         (rd: mreg) addr args k ms sp rs m1 chunk a m2 m1',
  (forall (c: code) (r1: freg) (r2: ireg) (n: int) (rs1: regset) m2',
   exec_store chunk (Val.add rs1#r2 (Vint n)) r1 rs1 m1' = OK (nextinstr rs1) m2' ->
   exists rs2,
   exec_instr ge c (mk_instr r1 r2 n) rs1 m1' = OK rs2 m2'
   /\ (forall (r: preg), r <> FR7 -> rs2 r = nextinstr rs1 r)) ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  mreg_type rd = Tfloat ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.storev chunk m1 a (ms rd) = Some m2 ->
  Mem.extends m1 m1' ->
  exists m2',
    Mem.extends m2 m2' /\
    exists rs',
    exec_straight (transl_load_store_float mk_instr is_immed rd addr args k) rs m1'
                        k rs' m2'
    /\ agree (undef_temps ms) sp rs'.
Proof.
  intros. unfold transl_load_store_float.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eauto. 
  intros [a' [A B]].
  exploit preg_val; eauto. instantiate (1 := rd). intros C.
  exploit Mem.storev_extends; eauto. unfold preg_of; rewrite H2. intros [m2' [D E]].
  exists m2'; split; auto.
  apply transl_load_store_correct with ms; auto.
  intros.
  assert (Val.add (rs1 r1) (Vint n) = a') by congruence.
  exploit (H fn (freg_of rd) r1 n rs1 m2').
  unfold exec_store. rewrite H8. rewrite H7; auto with ppcgen. rewrite D. auto.
  intros [rs2 [P Q]].
  exists rs2; split. apply exec_straight_one. auto. rewrite Q; auto with ppcgen.
  apply agree_exten_temps with rs; auto.
  intros. rewrite Q; auto with ppcgen. Simpl. apply H7; auto with ppcgen.
Qed.

End STRAIGHTLINE.


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
Require Import Machconcr.
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
  | FR FR2 => false
  | FR FR3 => false
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
  Machconcr.extcall_arg ms m sp l v ->
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
  Machconcr.extcall_args ms m sp ll vl ->
  exists vl', Asm.extcall_args rs m' ll vl' /\ Val.lessdef_list vl vl'.
Proof.
  induction 3.
  exists (@nil val); split; constructor.
  exploit extcall_arg_match; eauto. intros [v1' [A B]].
  exploit IHextcall_args; eauto. intros [vl' [C D]].
  exists(v1' :: vl'); split. constructor; auto. constructor; auto.
Qed.

Lemma extcall_arguments_match:
  forall ms m sp rs sg args m',
  agree ms sp rs ->
  Machconcr.extcall_arguments ms m sp sg args ->
  Mem.extends m m' ->
  exists args', Asm.extcall_arguments rs m' sg args' /\ Val.lessdef_list args args'.
Proof.
  unfold Machconcr.extcall_arguments, Asm.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
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

(** Loading a constant. *)

Lemma loadimm_correct:
  forall r n k rs m,
  exists rs',
     exec_straight (loadimm r n k) rs m  k rs' m
  /\ rs'#r = Vint n
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm.
  case (is_immed_arith n).
  (* single move *)
  exists (nextinstr (rs#r <- (Vint n))).
  split. apply exec_straight_one. reflexivity. reflexivity.  
  split. rewrite nextinstr_inv; auto with ppcgen.
   apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  case (is_immed_arith (Int.not n)).
  (* single move-complement *)
  exists (nextinstr (rs#r <- (Vint n))).
  split. apply exec_straight_one.
  simpl. change (Int.xor (Int.not n) Int.mone) with (Int.not (Int.not n)).
  rewrite Int.not_involutive. auto.
  reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen.
   apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* mov - or - or - or *)
  set (n1 := Int.and n (Int.repr 255)).
  set (n2 := Int.and n (Int.repr 65280)).
  set (n3 := Int.and n (Int.repr 16711680)).
  set (n4 := Int.and n (Int.repr 4278190080)).
  set (rs1 := nextinstr (rs#r <- (Vint n1))).
  set (rs2 := nextinstr (rs1#r <- (Val.or rs1#r (Vint n2)))).
  set (rs3 := nextinstr (rs2#r <- (Val.or rs2#r (Vint n3)))).
  set (rs4 := nextinstr (rs3#r <- (Val.or rs3#r (Vint n4)))).
  exists rs4.
  split. apply exec_straight_four with rs1 m rs2 m rs3 m; auto. 
  split. unfold rs4. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  unfold rs3. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  unfold rs2. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss.
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss.
  repeat rewrite Val.or_assoc. simpl. decEq. 
  unfold n4, n3, n2, n1. repeat rewrite <- Int.and_or_distrib. 
  change (Int.and n Int.mone = n). apply Int.and_mone.
  intros. 
  unfold rs4. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs3. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs2. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
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
  (* addi *)
  case (is_immed_arith n).
  exists (nextinstr (rs#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_one; auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* subi *)
  case (is_immed_arith (Int.neg n)).
  exists (nextinstr (rs#r1 <- (Val.sub rs#r2 (Vint (Int.neg n))))).
  split. apply exec_straight_one; auto.
  split. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss.
    apply Val.sub_opp_add.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* general *)
  set (n1 := Int.and n (Int.repr 255)).
  set (n2 := Int.and n (Int.repr 65280)).
  set (n3 := Int.and n (Int.repr 16711680)).
  set (n4 := Int.and n (Int.repr 4278190080)).
  set (rs1 := nextinstr (rs#r1 <- (Val.add rs#r2 (Vint n1)))).
  set (rs2 := nextinstr (rs1#r1 <- (Val.add rs1#r1 (Vint n2)))).
  set (rs3 := nextinstr (rs2#r1 <- (Val.add rs2#r1 (Vint n3)))).
  set (rs4 := nextinstr (rs3#r1 <- (Val.add rs3#r1 (Vint n4)))).
  exists rs4.
  split. apply exec_straight_four with rs1 m rs2 m rs3 m; auto. 
  simpl. 
  split. unfold rs4. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  unfold rs3. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  unfold rs2. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss.
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss.
  repeat rewrite Val.add_assoc. simpl. decEq. decEq. 
  unfold n4, n3, n2, n1. repeat rewrite Int.add_and.
  change (Int.and n Int.mone = n). apply Int.and_mone.
  vm_compute; auto.
  vm_compute; auto.
  vm_compute; auto.
  intros.
  unfold rs4. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs3. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs2. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

(* And integer immediate *)

Lemma andimm_correct:
  forall r1 r2 n k rs m,
  r2 <> IR14 ->
  exists rs',
     exec_straight (andimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.and rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> IR14 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm.
  (* andi *)
  case (is_immed_arith n).
  exists (nextinstr (rs#r1 <- (Val.and rs#r2 (Vint n)))).
  split. apply exec_straight_one; auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* bici *)
  case (is_immed_arith (Int.not n)).
  exists (nextinstr (rs#r1 <- (Val.and rs#r2 (Vint n)))).
  split. apply exec_straight_one; auto. simpl.
    change (Int.xor (Int.not n) Int.mone) with (Int.not (Int.not n)).
    rewrite Int.not_involutive. auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* general *)
  exploit loadimm_correct. intros [rs' [A [B C]]].
  exists (nextinstr (rs'#r1 <- (Val.and rs#r2 (Vint n)))).
  split. eapply exec_straight_trans. eauto. apply exec_straight_one.
  simpl. rewrite B. rewrite C; auto with ppcgen. 
  auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

(** Other integer immediate *)

Lemma makeimm_correct:
  forall (instr: ireg -> ireg -> shift_op -> instruction)
         (sem: val -> val -> val)
         r1 (r2: ireg) n k (rs : regset) m,
  (forall c r1 r2 so rs m,
   exec_instr ge c (instr r1 r2 so) rs m 
   = OK (nextinstr rs#r1 <- (sem rs#r2 (eval_shift_op so rs))) m) ->
   r2 <> IR14 ->
  exists rs',
     exec_straight (makeimm instr r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = sem rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> r' <> IR14 -> rs'#r' = rs#r'.
Proof.
  intros. unfold makeimm.
  case (is_immed_arith n).
  (* one immed instr *)
  exists (nextinstr (rs#r1 <- (sem rs#r2 (Vint n)))).
  split. apply exec_straight_one. 
    change (Vint n) with (eval_shift_op (SOimm n) rs). auto.
    auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* general case *)
  exploit loadimm_correct. intros [rs' [A [B C]]].
  exists (nextinstr (rs'#r1 <- (sem rs#r2 (Vint n)))).
  split. eapply exec_straight_trans. eauto. apply exec_straight_one. 
    rewrite <- B. rewrite <- (C r2). 
    change (rs' IR14) with (eval_shift_op (SOreg IR14) rs'). auto.
    congruence. auto with ppcgen. auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto with ppcgen.
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
    rewrite H. auto.
    auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

Lemma loadind_float_correct:
  forall (base: ireg) ofs dst (rs: regset) m v k,
  Mem.loadv Mfloat64 m (Val.add rs#base (Vint ofs)) = Some v ->
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
    simpl. unfold exec_load. rewrite B. rewrite Val.add_assoc. simpl. 
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
    simpl. unfold exec_store. rewrite B. rewrite C.
    rewrite Val.add_assoc. simpl. rewrite Int.add_zero. 
    rewrite H. auto. 
    congruence. auto with ppcgen. auto.
  intros. rewrite nextinstr_inv; auto.
Qed.

Lemma storeind_float_correct:
  forall (base: ireg) ofs (src: freg) (rs: regset) m m' k,
  Mem.storev Mfloat64 m (Val.add rs#base (Vint ofs)) (rs#src) = Some m' ->
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
    simpl. unfold exec_store. rewrite B. rewrite C.
    rewrite Val.add_assoc. simpl. rewrite Int.add_zero. 
    rewrite H. auto.
    congruence. congruence. auto with ppcgen. auto.
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
  eval_shift_op (transl_shift s r) rs = eval_shift_total s (rs#r).
Proof.
  intros. destruct s; simpl;
  unfold eval_shift_total, eval_shift, Val.shl, Val.shr, Val.shru, Val.ror;
  rewrite (s_amount_ltu s); auto.
Qed.

Lemma transl_shift_addr_correct:
  forall s (r: ireg) (rs: regset),
  eval_shift_addr (transl_shift_addr s r) rs = eval_shift_total s (rs#r).
Proof.
  intros. destruct s; simpl;
  unfold eval_shift_total, eval_shift, Val.shl, Val.shr, Val.shru, Val.ror;
  rewrite (s_amount_ltu s); auto.
Qed.

(** Translation of conditions *)

Lemma compare_int_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_int rs v1 v2) in
     rs1#CReq = (Val.cmp Ceq v1 v2)
  /\ rs1#CRne = (Val.cmp Cne v1 v2)
  /\ rs1#CRhs = (Val.cmpu Cge v1 v2)
  /\ rs1#CRlo = (Val.cmpu Clt v1 v2)
  /\ rs1#CRhi = (Val.cmpu Cgt v1 v2)
  /\ rs1#CRls = (Val.cmpu Cle v1 v2)
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
  forall cond args k rs m b,
  map mreg_type args = type_of_condition cond ->
  eval_condition cond (map rs (map preg_of args)) = Some b ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ rs'#(CR (crbit_for_cond cond)) = Val.of_bool b
  /\ forall r, important_preg r = true -> rs'#r = rs r.
Proof.
  intros until b; intros TY EV. rewrite <- (eval_condition_weaken _ _ EV). clear EV.  
  destruct cond; simpl in TY; TypeInv.
  (* Ccomp *)
  generalize (compare_int_spec rs (rs (ireg_of m0)) (rs (ireg_of m1))).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. case c; assumption.
  auto.
  (* Ccompu *)
  generalize (compare_int_spec rs (rs (ireg_of m0)) (rs (ireg_of m1))).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. case c; assumption.
  auto.
  (* Ccompshift *)
  generalize (compare_int_spec rs (rs (ireg_of m0)) (eval_shift_total s (rs (ireg_of m1)))).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite transl_shift_correct. case c; assumption.
  rewrite transl_shift_correct. auto.
  (* Ccompushift *)
  generalize (compare_int_spec rs (rs (ireg_of m0)) (eval_shift_total s (rs (ireg_of m1)))).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. rewrite transl_shift_correct. case c; assumption.
  rewrite transl_shift_correct. auto.
  (* Ccompimm *)
  destruct (is_immed_arith i).
  generalize (compare_int_spec rs (rs (ireg_of m0)) (Vint i)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto. 
  split. case c; assumption.
  auto.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  generalize (compare_int_spec rs' (rs (ireg_of m0)) (Vint i)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite R; eauto with ppcgen. auto.
  split. case c; assumption.
  intros. rewrite K; auto with ppcgen.
  (* Ccompuimm *)
  destruct (is_immed_arith i).
  generalize (compare_int_spec rs (rs (ireg_of m0)) (Vint i)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto. 
  split. case c; assumption.
  auto.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  generalize (compare_int_spec rs' (rs (ireg_of m0)) (Vint i)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite R; eauto with ppcgen. auto.
  split. case c; assumption.
  intros. rewrite K; auto with ppcgen.
  (* Ccompf *)
  generalize (compare_float_spec rs (rs (freg_of m0)) (rs (freg_of m1))).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. case c; assumption.
  auto.
  (* Cnotcompf *)
  generalize (compare_float_spec rs (rs (freg_of m0)) (rs (freg_of m1))).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  econstructor.
  split. apply exec_straight_one. simpl. eauto. auto.
  split. case c; try assumption.
    rewrite Val.negate_cmpf_ne. auto.
    rewrite Val.negate_cmpf_eq. auto.
  auto.
Qed.

(** Translation of arithmetic operations. *)

Ltac Simpl :=
  match goal with
  | [ |- nextinstr _ _ = _ ] => rewrite nextinstr_inv; [auto | auto with ppcgen]
  | [ |- Pregmap.get ?x (Pregmap.set ?x _ _) = _ ] => rewrite Pregmap.gss; auto
  | [ |- Pregmap.set ?x _ _ ?x = _ ] => rewrite Pregmap.gss; auto
  | [ |- Pregmap.get _ (Pregmap.set _ _ _) = _ ] => rewrite Pregmap.gso; [auto | auto with ppcgen]
  | [ |- Pregmap.set _ _ _ _ = _ ] => rewrite Pregmap.gso; [auto | auto with ppcgen]
  end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity ]
  | split; [try rewrite transl_shift_correct; repeat Simpl | intros; repeat Simpl] ].

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v,
  wt_instr (Mop op args res) ->
  eval_operation ge rs#IR13 op (map rs (map preg_of args)) = Some v ->
  exists rs',
     exec_straight (transl_op op args res k) rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r, important_preg r = true -> r <> preg_of res -> rs'#r = rs#r.
Proof.
  intros. rewrite <- (eval_operation_weaken _ _ _ _ H0). inv H.
  (* Omove *)
  simpl.
  exists (nextinstr (rs#(preg_of res) <- (rs#(preg_of r1)))).
  split. unfold preg_of; rewrite <- H2.
  destruct (mreg_type r1); apply exec_straight_one; auto.
  split. Simpl. Simpl.
  intros. Simpl. Simpl.
  (* Other instructions *)
  destruct op; simpl in H5; inv H5; TypeInv; try (TranslOpSimpl; fail).
  (* Omove again *)
  congruence.
  (* Ointconst *)
  generalize (loadimm_correct (ireg_of res) i k rs m). intros [rs' [A [B C]]]. 
  exists rs'. split. auto. split. auto. intros. auto with ppcgen.
  (* Oaddrstack *)
  generalize (addimm_correct (ireg_of res) IR13 i k rs m). 
  intros [rs' [EX [RES OTH]]].
  exists rs'. split. auto. split. auto. auto with ppcgen.
  (* Ocast8signed *)
  econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split. Simpl. Simpl. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  destruct (rs (ireg_of m0)); simpl; auto. rewrite Int.sign_ext_shr_shl. reflexivity.
  compute; auto.
  intros. repeat Simpl. 
  (* Ocast8unsigned *)
  econstructor; split.
  eapply exec_straight_one. simpl; eauto. auto. 
  split. Simpl. Simpl.
  destruct (rs (ireg_of m0)); simpl; auto. rewrite Int.zero_ext_and. reflexivity.
  compute; auto.
  intros. repeat Simpl.
  (* Ocast16signed *)
  econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split. Simpl. Simpl. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  destruct (rs (ireg_of m0)); simpl; auto. rewrite Int.sign_ext_shr_shl. reflexivity.
  compute; auto.
  intros. repeat Simpl. 
  (* Ocast16unsigned *)
  econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split. Simpl. Simpl. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  destruct (rs (ireg_of m0)); simpl; auto. rewrite Int.zero_ext_shru_shl. reflexivity.
  compute; auto.
  intros. repeat Simpl.
  (* Oaddimm *)
  generalize (addimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. split. auto. auto with ppcgen.
  (* Orsbimm *)
  exploit (makeimm_correct Prsb (fun v1 v2 => Val.sub v2 v1) (ireg_of res) (ireg_of m0));
  auto with ppcgen.
  intros [rs' [A [B C]]].
  exists rs'.
  split. eauto. split. rewrite B. auto. auto with ppcgen. 
  (* Omul *)
  destruct (ireg_eq (ireg_of res) (ireg_of m0) || ireg_eq (ireg_of res) (ireg_of m1)).
  econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto.
  split. repeat Simpl.
  intros. repeat Simpl.
  TranslOpSimpl.
  (* Oandimm *)
  generalize (andimm_correct (ireg_of res) (ireg_of m0) i k rs m
                            (ireg_of_not_IR14 m0)).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. split. auto. auto with ppcgen.
  (* Oorimm *)
  exploit (makeimm_correct Porr Val.or (ireg_of res) (ireg_of m0));
  auto with ppcgen.
  intros [rs' [A [B C]]]. 
  exists rs'. split. eauto. split. auto. auto with ppcgen.
  (* Oxorimm *)
  exploit (makeimm_correct Peor Val.xor (ireg_of res) (ireg_of m0));
  auto with ppcgen.
  intros [rs' [A [B C]]]. 
  exists rs'. split. eauto. split. auto. auto with ppcgen.
  (* Oshrximm *)
  assert (exists n, rs (ireg_of m0) = Vint n /\ Int.ltu i (Int.repr 31) = true).
    destruct (rs (ireg_of m0)); try discriminate.
    exists i0; split; auto. destruct (Int.ltu i (Int.repr 31)); discriminate || auto.
  destruct H as [n [ARG1 LTU]]. clear H0.
  assert (LTU': Int.ltu i Int.iwordsize = true).
    exploit Int.ltu_inv. eexact LTU. intro.
    unfold Int.ltu. apply zlt_true.
    assert (Int.unsigned (Int.repr 31) < Int.unsigned Int.iwordsize). compute; auto.
    omega.
  set (islt := Int.lt n Int.zero).
  set (rs1 := nextinstr (compare_int rs (Vint n) (Vint Int.zero))).
  assert (OTH1: forall r', important_preg r' = true -> rs1#r' = rs#r').
    generalize (compare_int_spec rs (Vint n) (Vint Int.zero)).
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
    unfold Val.cmp. change (Int.cmp Cge n Int.zero) with (negb islt).
    rewrite OTH2. rewrite OTH1. rewrite ARG1. 
    unfold rs3. case islt; reflexivity.
    destruct m0; reflexivity. auto with ppcgen. auto with ppcgen. discriminate. discriminate.
  simpl. auto. 
  auto. unfold rs3. case islt; auto. auto.
  split. unfold rs4. repeat Simpl. rewrite ARG1. simpl. rewrite LTU'. rewrite Int.shrx_shr.
  fold islt. unfold rs3. rewrite nextinstr_inv; auto with ppcgen. 
  destruct islt. rewrite RES2. change (rs1 (IR (ireg_of m0))) with (rs (IR (ireg_of m0))). 
  rewrite ARG1. simpl. rewrite LTU'. auto.
  rewrite Pregmap.gss. simpl. rewrite LTU'. auto. 
  assumption.
  intros. unfold rs4; repeat Simpl. unfold rs3; repeat Simpl. 
  transitivity (rs2 r). destruct islt; auto. Simpl. 
  rewrite OTH2; auto with ppcgen.
  (* Ocmp *)
  fold preg_of in *.
  assert (exists b, eval_condition c rs ## (preg_of ## args) = Some b /\ v = Val.of_bool b).
    fold preg_of in H0. destruct (eval_condition c rs ## (preg_of ## args)).
    exists b; split; auto. destruct b; inv H0; auto. congruence.
  clear H0. destruct H as [b [EVC VBO]]. rewrite (eval_condition_weaken _ _ EVC).
  destruct (transl_cond_correct c args 
             (Pmov (ireg_of res) (SOimm Int.zero)
              :: Pmovc (crbit_for_cond c) (ireg_of res) (SOimm Int.one) :: k)
             rs m b H1 EVC)
  as [rs1 [A [B C]]].
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (Vint Int.zero))).
  set (rs3 := nextinstr (if b then (rs2#(ireg_of res) <- Vtrue) else rs2)).
  exists rs3.
  split. eapply exec_straight_trans. eauto. 
  apply exec_straight_two with rs2 m; auto.
  simpl. replace (rs2 (crbit_for_cond c)) with (Val.of_bool b).
  unfold rs3. destruct b; auto.
  unfold rs3. destruct b; auto.
  split. unfold rs3. Simpl. destruct b. Simpl. unfold rs2. repeat Simpl.
  intros. unfold rs3. Simpl. transitivity (rs2 r). 
  destruct b; auto; Simpl. unfold rs2. repeat Simpl. 
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
    eval_addressing_total sp addr (map rs (map preg_of args)) = Val.add rs1#r1 (Vint n) ->
    (forall (r: preg), r <> PC -> r <> IR14 -> rs1 r = rs r) ->
    exists rs',
    exec_straight (mk_instr_imm r1 n :: k) rs1 m k rs' m' /\
    agree ms' sp rs') ->
  match mk_instr_gen with
  | None => True
  | Some mk =>
      (forall (r1: ireg) (sa: shift_addr) (rs1: regset) k,
      eval_addressing_total sp addr (map rs (map preg_of args)) = Val.add rs1#r1 (eval_shift_addr sa rs1) ->
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
  apply val_add_add_zero. 
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
  set (rs' := nextinstr (rs#IR14 <- (Val.add (rs (ireg_of m0)) (eval_shift_total s (rs (ireg_of m1)))))).
  exploit (H IR14 rs' Int.zero); eauto.
  unfold rs'. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  apply val_add_add_zero.
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
  exploit eval_addressing_weaken. eexact A. intros E.
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
  exploit eval_addressing_weaken. eexact A. intros E.
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
  exploit eval_addressing_weaken. eexact A. intros F.
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
   /\ (forall (r: preg), r <> FR3 -> rs2 r = nextinstr rs1 r)) ->
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
  exploit eval_addressing_weaken. eexact A. intros F.
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


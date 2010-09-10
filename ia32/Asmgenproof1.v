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

(** Correctness proof for IA32 generation: auxiliary results. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
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

Open Local Scope error_monad_scope.

(** * Correspondence between Mach registers and IA32 registers *)

Hint Extern 2 (_ <> _) => congruence: ppcgen.

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

Lemma preg_of_not_ESP:
  forall r, preg_of r <> ESP.
Proof.
  destruct r; simpl; congruence.
Qed.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  destruct r; simpl; congruence.
Qed.

Hint Resolve preg_of_not_ESP preg_of_not_PC: ppcgen.

Lemma ireg_of_eq:
  forall r r', ireg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold ireg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma freg_of_eq:
  forall r r', freg_of r = OK r' -> preg_of r = FR r'.
Proof.
  unfold freg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

(** Agreement between Mach register sets and IA32 register sets. *)

Record agree (ms: Mach.regset) (sp: val) (rs: Asm.regset) : Prop := mkagree {
  agree_sp: rs#ESP = sp;
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
  forall ms sp rs r r',
  agree ms sp rs ->
  ireg_of r = OK r' ->
  Val.lessdef (ms r) rs#r'.
Proof.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma freg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  freg_of r = OK r' ->
  Val.lessdef (ms r) (rs#r').
Proof.
  intros. rewrite <- (freg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma sp_val:
  forall ms sp rs,
  agree ms sp rs ->
  sp = rs#ESP.
Proof.
  intros. destruct H; auto.
Qed.

Hint Resolve preg_val ireg_val freg_val sp_val: ppcgen.

Definition important_preg (r: preg) : bool :=
  match r with
  | PC => false
  | IR _ => true
  | FR _ => true
  | ST0 => true
  | CR _ => false
  | RA => false
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
  rewrite H1; auto. apply sym_not_equal. apply preg_of_not_ESP.
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

Lemma agree_undef_unimportant_regs:
  forall ms sp rl rs,
  agree ms sp rs ->
  (forall r, In r rl -> important_preg r = false) ->
  agree ms sp (undef_regs rl rs).
Proof.
  induction rl; simpl; intros. auto.
  apply IHrl. apply agree_exten with rs; auto.
  intros. apply Pregmap.gso. red; intros; subst.
  assert (important_preg a = false) by auto. congruence.
  intros. apply H0; auto.
Qed.

Lemma agree_nextinstr_nf:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr_nf rs).
Proof.
  intros. unfold nextinstr_nf. apply agree_nextinstr. 
  apply agree_undef_unimportant_regs. auto.
  intro. simpl. ElimOrEq; auto.
Qed.

Definition nontemp_preg (r: preg) : bool :=
  match r with
  | PC => false
  | IR ECX => false
  | IR EDX => false
  | IR _ => true
  | FR XMM6 => false
  | FR XMM7 => false
  | FR _ => true
  | ST0 => false
  | CR _ => false
  | RA => false
  end.

Lemma nontemp_diff:
  forall r r',
  nontemp_preg r = true -> nontemp_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.

Hint Resolve nontemp_diff: ppcgen.

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

Lemma nextinstr_nf_inv:
  forall r rs, 
  match r with PC => False | CR _ => False | _ => True end ->
  (nextinstr_nf rs)#r = rs#r.
Proof.
  intros. unfold nextinstr_nf. rewrite nextinstr_inv. 
  simpl. repeat rewrite Pregmap.gso; auto.
  red; intro; subst; contradiction.
  red; intro; subst; contradiction.
  red; intro; subst; contradiction.
  red; intro; subst; contradiction.
  red; intro; subst; contradiction.
Qed.

Lemma nextinstr_nf_inv1:
  forall r rs,
  important_preg r = true -> (nextinstr_nf rs)#r = rs#r.
Proof.
  intros. apply nextinstr_nf_inv. unfold important_preg in H. 
  destruct r; auto; congruence.
Qed.

Lemma nextinstr_nf_inv2:
  forall r rs, 
  nontemp_preg r = true -> (nextinstr_nf rs)#r = rs#r.
Proof.
  intros. apply nextinstr_nf_inv. unfold nontemp_preg in H. 
  destruct r; auto; congruence.
Qed.

Lemma nextinstr_nf_set_preg:
  forall rs m v,
  (nextinstr_nf (rs#(preg_of m) <- v))#PC = Val.add rs#PC Vone.
Proof.
  intros. unfold nextinstr_nf.
  transitivity (nextinstr (rs#(preg_of m) <- v) PC). auto.
  apply nextinstr_set_preg.
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

(** Straight-line code is composed of processor instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

Inductive exec_straight: code -> regset -> mem -> 
                         code -> regset -> mem -> Prop :=
  | exec_straight_one:
      forall i1 c rs1 m1 rs2 m2,
      exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      exec_straight (i1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step:
      forall i c rs1 m1 rs2 m2 c' rs3 m3,
      exec_instr ge fn i rs1 m1 = Next rs2 m2 ->
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
  exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = Next rs3 m3 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  exec_straight (i1 :: i2 :: c) rs1 m1 c rs3 m3.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4,
  exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = Next rs3 m3 ->
  exec_instr ge fn i3 rs3 m3 = Next rs4 m4 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  rs4#PC = Val.add rs3#PC Vone ->
  exec_straight (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_two; eauto.
Qed.

(** * Correctness of IA32 constructor functions *)

(** Smart constructor for moves. *)

Lemma mk_mov_correct:
  forall rd rs k c rs1 m,
  mk_mov rd rs k = OK c ->
  exists rs2,
     exec_straight c rs1 m k rs2 m
  /\ rs2#rd = rs1#rs
  /\ forall r, important_preg r = true -> r <> rd -> rs2#r = rs1#r.
Proof.
  unfold mk_mov; intros. 
  destruct rd; try (monadInv H); destruct rs; monadInv H.
(* mov *)
  econstructor. split. apply exec_straight_one. simpl. eauto. auto. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gso. auto. 
(* movd *)
  econstructor. split. apply exec_straight_one. simpl. eauto. auto. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gso. auto. 
(* getfp0 *)
  econstructor. split. apply exec_straight_one. simpl. eauto. auto. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gso; auto.
(* setfp0 *)
  econstructor. split. apply exec_straight_one. simpl. eauto. auto. 
  split. auto. 
  intros. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gso. auto. 
Qed.

(** Smart constructor for shifts *)

Ltac SRes :=
  match goal with
  | [ |- nextinstr _ _ = _ ] => rewrite nextinstr_inv; [auto | auto with ppcgen]
  | [ |- nextinstr_nf _ _ = _ ] => rewrite nextinstr_nf_inv; [auto | auto with ppcgen]
  | [ |- Pregmap.get ?x (Pregmap.set ?x _ _) = _ ] => rewrite Pregmap.gss; auto
  | [ |- Pregmap.set ?x _ _ ?x = _ ] => rewrite Pregmap.gss; auto
  | [ |- Pregmap.get _ (Pregmap.set _ _ _) = _ ] => rewrite Pregmap.gso; [auto | auto with ppcgen]
  | [ |- Pregmap.set _ _ _ _ = _ ] => rewrite Pregmap.gso; [auto | auto with ppcgen]
  end.

Ltac SOther :=
  match goal with
  | [ |- nextinstr _ _ = _ ] => rewrite nextinstr_inv; [auto | auto with ppcgen]
  | [ |- nextinstr_nf _ _ = _ ] => rewrite nextinstr_nf_inv2; [auto | auto with ppcgen]
  | [ |- Pregmap.get ?x (Pregmap.set ?x _ _) = _ ] => rewrite Pregmap.gss; auto
  | [ |- Pregmap.set ?x _ _ ?x = _ ] => rewrite Pregmap.gss; auto
  | [ |- Pregmap.get _ (Pregmap.set _ _ _) = _ ] => rewrite Pregmap.gso; [auto | auto with ppcgen]
  | [ |- Pregmap.set _ _ _ _ = _ ] => rewrite Pregmap.gso; [auto | auto with ppcgen]
  end.

Lemma mk_shift_correct:
  forall sinstr ssem r1 r2 k c rs1 m,
  mk_shift sinstr r1 r2 k = OK c ->
  (forall r c rs m,
   exec_instr ge c (sinstr r) rs m = Next (nextinstr_nf (rs#r <- (ssem rs#r rs#ECX))) m) ->
  exists rs2,
     exec_straight c rs1 m k rs2 m
  /\ rs2#r1 = ssem rs1#r1 rs1#r2
  /\ forall r, nontemp_preg r = true -> r <> r1 -> rs2#r = rs1#r.
Proof.
  unfold mk_shift; intros. 
  destruct (ireg_eq r2 ECX); monadInv H. 
(* fast case *)
  econstructor. split. apply exec_straight_one. apply H0. auto. 
  split. repeat SRes.
  intros. repeat SOther.
(* general case *)
  monadInv EQ.
  econstructor. split. eapply exec_straight_two. simpl; eauto. apply H0. 
  auto. auto. 
  split. repeat SRes. repeat rewrite nextinstr_inv; auto with ppcgen.
  rewrite Pregmap.gss. decEq. rewrite Pregmap.gso; auto. congruence.
  intros. repeat SOther.
Qed.

(** Smart constructor for division *)


Lemma mk_div_correct:
  forall mkinstr dsem msem r1 r2 k c rs1 m,
  mk_div mkinstr r1 r2 k = OK c ->
  (forall r c rs m,
   exec_instr ge c (mkinstr r) rs m =
   Next (nextinstr_nf (rs#EAX <- (dsem rs#EAX (rs#EDX <- Vundef)#r) 
                         #EDX <- (msem rs#EAX (rs#EDX <- Vundef)#r))) m) ->
  exists rs2,
     exec_straight c rs1 m k rs2 m
  /\ rs2#r1 = dsem rs1#r1 rs1#r2
  /\ forall r, nontemp_preg r = true -> r <> r1 -> rs2#r = rs1#r.
Proof.
  unfold mk_div; intros. 
  destruct (ireg_eq r1 EAX). destruct (ireg_eq r2 EDX); monadInv H.
(* r1=EAX r2=EDX *)
  econstructor. split. eapply exec_straight_two. simpl; eauto. apply H0. auto. auto.
  split. SRes. 
  intros. repeat SOther. 
(* r1=EAX r2<>EDX *)
  econstructor. split. eapply exec_straight_one. apply H0. auto.
  split. repeat SRes. decEq. apply Pregmap.gso. congruence. 
  intros. repeat SOther. 
(* r1 <> EAX *)
  monadInv H. monadInv EQ. destruct (ireg_eq r2 EAX); monadInv EQ0.
(* r1 <> EAX, r1 <> ECX, r2 = EAX *)
  set (rs2 := nextinstr (rs1#ECX <- (rs1#EAX))).
  set (rs3 := nextinstr (rs2#EAX <- (rs2#r1))).
  set (rs4 := nextinstr_nf (rs3#EAX <- (dsem rs3#EAX (rs3#EDX <- Vundef)#ECX) 
                               #EDX <- (msem rs3#EAX (rs3#EDX <- Vundef)#ECX))).
  set (rs5 := nextinstr (rs4#r1 <- (rs4#EAX))).
  set (rs6 := nextinstr (rs5#EAX <- (rs5#ECX))).
  exists rs6. split. apply exec_straight_step with rs2 m; auto.
  apply exec_straight_step with rs3 m; auto.
  apply exec_straight_step with rs4 m; auto. apply H0.
  apply exec_straight_step with rs5 m; auto.
  apply exec_straight_one; auto.
  split. unfold rs6. SRes. unfold rs5. repeat SRes.
  unfold rs4. repeat SRes. decEq.
  unfold rs3. repeat SRes. unfold rs2. repeat SRes. 
  intros. unfold rs6. SOther.
  unfold Pregmap.set. destruct (PregEq.eq r EAX). subst r.
  unfold rs5. repeat SOther.
  unfold rs5. repeat SOther. unfold rs4. repeat SOther. 
  unfold rs3. repeat SOther. unfold rs2. repeat SOther. 
(* r1 <> EAX, r1 <> ECX, r2 <> EAX *)
  set (rs2 := nextinstr (rs1#XMM7 <- (rs1#EAX))).
  set (rs3 := nextinstr (rs2#ECX <- (rs2#r2))).
  set (rs4 := nextinstr (rs3#EAX <- (rs3#r1))).
  set (rs5 := nextinstr_nf (rs4#EAX <- (dsem rs4#EAX (rs4#EDX <- Vundef)#ECX) 
                               #EDX <- (msem rs4#EAX (rs4#EDX <- Vundef)#ECX))).
  set (rs6 := nextinstr (rs5#r2 <- (rs5#ECX))).
  set (rs7 := nextinstr (rs6#r1 <- (rs6#EAX))).
  set (rs8 := nextinstr (rs7#EAX <- (rs7#XMM7))).
  exists rs8. split. apply exec_straight_step with rs2 m; auto.
  apply exec_straight_step with rs3 m; auto.
  apply exec_straight_step with rs4 m; auto.
  apply exec_straight_step with rs5 m; auto. apply H0. 
  apply exec_straight_step with rs6 m; auto.
  apply exec_straight_step with rs7 m; auto.
  apply exec_straight_one; auto.
  split. unfold rs8. SRes. unfold rs7. repeat SRes.
  unfold rs6. repeat SRes. unfold rs5. repeat SRes. 
  decEq. unfold rs4. repeat SRes. unfold rs3. repeat SRes. 
   intros. unfold rs8. SOther.
  unfold Pregmap.set. destruct (PregEq.eq r EAX). subst r. auto.
  unfold rs7. repeat SOther. unfold rs6. SOther.
  unfold Pregmap.set. destruct (PregEq.eq r r2). subst r. auto. 
  unfold rs5. repeat SOther. unfold rs4. repeat SOther.
  unfold rs3. repeat SOther. unfold rs2. repeat SOther.
Qed.

(** Smart constructor for modulus *)

Lemma mk_mod_correct:
  forall mkinstr dsem msem r1 r2 k c rs1 m,
  mk_mod mkinstr r1 r2 k = OK c ->
  (forall r c rs m,
   exec_instr ge c (mkinstr r) rs m =
   Next (nextinstr_nf (rs#EAX <- (dsem rs#EAX (rs#EDX <- Vundef)#r) 
                         #EDX <- (msem rs#EAX (rs#EDX <- Vundef)#r))) m) ->
  exists rs2,
     exec_straight c rs1 m k rs2 m
  /\ rs2#r1 = msem rs1#r1 rs1#r2
  /\ forall r, nontemp_preg r = true -> r <> r1 -> rs2#r = rs1#r.
Proof.
  unfold mk_mod; intros. 
  destruct (ireg_eq r1 EAX). destruct (ireg_eq r2 EDX); monadInv H.
(* r1=EAX r2=EDX *)
  econstructor. split. eapply exec_straight_three.
  simpl; eauto. apply H0. simpl; eauto. auto. auto. auto.
  split. SRes. 
  intros. repeat SOther. 
(* r1=EAX r2<>EDX *)
  econstructor. split. eapply exec_straight_two. apply H0. simpl; eauto. auto. auto.
  split. repeat SRes. decEq. apply Pregmap.gso. congruence. 
  intros. repeat SOther. 
(* r1 <> EAX *)
  monadInv H. monadInv EQ. destruct (ireg_eq r2 EDX); monadInv EQ0.
(* r1 <> EAX, r1 <> ECX, r2 = EDX *)
  set (rs2 := nextinstr (rs1#XMM7 <- (rs1#EAX))).
  set (rs3 := nextinstr (rs2#ECX <- (rs2#EDX))).
  set (rs4 := nextinstr (rs3#EAX <- (rs3#r1))).
  set (rs5 := nextinstr_nf (rs4#EAX <- (dsem rs4#EAX (rs4#EDX <- Vundef)#ECX) 
                               #EDX <- (msem rs4#EAX (rs4#EDX <- Vundef)#ECX))).
  set (rs6 := nextinstr (rs5#r1 <- (rs5#EDX))).
  set (rs7 := nextinstr (rs6#EAX <- (rs6#XMM7))).
  exists rs7. split. apply exec_straight_step with rs2 m; auto.
  apply exec_straight_step with rs3 m; auto.
  apply exec_straight_step with rs4 m; auto.
  apply exec_straight_step with rs5 m; auto. apply H0. 
  apply exec_straight_step with rs6 m; auto.
  apply exec_straight_one; auto.
  split. unfold rs7. repeat SRes. unfold rs6. repeat SRes.
  unfold rs5. repeat SRes. decEq.
  unfold rs4. repeat SRes. unfold rs3. repeat SRes. 
  intros. unfold rs7. SOther.
  unfold Pregmap.set. destruct (PregEq.eq r EAX). subst r.
  unfold rs6. repeat SOther.
  unfold rs6. repeat SOther.
  unfold rs5. repeat SOther. unfold rs4. repeat SOther. 
  unfold rs3. repeat SOther. unfold rs2. repeat SOther. 
(* r1 <> EAX, r1 <> ECX, r2 <> EDX *)
  set (rs2 := nextinstr (rs1#XMM7 <- (rs1#EAX))).
  set (rs3 := nextinstr (rs2#ECX <- (rs2#r2))).
  set (rs4 := nextinstr (rs3#EAX <- (rs3#r1))).
  set (rs5 := nextinstr_nf (rs4#EAX <- (dsem rs4#EAX (rs4#EDX <- Vundef)#ECX) 
                               #EDX <- (msem rs4#EAX (rs4#EDX <- Vundef)#ECX))).
  set (rs6 := nextinstr (rs5#r2 <- (rs5#ECX))).
  set (rs7 := nextinstr (rs6#r1 <- (rs6#EDX))).
  set (rs8 := nextinstr (rs7#EAX <- (rs7#XMM7))).
  exists rs8. split. apply exec_straight_step with rs2 m; auto.
  apply exec_straight_step with rs3 m; auto.
  apply exec_straight_step with rs4 m; auto.
  apply exec_straight_step with rs5 m; auto. apply H0. 
  apply exec_straight_step with rs6 m; auto.
  apply exec_straight_step with rs7 m; auto.
  apply exec_straight_one; auto.
  split. unfold rs8. SRes. unfold rs7. repeat SRes.
  unfold rs6. repeat SRes. unfold rs5. repeat SRes. 
  decEq. unfold rs4. repeat SRes. unfold rs3. repeat SRes. 
   intros. unfold rs8. SOther.
  unfold Pregmap.set. destruct (PregEq.eq r EAX). subst r. auto.
  unfold rs7. repeat SOther. unfold rs6. SOther.
  unfold Pregmap.set. destruct (PregEq.eq r r2). subst r. auto. 
  unfold rs5. repeat SOther. unfold rs4. repeat SOther.
  unfold rs3. repeat SOther. unfold rs2. repeat SOther.
Qed.

(** Smart constructor for [shrx] *)

Lemma mk_shrximm_correct:
  forall r1 n k c (rs1: regset) x m,
  mk_shrximm r1 n k = OK c ->
  rs1#r1 = Vint x ->
  Int.ltu n (Int.repr 31) = true ->
  exists rs2,
     exec_straight c rs1 m k rs2 m
  /\ rs2#r1 = Vint (Int.shrx x n)
  /\ forall r, nontemp_preg r = true -> r <> r1 -> rs2#r = rs1#r.
Proof.
  unfold mk_shrximm; intros. monadInv H. monadInv EQ.
  rewrite Int.shrx_shr; auto.
  set (tnm1 := Int.sub (Int.shl Int.one n) Int.one).
  set (x' := Int.add x tnm1).
  set (rs2 := nextinstr (compare_ints (Vint x) (Vint Int.zero) rs1)).
  set (rs3 := nextinstr (rs2#ECX <- (Vint x'))).
  set (rs4 := nextinstr (if Int.lt x Int.zero then rs3#r1 <- (Vint x') else rs3)).
  set (rs5 := nextinstr_nf (rs4#r1 <- (Val.shr rs4#r1 (Vint n)))).
  assert (rs3#r1 = Vint x). unfold rs3. SRes. SRes. 
  exists rs5. split. 
  apply exec_straight_step with rs2 m. simpl. rewrite H0. simpl. rewrite Int.and_idem. auto. auto.
  apply exec_straight_step with rs3 m. simpl. 
  change (rs2 r1) with (rs1 r1). rewrite H0. simpl. 
  rewrite (Int.add_commut Int.zero tnm1). rewrite Int.add_zero. auto. auto.
  apply exec_straight_step with rs4 m. simpl. 
  change (rs3 SOF) with (rs2 SOF). unfold rs2. rewrite nextinstr_inv; auto with ppcgen. 
  unfold compare_ints. rewrite Pregmap.gso; auto with ppcgen. rewrite Pregmap.gss. 
  simpl. unfold rs4. destruct (Int.lt x Int.zero); auto. 
  unfold rs4. destruct (Int.lt x Int.zero); auto.
  apply exec_straight_one. auto. auto.
  split. unfold rs5. SRes. SRes. unfold rs4. rewrite nextinstr_inv; auto with ppcgen.
  assert (Int.ltu n Int.iwordsize = true).
    unfold Int.ltu in *. change (Int.unsigned (Int.repr 31)) with 31 in H1. 
    destruct (zlt (Int.unsigned n) 31); try discriminate.
    change (Int.unsigned Int.iwordsize) with 32. apply zlt_true. omega.
  destruct (Int.lt x Int.zero). rewrite Pregmap.gss. unfold Val.shr. rewrite H2. auto.
  rewrite H. unfold Val.shr. rewrite H2. auto. 
  intros. unfold rs5. repeat SOther. unfold rs4. SOther.
  transitivity (rs3#r). destruct (Int.lt x Int.zero). SOther. auto. 
  unfold rs3. repeat SOther. unfold rs2. repeat SOther. 
  unfold compare_ints. repeat SOther. 
Qed.

(** Smart constructor for integer conversions *)

Lemma mk_intconv_correct:
  forall mk sem rd rs k c rs1 m,
  mk_intconv mk rd rs k = OK c ->
  (forall c rd rs r m,
   exec_instr ge c (mk rd rs) r m = Next (nextinstr (r#rd <- (sem r#rs))) m) ->
  exists rs2,
     exec_straight c rs1 m k rs2 m
  /\ rs2#rd = sem rs1#rs
  /\ forall r, nontemp_preg r = true -> r <> rd -> rs2#r = rs1#r.
Proof.
  unfold mk_intconv; intros. destruct (low_ireg rs); monadInv H.
  econstructor. split. apply exec_straight_one. rewrite H0. eauto. auto. 
  split. repeat SRes.
  intros. repeat SOther.
  econstructor. split. eapply exec_straight_two. 
  simpl. eauto. apply H0. auto. auto. 
  split. repeat SRes. 
  intros. repeat SOther. 
Qed.

(** Smart constructor for small stores *)

Lemma addressing_mentions_correct:
  forall a r (rs1 rs2: regset),
  (forall (r': ireg), r' <> r -> rs1 r' = rs2 r') ->
  addressing_mentions a r = false ->
  eval_addrmode ge a rs1 = eval_addrmode ge a rs2.
Proof.
  intros until rs2; intro AG. unfold addressing_mentions, eval_addrmode.
  destruct a. intros. destruct (orb_false_elim _ _ H). unfold proj_sumbool in *.
  decEq. destruct base; auto. apply AG. destruct (ireg_eq r i); congruence.
  decEq. destruct ofs as [[r' sc] | ]; auto. rewrite AG; auto. destruct (ireg_eq r r'); congruence.
Qed.

Lemma mk_smallstore_correct:
  forall chunk sto addr r k c rs1 m1 m2,
  mk_smallstore sto addr r k = OK c ->
  Mem.storev chunk m1 (eval_addrmode ge addr rs1) (rs1 r) = Some m2 ->
  (forall c r addr rs m,
   exec_instr ge c (sto addr r) rs m = exec_store ge chunk m addr rs r) ->
  exists rs2,
     exec_straight c rs1 m1 k rs2 m2
  /\ forall r, nontemp_preg r = true -> rs2#r = rs1#r.
Proof.
  unfold mk_smallstore; intros. 
  remember (low_ireg r) as low. destruct low.
(* low reg *)
  monadInv H. econstructor; split. apply exec_straight_one. rewrite H1. 
  unfold exec_store. rewrite H0. eauto. auto. 
  intros. SOther.
(* high reg *)
   remember (addressing_mentions addr ECX) as mentions. destruct mentions; monadInv H.
(* ECX is mentioned. *)
  assert (r <> ECX). red; intros; subst r; discriminate. 
  set (rs2 := nextinstr (rs1#ECX <- (eval_addrmode ge addr rs1))).
  set (rs3 := nextinstr (rs2#EDX <- (rs1 r))).
  econstructor; split.
  apply exec_straight_three with rs2 m1 rs3 m1. 
  simpl. auto. 
  simpl. replace (rs2 r) with (rs1 r). auto. symmetry. unfold rs2. repeat SRes. 
  rewrite H1. unfold exec_store. simpl. rewrite Int.add_zero. 
  change (rs3 EDX) with (rs1 r).
  change (rs3 ECX) with (eval_addrmode ge addr rs1).
  replace (Val.add (eval_addrmode ge addr rs1) (Vint Int.zero))
     with (eval_addrmode ge addr rs1).
  rewrite H0. eauto.
  destruct (eval_addrmode ge addr rs1); simpl in H0; try discriminate.
  simpl. rewrite Int.add_zero; auto. 
  auto. auto. auto. 
  intros. repeat SOther. unfold rs3. repeat SOther. unfold rs2. repeat SOther.
(* ECX is not mentioned *)
  set (rs2 := nextinstr (rs1#ECX <- (rs1 r))).
  econstructor; split.
  apply exec_straight_two with rs2 m1.
  simpl. auto.
  rewrite H1. unfold exec_store. 
  rewrite (addressing_mentions_correct addr ECX rs2 rs1); auto.
  change (rs2 ECX) with (rs1 r). rewrite H0. eauto. 
  intros. unfold rs2. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gso; auto with ppcgen.
  auto. auto. 
  intros. repeat SOther. unfold rs2. repeat SOther.
Qed.

(** Accessing slots in the stack frame *)

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) c m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, important_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  unfold loadind; intros.
  set (addr := Addrmode (Some base) None (inl (ident * int) ofs)) in *.
  assert (eval_addrmode ge addr rs = Val.add rs#base (Vint ofs)).
    unfold addr. simpl. rewrite Int.add_commut; rewrite Int.add_zero; auto. 
  destruct ty; simpl in H0.
  (* int *)
  monadInv H.
  rewrite (ireg_of_eq _ _ EQ). econstructor.
  split. apply exec_straight_one. simpl. unfold exec_load. rewrite H1. rewrite H0.
  eauto. auto. 
  split. repeat SRes. 
  intros. rewrite nextinstr_nf_inv1; auto. SOther.
  (* float *)
  exists (nextinstr_nf (rs#(preg_of dst) <- v)).
  split. destruct (preg_of dst); inv H; apply exec_straight_one; simpl; auto.
  unfold exec_load. rewrite H1; rewrite H0; auto. 
  unfold exec_load. rewrite H1; rewrite H0; auto. 
  split. rewrite nextinstr_nf_inv1. SRes. apply preg_of_important.
  intros. rewrite nextinstr_nf_inv1; auto. SOther.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) c m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  exists rs',
     exec_straight c rs m k rs' m'
  /\ forall r, important_preg r = true -> rs'#r = rs#r.
Proof.
  unfold storeind; intros.
  set (addr := Addrmode (Some base) None (inl (ident * int) ofs)) in *.
  assert (eval_addrmode ge addr rs = Val.add rs#base (Vint ofs)).
    unfold addr. simpl. rewrite Int.add_commut; rewrite Int.add_zero; auto. 
  destruct ty; simpl in H0.
  (* int *)
  monadInv H.
  rewrite (ireg_of_eq _ _ EQ) in H0. econstructor.
  split. apply exec_straight_one. simpl. unfold exec_store. rewrite H1. rewrite H0.
  eauto. auto. 
  intros. apply nextinstr_nf_inv1; auto. 
  (* float *)
  destruct (preg_of src); inv H.
  econstructor; split. apply exec_straight_one.
  simpl. unfold exec_store. rewrite H1; rewrite H0. eauto. auto.
  intros. apply nextinstr_nf_inv1; auto.
  econstructor; split. apply exec_straight_one.
  simpl. unfold exec_store. rewrite H1; rewrite H0. eauto. auto.
  intros. apply nextinstr_nf_inv1; auto.
Qed.

(** Translation of addressing modes *)

Lemma transl_addressing_mode_correct:
  forall addr args am (rs: regset) v,
  transl_addressing addr args = OK am ->
  eval_addressing ge (rs ESP) addr (List.map rs (List.map preg_of args)) = Some v ->
  eval_addrmode ge am rs = v.
Proof.
  assert (A: forall n, Int.add Int.zero n = n). 
    intros. rewrite Int.add_commut. apply Int.add_zero.
  assert (B: forall n i, (if Int.eq i Int.one then Vint n else Vint (Int.mul n i)) = Vint (Int.mul n i)).
    intros. generalize (Int.eq_spec i Int.one); destruct (Int.eq i Int.one); intros.
    subst i. rewrite Int.mul_one. auto. auto.
  unfold transl_addressing; intros.
  destruct addr; repeat (destruct args; try discriminate); simpl in H0.
(* indexed *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ) in H0. simpl.
  destruct (rs x); inv H0; simpl. rewrite A; auto. rewrite A; auto.
(* indexed2 *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ) in H0; rewrite (ireg_of_eq _ _ EQ1) in H0. simpl.
  destruct (rs x); try discriminate; destruct (rs x0); inv H0; simpl.
  rewrite Int.add_assoc; auto. 
  repeat rewrite Int.add_assoc. decEq. decEq. apply Int.add_commut.
  rewrite Int.add_assoc; auto.
(* scaled *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ) in H0. simpl.
  destruct (rs x); inv H0; simpl.
  rewrite B. simpl. rewrite A. auto.
(* indexed2scaled *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ) in H0; rewrite (ireg_of_eq _ _ EQ1) in H0. simpl.
  destruct (rs x); try discriminate; destruct (rs x0); inv H0; simpl.
  rewrite B. simpl. auto.
  rewrite B. simpl. auto.
(* global *)
  inv H. simpl. unfold symbol_offset. destruct (Genv.find_symbol ge i); inv H0.
  repeat rewrite Int.add_zero. auto.
(* based *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ) in H0. simpl.
  destruct (rs x); inv H0; simpl.
  unfold symbol_offset. destruct (Genv.find_symbol ge i); inv H1. 
  rewrite Int.add_zero; auto.
(* basedscaled *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ) in H0. simpl.
  destruct (rs x); inv H0; simpl.
  rewrite B. unfold symbol_offset. destruct (Genv.find_symbol ge i0); inv H1. 
  simpl. rewrite Int.add_zero. auto.
(* instack *)
  inv H; simpl. unfold offset_sp in H0. 
  destruct (rs ESP); inv H0. simpl. rewrite A; auto. 
Qed.

(** Processor conditions and comparisons *)

Lemma compare_ints_spec:
  forall rs v1 v2,
  let rs' := nextinstr (compare_ints v1 v2 rs) in
     rs'#ZF = Val.cmp Ceq v1 v2
  /\ rs'#CF = Val.cmpu Clt v1 v2
  /\ rs'#SOF = Val.cmp Clt v1 v2
  /\ (forall r, nontemp_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_ints.
  split. auto. 
  split. auto.
  split. auto.
  intros. repeat SOther. 
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

Lemma testcond_for_signed_comparison_correct_ii:
  forall c n1 n2 rs,
  eval_testcond (testcond_for_signed_comparison c)
                (nextinstr (compare_ints (Vint n1) (Vint n2) rs)) =
  Some(Int.cmp c n1 n2).
Proof.
  intros. generalize (compare_ints_spec rs (Vint n1) (Vint n2)).
  set (rs' := nextinstr (compare_ints (Vint n1) (Vint n2) rs)). 
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
  destruct (Int.eq n1 n2); auto.
  destruct (Int.eq n1 n2); auto.
  destruct (Int.lt n1 n2); auto.
  rewrite int_not_lt. destruct (Int.lt n1 n2); destruct (Int.eq n1 n2); auto.
  rewrite (int_lt_not n1 n2). destruct (Int.lt n1 n2); destruct (Int.eq n1 n2); auto.
  destruct (Int.lt n1 n2); auto.
Qed.

Lemma testcond_for_signed_comparison_correct_pi:
  forall c blk n1 n2 rs b,
  eval_compare_null c n2 = Some b ->
  eval_testcond (testcond_for_signed_comparison c)
                (nextinstr (compare_ints (Vptr blk n1) (Vint n2) rs)) = Some b.
Proof.
  intros.
  revert H. unfold eval_compare_null. 
  generalize (Int.eq_spec n2 Int.zero); destruct (Int.eq n2 Int.zero); intros; try discriminate.
  subst n2.
  generalize (compare_ints_spec rs (Vptr blk n1) (Vint Int.zero)).
  set (rs' := nextinstr (compare_ints (Vptr blk n1) (Vint Int.zero) rs)). 
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl; try discriminate.
  rewrite <- H0; auto.
  rewrite <- H0; auto.
Qed.

Lemma testcond_for_signed_comparison_correct_ip:
  forall c blk n1 n2 rs b,
  eval_compare_null c n1 = Some b ->
  eval_testcond (testcond_for_signed_comparison c)
                (nextinstr (compare_ints (Vint n1) (Vptr blk n2) rs)) = Some b.
Proof.
  intros.
  revert H. unfold eval_compare_null. 
  generalize (Int.eq_spec n1 Int.zero); destruct (Int.eq n1 Int.zero); intros; try discriminate.
  subst n1.
  generalize (compare_ints_spec rs (Vint Int.zero) (Vptr blk n2)).
  set (rs' := nextinstr (compare_ints (Vint Int.zero) (Vptr blk n2) rs)). 
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl; try discriminate.
  rewrite <- H0; auto.
  rewrite <- H0; auto.
Qed.

Lemma testcond_for_signed_comparison_correct_pp:
  forall c b1 n1 b2 n2 rs b,
  (if eq_block b1 b2 then Some (Int.cmp c n1 n2) else eval_compare_mismatch c) = Some b ->
  eval_testcond (testcond_for_signed_comparison c)
                (nextinstr (compare_ints (Vptr b1 n1) (Vptr b2 n2) rs)) =
  Some b.
Proof.
  intros. generalize (compare_ints_spec rs (Vptr b1 n1) (Vptr b2 n2)).
  set (rs' := nextinstr (compare_ints (Vptr b1 n1) (Vptr b2 n2) rs)). 
  intros [A [B [C D]]]. unfold eq_block in H.
  unfold eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
  destruct (zeq b1 b2). inversion H. destruct (Int.eq n1 n2); auto.
  rewrite <- H; auto.
  destruct (zeq b1 b2). inversion H. destruct (Int.eq n1 n2); auto.
  rewrite <- H; auto.
  destruct (zeq b1 b2). inversion H. destruct (Int.lt n1 n2); auto.
  discriminate.
  destruct (zeq b1 b2). inversion H. 
  rewrite int_not_lt. destruct (Int.lt n1 n2); destruct (Int.eq n1 n2); auto.
  discriminate.
  destruct (zeq b1 b2). inversion H. 
  rewrite (int_lt_not n1 n2). destruct (Int.lt n1 n2); destruct (Int.eq n1 n2); auto.
  discriminate.
  destruct (zeq b1 b2). inversion H. destruct (Int.lt n1 n2); auto.
  discriminate.
Qed.

Lemma testcond_for_unsigned_comparison_correct:
  forall c n1 n2 rs,
  eval_testcond (testcond_for_unsigned_comparison c)
                (nextinstr (compare_ints (Vint n1) (Vint n2) rs)) =
  Some(Int.cmpu c n1 n2).
Proof.
  intros. generalize (compare_ints_spec rs (Vint n1) (Vint n2)).
  set (rs' := nextinstr (compare_ints (Vint n1) (Vint n2) rs)). 
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
  destruct (Int.eq n1 n2); auto.
  destruct (Int.eq n1 n2); auto.
  destruct (Int.ltu n1 n2); auto.
  rewrite int_not_ltu. destruct (Int.ltu n1 n2); destruct (Int.eq n1 n2); auto.
  rewrite (int_ltu_not n1 n2). destruct (Int.ltu n1 n2); destruct (Int.eq n1 n2); auto.
  destruct (Int.ltu n1 n2); auto.
Qed.

Lemma compare_floats_spec:
  forall rs n1 n2,
  let rs' := nextinstr (compare_floats (Vfloat n1) (Vfloat n2) rs) in
     rs'#ZF = Val.of_bool (negb (Float.cmp Cne n1 n2))
  /\ rs'#CF = Val.of_bool (negb (Float.cmp Cge n1 n2))
  /\ rs'#PF = Val.of_bool (negb (Float.cmp Ceq n1 n2 || Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2))
  /\ (forall r, nontemp_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_floats.
  split. auto. 
  split. auto.
  split. auto.
  intros. repeat SOther. 
Qed.

Definition swap_floats (c: comparison) (n1 n2: float) : float :=
  match c with
  | Clt | Cle => n2
  | Ceq | Cne | Cgt | Cge => n1
  end.

Lemma testcond_for_float_comparison_correct:
  forall c n1 n2 rs,
  eval_testcond (testcond_for_condition (Ccompf c))
                (nextinstr (compare_floats (Vfloat (swap_floats c n1 n2))
                                           (Vfloat (swap_floats c n2 n1)) rs)) =
  Some(Float.cmp c n1 n2).
Proof.
  intros.
  generalize (compare_floats_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats (Vfloat (swap_floats c n1 n2))
                                        (Vfloat (swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
(* eq *)
  rewrite Float.cmp_ne_eq.
  caseEq (Float.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2); auto.
(* ne *)
  rewrite Float.cmp_ne_eq.
  caseEq (Float.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2); auto.
(* lt *)
  rewrite <- (Float.cmp_swap Cge n1 n2).
  rewrite <- (Float.cmp_swap Cne n1 n2).
  simpl.
  rewrite Float.cmp_ne_eq. rewrite Float.cmp_le_lt_eq.
  caseEq (Float.cmp Clt n1 n2); intros; simpl.
  caseEq (Float.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float.cmp_lt_eq_false; eauto. 
  auto. 
  destruct (Float.cmp Ceq n1 n2); auto.
(* le *)
  rewrite <- (Float.cmp_swap Cge n1 n2). simpl.
  destruct (Float.cmp Cle n1 n2); auto.
(* gt *)
  rewrite Float.cmp_ne_eq. rewrite Float.cmp_ge_gt_eq. 
  caseEq (Float.cmp Cgt n1 n2); intros; simpl.
  caseEq (Float.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float.cmp_gt_eq_false; eauto. 
  auto. 
  destruct (Float.cmp Ceq n1 n2); auto.
(* ge *)
  destruct (Float.cmp Cge n1 n2); auto.
Qed.

Lemma testcond_for_neg_float_comparison_correct:
  forall c n1 n2 rs,
  eval_testcond (testcond_for_condition (Cnotcompf c))
                (nextinstr (compare_floats (Vfloat (swap_floats c n1 n2))
                                           (Vfloat (swap_floats c n2 n1)) rs)) =
  Some(negb(Float.cmp c n1 n2)).
Proof.
  intros.
  generalize (compare_floats_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats (Vfloat (swap_floats c n1 n2))
                                        (Vfloat (swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
(* eq *)
  rewrite Float.cmp_ne_eq.
  caseEq (Float.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2); auto.
(* ne *)
  rewrite Float.cmp_ne_eq.
  caseEq (Float.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2); auto.
(* lt *)
  rewrite <- (Float.cmp_swap Cge n1 n2).
  rewrite <- (Float.cmp_swap Cne n1 n2).
  simpl.
  rewrite Float.cmp_ne_eq. rewrite Float.cmp_le_lt_eq.
  caseEq (Float.cmp Clt n1 n2); intros; simpl.
  caseEq (Float.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float.cmp_lt_eq_false; eauto.
  auto. 
  destruct (Float.cmp Ceq n1 n2); auto.
(* le *)
  rewrite <- (Float.cmp_swap Cge n1 n2). simpl.
  destruct (Float.cmp Cle n1 n2); auto.
(* gt *)
  rewrite Float.cmp_ne_eq. rewrite Float.cmp_ge_gt_eq. 
  caseEq (Float.cmp Cgt n1 n2); intros; simpl.
  caseEq (Float.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float.cmp_gt_eq_false; eauto. 
  auto. 
  destruct (Float.cmp Ceq n1 n2); auto.
(* ge *)
  destruct (Float.cmp Cge n1 n2); auto.
Qed.

Lemma transl_cond_correct:
  forall cond args k c rs m b,
  transl_cond cond args k = OK c ->
  eval_condition cond (map rs (map preg_of args)) = Some b ->
  exists rs',
     exec_straight c rs m k rs' m
  /\ eval_testcond (testcond_for_condition cond) rs' = Some b
  /\ forall r, nontemp_preg r = true -> rs'#r = rs r.
Proof.
  unfold transl_cond; intros. 
  destruct cond; repeat (destruct args; try discriminate); monadInv H.
(* comp *)
  simpl map in H0. rewrite (ireg_of_eq _ _ EQ) in H0. rewrite (ireg_of_eq _ _ EQ1) in H0.
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. simpl in H0. FuncInv.
  subst b. apply testcond_for_signed_comparison_correct_ii. 
  apply testcond_for_signed_comparison_correct_ip; auto. 
  apply testcond_for_signed_comparison_correct_pi; auto.
  apply testcond_for_signed_comparison_correct_pp; auto.
  intros. unfold compare_ints. repeat SOther.
(* compu *)
  simpl map in H0. rewrite (ireg_of_eq _ _ EQ) in H0. rewrite (ireg_of_eq _ _ EQ1) in H0.
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. simpl in H0. FuncInv.
  subst b. apply testcond_for_unsigned_comparison_correct. 
  intros. unfold compare_ints. repeat SOther.
(* compimm *)
  simpl map in H0. rewrite (ireg_of_eq _ _ EQ) in H0.
  econstructor. split. apply exec_straight_one. simpl; eauto. auto.
  split. simpl in H0. FuncInv. 
  subst b. apply testcond_for_signed_comparison_correct_ii. 
  apply testcond_for_signed_comparison_correct_pi; auto.
  intros. unfold compare_ints. repeat SOther.
(* compuimm *)
  simpl map in H0. rewrite (ireg_of_eq _ _ EQ) in H0.
  exists (nextinstr (compare_ints (rs x) (Vint i) rs)).
  split. destruct (Int.eq_dec i Int.zero). 
  apply exec_straight_one. subst i. simpl.
  simpl in H0. FuncInv. simpl. rewrite Int.and_idem. auto. auto.
  apply exec_straight_one; auto.
  split. simpl in H0. FuncInv.
  subst b. apply testcond_for_unsigned_comparison_correct.
  intros. unfold compare_ints. repeat SOther.
(* compf *)
  simpl map in H0. rewrite (freg_of_eq _ _ EQ) in H0. rewrite (freg_of_eq _ _ EQ1) in H0.
  remember (rs x) as v1; remember (rs x0) as v2. simpl in H0. FuncInv.
  exists (nextinstr (compare_floats (Vfloat (swap_floats c0 f f0)) (Vfloat (swap_floats c0 f0 f)) rs)).
  split. apply exec_straight_one. 
  destruct c0; unfold floatcomp, exec_instr, swap_floats; congruence.
  auto.
  split. subst b. apply testcond_for_float_comparison_correct. 
  intros. unfold compare_floats. repeat SOther.
(* notcompf *)
  simpl map in H0. rewrite (freg_of_eq _ _ EQ) in H0. rewrite (freg_of_eq _ _ EQ1) in H0.
  remember (rs x) as v1; remember (rs x0) as v2. simpl in H0. FuncInv.
  exists (nextinstr (compare_floats (Vfloat (swap_floats c0 f f0)) (Vfloat (swap_floats c0 f0 f)) rs)).
  split. apply exec_straight_one. 
  destruct c0; unfold floatcomp, exec_instr, swap_floats; congruence.
  auto.
  split. subst b. apply testcond_for_neg_float_comparison_correct. 
  intros. unfold compare_floats. repeat SOther.
(* maskzero *)
  simpl map in H0. rewrite (ireg_of_eq _ _ EQ) in H0.
  econstructor. split. apply exec_straight_one. simpl; eauto. auto.
  split. simpl in H0. FuncInv. simpl.
  generalize (compare_ints_spec rs (Vint (Int.and i0 i)) Vzero).
  intros [A B]. rewrite A. subst b. simpl. destruct (Int.eq (Int.and i0 i) Int.zero); auto.
  intros. unfold compare_ints. repeat SOther.
(* masknotzero *)
  simpl map in H0. rewrite (ireg_of_eq _ _ EQ) in H0.
  econstructor. split. apply exec_straight_one. simpl; eauto. auto.
  split. simpl in H0. FuncInv. simpl.
  generalize (compare_ints_spec rs (Vint (Int.and i0 i)) Vzero).
  intros [A B]. rewrite A. subst b. simpl. destruct (Int.eq (Int.and i0 i) Int.zero); auto.
  intros. unfold compare_ints. repeat SOther.
Qed.

(** Translation of arithmetic operations. *)

(*
Ltac TranslOpSimpl :=
  match goal with
  | |- exists rs' : regset,
         exec_straight ?c ?rs ?m ?k rs' ?m /\
         agree (Regmap.set ?res ?v ?ms) ?sp rs'  =>
    (exists (nextinstr (rs#(ireg_of res) <- v));
     split; 
     [ apply exec_straight_one;
       [ repeat (rewrite (ireg_val ms sp rs); auto); reflexivity
       | reflexivity ]
     | auto with ppcgen ])
  ||
    (exists (nextinstr (rs#(freg_of res) <- v));
     split; 
     [ apply exec_straight_one;
       [ repeat (rewrite (freg_val ms sp rs); auto); reflexivity
       | reflexivity ]
     | auto with ppcgen ])
  end.
*)

Ltac ArgsInv :=
  match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args; ArgsInv
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: assertion _ = OK _ |- _ ] => monadInv H; subst; ArgsInv
  | [ H: ireg_of _ = OK _ |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *; clear H; ArgsInv
  | [ H: freg_of _ = OK _ |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *; clear H; ArgsInv
  | _ => idtac
  end.

Ltac TranslOp :=
  econstructor; split;
  [ apply exec_straight_one; [ simpl; eauto | auto ] 
  | split; [ repeat SRes | intros; repeat SOther ]].

(* Move elsewhere *)

Lemma transl_op_correct:
  forall op args res k c (rs: regset) m v,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#ESP) op (map rs (map preg_of args)) = Some v ->
  exists rs',
     exec_straight c rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r, 
     match op with Omove => important_preg r = true | _ => nontemp_preg r = true end ->
     r <> preg_of res -> rs' r = rs r.
Proof.
  intros until v; intros TR EV.
  rewrite <- (eval_operation_weaken _ _ _ _ EV).
  destruct op; simpl in TR; ArgsInv; try (TranslOp; fail).
(* move *)
  exploit mk_mov_correct; eauto. intros [rs2 [A [B C]]]. 
  exists rs2. split. eauto. split. simpl. auto. auto.
(* cast8signed *)
  eapply mk_intconv_correct; eauto.
(* cast8unsigned *)
  eapply mk_intconv_correct; eauto. 
(* cast16signed *)
  eapply mk_intconv_correct; eauto.
(* cast16unsigned *)
  eapply mk_intconv_correct; eauto.
(* div *)
  eapply mk_div_correct; eauto. intros. simpl. eauto. 
(* divu *)
  eapply mk_div_correct; eauto. intros. simpl. eauto. 
(* mod *)
  eapply mk_mod_correct; eauto. intros. simpl. eauto. 
(* modu *)
  eapply mk_mod_correct; eauto. intros. simpl. eauto. 
(* shl *)
  eapply mk_shift_correct; eauto. 
(* shr *)
  eapply mk_shift_correct; eauto. 
(* shrximm *)
  remember (rs x0) as v1. FuncInv.
  remember (Int.ltu i (Int.repr 31)) as L. destruct L; inv EV.
  simpl. replace (Int.ltu i Int.iwordsize) with true. 
  apply mk_shrximm_correct; auto.
  unfold Int.ltu. rewrite zlt_true; auto. 
  generalize (Int.ltu_inv _ _ (sym_equal HeqL)).
  assert (Int.unsigned (Int.repr 31) < Int.unsigned Int.iwordsize) by (compute; auto).
  omega. 
(* shru *)
  eapply mk_shift_correct; eauto.
(* lea *)
  exploit transl_addressing_mode_correct; eauto. intros EA.
  rewrite (eval_addressing_weaken _ _ _ _ EV). rewrite <- EA. 
  TranslOp.
(* condition *)
  remember (eval_condition c0 rs ## (preg_of ## args)) as ob. destruct ob; inv EV. 
  rewrite (eval_condition_weaken _ _ (sym_equal Heqob)). 
  exploit transl_cond_correct; eauto. intros [rs2 [P [Q R]]].
  exists (nextinstr (rs2#ECX <- Vundef #EDX <- Vundef #x <- v)).
  split. eapply exec_straight_trans. eauto. 
  apply exec_straight_one. simpl. rewrite Q. destruct b; inv H0; auto. auto.
  split. repeat SRes. destruct b; inv H0; auto. 
  intros. repeat SOther. 
Qed.

(** Translation of memory loads. *)

Lemma transl_load_correct:
  forall chunk addr args dest k c (rs: regset) m a v,
  transl_load chunk addr args dest k = OK c ->
  eval_addressing ge (rs#ESP) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight c rs m k rs' m
  /\ rs'#(preg_of dest) = v
  /\ forall r, nontemp_preg r = true -> r <> preg_of dest -> rs'#r = rs#r.
Proof.
  unfold transl_load; intros. monadInv H. 
  exploit transl_addressing_mode_correct; eauto. intro EA.
  set (rs2 := nextinstr_nf (rs#(preg_of dest) <- v)).
  assert (exec_load ge chunk m x rs (preg_of dest) = Next rs2 m).
    unfold exec_load. rewrite EA. rewrite H1. auto.
  assert (rs2 PC = Val.add (rs PC) Vone).
    transitivity (Val.add ((rs#(preg_of dest) <- v) PC) Vone).
    auto. decEq. apply Pregmap.gso; auto with ppcgen.
  exists rs2. split. 
  destruct chunk; ArgsInv; apply exec_straight_one; simpl; auto.
  split. unfold rs2. rewrite nextinstr_nf_inv1. SRes. apply preg_of_important.
  intros. unfold rs2. repeat SOther. 
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs#ESP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a (rs (preg_of src)) = Some m' ->
  exists rs',
     exec_straight c rs m k rs' m'
  /\ forall r, nontemp_preg r = true -> rs'#r = rs#r.
Proof.
  unfold transl_store; intros. monadInv H. 
  exploit transl_addressing_mode_correct; eauto. intro EA. rewrite <- EA in H1.
  destruct chunk; ArgsInv.
(* int8signed *)
  eapply mk_smallstore_correct; eauto.
  intros. simpl. unfold exec_store.
  destruct (eval_addrmode ge addr0 rs0); simpl; auto. rewrite Mem.store_signed_unsigned_8; auto.
(* int8unsigned *)
  eapply mk_smallstore_correct; eauto.
(* int16signed *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. 
  replace (Mem.storev Mint16unsigned m (eval_addrmode ge x rs) (rs x0))
     with (Mem.storev Mint16signed m (eval_addrmode ge x rs) (rs x0)).
  rewrite H1. eauto.
  destruct (eval_addrmode ge x rs); simpl; auto. rewrite Mem.store_signed_unsigned_16; auto.
  auto.
  intros. SOther.
(* int16unsigned *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. SOther.
(* int32 *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. SOther.
(* float32 *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. SOther.
(* float64 *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. SOther.
Qed.

End STRAIGHTLINE.


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
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Machconcr.
Require Import Machtyping.
Require Import Asm.
Require Import Asmgen.
Require Conventions.

(** * Correspondence between Mach registers and PPC registers *)

Hint Extern 2 (_ <> _) => discriminate: ppcgen.

(** Mapping from Mach registers to PPC registers. *)

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

(** Characterization of PPC registers that correspond to Mach registers. *)

Definition is_data_reg (r: preg) : Prop :=
  match r with
  | IR IR14 => False
  | CR _ => False
  | PC => False
  | _ => True
  end.

Lemma ireg_of_is_data_reg:
  forall (r: mreg), is_data_reg (ireg_of r).
Proof.
  destruct r; exact I.
Qed.

Lemma freg_of_is_data_reg:
  forall (r: mreg), is_data_reg (ireg_of r).
Proof.
  destruct r; exact I.
Qed.

Lemma preg_of_is_data_reg:
  forall (r: mreg), is_data_reg (preg_of r).
Proof.
  destruct r; exact I.
Qed.

Lemma ireg_of_not_IR13:
  forall r, ireg_of r <> IR13.
Proof.
  intro. case r; discriminate.
Qed.
Lemma ireg_of_not_IR14:
  forall r, ireg_of r <> IR14.
Proof.
  intro. case r; discriminate.
Qed.

Hint Resolve ireg_of_not_IR13 ireg_of_not_IR14: ppcgen.

Lemma preg_of_not:
  forall r1 r2, ~(is_data_reg r2) -> preg_of r1 <> r2.
Proof.
  intros; red; intro. subst r2. elim H. apply preg_of_is_data_reg.
Qed.
Hint Resolve preg_of_not: ppcgen.

Lemma preg_of_not_IR13:
  forall r, preg_of r <> IR13.
Proof.
  intro. case r; discriminate.
Qed.
Hint Resolve preg_of_not_IR13: ppcgen.

(** Agreement between Mach register sets and PPC register sets. *)

Definition agree (ms: Mach.regset) (sp: val) (rs: Asm.regset) :=
  rs#IR13 = sp /\ forall r: mreg, ms r = rs#(preg_of r).

Lemma preg_val:
  forall ms sp rs r,
  agree ms sp rs -> ms r = rs#(preg_of r).
Proof.
  intros. elim H. auto.
Qed.
  
Lemma ireg_val:
  forall ms sp rs r,
  agree ms sp rs ->
  mreg_type r = Tint ->
  ms r = rs#(ireg_of r).
Proof.
  intros. elim H; intros.
  generalize (H2 r). unfold preg_of. rewrite H0. auto.
Qed.

Lemma freg_val:
  forall ms sp rs r,
  agree ms sp rs ->
  mreg_type r = Tfloat ->
  ms r = rs#(freg_of r).
Proof.
  intros. elim H; intros.
  generalize (H2 r). unfold preg_of. rewrite H0. auto.
Qed.

Lemma sp_val:
  forall ms sp rs,
  agree ms sp rs ->
  sp = rs#IR13.
Proof.
  intros. elim H; auto.
Qed.

Lemma agree_exten_1:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, is_data_reg r -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  unfold agree; intros. elim H; intros.
  split. rewrite H0. auto. exact I. 
  intros. rewrite H0. auto. apply preg_of_is_data_reg.
Qed.

Lemma agree_exten_2:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, r <> PC -> r <> IR14 -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. eapply agree_exten_1; eauto. 
  intros. apply H0; red; intro; subst r; elim H1.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v,
  agree ms sp rs ->
  agree (Regmap.set r v ms) sp (rs#(preg_of r) <- v).
Proof.
  unfold agree; intros. elim H; intros; clear H.
  split. rewrite Pregmap.gso. auto. apply sym_not_eq. apply preg_of_not_IR13.
  intros. unfold Regmap.set. case (RegEq.eq r0 r); intro.
  subst r0. rewrite Pregmap.gss. auto.
  rewrite Pregmap.gso. auto. red; intro. 
  elim n. apply preg_of_injective; auto.
Qed.
Hint Resolve agree_set_mreg: ppcgen.

Lemma agree_set_mireg:
  forall ms sp rs r v,
  agree ms sp (rs#(preg_of r) <- v) ->
  mreg_type r = Tint ->
  agree ms sp (rs#(ireg_of r) <- v).
Proof.
  intros. unfold preg_of in H. rewrite H0 in H. auto.
Qed.
Hint Resolve agree_set_mireg: ppcgen.

Lemma agree_set_mfreg:
  forall ms sp rs r v,
  agree ms sp (rs#(preg_of r) <- v) ->
  mreg_type r = Tfloat ->
  agree ms sp (rs#(freg_of r) <- v).
Proof.
  intros. unfold preg_of in H. rewrite H0 in H. auto.
Qed.
Hint Resolve agree_set_mfreg: ppcgen.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  ~(is_data_reg r) ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten_1 with rs.
  auto. intros. apply Pregmap.gso. red; intro; subst r0; contradiction.
Qed.
Hint Resolve agree_set_other: ppcgen.

Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_set_other. auto. auto.
Qed.
Hint Resolve agree_nextinstr: ppcgen.

Lemma agree_set_mireg_twice:
  forall ms sp rs r v v',
  agree ms sp rs ->
  mreg_type r = Tint ->
  agree (Regmap.set r v ms) sp (rs #(ireg_of r) <- v' #(ireg_of r) <- v).
Proof.
  intros. replace (IR (ireg_of r)) with (preg_of r). elim H; intros.
  split. repeat (rewrite Pregmap.gso; auto with ppcgen).
  intros. case (mreg_eq r r0); intro.
  subst r0. rewrite Regmap.gss. rewrite Pregmap.gss. auto.
  assert (preg_of r <> preg_of r0). 
    red; intro. elim n. apply preg_of_injective. auto.
  rewrite Regmap.gso; auto.
  repeat (rewrite Pregmap.gso; auto).
  unfold preg_of. rewrite H0. auto.
Qed.
Hint Resolve agree_set_mireg_twice: ppcgen.

Lemma agree_set_twice_mireg:
  forall ms sp rs r v v',
  agree (Regmap.set r v' ms) sp rs ->
  mreg_type r = Tint ->
  agree (Regmap.set r v ms) sp (rs#(ireg_of r) <- v).
Proof.
  intros. elim H; intros.
  split. rewrite Pregmap.gso. auto. 
  generalize (ireg_of_not_IR13 r); congruence.
  intros. generalize (H2 r0). 
  case (mreg_eq r0 r); intro.
  subst r0. repeat rewrite Regmap.gss. unfold preg_of; rewrite H0.
  rewrite Pregmap.gss. auto.
  repeat rewrite Regmap.gso; auto.
  rewrite Pregmap.gso. auto. 
  replace (IR (ireg_of r)) with (preg_of r).
  red; intros. elim n. apply preg_of_injective; auto.
  unfold preg_of. rewrite H0. auto.
Qed.
Hint Resolve agree_set_twice_mireg: ppcgen.

Lemma agree_set_commut:
  forall ms sp rs r1 r2 v1 v2,
  r1 <> r2 ->
  agree ms sp ((rs#r2 <- v2)#r1 <- v1) ->
  agree ms sp ((rs#r1 <- v1)#r2 <- v2).
Proof.
  intros. apply agree_exten_1 with ((rs#r2 <- v2)#r1 <- v1). auto.
  intros. 
  case (preg_eq r r1); intro.
  subst r1. rewrite Pregmap.gss. rewrite Pregmap.gso. rewrite Pregmap.gss.
  auto. auto.
  case (preg_eq r r2); intro.
  subst r2. rewrite Pregmap.gss. rewrite Pregmap.gso. rewrite Pregmap.gss.
  auto. auto.
  repeat (rewrite Pregmap.gso; auto). 
Qed. 
Hint Resolve agree_set_commut: ppcgen.

Lemma agree_nextinstr_commut:
  forall ms sp rs r v,
  agree ms sp (rs#r <- v) ->
  r <> PC ->
  agree ms sp ((nextinstr rs)#r <- v).
Proof.
  intros. unfold nextinstr. apply agree_set_commut. auto. 
  apply agree_set_other. auto. auto. 
Qed.
Hint Resolve agree_nextinstr_commut: ppcgen.

Lemma agree_set_mireg_exten:
  forall ms sp rs r v (rs': regset),
  agree ms sp rs ->
  mreg_type r = Tint ->
  rs'#(ireg_of r) = v ->
  (forall r', r' <> PC -> r' <> ireg_of r -> r' <> IR14 -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. apply agree_exten_2 with (rs#(ireg_of r) <- v).
  auto with ppcgen.
  intros. unfold Pregmap.set. case (PregEq.eq r0 (ireg_of r)); intro.
  subst r0. auto. apply H2; auto.
Qed.

(** Useful properties of the PC and GPR0 registers. *)

Lemma nextinstr_inv:
  forall r rs, r <> PC -> (nextinstr rs)#r = rs#r.
Proof.
  intros. unfold nextinstr. apply Pregmap.gso. auto.
Qed.
Hint Resolve nextinstr_inv: ppcgen.

Lemma nextinstr_set_preg:
  forall rs m v,
  (nextinstr (rs#(preg_of m) <- v))#PC = Val.add rs#PC Vone.
Proof.
  intros. unfold nextinstr. rewrite Pregmap.gss. 
  rewrite Pregmap.gso. auto. apply sym_not_eq. auto with ppcgen.
Qed.
Hint Resolve nextinstr_set_preg: ppcgen.

(** Connection between Mach and Asm calling conventions for external
    functions. *)

Lemma extcall_arg_match:
  forall ms sp rs m l v,
  agree ms sp rs ->
  Machconcr.extcall_arg ms m sp l v ->
  Asm.extcall_arg rs m l v.
Proof.
  intros. inv H0. 
  rewrite (preg_val _ _ _ r H). constructor.
  rewrite (sp_val _ _ _ H) in H1.
  destruct ty; unfold load_stack in H1.
  econstructor. reflexivity. assumption.
  econstructor. reflexivity. assumption.
Qed.

Lemma extcall_args_match:
  forall ms sp rs m, agree ms sp rs ->
  forall ll vl,
  Machconcr.extcall_args ms m sp ll vl ->
  Asm.extcall_args rs m ll vl.
Proof.
  induction 2; constructor; auto. eapply extcall_arg_match; eauto.
Qed.

Lemma extcall_arguments_match:
  forall ms m sp rs sg args,
  agree ms sp rs ->
  Machconcr.extcall_arguments ms m sp sg args ->
  Asm.extcall_arguments rs m sg args.
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
  simpl. rewrite B. rewrite C; auto with ppcgen. congruence.
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

Ltac TypeInv :=
  match goal with
  | H: (List.map ?f ?x = nil) |- _ =>
      destruct x; [clear H | simpl in H; discriminate]
  | H: (List.map ?f ?x = ?hd :: ?tl) |- _ =>
      destruct x; simpl in H;
      [ discriminate |
        injection H; clear H; let T := fresh "T" in (
          intros H T; TypeInv) ]
  | _ => idtac
  end.

(** Translation of conditions. *)

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
  /\ forall r', is_data_reg r' -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1. intuition; try reflexivity. 
  rewrite nextinstr_inv; [unfold compare_int; repeat rewrite Pregmap.gso; auto | idtac];
  red; intro; subst r'; elim H.
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
  /\ forall r', is_data_reg r' -> rs'#r' = rs#r'.
Proof.
  intros. unfold rs'. intuition; try reflexivity. 
  rewrite nextinstr_inv; [unfold compare_float; repeat rewrite Pregmap.gso; auto | idtac];
  red; intro; subst r'; elim H.
Qed.

Lemma transl_cond_correct:
  forall cond args k ms sp rs m b,
  map mreg_type args = type_of_condition cond ->
  agree ms sp rs ->
  eval_condition cond (map ms args) = Some b ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ rs'#(CR (crbit_for_cond cond)) = Val.of_bool b
  /\ agree ms sp rs'.
Proof.
  intros.
  rewrite <- (eval_condition_weaken _ _ H1). clear H1. 
  destruct cond; simpl in H; TypeInv; simpl.
  (* Ccomp *)
  generalize (compare_int_spec rs ms#m0 ms#m1).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_int rs ms#m0 ms#m1)).
  split. apply exec_straight_one. simpl. 
  repeat rewrite <- (ireg_val ms sp rs); trivial. 
  reflexivity.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs; auto.
  (* Ccompu *)
  generalize (compare_int_spec rs ms#m0 ms#m1).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_int rs ms#m0 ms#m1)).
  split. apply exec_straight_one. simpl. 
  repeat rewrite <- (ireg_val ms sp rs); trivial. 
  reflexivity.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs; auto.
  (* Ccompshift *)
  generalize (compare_int_spec rs ms#m0 (eval_shift_total s ms#m1)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_int rs ms#m0 (eval_shift_total s ms#m1))).
  split. apply exec_straight_one. simpl.
  rewrite transl_shift_correct. 
  repeat rewrite <- (ireg_val ms sp rs); trivial.
  reflexivity.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs; auto.
  (* Ccompushift *)
  generalize (compare_int_spec rs ms#m0 (eval_shift_total s ms#m1)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_int rs ms#m0 (eval_shift_total s ms#m1))).
  split. apply exec_straight_one. simpl.
  rewrite transl_shift_correct. 
  repeat rewrite <- (ireg_val ms sp rs); trivial.
  reflexivity.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs; auto.
  (* Ccompimm *)
  destruct (is_immed_arith i).
  generalize (compare_int_spec rs ms#m0 (Vint i)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_int rs ms#m0 (Vint i))).
  split. apply exec_straight_one. simpl. 
  rewrite <- (ireg_val ms sp rs); trivial. auto.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs; auto.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  assert (AG: agree ms sp rs'). apply agree_exten_2 with rs; auto. 
  generalize (compare_int_spec rs' ms#m0 (Vint i)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_int rs' ms#m0 (Vint i))).
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite <- (ireg_val ms sp rs'); trivial. auto.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs'; auto.
  (* Ccompuimm *)
  destruct (is_immed_arith i).
  generalize (compare_int_spec rs ms#m0 (Vint i)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_int rs ms#m0 (Vint i))).
  split. apply exec_straight_one. simpl. 
  rewrite <- (ireg_val ms sp rs); trivial. auto.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs; auto.
  exploit (loadimm_correct IR14). intros [rs' [P [Q R]]].
  assert (AG: agree ms sp rs'). apply agree_exten_2 with rs; auto. 
  generalize (compare_int_spec rs' ms#m0 (Vint i)).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_int rs' ms#m0 (Vint i))).
  split. eapply exec_straight_trans. eexact P. apply exec_straight_one. simpl.
  rewrite Q. rewrite <- (ireg_val ms sp rs'); trivial. auto.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs'; auto.
  (* Ccompf *)
  generalize (compare_float_spec rs ms#m0 ms#m1).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_float rs ms#m0 ms#m1)).
  split. apply exec_straight_one. simpl. 
  repeat rewrite <- (freg_val ms sp rs); trivial. auto.
  split. 
  case c; simpl; auto.
  apply agree_exten_1 with rs; auto.
  (* Cnotcompf *)
  generalize (compare_float_spec rs ms#m0 ms#m1).
  intros [A [B [C [D [E [F [G [H [I [J K]]]]]]]]]].
  exists (nextinstr (compare_float rs ms#m0 ms#m1)).
  split. apply exec_straight_one. simpl. 
  repeat rewrite <- (freg_val ms sp rs); trivial. auto.
  split. 
  case c; simpl; auto.
    rewrite Val.negate_cmpf_ne. auto.
    rewrite Val.negate_cmpf_eq. auto.
  apply agree_exten_1 with rs; auto.
Qed.

(** Translation of arithmetic operations. *)

Ltac TranslOpSimpl :=
  match goal with
  | |- exists rs' : regset,
         exec_straight ?c ?rs ?m ?k rs' ?m /\
         agree (Regmap.set ?res ?v ?ms) ?sp rs'  =>
    (exists (nextinstr (rs#(ireg_of res) <- v));
     split; 
     [ apply exec_straight_one;
       [ repeat (rewrite (ireg_val ms sp rs); auto);
         simpl; try rewrite transl_shift_correct; reflexivity
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

Lemma transl_op_correct:
  forall op args res k ms sp rs m v,
  wt_instr (Mop op args res) ->
  agree ms sp rs ->
  eval_operation ge sp op (map ms args) = Some v ->
  exists rs',
     exec_straight (transl_op op args res k) rs m k rs' m
  /\ agree (Regmap.set res v ms) sp rs'.
Proof.
  intros. rewrite <- (eval_operation_weaken _ _ _ _ H1). (*clear H1; clear v.*)
  inversion H.
  (* Omove *)
  simpl. exists (nextinstr (rs#(preg_of res) <- (ms r1))).
  split. caseEq (mreg_type r1); intro.
  apply exec_straight_one. simpl. rewrite (ireg_val ms sp rs); auto.
  simpl. unfold preg_of. rewrite <- H3. rewrite H6. reflexivity.
  auto with ppcgen.
  apply exec_straight_one. simpl. rewrite (freg_val ms sp rs); auto.
  simpl. unfold preg_of. rewrite <- H3. rewrite H6. reflexivity.
  auto with ppcgen.
  auto with ppcgen.
  (* Other instructions *)
  clear H2 H3 H5. 
  destruct op; simpl in H6; injection H6; clear H6; intros;
  TypeInv; simpl; try (TranslOpSimpl).
  (* Omove again *)
  congruence.
  (* Ointconst *)
  generalize (loadimm_correct (ireg_of res) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. 
  apply agree_set_mireg_exten with rs; auto. 
  (* Oaddrstack *)
  generalize (addimm_correct (ireg_of res) IR13 i k rs m). 
  intros [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  apply agree_set_mireg_exten with rs; auto.
  rewrite (sp_val ms sp rs). auto. auto.
  (* Ocast8signed *)
  set (rs1 := nextinstr (rs#(ireg_of res) <- (Val.shl (ms m0) (Vint (Int.repr 24))))).
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (Val.shr (rs1 (ireg_of res)) (Vint (Int.repr 24))))).
  exists rs2. split.
  apply exec_straight_two with rs1 m; auto.
  simpl. rewrite <- (ireg_val ms sp rs); auto.
  unfold rs2. 
  replace (Val.shr (rs1 (ireg_of res)) (Vint (Int.repr 24))) with (Val.sign_ext 8 (ms m0)).
  apply agree_nextinstr. unfold rs1. apply agree_nextinstr_commut.
  apply agree_set_mireg_twice; auto with ppcgen. auto with ppcgen. 
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  destruct (ms m0); simpl; auto. rewrite Int.sign_ext_shr_shl. reflexivity.
  vm_compute; auto. 
  (* Ocast8unsigned *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.and (ms m0) (Vint (Int.repr 255))))).
  split. apply exec_straight_one. repeat (rewrite (ireg_val ms sp rs)); auto. reflexivity.
  replace (Val.zero_ext 8 (ms m0))
      with (Val.and (ms m0) (Vint (Int.repr 255))).
  auto with ppcgen. 
  destruct (ms m0); simpl; auto. rewrite Int.zero_ext_and. reflexivity. 
  vm_compute; auto.
  (* Ocast16signed *)
  set (rs1 := nextinstr (rs#(ireg_of res) <- (Val.shl (ms m0) (Vint (Int.repr 16))))).
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (Val.shr (rs1 (ireg_of res)) (Vint (Int.repr 16))))).
  exists rs2. split.
  apply exec_straight_two with rs1 m; auto.
  simpl. rewrite <- (ireg_val ms sp rs); auto. 
  unfold rs2. 
  replace (Val.shr (rs1 (ireg_of res)) (Vint (Int.repr 16))) with (Val.sign_ext 16 (ms m0)).
  apply agree_nextinstr. unfold rs1. apply agree_nextinstr_commut.
  apply agree_set_mireg_twice; auto with ppcgen. auto with ppcgen. 
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  destruct (ms m0); simpl; auto. rewrite Int.sign_ext_shr_shl. reflexivity.
  vm_compute; auto. 
  (* Ocast16unsigned *)
  set (rs1 := nextinstr (rs#(ireg_of res) <- (Val.shl (ms m0) (Vint (Int.repr 16))))).
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (Val.shru (rs1 (ireg_of res)) (Vint (Int.repr 16))))).
  exists rs2. split.
  apply exec_straight_two with rs1 m; auto.
  simpl. rewrite <- (ireg_val ms sp rs); auto. 
  unfold rs2. 
  replace (Val.shru (rs1 (ireg_of res)) (Vint (Int.repr 16))) with (Val.zero_ext 16 (ms m0)).
  apply agree_nextinstr. unfold rs1. apply agree_nextinstr_commut.
  apply agree_set_mireg_twice; auto with ppcgen. auto with ppcgen. 
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  destruct (ms m0); simpl; auto. rewrite Int.zero_ext_shru_shl. reflexivity.
  vm_compute; auto. 
  (* Oaddimm *)
  generalize (addimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto.
  apply agree_set_mireg_exten with rs; auto.
  rewrite (ireg_val ms sp rs); auto. 
  (* Orsbimm *)
  exploit (makeimm_correct Prsb (fun v1 v2 => Val.sub v2 v1) (ireg_of res) (ireg_of m0));
  auto with ppcgen.
  intros [rs' [A [B C]]].
  exists rs'.
  split. eauto.
  apply agree_set_mireg_exten with rs; auto. rewrite B. 
  rewrite <- (ireg_val ms sp rs); auto. 
  (* Omul *)
  destruct (ireg_eq (ireg_of res) (ireg_of m0) || ireg_eq (ireg_of res) (ireg_of m1)).
  set (rs1 := nextinstr (rs#IR14 <- (Val.mul (ms m0) (ms m1)))).
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (rs1#IR14))).
  exists rs2; split.
  apply exec_straight_two with rs1 m; auto.
  simpl. repeat rewrite <- (ireg_val ms sp rs); auto.
  unfold rs2. unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss. 
  apply agree_nextinstr. apply agree_nextinstr_commut. 
  apply agree_set_mireg; auto.  apply agree_set_mreg. apply agree_set_other. auto.
  simpl; auto. auto with ppcgen. discriminate.
  TranslOpSimpl.
  (* Oandimm *)
  generalize (andimm_correct (ireg_of res) (ireg_of m0) i k rs m
                            (ireg_of_not_IR14 m0)).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto.
  apply agree_set_mireg_exten with rs; auto.
  rewrite (ireg_val ms sp rs); auto. 
  (* Oorimm *)
  exploit (makeimm_correct Porr Val.or (ireg_of res) (ireg_of m0));
  auto with ppcgen.
  intros [rs' [A [B C]]].
  exists rs'.
  split. eauto.
  apply agree_set_mireg_exten with rs; auto. rewrite B. 
  rewrite <- (ireg_val ms sp rs); auto. 
  (* Oxorimm *)
  exploit (makeimm_correct Peor Val.xor (ireg_of res) (ireg_of m0));
  auto with ppcgen.
  intros [rs' [A [B C]]].
  exists rs'.
  split. eauto.
  apply agree_set_mireg_exten with rs; auto. rewrite B. 
  rewrite <- (ireg_val ms sp rs); auto.
  (* Oshrximm *)
  assert (exists n, ms m0 = Vint n /\ Int.ltu i (Int.repr 31) = true).
    simpl in H1. destruct (ms m0); try discriminate.
    exists i0; split; auto. destruct (Int.ltu i (Int.repr 31)); discriminate || auto.
  destruct H3 as [n [ARG1 LTU]].
  assert (LTU': Int.ltu i (Int.repr 32) = true).
    exploit Int.ltu_inv. eexact LTU. intro.
    unfold Int.ltu. apply zlt_true.
    assert (Int.unsigned (Int.repr 31) < Int.unsigned (Int.repr 32)). vm_compute; auto.
    omega.
  assert (RSm0: rs (ireg_of m0) = Vint n).
    rewrite <- ARG1. symmetry. eapply ireg_val; eauto. 
  set (islt := Int.lt n Int.zero).
  set (rs1 := nextinstr (compare_int rs (Vint n) (Vint Int.zero))).
  assert (OTH1: forall r', is_data_reg r' -> rs1#r' = rs#r').
    generalize (compare_int_spec rs (Vint n) (Vint Int.zero)).
    fold rs1. intros [A B]. intuition.
  exploit (addimm_correct IR14 (ireg_of m0) (Int.sub (Int.shl Int.one i) Int.one)).
  intros [rs2 [EXEC2 [RES2 OTH2]]].
  set (rs3 := nextinstr (if islt then rs2 else rs2#IR14 <- (Vint n))).
  set (rs4 := nextinstr (rs3#(ireg_of res) <- (Val.shr rs3#IR14 (Vint i)))).
  exists rs4; split.
  apply exec_straight_step with rs1 m.
  simpl. rewrite RSm0. auto. auto.
  eapply exec_straight_trans. eexact EXEC2.
  apply exec_straight_two with rs3 m.
  simpl. rewrite OTH2. change (rs1 CRge) with (Val.cmp Cge (Vint n) (Vint Int.zero)).
    unfold Val.cmp. change (Int.cmp Cge n Int.zero) with (negb islt).
    rewrite OTH2. rewrite OTH1. rewrite RSm0. 
    unfold rs3. case islt; reflexivity.
    apply ireg_of_is_data_reg. decEq; auto with ppcgen. auto with ppcgen. congruence. congruence.
  simpl. auto. 
  auto. unfold rs3. case islt; auto. auto.
  (* agreement *)
  assert (RES4: rs4#(ireg_of res) = Vint(Int.shrx n i)).
    unfold rs4. rewrite nextinstr_inv; auto. rewrite Pregmap.gss.
    rewrite Int.shrx_shr. fold islt. unfold rs3.
    repeat rewrite nextinstr_inv; auto. 
    case islt. rewrite RES2. rewrite OTH1. rewrite RSm0. 
    simpl. rewrite LTU'. auto.
    apply ireg_of_is_data_reg. 
    rewrite Pregmap.gss. simpl. rewrite LTU'. auto. congruence.
    exact LTU. auto with ppcgen. 
  assert (OTH4: forall r, is_data_reg r -> r <> ireg_of res -> rs4#r = rs#r).
    intros. 
    assert (r <> PC). red; intro; subst r; elim H3.
    assert (r <> IR14). red; intro; subst r; elim H3.
    unfold rs4. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
    unfold rs3. rewrite nextinstr_inv; auto.
    transitivity (rs2 r).
    case islt. auto. apply Pregmap.gso; auto.
    rewrite OTH2; auto. 
  apply agree_exten_1 with (rs#(ireg_of res) <- (Val.shrx (ms m0) (Vint i))).
  auto with ppcgen.
  intros. unfold Pregmap.set. destruct (PregEq.eq r (ireg_of res)).
  subst r. rewrite ARG1. simpl. rewrite LTU'. auto.
  auto.
  (* Ointoffloat *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.intoffloat (ms m0)))).
  split. apply exec_straight_one. 
  repeat (rewrite (freg_val ms sp rs); auto).
  reflexivity. auto with ppcgen.
  (* Ointuoffloat *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.intuoffloat (ms m0)))).
  split. apply exec_straight_one. 
  repeat (rewrite (freg_val ms sp rs); auto).
  reflexivity. auto with ppcgen.
  (* Ofloatofint *)
  exists (nextinstr (rs#(freg_of res) <- (Val.floatofint (ms m0)))).
  split. apply exec_straight_one. 
  repeat (rewrite (ireg_val ms sp rs); auto).
  reflexivity. auto 10 with ppcgen.
  (* Ofloatofintu *)
  exists (nextinstr (rs#(freg_of res) <- (Val.floatofintu (ms m0)))).
  split. apply exec_straight_one. 
  repeat (rewrite (ireg_val ms sp rs); auto).
  reflexivity. auto 10 with ppcgen.
  (* Ocmp *)
  assert (exists b, eval_condition c ms##args = Some b /\ v = Val.of_bool b).
    simpl in H1. destruct (eval_condition c ms##args). 
    destruct b; inv H1. exists true; auto. exists false; auto.
    discriminate.
  destruct H5 as [b [EVC EQ]].
  exploit transl_cond_correct; eauto. intros [rs' [A [B C]]].
  rewrite (eval_condition_weaken _ _ EVC).
  set (rs1 := nextinstr (rs'#(ireg_of res) <- (Vint Int.zero))).
  set (rs2 := nextinstr (if b then (rs1#(ireg_of res) <- Vtrue) else rs1)).
  exists rs2; split.
  eapply exec_straight_trans. eauto. 
  apply exec_straight_two with rs1 m; auto.
  simpl. replace (rs1 (crbit_for_cond c)) with (Val.of_bool b).
  unfold rs2. destruct b; auto. 
  unfold rs2. destruct b; auto.
  apply agree_set_mireg_exten with rs'; auto.
  unfold rs2. rewrite nextinstr_inv; auto with ppcgen. 
  destruct b. apply Pregmap.gss.
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. unfold rs2. rewrite nextinstr_inv; auto. 
  transitivity (rs1 r'). destruct b; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
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
    eval_addressing_total sp addr (map ms args) = Val.add rs1#r1 (Vint n) ->
    agree ms sp rs1 ->
    exists rs',
    exec_straight (mk_instr_imm r1 n :: k) rs1 m k rs' m' /\
    agree ms' sp rs') ->
  match mk_instr_gen with
  | None => True
  | Some mk =>
      (forall (r1: ireg) (sa: shift_addr) (rs1: regset) k,
      eval_addressing_total sp addr (map ms args) = Val.add rs1#r1 (eval_shift_addr sa rs1) ->
      agree ms sp rs1 ->
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
  apply H; eauto. simpl. rewrite (ireg_val ms sp rs); auto.
  (* Aindexed, large displacement *)
  exploit (addimm_correct IR14 (ireg_of t)); eauto with ppcgen. 
  intros [rs' [A [B C]]].
  exploit (H IR14 rs' Int.zero); eauto.
  simpl. rewrite (ireg_val ms sp rs); auto. rewrite B.
  rewrite Val.add_assoc. simpl Val.add. rewrite Int.add_zero. reflexivity.
  apply agree_exten_2 with rs; auto. 
  intros [rs'' [D E]].
  exists rs''; split.
  eapply exec_straight_trans. eexact A. eexact D. auto.
  (* Aindexed2 *)
  destruct mk_instr_gen as [mk | ]. 
  (* binary form available *)
  apply H0; auto. simpl. repeat rewrite (ireg_val ms sp rs); auto. 
  (* binary form not available *)
  set (rs' := nextinstr (rs#IR14 <- (Val.add (ms t) (ms t0)))).
  exploit (H IR14 rs' Int.zero); eauto.
  simpl. repeat rewrite (ireg_val ms sp rs); auto.
  unfold rs'. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  repeat rewrite (ireg_val ms sp rs); auto. apply val_add_add_zero. 
  unfold rs'; auto with ppcgen.
  intros [rs'' [A B]].
  exists rs''; split.
  eapply exec_straight_step with (rs2 := rs'); eauto.
  simpl. repeat rewrite <- (ireg_val ms sp rs); auto.
  auto.
  (* Aindexed2shift *)
  destruct mk_instr_gen as [mk | ]. 
  (* binary form available *)
  apply H0; auto. simpl. repeat rewrite (ireg_val ms sp rs); auto.
  rewrite transl_shift_addr_correct. auto.
  (* binary form not available *)
  set (rs' := nextinstr (rs#IR14 <- (Val.add (ms t) (eval_shift_total s (ms t0))))).
  exploit (H IR14 rs' Int.zero); eauto.
  simpl. repeat rewrite (ireg_val ms sp rs); auto.
  unfold rs'. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  repeat rewrite (ireg_val ms sp rs); auto. apply val_add_add_zero. 
  unfold rs'; auto with ppcgen.
  intros [rs'' [A B]].
  exists rs''; split.
  eapply exec_straight_step with (rs2 := rs'); eauto.
  simpl. rewrite transl_shift_correct. 
  repeat rewrite <- (ireg_val ms sp rs); auto.
  auto.
  (* Ainstack *)
  destruct (is_immed i).
  (* Ainstack, short displacement *)
  apply H. simpl.  rewrite (sp_val ms sp rs); auto. auto. 
  (* Ainstack, large displacement *)
  exploit (addimm_correct IR14 IR13); eauto with ppcgen. 
  intros [rs' [A [B C]]].
  exploit (H IR14 rs' Int.zero); eauto.
  simpl. rewrite (sp_val ms sp rs); auto. rewrite B.
  rewrite Val.add_assoc. simpl Val.add. rewrite Int.add_zero. reflexivity.
  apply agree_exten_2 with rs; auto. 
  intros [rs'' [D E]].
  exists rs''; split.
  eapply exec_straight_trans. eexact A. eexact D. auto.
Qed.

Lemma transl_load_int_correct:
  forall (mk_instr: ireg -> ireg -> shift_addr -> instruction)
         (is_immed: int -> bool)
         (rd: mreg) addr args k ms sp rs m chunk a v,
  (forall (c: code) (r1 r2: ireg) (sa: shift_addr) (rs1: regset),
    exec_instr ge c (mk_instr r1 r2 sa) rs1 m =
    exec_load chunk (Val.add rs1#r2 (eval_shift_addr sa rs1)) r1 rs1 m) ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  mreg_type rd = Tint ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
    exec_straight (transl_load_store_int mk_instr is_immed rd addr args k) rs m
                        k rs' m
  /\ agree (Regmap.set rd v ms) sp rs'.
Proof.
  intros. unfold transl_load_store_int.
  exploit eval_addressing_weaken. eauto. intros. 
  apply transl_load_store_correct with ms; auto.
  intros. exists (nextinstr (rs1#(ireg_of rd) <- v)); split.
  apply exec_straight_one. rewrite H. simpl. rewrite <- H6. rewrite H5. 
  unfold exec_load. rewrite H4. auto. auto.
  auto with ppcgen.
  intros. exists (nextinstr (rs1#(ireg_of rd) <- v)); split.
  apply exec_straight_one. rewrite H. simpl. rewrite <- H6. rewrite H5. 
  unfold exec_load. rewrite H4. auto. auto.
  auto with ppcgen.
Qed.

Lemma transl_load_float_correct:
  forall (mk_instr: freg -> ireg -> int -> instruction)
         (is_immed: int -> bool)
         (rd: mreg) addr args k ms sp rs m chunk a v,
  (forall (c: code) (r1: freg) (r2: ireg) (n: int) (rs1: regset),
    exec_instr ge c (mk_instr r1 r2 n) rs1 m =
    exec_load chunk (Val.add rs1#r2 (Vint n)) r1 rs1 m) ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  mreg_type rd = Tfloat ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
    exec_straight (transl_load_store_float mk_instr is_immed rd addr args k) rs m
                        k rs' m
  /\ agree (Regmap.set rd v ms) sp rs'.
Proof.
  intros. unfold transl_load_store_float.
  exploit eval_addressing_weaken. eauto. intros. 
  apply transl_load_store_correct with ms; auto.
  intros. exists (nextinstr (rs1#(freg_of rd) <- v)); split.
  apply exec_straight_one. rewrite H. rewrite <- H6. rewrite H5. 
  unfold exec_load. rewrite H4. auto. auto.
  auto with ppcgen.
Qed.

Lemma transl_store_int_correct:
  forall (mk_instr: ireg -> ireg -> shift_addr -> instruction)
         (is_immed: int -> bool)
         (rd: mreg) addr args k ms sp rs m chunk a m',
  (forall (c: code) (r1 r2: ireg) (sa: shift_addr) (rs1: regset),
    exec_instr ge c (mk_instr r1 r2 sa) rs1 m =
    exec_store chunk (Val.add rs1#r2 (eval_shift_addr sa rs1)) r1 rs1 m) ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  mreg_type rd = Tint ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.storev chunk m a (ms rd) = Some m' ->
  exists rs',
    exec_straight (transl_load_store_int mk_instr is_immed rd addr args k) rs m
                        k rs' m'
  /\ agree ms sp rs'.
Proof.
  intros. unfold transl_load_store_int.
  exploit eval_addressing_weaken. eauto. intros. 
  apply transl_load_store_correct with ms; auto.
  intros. exists (nextinstr rs1); split.
  apply exec_straight_one. rewrite H. simpl. rewrite <- H6. rewrite H5.
  unfold exec_store. rewrite <- (ireg_val ms sp rs1); auto.
  rewrite H4. auto. auto.
  auto with ppcgen.
  intros. exists (nextinstr rs1); split.
  apply exec_straight_one. rewrite H. simpl. rewrite <- H6. rewrite H5.
  unfold exec_store. rewrite <- (ireg_val ms sp rs1); auto.
  rewrite H4. auto. auto.
  auto with ppcgen.
Qed.

Lemma transl_store_float_correct:
  forall (mk_instr: freg -> ireg -> int -> instruction)
         (is_immed: int -> bool)
         (rd: mreg) addr args k ms sp rs m chunk a m',
  (forall (c: code) (r1: freg) (r2: ireg) (n: int) (rs1: regset),
    exec_instr ge c (mk_instr r1 r2 n) rs1 m =
    exec_store chunk (Val.add rs1#r2 (Vint n)) r1 rs1 m) ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  mreg_type rd = Tfloat ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.storev chunk m a (ms rd) = Some m' ->
  exists rs',
    exec_straight (transl_load_store_float mk_instr is_immed rd addr args k) rs m
                        k rs' m'
  /\ agree ms sp rs'.
Proof.
  intros. unfold transl_load_store_float.
  exploit eval_addressing_weaken. eauto. intros. 
  apply transl_load_store_correct with ms; auto.
  intros. exists (nextinstr rs1); split.
  apply exec_straight_one. rewrite H. simpl. rewrite <- H6. rewrite H5.
  unfold exec_store. rewrite <- (freg_val ms sp rs1); auto.
  rewrite H4. auto. auto.
  auto with ppcgen.
Qed.

End STRAIGHTLINE.


(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Errors Maps.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Op Locations Mach Conventions.
Require Import Asm Asmgen Asmgenproof0.

(** Decomposition of integer constants. *)

Lemma make_immed32_sound:
  forall n,
  match make_immed32 n with
  | Imm32_single imm => n = imm
  | Imm32_pair hi lo => n = Int.add (Int.shl hi (Int.repr 12)) lo
  end.
Proof.
  intros; unfold make_immed32. set (lo := Int.sign_ext 12 n).
  predSpec Int.eq Int.eq_spec n lo.
- auto.
- set (m := Int.sub n lo).
  assert (A: Int.eqmod (two_p 12) (Int.unsigned lo) (Int.unsigned n)) by (apply Int.eqmod_sign_ext'; compute; auto).
  assert (B: Int.eqmod (two_p 12) (Int.unsigned n - Int.unsigned  lo) 0).
  { replace 0 with (Int.unsigned n - Int.unsigned n) by omega.
    auto using Int.eqmod_sub, Int.eqmod_refl. }
  assert (C: Int.eqmod (two_p 12) (Int.unsigned m) 0).
  { apply Int.eqmod_trans with (Int.unsigned n - Int.unsigned lo); auto.
    apply Int.eqmod_divides with Int.modulus. apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
    exists (two_p (32-12)); auto. }
  assert (D: Int.modu m (Int.repr 4096) = Int.zero).
  { apply Int.eqmod_mod_eq in C. unfold Int.modu. 
    change (Int.unsigned (Int.repr 4096)) with (two_p 12). rewrite C. 
    reflexivity.
    apply two_p_gt_ZERO; omega. }
  rewrite <- (Int.divu_pow2 m (Int.repr 4096) (Int.repr 12)) by auto.
  rewrite Int.shl_mul_two_p. 
  change (two_p (Int.unsigned (Int.repr 12))) with 4096.
  replace (Int.mul (Int.divu m (Int.repr 4096)) (Int.repr 4096)) with m.
  unfold m. rewrite Int.sub_add_opp. rewrite Int.add_assoc. rewrite <- (Int.add_commut lo).
  rewrite Int.add_neg_zero. rewrite Int.add_zero. auto.
  rewrite (Int.modu_divu_Euclid m (Int.repr 4096)) at 1 by (vm_compute; congruence).
  rewrite D. apply Int.add_zero.
Qed.

Lemma make_immed64_sound:
  forall n,
  match make_immed64 n with
  | Imm64_single imm => n = imm
  | Imm64_pair hi lo => n = Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo
  | Imm64_large imm => n = imm
  end.
Proof.
  intros; unfold make_immed64. set (lo := Int64.sign_ext 12 n).
  predSpec Int64.eq Int64.eq_spec n lo.
- auto.
- set (m := Int64.sub n lo).
  set (p := Int64.zero_ext 20 (Int64.shru m (Int64.repr 12))).
  predSpec Int64.eq Int64.eq_spec n (Int64.add (Int64.sign_ext 32 (Int64.shl p (Int64.repr 12))) lo).
  auto.
  auto.
Qed.

(** Properties of registers *)

Lemma ireg_of_not_X31:
  forall m r, ireg_of m = OK r -> IR r <> IR X31.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.

Lemma ireg_of_not_X31':
  forall m r, ireg_of m = OK r -> r <> X31.
Proof.
  intros. apply ireg_of_not_X31 in H. congruence.
Qed.

Hint Resolve ireg_of_not_X31 ireg_of_not_X31': asmgen.

(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of RISC-V constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** 32-bit integer constants and arithmetic *)

Lemma load_hilo32_correct:
  forall rd hi lo k rs m,
  exists rs',
     exec_straight ge fn (load_hilo32 rd hi lo k) rs m k rs' m
  /\ rs'#rd = Vint (Int.add (Int.shl hi (Int.repr 12)) lo)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold load_hilo32; intros. 
  predSpec Int.eq Int.eq_spec lo Int.zero.
- subst lo. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. rewrite Int.add_zero. Simpl.
  intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split. Simpl. 
  intros; Simpl.
Qed.

Lemma loadimm32_correct:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm32 rd n k) rs m k rs' m
  /\ rs'#rd = Vint n
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm32; intros. generalize (make_immed32_sound n); intros E.
  destruct (make_immed32 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. rewrite Int.add_zero_l; Simpl. 
  intros; Simpl.
- rewrite E. apply load_hilo32_correct.
Qed.

Lemma opimm32_correct:
  forall (op: ireg -> ireg0 -> ireg0 -> instruction)
         (opi: ireg -> ireg0 -> int -> instruction)
         (sem: val -> val -> val) m,
  (forall d s1 s2 rs,
   exec_instr ge fn (op d s1 s2) rs m = Next (nextinstr (rs#d <- (sem rs##s1 rs##s2))) m) ->
  (forall d s n rs,
   exec_instr ge fn (opi d s n) rs m = Next (nextinstr (rs#d <- (sem rs##s (Vint n)))) m) ->
  forall rd r1 n k rs,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (opimm32 op opi rd r1 n k) rs m k rs' m
  /\ rs'#rd = sem rs##r1 (Vint n)
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold opimm32. generalize (make_immed32_sound n); intros E.
  destruct (make_immed32 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. rewrite H0. simpl; eauto. auto.
  split. Simpl. intros; Simpl.
- destruct (load_hilo32_correct X31 hi lo (op rd r1 X31 :: k) rs m)
  as (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. 
  rewrite H; eauto. auto.
  split. Simpl. simpl. rewrite B, C, E. auto. congruence. congruence.
  intros; Simpl. 
Qed.

(** 64-bit integer constants and arithmetic *)

Lemma load_hilo64_correct:
  forall rd hi lo k rs m,
  exists rs',
     exec_straight ge fn (load_hilo64 rd hi lo k) rs m k rs' m
  /\ rs'#rd = Vlong (Int64.add (Int64.sign_ext 32 (Int64.shl hi (Int64.repr 12))) lo)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold load_hilo64; intros. 
  predSpec Int64.eq Int64.eq_spec lo Int64.zero.
- subst lo. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. rewrite Int64.add_zero. Simpl.
  intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split. Simpl. 
  intros; Simpl.
Qed.

Lemma loadimm64_correct:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm64 rd n k) rs m k rs' m
  /\ rs'#rd = Vlong n
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  unfold loadimm64; intros. generalize (make_immed64_sound n); intros E.
  destruct (make_immed64 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. rewrite Int64.add_zero_l; Simpl. 
  intros; Simpl.
- exploit load_hilo64_correct; eauto. intros (rs' & A & B & C).
  rewrite E. exists rs'; eauto.
- subst imm. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. 
  intros; Simpl.
Qed.

Lemma opimm64_correct:
  forall (op: ireg -> ireg0 -> ireg0 -> instruction)
         (opi: ireg -> ireg0 -> int64 -> instruction)
         (sem: val -> val -> val) m,
  (forall d s1 s2 rs,
   exec_instr ge fn (op d s1 s2) rs m = Next (nextinstr (rs#d <- (sem rs###s1 rs###s2))) m) ->
  (forall d s n rs,
   exec_instr ge fn (opi d s n) rs m = Next (nextinstr (rs#d <- (sem rs###s (Vlong n)))) m) ->
  forall rd r1 n k rs,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (opimm64 op opi rd r1 n k) rs m k rs' m
  /\ rs'#rd = sem rs##r1 (Vlong n)
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold opimm64. generalize (make_immed64_sound n); intros E.
  destruct (make_immed64 n). 
- subst imm. econstructor; split. 
  apply exec_straight_one. rewrite H0. simpl; eauto. auto.
  split. Simpl. intros; Simpl.
- destruct (load_hilo64_correct X31 hi lo (op rd r1 X31 :: k) rs m)
  as (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. 
  rewrite H; eauto. auto.
  split. Simpl. simpl. rewrite B, C, E. auto. congruence. congruence.
  intros; Simpl. 
- subst imm. econstructor; split. 
  eapply exec_straight_two. simpl; eauto. rewrite H. simpl; eauto. auto. auto.
  split. Simpl. intros; Simpl.
Qed.

(** Add offset to pointer *)

Lemma addptrofs_correct:
  forall rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (addptrofs rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.offset_ptr rs#r1 n) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  unfold addptrofs; intros.
  destruct (Ptrofs.eq_dec n Ptrofs.zero).
- subst n. econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. destruct (rs r1); simpl; auto. rewrite Ptrofs.add_zero; auto.
  intros; Simpl.
- destruct Archi.ptr64 eqn:SF.
+ unfold addimm64.
  exploit (opimm64_correct Paddl Paddil Val.addl); eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto.
  rewrite B. simpl. destruct (rs r1); simpl; auto. rewrite SF.
  rewrite Ptrofs.of_int64_to_int64 by auto. auto.
+ unfold addimm32.
  exploit (opimm32_correct Paddw Paddiw Val.add); eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto.
  rewrite B. simpl. destruct (rs r1); simpl; auto. rewrite SF.
  rewrite Ptrofs.of_int_to_int by auto. auto.
Qed.

Lemma addptrofs_correct_2:
  forall rd r1 n k (rs: regset) m b ofs,
  r1 <> X31 -> rs#r1 = Vptr b ofs ->
  exists rs',
     exec_straight ge fn (addptrofs rd r1 n k) rs m k rs' m
  /\ rs'#rd = Vptr b (Ptrofs.add ofs n)
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. exploit (addptrofs_correct rd r1 n); eauto. intros (rs' & A & B & C).
  exists rs'; intuition eauto. 
  rewrite H0 in B. inv B. auto.
Qed.

(** Translation of conditional branches *)

Lemma transl_cbranch_int32s_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmp_bool cmp rs##r1 rs##r2 = Some b ->
  exec_instr ge fn (transl_cbranch_int32s cmp r1 r2 lbl) rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; rewrite ? H.
- destruct rs##r1; simpl in H; try discriminate. destruct rs##r2; inv H.
  simpl; auto.
- destruct rs##r1; simpl in H; try discriminate. destruct rs##r2; inv H.
  simpl; auto.
- auto.
- rewrite <- Val.swap_cmp_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmp_bool. simpl. rewrite H; auto.
- auto.
Qed.

Lemma transl_cbranch_int32u_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmpu_bool (Mem.valid_pointer m) cmp rs##r1 rs##r2 = Some b ->
  exec_instr ge fn (transl_cbranch_int32u cmp r1 r2 lbl) rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; rewrite ? H; auto.
- rewrite <- Val.swap_cmpu_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmpu_bool. simpl. rewrite H; auto.
Qed.

Lemma transl_cbranch_int64s_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmpl_bool cmp rs###r1 rs###r2 = Some b ->
  exec_instr ge fn (transl_cbranch_int64s cmp r1 r2 lbl) rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; rewrite ? H.
- destruct rs###r1; simpl in H; try discriminate. destruct rs###r2; inv H.
  simpl; auto.
- destruct rs###r1; simpl in H; try discriminate. destruct rs###r2; inv H.
  simpl; auto.
- auto.
- rewrite <- Val.swap_cmpl_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmpl_bool. simpl. rewrite H; auto.
- auto.
Qed.

Lemma transl_cbranch_int64u_correct:
  forall cmp r1 r2 lbl (rs: regset) m b,
  Val.cmplu_bool (Mem.valid_pointer m) cmp rs###r1 rs###r2 = Some b ->
  exec_instr ge fn (transl_cbranch_int64u cmp r1 r2 lbl) rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct cmp; simpl; rewrite ? H; auto.
- rewrite <- Val.swap_cmplu_bool. simpl. rewrite H; auto.
- rewrite <- Val.swap_cmplu_bool. simpl. rewrite H; auto.
Qed.

Lemma transl_cond_float_correct:
  forall (rs: regset) m cmp rd r1 r2 insn normal v,
  transl_cond_float cmp rd r1 r2 = (insn, normal) ->
  v = (if normal then Val.cmpf cmp rs#r1 rs#r2 else Val.notbool (Val.cmpf cmp rs#r1 rs#r2)) ->
  exec_instr ge fn insn rs m = Next (nextinstr (rs#rd <- v)) m.
Proof.
  intros. destruct cmp; simpl in H; inv H; auto. 
- rewrite Val.negate_cmpf_eq. auto.
- simpl. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpf, Val.cmpf_bool.
  rewrite <- Float.cmp_swap. auto.
- simpl. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpf, Val.cmpf_bool.
  rewrite <- Float.cmp_swap. auto.
Qed.

Lemma transl_cond_single_correct:
  forall (rs: regset) m cmp rd r1 r2 insn normal v,
  transl_cond_single cmp rd r1 r2 = (insn, normal) ->
  v = (if normal then Val.cmpfs cmp rs#r1 rs#r2 else Val.notbool (Val.cmpfs cmp rs#r1 rs#r2)) ->
  exec_instr ge fn insn rs m = Next (nextinstr (rs#rd <- v)) m.
Proof.
  intros. destruct cmp; simpl in H; inv H; auto. 
- simpl. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpfs, Val.cmpfs_bool.
  rewrite Float32.cmp_ne_eq. destruct (Float32.cmp Ceq f0 f); auto.
- simpl. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpfs, Val.cmpfs_bool.
  rewrite <- Float32.cmp_swap. auto.
- simpl. f_equal. f_equal. f_equal. destruct (rs r2), (rs r1); auto. unfold Val.cmpfs, Val.cmpfs_bool.
  rewrite <- Float32.cmp_swap. auto.
Qed.

Remark branch_on_X31:
  forall normal lbl (rs: regset) m b,
  rs#X31 = Val.of_bool (eqb normal b) -> 
  exec_instr ge fn (if normal then Pbnew X31 X0 lbl else Pbeqw X31 X0 lbl) rs m =
  eval_branch fn lbl rs m (Some b).
Proof.
  intros. destruct normal; simpl; rewrite H; simpl; destruct b; reflexivity. 
Qed.

Ltac ArgsInv :=
  repeat (match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  end);
  subst;
  repeat (match goal with
  | [ H: ireg_of _ = OK _ |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *
  | [ H: freg_of _ = OK _ |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *
  end).

Inductive exec_straight_opt: code -> regset -> mem -> code -> regset -> mem -> Prop :=
  | exec_straight_opt_refl: forall c rs m,
      exec_straight_opt c rs m c rs m
  | exec_straight_opt_intro: forall c1 rs1 m1 c2 rs2 m2,
      exec_straight ge fn c1 rs1 m1 c2 rs2 m2 ->
      exec_straight_opt c1 rs1 m1 c2 rs2 m2.

Remark exec_straight_opt_right:
  forall c3 rs3 m3 c1 rs1 m1 c2 rs2 m2,
  exec_straight_opt c1 rs1 m1 c2 rs2 m2 ->
  exec_straight ge fn c2 rs2 m2 c3 rs3 m3 ->
  exec_straight ge fn c1 rs1 m1 c3 rs3 m3.
Proof.
  destruct 1; intros. auto. eapply exec_straight_trans; eauto. 
Qed.

Lemma transl_cbranch_correct_1:
  forall cond args lbl k c m ms b sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some b ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = eval_branch fn lbl rs' m' (Some b)
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros TRANSL EVAL AG MEXT.
  set (vl' := map rs (map preg_of args)). 
  assert (EVAL': eval_condition cond vl' m' = Some b).
  { apply eval_condition_lessdef with (map ms args) m; auto. eapply preg_vals; eauto. }
  clear EVAL MEXT AG.
  destruct cond; simpl in TRANSL; ArgsInv.
- exists rs, (transl_cbranch_int32s c0 x x0 lbl).
  intuition auto. constructor. apply transl_cbranch_int32s_correct; auto.
- exists rs, (transl_cbranch_int32u c0 x x0 lbl).
  intuition auto. constructor. apply transl_cbranch_int32u_correct; auto.
- predSpec Int.eq Int.eq_spec n Int.zero.
+ subst n. exists rs, (transl_cbranch_int32s c0 x X0 lbl).
  intuition auto. constructor. apply transl_cbranch_int32s_correct; auto.
+ exploit (loadimm32_correct X31 n); eauto. intros (rs' & A & B & C).
  exists rs', (transl_cbranch_int32s c0 x X31 lbl).
  split. constructor; eexact A. split; auto.
  apply transl_cbranch_int32s_correct; auto.
  simpl; rewrite B, C; eauto with asmgen.
- predSpec Int.eq Int.eq_spec n Int.zero.
+ subst n. exists rs, (transl_cbranch_int32u c0 x X0 lbl).
  intuition auto. constructor. apply transl_cbranch_int32u_correct; auto.
+ exploit (loadimm32_correct X31 n); eauto. intros (rs' & A & B & C).
  exists rs', (transl_cbranch_int32u c0 x X31 lbl).
  split. constructor; eexact A. split; auto.
  apply transl_cbranch_int32u_correct; auto.
  simpl; rewrite B, C; eauto with asmgen.
- exists rs, (transl_cbranch_int64s c0 x x0 lbl).
  intuition auto. constructor. apply transl_cbranch_int64s_correct; auto.
- exists rs, (transl_cbranch_int64u c0 x x0 lbl).
  intuition auto. constructor. apply transl_cbranch_int64u_correct; auto.
- predSpec Int64.eq Int64.eq_spec n Int64.zero.
+ subst n. exists rs, (transl_cbranch_int64s c0 x X0 lbl).
  intuition auto. constructor. apply transl_cbranch_int64s_correct; auto.
+ exploit (loadimm64_correct X31 n); eauto. intros (rs' & A & B & C).
  exists rs', (transl_cbranch_int64s c0 x X31 lbl).
  split. constructor; eexact A. split; auto.
  apply transl_cbranch_int64s_correct; auto.
  simpl; rewrite B, C; eauto with asmgen.
- predSpec Int64.eq Int64.eq_spec n Int64.zero.
+ subst n. exists rs, (transl_cbranch_int64u c0 x X0 lbl).
  intuition auto. constructor. apply transl_cbranch_int64u_correct; auto.
+ exploit (loadimm64_correct X31 n); eauto. intros (rs' & A & B & C).
  exists rs', (transl_cbranch_int64u c0 x X31 lbl).
  split. constructor; eexact A. split; auto.
  apply transl_cbranch_int64u_correct; auto.
  simpl; rewrite B, C; eauto with asmgen.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:TC; inv EQ2.
  set (v := if normal then Val.cmpf c0 rs#x rs#x0 else Val.notbool (Val.cmpf c0 rs#x rs#x0)).
  assert (V: v = Val.of_bool (eqb normal b)).
  { unfold v, Val.cmpf. rewrite EVAL'. destruct normal, b; reflexivity. }
  econstructor; econstructor.
  split. constructor. apply exec_straight_one. eapply transl_cond_float_correct with (v := v); eauto. auto.
  split. rewrite V; destruct normal, b; reflexivity.
  intros; Simpl.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:TC; inv EQ2.
  assert (EVAL'': Val.cmpf_bool c0 (rs x) (rs x0) = Some (negb b)).
  { destruct (Val.cmpf_bool c0 (rs x) (rs x0)) as [[]|]; inv EVAL'; auto. }
  set (v := if normal then Val.cmpf c0 rs#x rs#x0 else Val.notbool (Val.cmpf c0 rs#x rs#x0)).
  assert (V: v = Val.of_bool (xorb normal b)).
  { unfold v, Val.cmpf. rewrite EVAL''. destruct normal, b; reflexivity. }
  econstructor; econstructor.
  split. constructor. apply exec_straight_one. eapply transl_cond_float_correct with (v := v); eauto. auto.
  split. rewrite V; destruct normal, b; reflexivity.
  intros; Simpl.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:TC; inv EQ2.
  set (v := if normal then Val.cmpfs c0 rs#x rs#x0 else Val.notbool (Val.cmpfs c0 rs#x rs#x0)).
  assert (V: v = Val.of_bool (eqb normal b)).
  { unfold v, Val.cmpfs. rewrite EVAL'. destruct normal, b; reflexivity. }
  econstructor; econstructor.
  split. constructor. apply exec_straight_one. eapply transl_cond_single_correct with (v := v); eauto. auto.
  split. rewrite V; destruct normal, b; reflexivity.
  intros; Simpl.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:TC; inv EQ2.
  assert (EVAL'': Val.cmpfs_bool c0 (rs x) (rs x0) = Some (negb b)).
  { destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) as [[]|]; inv EVAL'; auto. }
  set (v := if normal then Val.cmpfs c0 rs#x rs#x0 else Val.notbool (Val.cmpfs c0 rs#x rs#x0)).
  assert (V: v = Val.of_bool (xorb normal b)).
  { unfold v, Val.cmpfs. rewrite EVAL''. destruct normal, b; reflexivity. }
  econstructor; econstructor.
  split. constructor. apply exec_straight_one. eapply transl_cond_single_correct with (v := v); eauto. auto.
  split. rewrite V; destruct normal, b; reflexivity.
  intros; Simpl.
Qed.

Lemma transl_cbranch_correct_true:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some true ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs', exists insn,
     exec_straight_opt c rs m' (insn :: k) rs' m'
  /\ exec_instr ge fn insn rs' m' = goto_label fn lbl rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. eapply transl_cbranch_correct_1 with (b := true); eauto.
Qed. 

Lemma transl_cbranch_correct_false:
  forall cond args lbl k c m ms sp rs m',
  transl_cbranch cond args lbl k = OK c ->
  eval_condition cond (List.map ms args) m = Some false ->
  agree ms sp rs ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. exploit transl_cbranch_correct_1; eauto. simpl. 
  intros (rs' & insn & A & B & C).
  exists (nextinstr rs').
  split. eapply exec_straight_opt_right; eauto. apply exec_straight_one; auto.
  intros; Simpl. 
Qed.

(** Translation of condition operators *)

Lemma transl_cond_int32s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int32s cmp rd r1 r2 k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs##r1 rs##r2) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl. destruct (rs##r1); auto. destruct (rs##r2); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl. destruct (rs##r1); auto. destruct (rs##r2); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold Val.cmp. rewrite <- Val.swap_cmp_bool.
  simpl. rewrite (Val.negate_cmp_bool Clt). 
  destruct (Val.cmp_bool Clt rs##r2 rs##r1) as [[]|]; auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl. unfold Val.cmp. rewrite <- Val.swap_cmp_bool. auto.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold Val.cmp. rewrite (Val.negate_cmp_bool Clt). 
  destruct (Val.cmp_bool Clt rs##r1 rs##r2) as [[]|]; auto.
Qed.

Lemma transl_cond_int32u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int32u cmp rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.cmpu (Mem.valid_pointer m) cmp rs##r1 rs##r2
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold Val.cmpu. rewrite <- Val.swap_cmpu_bool.
  simpl. rewrite (Val.negate_cmpu_bool (Mem.valid_pointer m) Cle). 
  destruct (Val.cmpu_bool (Mem.valid_pointer m) Cle rs##r1 rs##r2) as [[]|]; auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl. unfold Val.cmpu. rewrite <- Val.swap_cmpu_bool. auto.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold Val.cmpu. rewrite (Val.negate_cmpu_bool (Mem.valid_pointer m) Clt). 
  destruct (Val.cmpu_bool (Mem.valid_pointer m) Clt rs##r1 rs##r2) as [[]|]; auto.
Qed.

Lemma transl_cond_int64s_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int64s cmp rd r1 r2 k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs###r1 rs###r2)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl. destruct (rs###r1); auto. destruct (rs###r2); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl. destruct (rs###r1); auto. destruct (rs###r2); auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold Val.cmpl. rewrite <- Val.swap_cmpl_bool.
  simpl. rewrite (Val.negate_cmpl_bool Clt). 
  destruct (Val.cmpl_bool Clt rs###r2 rs###r1) as [[]|]; auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl. unfold Val.cmpl. rewrite <- Val.swap_cmpl_bool. auto.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold Val.cmpl. rewrite (Val.negate_cmpl_bool Clt). 
  destruct (Val.cmpl_bool Clt rs###r1 rs###r2) as [[]|]; auto.
Qed.

Lemma transl_cond_int64u_correct:
  forall cmp rd r1 r2 k rs m,
  exists rs',
     exec_straight ge fn (transl_cond_int64u cmp rd r1 r2 k) rs m k rs' m
  /\ rs'#rd = Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs###r1 rs###r2)
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r. 
Proof.
  intros. destruct cmp; simpl. 
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold Val.cmplu. rewrite <- Val.swap_cmplu_bool.
  simpl. rewrite (Val.negate_cmplu_bool (Mem.valid_pointer m) Cle). 
  destruct (Val.cmplu_bool (Mem.valid_pointer m) Cle rs###r1 rs###r2) as [[]|]; auto.
- econstructor; split. apply exec_straight_one; [simpl; eauto|auto].
  split; intros; Simpl. unfold Val.cmplu. rewrite <- Val.swap_cmplu_bool. auto.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold Val.cmplu. rewrite (Val.negate_cmplu_bool (Mem.valid_pointer m) Clt). 
  destruct (Val.cmplu_bool (Mem.valid_pointer m) Clt rs###r1 rs###r2) as [[]|]; auto.
Qed.

Lemma transl_condimm_int32s_correct:
  forall cmp rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int32s cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.cmp cmp rs#r1 (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold transl_condimm_int32s.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. exploit transl_cond_int32s_correct. intros (rs' & A & B & C).
  exists rs'; eauto.
- assert (DFL:
    exists rs',
      exec_straight ge fn (loadimm32 X31 n (transl_cond_int32s cmp rd r1 X31 k)) rs m k rs' m
   /\ Val.lessdef (Val.cmp cmp rs#r1 (Vint n)) rs'#rd
   /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r).
  { exploit loadimm32_correct; eauto. intros (rs1 & A1 & B1 & C1).
    exploit transl_cond_int32s_correct; eauto. intros (rs2 & A2 & B2 & C2).
    exists rs2; split. 
    eapply exec_straight_trans. eexact A1. eexact A2. 
    split. simpl in B2. rewrite B1, C1 in B2 by auto with asmgen. auto.
    intros; transitivity (rs1 r); auto. }
  destruct cmp.
+ unfold xorimm32. 
  exploit (opimm32_correct Pxorw Pxoriw Val.xor); eauto. intros (rs1 & A1 & B1 & C1).
  exploit transl_cond_int32s_correct; eauto. intros (rs2 & A2 & B2 & C2).
  exists rs2; split. 
  eapply exec_straight_trans. eexact A1. eexact A2. 
  split. simpl in B2; rewrite B1 in B2; simpl in B2. destruct (rs#r1); auto.
  unfold Val.cmp in B2; simpl in B2; rewrite Int.xor_is_zero in B2. exact B2.
  intros; transitivity (rs1 r); auto.
+ unfold xorimm32. 
  exploit (opimm32_correct Pxorw Pxoriw Val.xor); eauto. intros (rs1 & A1 & B1 & C1).
  exploit transl_cond_int32s_correct; eauto. intros (rs2 & A2 & B2 & C2).
  exists rs2; split. 
  eapply exec_straight_trans. eexact A1. eexact A2. 
  split. simpl in B2; rewrite B1 in B2; simpl in B2. destruct (rs#r1); auto.
  unfold Val.cmp in B2; simpl in B2; rewrite Int.xor_is_zero in B2. exact B2.
  intros; transitivity (rs1 r); auto.
+ exploit (opimm32_correct Psltw Psltiw (Val.cmp Clt)); eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. rewrite B1; auto.
+ predSpec Int.eq Int.eq_spec n (Int.repr Int.max_signed).
* subst n. exploit loadimm32_correct; eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. 
  unfold Val.cmp; destruct (rs#r1); simpl; auto. rewrite B1. 
  unfold Int.lt. rewrite zlt_false. auto. 
  change (Int.signed (Int.repr Int.max_signed)) with Int.max_signed.
  generalize (Int.signed_range i); omega.
* exploit (opimm32_correct Psltw Psltiw (Val.cmp Clt)); eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. 
  rewrite B1. unfold Val.cmp; simpl; destruct (rs#r1); simpl; auto.
  unfold Int.lt. replace (Int.signed (Int.add n Int.one)) with (Int.signed n + 1).
  destruct (zlt (Int.signed n) (Int.signed i)).
  rewrite zlt_false by omega. auto.
  rewrite zlt_true by omega. auto.
  rewrite Int.add_signed. symmetry; apply Int.signed_repr. 
  assert (Int.signed n <> Int.max_signed).
  { red; intros E. elim H1. rewrite <- (Int.repr_signed n). rewrite E. auto. }
  generalize (Int.signed_range n); omega.
+ apply DFL.
+ apply DFL.
Qed.

Lemma transl_condimm_int32u_correct:
  forall cmp rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int32u cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r1 (Vint n)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold transl_condimm_int32u.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. exploit transl_cond_int32u_correct. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto. rewrite B; auto.
- assert (DFL:
    exists rs',
      exec_straight ge fn (loadimm32 X31 n (transl_cond_int32u cmp rd r1 X31 k)) rs m k rs' m
   /\ Val.lessdef (Val.cmpu (Mem.valid_pointer m) cmp rs#r1 (Vint n)) rs'#rd
   /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r).
  { exploit loadimm32_correct; eauto. intros (rs1 & A1 & B1 & C1).
    exploit transl_cond_int32u_correct; eauto. intros (rs2 & A2 & B2 & C2).
    exists rs2; split. 
    eapply exec_straight_trans. eexact A1. eexact A2. 
    split. simpl in B2. rewrite B1, C1 in B2 by auto with asmgen. rewrite B2; auto.
    intros; transitivity (rs1 r); auto. }
  destruct cmp.
+ apply DFL.
+ apply DFL.
+ exploit (opimm32_correct Psltuw Psltiuw (Val.cmpu (Mem.valid_pointer m) Clt) m); eauto.
  intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. rewrite B1; auto.
+ apply DFL.
+ apply DFL.
+ apply DFL.
Qed.

Lemma transl_condimm_int64s_correct:
  forall cmp rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int64s cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs#r1 (Vlong n))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold transl_condimm_int64s.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
- subst n. exploit transl_cond_int64s_correct. intros (rs' & A & B & C).
  exists rs'; eauto.
- assert (DFL:
    exists rs',
      exec_straight ge fn (loadimm64 X31 n (transl_cond_int64s cmp rd r1 X31 k)) rs m k rs' m
   /\ Val.lessdef (Val.maketotal (Val.cmpl cmp rs#r1 (Vlong n))) rs'#rd
   /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r).
  { exploit loadimm64_correct; eauto. intros (rs1 & A1 & B1 & C1).
    exploit transl_cond_int64s_correct; eauto. intros (rs2 & A2 & B2 & C2).
    exists rs2; split. 
    eapply exec_straight_trans. eexact A1. eexact A2. 
    split. simpl in B2. rewrite B1, C1 in B2 by auto with asmgen. auto.
    intros; transitivity (rs1 r); auto. }
  destruct cmp.
+ unfold xorimm64. 
  exploit (opimm64_correct Pxorl Pxoril Val.xorl); eauto. intros (rs1 & A1 & B1 & C1).
  exploit transl_cond_int64s_correct; eauto. intros (rs2 & A2 & B2 & C2).
  exists rs2; split. 
  eapply exec_straight_trans. eexact A1. eexact A2. 
  split. simpl in B2; rewrite B1 in B2; simpl in B2. destruct (rs#r1); auto.
  unfold Val.cmpl in B2; simpl in B2; rewrite Int64.xor_is_zero in B2. exact B2.
  intros; transitivity (rs1 r); auto.
+ unfold xorimm64. 
  exploit (opimm64_correct Pxorl Pxoril Val.xorl); eauto. intros (rs1 & A1 & B1 & C1).
  exploit transl_cond_int64s_correct; eauto. intros (rs2 & A2 & B2 & C2).
  exists rs2; split. 
  eapply exec_straight_trans. eexact A1. eexact A2. 
  split. simpl in B2; rewrite B1 in B2; simpl in B2. destruct (rs#r1); auto.
  unfold Val.cmpl in B2; simpl in B2; rewrite Int64.xor_is_zero in B2. exact B2.
  intros; transitivity (rs1 r); auto.
+ exploit (opimm64_correct Psltl Psltil (fun v1 v2 => Val.maketotal (Val.cmpl Clt v1 v2))); eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. rewrite B1; auto.
+ predSpec Int64.eq Int64.eq_spec n (Int64.repr Int64.max_signed).
* subst n. exploit loadimm32_correct; eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. 
  unfold Val.cmpl; destruct (rs#r1); simpl; auto. rewrite B1. 
  unfold Int64.lt. rewrite zlt_false. auto. 
  change (Int64.signed (Int64.repr Int64.max_signed)) with Int64.max_signed.
  generalize (Int64.signed_range i); omega.
* exploit (opimm64_correct Psltl Psltil (fun v1 v2 => Val.maketotal (Val.cmpl Clt v1 v2))); eauto. intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. 
  rewrite B1. unfold Val.cmpl; simpl; destruct (rs#r1); simpl; auto.
  unfold Int64.lt. replace (Int64.signed (Int64.add n Int64.one)) with (Int64.signed n + 1).
  destruct (zlt (Int64.signed n) (Int64.signed i)).
  rewrite zlt_false by omega. auto.
  rewrite zlt_true by omega. auto.
  rewrite Int64.add_signed. symmetry; apply Int64.signed_repr. 
  assert (Int64.signed n <> Int64.max_signed).
  { red; intros E. elim H1. rewrite <- (Int64.repr_signed n). rewrite E. auto. }
  generalize (Int64.signed_range n); omega.
+ apply DFL.
+ apply DFL.
Qed.

Lemma transl_condimm_int64u_correct:
  forall cmp rd r1 n k rs m,
  r1 <> X31 ->
  exists rs',
     exec_straight ge fn (transl_condimm_int64u cmp rd r1 n k) rs m k rs' m
  /\ Val.lessdef (Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs#r1 (Vlong n))) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. unfold transl_condimm_int64u.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
- subst n. exploit transl_cond_int64u_correct. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split; auto. rewrite B; auto.
- assert (DFL:
    exists rs',
      exec_straight ge fn (loadimm64 X31 n (transl_cond_int64u cmp rd r1 X31 k)) rs m k rs' m
   /\ Val.lessdef (Val.maketotal (Val.cmplu (Mem.valid_pointer m) cmp rs#r1 (Vlong n))) rs'#rd
   /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r).
  { exploit loadimm64_correct; eauto. intros (rs1 & A1 & B1 & C1).
    exploit transl_cond_int64u_correct; eauto. intros (rs2 & A2 & B2 & C2).
    exists rs2; split. 
    eapply exec_straight_trans. eexact A1. eexact A2. 
    split. simpl in B2. rewrite B1, C1 in B2 by auto with asmgen. rewrite B2; auto.
    intros; transitivity (rs1 r); auto. }
  destruct cmp.
+ apply DFL.
+ apply DFL.
+ exploit (opimm64_correct Psltul Psltiul (fun v1 v2 => Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt v1 v2)) m); eauto.
  intros (rs1 & A1 & B1 & C1).
  exists rs1; split. eexact A1. split; auto. rewrite B1; auto.
+ apply DFL.
+ apply DFL.
+ apply DFL.
Qed.

Lemma transl_cond_op_correct:
  forall cond rd args k c rs m,
  transl_cond_op cond rd args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)) rs'#rd
  /\ forall r, r <> PC -> r <> rd -> r <> X31 -> rs'#r = rs#r.
Proof.
  assert (MKTOT: forall ob, Val.of_optbool ob = Val.maketotal (option_map Val.of_bool ob)).
  { destruct ob as [[]|]; reflexivity. }
  intros until m; intros TR.
  destruct cond; simpl in TR; ArgsInv.
+ (* cmp *)
  exploit transl_cond_int32s_correct; eauto. intros (rs' & A & B & C). exists rs'; eauto.
+ (* cmpu *)
  exploit transl_cond_int32u_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B; auto.
+ (* cmpimm *)
  apply transl_condimm_int32s_correct; eauto with asmgen.
+ (* cmpuimm *)
  apply transl_condimm_int32u_correct; eauto with asmgen.
+ (* cmpl *)
  exploit transl_cond_int64s_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmplu *)
  exploit transl_cond_int64u_correct; eauto. intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite B, MKTOT; eauto.
+ (* cmplimm *)
  exploit transl_condimm_int64s_correct; eauto. instantiate (1 := x); eauto with asmgen. 
  intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmpluimm *)
  exploit transl_condimm_int64u_correct; eauto. instantiate (1 := x); eauto with asmgen. 
  intros (rs' & A & B & C).
  exists rs'; repeat split; eauto. rewrite MKTOT; eauto.
+ (* cmpf *)
  destruct (transl_cond_float c0 rd x x0) as [insn normal] eqn:TR.
  fold (Val.cmpf c0 (rs x) (rs x0)).
  set (v := Val.cmpf c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_float_correct with (v := v); eauto. auto.
  split; intros; Simpl.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_float_correct with (v := Val.notbool v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl. unfold v, Val.cmpf. destruct (Val.cmpf_bool c0 (rs x) (rs x0)) as [[]|]; auto.
+ (* notcmpf *)
  destruct (transl_cond_float c0 rd x x0) as [insn normal] eqn:TR.
  rewrite Val.notbool_negb_3. fold (Val.cmpf c0 (rs x) (rs x0)).
  set (v := Val.cmpf c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_float_correct with (v := v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl. unfold v, Val.cmpf. destruct (Val.cmpf_bool c0 (rs x) (rs x0)) as [[]|]; auto.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_float_correct with (v := Val.notbool v); eauto. auto.
  split; intros; Simpl.
+ (* cmpfs *)
  destruct (transl_cond_single c0 rd x x0) as [insn normal] eqn:TR.
  fold (Val.cmpfs c0 (rs x) (rs x0)).
  set (v := Val.cmpfs c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_single_correct with (v := v); eauto. auto.
  split; intros; Simpl.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_single_correct with (v := Val.notbool v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl. unfold v, Val.cmpfs. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) as [[]|]; auto.
+ (* notcmpfs *)
  destruct (transl_cond_single c0 rd x x0) as [insn normal] eqn:TR.
  rewrite Val.notbool_negb_3. fold (Val.cmpfs c0 (rs x) (rs x0)).
  set (v := Val.cmpfs c0 (rs x) (rs x0)).
  destruct normal; inv EQ2.
* econstructor; split.
  eapply exec_straight_two.
  eapply transl_cond_single_correct with (v := v); eauto.
  simpl; reflexivity.
  auto. auto.
  split; intros; Simpl. unfold v, Val.cmpfs. destruct (Val.cmpfs_bool c0 (rs x) (rs x0)) as [[]|]; auto.
* econstructor; split.
  apply exec_straight_one. eapply transl_cond_single_correct with (v := Val.notbool v); eauto. auto.
  split; intros; Simpl.
Qed.

(** Some arithmetic properties. *)

Remark cast32unsigned_from_cast32signed:
  forall i, Int64.repr (Int.unsigned i) = Int64.zero_ext 32 (Int64.repr (Int.signed i)).
Proof.
  intros. apply Int64.same_bits_eq; intros. 
  rewrite Int64.bits_zero_ext, !Int64.testbit_repr by tauto.
  rewrite Int.bits_signed by tauto. fold (Int.testbit i i0).
  change Int.zwordsize with 32.
  destruct (zlt i0 32). auto. apply Int.bits_above. auto.
Qed.

(* Translation of arithmetic operations *)

Ltac SimplEval H :=
  match type of H with
  | Some _ = None _ => discriminate
  | Some _ = Some _ => inv H
  | ?a = Some ?b => let A := fresh in assert (A: Val.maketotal a = b) by (rewrite H; reflexivity)
end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  assert (SAME: forall v1 v2, v1 = v2 -> Val.lessdef v2 v1). { intros; subst; auto. }
Opaque Int.eq.
  intros until c; intros TR EV.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; SimplEval EV; try TranslOpSimpl.
- (* move *)
  destruct (preg_of res), (preg_of m0); inv TR; TranslOpSimpl.
- (* intconst *)
  exploit loadimm32_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* longconst *)
  exploit loadimm64_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* floatconst *)
  destruct (Float.eq_dec n Float.zero).
+ subst n. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
+ econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
- (* singleconst *)
  destruct (Float32.eq_dec n Float32.zero).
+ subst n. econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
+ econstructor; split. 
  apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
- (* addrsymbol *)
  destruct (Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)).
+ set (rs1 := nextinstr (rs#x <- (Genv.symbol_address ge id Ptrofs.zero))).
  exploit (addptrofs_correct x x ofs k rs1 m); eauto with asmgen. 
  intros (rs2 & A & B & C).
  exists rs2; split. 
  apply exec_straight_step with rs1 m; auto.
  split. replace ofs with (Ptrofs.add Ptrofs.zero ofs) by (apply Ptrofs.add_zero_l). 
  rewrite Genv.shift_symbol_address.
  replace (rs1 x) with (Genv.symbol_address ge id Ptrofs.zero) in B by (unfold rs1; Simpl).
  exact B.
  intros. rewrite C by eauto with asmgen. unfold rs1; Simpl.  
+ TranslOpSimpl.
- (* stackoffset *)
  exploit addptrofs_correct. instantiate (1 := X2); auto with asmgen. intros (rs' & A & B & C).
  exists rs'; split; eauto. auto with asmgen.
- (* cast8signed *)
  econstructor; split.
  eapply exec_straight_two. simpl;eauto. simpl;eauto. auto. auto.
  split; intros; Simpl.
  assert (A: Int.ltu (Int.repr 24) Int.iwordsize = true) by auto.
  destruct (rs x0); auto; simpl. rewrite A; simpl. rewrite A. 
  apply Val.lessdef_same. f_equal. apply Int.sign_ext_shr_shl. split; reflexivity.
- (* cast16signed *)
  econstructor; split.
  eapply exec_straight_two. simpl;eauto. simpl;eauto. auto. auto.
  split; intros; Simpl.
  assert (A: Int.ltu (Int.repr 16) Int.iwordsize = true) by auto.
  destruct (rs x0); auto; simpl. rewrite A; simpl. rewrite A. 
  apply Val.lessdef_same. f_equal. apply Int.sign_ext_shr_shl. split; reflexivity.
- (* addimm *)
  exploit (opimm32_correct Paddw Paddiw Val.add); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen. 
- (* andimm *)
  exploit (opimm32_correct Pandw Pandiw Val.and); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* orimm *)
  exploit (opimm32_correct Porw Poriw Val.or); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* xorimm *)
  exploit (opimm32_correct Pxorw Pxoriw Val.xor); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* shrximm *)
  clear H. exploit Val.shrx_shr_2; eauto. intros E; subst v; clear EV.
  destruct (Int.eq n Int.zero).
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
+ change (Int.repr 32) with Int.iwordsize. set (n' := Int.sub Int.iwordsize n).
  econstructor; split.
  eapply exec_straight_step. simpl; reflexivity. auto. 
  eapply exec_straight_step. simpl; reflexivity. auto. 
  eapply exec_straight_step. simpl; reflexivity. auto. 
  apply exec_straight_one. simpl; reflexivity. auto. 
  split; intros; Simpl.
- (* longofintu *)
  econstructor; split.
  eapply exec_straight_three. simpl; eauto. simpl; eauto. simpl; eauto. auto. auto. auto.
  split; intros; Simpl. destruct (rs x0); auto. simpl. 
  assert (A: Int.ltu (Int.repr 32) Int64.iwordsize' = true) by auto.
  rewrite A; simpl. rewrite A. apply Val.lessdef_same. f_equal.
  rewrite cast32unsigned_from_cast32signed. apply Int64.zero_ext_shru_shl. compute; auto.
- (* addlimm *)
  exploit (opimm64_correct Paddl Paddil Val.addl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen. 
- (* andimm *)
  exploit (opimm64_correct Pandl Pandil Val.andl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* orimm *)
  exploit (opimm64_correct Porl Poril Val.orl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* xorimm *)
  exploit (opimm64_correct Pxorl Pxoril Val.xorl); auto. instantiate (1 := x0); eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split; eauto. rewrite B; auto with asmgen.
- (* shrxlimm *)
  clear H. exploit Val.shrxl_shrl_2; eauto. intros E; subst v; clear EV.
  destruct (Int.eq n Int.zero).
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros; Simpl. 
+ change (Int.repr 64) with Int64.iwordsize'. set (n' := Int.sub Int64.iwordsize' n).
  econstructor; split.
  eapply exec_straight_step. simpl; reflexivity. auto. 
  eapply exec_straight_step. simpl; reflexivity. auto. 
  eapply exec_straight_step. simpl; reflexivity. auto. 
  apply exec_straight_one. simpl; reflexivity. auto. 
  split; intros; Simpl.
- (* cond *)
  exploit transl_cond_op_correct; eauto. intros (rs' & A & B & C).
  exists rs'; split. eexact A. eauto with asmgen.
Qed.

(** Memory accesses *)

Lemma indexed_memory_access_correct:
  forall mk_instr base ofs k rs m,
  base <> X31 ->
  exists base' ofs' rs',
     exec_straight_opt (indexed_memory_access mk_instr base ofs k) rs m
                       (mk_instr base' ofs' :: k) rs' m
  /\ Val.offset_ptr rs'#base' (eval_offset ge ofs') = Val.offset_ptr rs#base ofs
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  unfold indexed_memory_access; intros.
  destruct Archi.ptr64 eqn:SF.
- generalize (make_immed64_sound (Ptrofs.to_int64 ofs)); intros EQ.
  destruct (make_immed64 (Ptrofs.to_int64 ofs)).
+ econstructor; econstructor; econstructor; split.
  apply exec_straight_opt_refl. 
  split; auto. simpl. subst imm. rewrite Ptrofs.of_int64_to_int64 by auto. auto.
+ econstructor; econstructor; econstructor; split. 
  constructor. eapply exec_straight_two. 
  simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_assoc. f_equal. f_equal. 
  rewrite <- (Ptrofs.of_int64_to_int64 SF ofs). rewrite EQ. 
  symmetry; auto with ptrofs.
+ econstructor; econstructor; econstructor; split. 
  constructor. eapply exec_straight_two. 
  simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. unfold eval_offset. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_zero. subst imm. rewrite Ptrofs.of_int64_to_int64 by auto. auto.
- generalize (make_immed32_sound (Ptrofs.to_int ofs)); intros EQ.
  destruct (make_immed32 (Ptrofs.to_int ofs)).
+ econstructor; econstructor; econstructor; split.
  apply exec_straight_opt_refl. 
  split; auto. simpl. subst imm. rewrite Ptrofs.of_int_to_int by auto. auto.
+ econstructor; econstructor; econstructor; split. 
  constructor. eapply exec_straight_two. 
  simpl; eauto. simpl; eauto. auto. auto. 
  split; intros; Simpl. destruct (rs base); auto; simpl. rewrite SF. simpl.
  rewrite Ptrofs.add_assoc. f_equal. f_equal. 
  rewrite <- (Ptrofs.of_int_to_int SF ofs). rewrite EQ. 
  symmetry; auto with ptrofs.
Qed.

Lemma indexed_load_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) rd m,
  (forall base ofs rs,
     exec_instr ge fn (mk_instr base ofs) rs m = exec_load ge chunk rs m rd base ofs) ->
  forall (base: ireg) ofs k (rs: regset) v,
  Mem.loadv chunk m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> X31 -> rd <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk_instr base ofs k) rs m k rs' m
  /\ rs'#rd = v
  /\ forall r, r <> PC -> r <> X31 -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC; intros until v; intros LOAD NOT31 NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. rewrite EXEC.
  unfold exec_load. rewrite B, LOAD. eauto. Simpl. 
  split; intros; Simpl.
Qed.

Lemma indexed_store_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) r1 m,
  (forall base ofs rs,
     exec_instr ge fn (mk_instr base ofs) rs m = exec_store ge chunk rs m r1 base ofs) ->
  forall (base: ireg) ofs k (rs: regset) m',
  Mem.storev chunk m (Val.offset_ptr rs#base ofs) (rs#r1) = Some m' ->
  base <> X31 -> r1 <> X31 -> r1 <> PC ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk_instr base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m; intros EXEC; intros until m'; intros STORE NOT31 NOT31' NOTPC.
  exploit indexed_memory_access_correct; eauto.
  intros (base' & ofs' & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. rewrite EXEC.
  unfold exec_store. rewrite B, C, STORE by auto. eauto. auto. 
  intros; Simpl.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> X31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> X31 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR LOAD NOT31. 
  assert (A: exists mk_instr,
                c = indexed_memory_access mk_instr base ofs k
             /\ forall base' ofs' rs',
                   exec_instr ge fn (mk_instr base' ofs') rs' m =
                   exec_load ge (chunk_of_type ty) rs' m (preg_of dst) base' ofs').
  { unfold loadind in TR. destruct ty, (preg_of dst); inv TR; econstructor; split; eauto. }
  destruct A as (mk_instr & B & C). subst c. 
  eapply indexed_load_access_correct; eauto with asmgen. 
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  base <> X31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR STORE NOT31. 
  assert (A: exists mk_instr,
                c = indexed_memory_access mk_instr base ofs k
             /\ forall base' ofs' rs',
                   exec_instr ge fn (mk_instr base' ofs') rs' m =
                   exec_store ge (chunk_of_type ty) rs' m (preg_of src) base' ofs').
  { unfold storeind in TR. destruct ty, (preg_of src); inv TR; econstructor; split; eauto. }
  destruct A as (mk_instr & B & C). subst c. 
  eapply indexed_store_access_correct; eauto with asmgen. 
Qed.

Lemma loadind_ptr_correct:
  forall (base: ireg) ofs (dst: ireg) k (rs: regset) m v,
  Mem.loadv Mptr m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> X31 ->
  exists rs',
     exec_straight ge fn (loadind_ptr base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> X31 -> r <> dst -> rs'#r = rs#r.
Proof.
  intros. eapply indexed_load_access_correct; eauto with asmgen.
  intros. unfold Mptr. destruct Archi.ptr64; auto. 
Qed.

Lemma storeind_ptr_correct:
  forall (base: ireg) ofs (src: ireg) k (rs: regset) m m',
  Mem.storev Mptr m (Val.offset_ptr rs#base ofs) rs#src = Some m' ->
  base <> X31 -> src <> X31 ->
  exists rs',
     exec_straight ge fn (storeind_ptr src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros. eapply indexed_store_access_correct with (r1 := src); eauto with asmgen.
  intros. unfold Mptr. destruct Archi.ptr64; auto. 
Qed.

Lemma transl_memory_access_correct:
  forall mk_instr addr args k c (rs: regset) m v,
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  exists base ofs rs',
     exec_straight_opt c rs m (mk_instr base ofs :: k) rs' m
  /\ Val.offset_ptr rs'#base (eval_offset ge ofs) = v
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV. 
  unfold transl_memory_access in TR; destruct addr; ArgsInv.
- (* indexed *)
  inv EV. apply indexed_memory_access_correct; eauto with asmgen.
- (* global *)
  simpl in EV. inv EV. inv TR.  econstructor; econstructor; econstructor; split.
  constructor. apply exec_straight_one. simpl; eauto. auto. 
  split; intros; Simpl. unfold eval_offset. apply low_high_half.
- (* stack *)
  inv TR. inv EV. apply indexed_memory_access_correct; eauto with asmgen.
Qed.

Lemma transl_load_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) addr args k c rd (rs: regset) m v v',
  (forall base ofs rs,
     exec_instr ge fn (mk_instr base ofs) rs m = exec_load ge chunk rs m rd base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.loadv chunk m v = Some v' ->
  rd <> PC ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#rd = v'
  /\ forall r, r <> PC -> r <> X31 -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until v'; intros INSTR TR EV LOAD NOTPC. 
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. 
  rewrite INSTR. unfold exec_load. rewrite B, LOAD. reflexivity. Simpl. 
  split; intros; Simpl.
Qed.

Lemma transl_store_access_correct:
  forall chunk (mk_instr: ireg -> offset -> instruction) addr args k c r1 (rs: regset) m v m',
  (forall base ofs rs,
     exec_instr ge fn (mk_instr base ofs) rs m = exec_store ge chunk rs m r1 base ofs) ->
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some v ->
  Mem.storev chunk m v rs#r1 = Some m' ->
  r1 <> PC -> r1 <> X31 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros INSTR TR EV STORE NOTPC NOT31. 
  exploit transl_memory_access_correct; eauto.
  intros (base & ofs & rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_opt_right. eexact A. apply exec_straight_one. 
  rewrite INSTR. unfold exec_store. rewrite B, C, STORE by auto. reflexivity. auto.
  intros; Simpl.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m a v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> X31 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v; intros TR EV LOAD. 
  assert (A: exists mk_instr,
      transl_memory_access mk_instr addr args k = OK c
   /\ forall base ofs rs,
        exec_instr ge fn (mk_instr base ofs) rs m = exec_load ge chunk rs m (preg_of dst) base ofs).
  { unfold transl_load in TR; destruct chunk; ArgsInv; econstructor; (split; [eassumption|auto]). }
  destruct A as (mk_instr & B & C).
  eapply transl_load_access_correct; eauto with asmgen.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge rs#SP addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> X31 -> rs'#r = rs#r.
Proof.
  intros until m'; intros TR EV STORE. 
  assert (A: exists mk_instr chunk',
      transl_memory_access mk_instr addr args k = OK c
   /\ (forall base ofs rs,
        exec_instr ge fn (mk_instr base ofs) rs m = exec_store ge chunk' rs m (preg_of src) base ofs)
   /\ Mem.storev chunk m a rs#(preg_of src) = Mem.storev chunk' m a rs#(preg_of src)).
  { unfold transl_store in TR; destruct chunk; ArgsInv;
    (econstructor; econstructor; split; [eassumption | split; [ intros; simpl; reflexivity | auto]]).
    destruct a; auto. apply Mem.store_signed_unsigned_8. 
    destruct a; auto. apply Mem.store_signed_unsigned_16. 
  }
  destruct A as (mk_instr & chunk' & B & C & D).
  rewrite D in STORE; clear D. 
  eapply transl_store_access_correct; eauto with asmgen.
Qed.

(** Function epilogues *)

Lemma make_epilogue_correct:
  forall ge0 f m stk soff cs m' ms rs k tm,
  load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge fn (make_epilogue f k) rs tm k rs' tm'
  /\ agree ms (parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#RA = parent_ra cs
  /\ rs'#SP = parent_sp cs
  /\ (forall r, r <> PC -> r <> RA -> r <> SP -> r <> X31 -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold make_epilogue. 
  rewrite chunk_of_Tptr in *. 
  exploit (loadind_ptr_correct SP (fn_retaddr_ofs f) RA (Pfreeframe (fn_stacksize f) (fn_link_ofs f) :: k) rs tm).
    rewrite <- (sp_val _ _ _ AG). simpl. eexact LRA'. congruence.
  intros (rs1 & A1 & B1 & C1).
  econstructor; econstructor; split.
  eapply exec_straight_trans. eexact A1. apply exec_straight_one. simpl. 
    rewrite (C1 X2) by auto with asmgen. rewrite <- (sp_val _ _ _ AG). simpl; rewrite LP'. 
    rewrite FREE'. eauto. auto. 
  split. apply agree_nextinstr. apply agree_set_other; auto with asmgen. 
    apply agree_change_sp with (Vptr stk soff).
    apply agree_exten with rs; auto. intros; apply C1; auto with asmgen.
    eapply parent_sp_def; eauto.
  split. auto.
  split. Simpl. 
  split. Simpl. 
  intros. Simpl. 
Qed.

End CONSTRUCTORS.


 

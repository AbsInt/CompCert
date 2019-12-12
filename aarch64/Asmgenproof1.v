(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for AArch64 code generation: auxiliary results. *)

Require Import Recdef Coqlib Zwf Zbits.
Require Import Maps Errors AST Integers Floats Values Memory Globalenvs.
Require Import Op Locations Mach Asm Conventions.
Require Import Asmgen.
Require Import Asmgenproof0.

Local Transparent Archi.ptr64.

(** Properties of registers *)

Lemma preg_of_iregsp_not_PC: forall r, preg_of_iregsp r <> PC.
Proof.
  destruct r; simpl; congruence.
Qed.
Hint Resolve preg_of_iregsp_not_PC: asmgen.

Lemma preg_of_not_X16: forall r, preg_of r <> X16.
Proof.
  destruct r; simpl; congruence.
Qed.

Lemma ireg_of_not_X16: forall r x, ireg_of r = OK x -> x <> X16.
Proof.
  unfold ireg_of; intros. destruct (preg_of r) eqn:E; inv H.
  red; intros; subst x. elim (preg_of_not_X16 r); auto.
Qed.

Lemma ireg_of_not_X16': forall r x, ireg_of r = OK x -> IR x <> IR X16.
Proof.
  intros. apply ireg_of_not_X16 in H. congruence.
Qed.

Hint Resolve preg_of_not_X16 ireg_of_not_X16 ireg_of_not_X16': asmgen.

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

(** Decomposition of integer literals *)

Inductive wf_decomposition: list (Z * Z) -> Prop :=
  | wf_decomp_nil:
      wf_decomposition nil
  | wf_decomp_cons: forall m n p l,
      n = Zzero_ext 16 m -> 0 <= p -> wf_decomposition l ->
      wf_decomposition ((n, p) :: l).

Lemma decompose_int_wf:
  forall N n p, 0 <= p -> wf_decomposition (decompose_int N n p).
Proof.
Local Opaque Zzero_ext.
  induction N as [ | N]; simpl; intros.
- constructor.
- set (frag := Zzero_ext 16 (Z.shiftr n p)) in *. destruct (Z.eqb frag 0).
+ apply IHN. omega.
+ econstructor. reflexivity. omega. apply IHN; omega. 
Qed.

Fixpoint recompose_int (accu: Z) (l: list (Z * Z)) : Z :=
  match l with
  | nil => accu
  | (n, p) :: l => recompose_int (Zinsert accu n p 16) l
  end.

Lemma decompose_int_correct:
  forall N n p accu,
  0 <= p ->
  (forall i, p <= i -> Z.testbit accu i = false) ->
  (forall i, 0 <= i < p + Z.of_nat N * 16 ->
   Z.testbit (recompose_int accu (decompose_int N n p)) i =
   if zlt i p then Z.testbit accu i else Z.testbit n i).
Proof.
  induction N as [ | N]; intros until accu; intros PPOS ABOVE i RANGE.
- simpl. rewrite zlt_true; auto. xomega.
- rewrite inj_S in RANGE. simpl.
  set (frag := Zzero_ext 16 (Z.shiftr n p)).
  assert (FRAG: forall i, p <= i < p + 16 -> Z.testbit n i = Z.testbit frag (i - p)).
  { unfold frag; intros. rewrite Zzero_ext_spec by omega. rewrite zlt_true by omega.
    rewrite Z.shiftr_spec by omega. f_equal; omega. }
  destruct (Z.eqb_spec frag 0).
+ rewrite IHN.
* destruct (zlt i p). rewrite zlt_true by omega. auto.
  destruct (zlt i (p + 16)); auto.
  rewrite ABOVE by omega. rewrite FRAG by omega. rewrite e, Z.testbit_0_l. auto.
* omega.
* intros; apply ABOVE; omega.
* xomega.
+ simpl. rewrite IHN.
* destruct (zlt i (p + 16)).
** rewrite Zinsert_spec by omega. unfold proj_sumbool.
   rewrite zlt_true by omega.
   destruct (zlt i p).
   rewrite zle_false by omega. auto.
   rewrite zle_true by omega. simpl. symmetry; apply FRAG; omega.
** rewrite Z.ldiff_spec, Z.shiftl_spec by omega.
   change 65535 with (two_p 16 - 1). rewrite Ztestbit_two_p_m1 by omega.
   rewrite zlt_false by omega. rewrite zlt_false by omega. apply andb_true_r. 
* omega.
* intros. rewrite Zinsert_spec by omega. unfold proj_sumbool.
  rewrite zle_true by omega. rewrite zlt_false by omega. simpl.
  apply ABOVE. omega.
* xomega.
Qed.

Corollary decompose_int_eqmod: forall N n,
  eqmod (two_power_nat (N * 16)%nat) (recompose_int 0 (decompose_int N n 0)) n.
Proof.
  intros; apply eqmod_same_bits; intros.
  rewrite decompose_int_correct. apply zlt_false; omega. 
  omega. intros; apply Z.testbit_0_l. xomega.
Qed.

Corollary decompose_notint_eqmod: forall N n,
  eqmod (two_power_nat (N * 16)%nat)
        (Z.lnot (recompose_int 0 (decompose_int N (Z.lnot n) 0))) n.
Proof.
  intros; apply eqmod_same_bits; intros.
  rewrite Z.lnot_spec, decompose_int_correct.
  rewrite zlt_false by omega. rewrite Z.lnot_spec by omega. apply negb_involutive.
  omega. intros; apply Z.testbit_0_l. xomega. omega.
Qed.

Lemma negate_decomposition_wf:
  forall l, wf_decomposition l -> wf_decomposition (negate_decomposition l).
Proof.
  induction 1; simpl; econstructor; auto.
  instantiate (1 := (Z.lnot m)).
  apply equal_same_bits; intros.
  rewrite H. change 65535 with (two_p 16 - 1).
  rewrite Z.lxor_spec, !Zzero_ext_spec, Z.lnot_spec, Ztestbit_two_p_m1 by omega.
  destruct (zlt i 16).
  apply xorb_true_r.
  auto.
Qed.

Lemma Zinsert_eqmod:
  forall n x1 x2 y p l, 0 <= p -> 0 <= l ->
  eqmod (two_power_nat n) x1 x2 ->
  eqmod (two_power_nat n) (Zinsert x1 y p l) (Zinsert x2 y p l).
Proof.
  intros. apply eqmod_same_bits; intros. rewrite ! Zinsert_spec by omega.
  destruct (zle p i && zlt i (p + l)); auto.
  apply same_bits_eqmod with n; auto.
Qed.

Lemma Zinsert_0_l:
  forall y p l,
  0 <= p -> 0 <= l ->
  Z.shiftl (Zzero_ext l y) p = Zinsert 0 (Zzero_ext l y) p l.
Proof.
  intros. apply equal_same_bits; intros.
  rewrite Zinsert_spec by omega. unfold proj_sumbool.
  destruct (zlt i p); [rewrite zle_false by omega|rewrite zle_true by omega]; simpl.
- rewrite Z.testbit_0_l, Z.shiftl_spec_low by auto. auto.
- rewrite Z.shiftl_spec by omega. 
  destruct (zlt i (p + l)); auto.
  rewrite Zzero_ext_spec, zlt_false, Z.testbit_0_l by omega. auto.
Qed.

Lemma recompose_int_negated:
  forall l, wf_decomposition l ->
  forall accu, recompose_int (Z.lnot accu) (negate_decomposition l) = Z.lnot (recompose_int accu l).
Proof.
  induction 1; intros accu; simpl.
- auto.
- rewrite <- IHwf_decomposition. f_equal. apply equal_same_bits; intros. 
  rewrite Z.lnot_spec, ! Zinsert_spec, Z.lxor_spec, Z.lnot_spec by omega.
  unfold proj_sumbool.
  destruct (zle p i); simpl; auto.
  destruct (zlt i (p + 16)); simpl; auto.
  change 65535 with (two_p 16 - 1).
  rewrite Ztestbit_two_p_m1 by omega. rewrite zlt_true by omega.
  apply xorb_true_r. 
Qed.

Lemma exec_loadimm_k_w:
  forall (rd: ireg) k m l,
  wf_decomposition l ->
  forall (rs: regset) accu,
  rs#rd = Vint (Int.repr accu) ->
  exists rs',
     exec_straight_opt ge fn (loadimm_k W rd l k) rs m k rs' m
  /\ rs'#rd = Vint (Int.repr (recompose_int accu l))
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  induction 1; intros rs accu ACCU; simpl.
- exists rs; split. apply exec_straight_opt_refl. auto.
- destruct (IHwf_decomposition
                (nextinstr (rs#rd <- (insert_in_int rs#rd n p 16)))
                (Zinsert accu n p 16))
  as (rs' & P & Q & R).
  Simpl. rewrite ACCU. simpl. f_equal. apply Int.eqm_samerepr. 
  apply Zinsert_eqmod. auto. omega. apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
  exists rs'; split.
  eapply exec_straight_opt_step_opt. simpl; eauto. auto. exact P.
  split. exact Q. intros; Simpl. rewrite R by auto. Simpl.
Qed.

Lemma exec_loadimm_z_w:
  forall rd l k rs m,
  wf_decomposition l ->
  exists rs',
     exec_straight ge fn (loadimm_z W rd l k) rs m k rs' m
  /\ rs'#rd = Vint (Int.repr (recompose_int 0 l))
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm_z; destruct 1.
- econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl.
  intros; Simpl.
- set (accu0 := Zinsert 0 n p 16).
  set (rs1 := nextinstr (rs#rd <- (Vint (Int.repr accu0)))).
  destruct (exec_loadimm_k_w rd k m l H1 rs1 accu0) as (rs2 & P & Q & R); auto.
  unfold rs1; Simpl.
  exists rs2; split.
  eapply exec_straight_opt_step; eauto.
  simpl. unfold rs1. do 5 f_equal. unfold accu0. rewrite H. apply Zinsert_0_l; omega.
  reflexivity.
  split. exact Q. 
  intros. rewrite R by auto. unfold rs1; Simpl.
Qed.

Lemma exec_loadimm_n_w:
  forall rd l k rs m,
  wf_decomposition l ->
  exists rs',
     exec_straight ge fn (loadimm_n W rd l k) rs m k rs' m
  /\ rs'#rd = Vint (Int.repr (Z.lnot (recompose_int 0 l)))
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm_n; destruct 1.
- econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. 
  intros; Simpl.
- set (accu0 := Z.lnot (Zinsert 0 n p 16)).
  set (rs1 := nextinstr (rs#rd <- (Vint (Int.repr accu0)))).
  destruct (exec_loadimm_k_w rd k m (negate_decomposition l) 
                                    (negate_decomposition_wf l H1)
                                    rs1 accu0) as (rs2 & P & Q & R).
  unfold rs1; Simpl.
  exists rs2; split.
  eapply exec_straight_opt_step; eauto.
  simpl. unfold rs1. do 5 f_equal.
  unfold accu0. f_equal. rewrite H. apply Zinsert_0_l; omega.
  reflexivity.  
  split. unfold accu0 in Q; rewrite recompose_int_negated in Q by auto. exact Q.
  intros. rewrite R by auto. unfold rs1; Simpl.
Qed.

Lemma exec_loadimm32:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm32 rd n k) rs m k rs' m
  /\ rs'#rd = Vint n
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm32, loadimm; intros.
  destruct (is_logical_imm32 n).
- econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. rewrite Int.repr_unsigned, Int.or_zero_l; auto.
  intros; Simpl.
- set (dz := decompose_int 2%nat (Int.unsigned n) 0).
  set (dn := decompose_int 2%nat (Z.lnot (Int.unsigned n)) 0).
  assert (A: Int.repr (recompose_int 0 dz) = n).
  { transitivity (Int.repr (Int.unsigned n)).
    apply Int.eqm_samerepr. apply decompose_int_eqmod. 
    apply Int.repr_unsigned. }
  assert (B: Int.repr (Z.lnot (recompose_int 0 dn)) = n).
  { transitivity (Int.repr (Int.unsigned n)).
    apply Int.eqm_samerepr. apply decompose_notint_eqmod. 
    apply Int.repr_unsigned. }
  destruct Nat.leb.
+ rewrite <- A. apply exec_loadimm_z_w. apply decompose_int_wf; omega.
+ rewrite <- B. apply exec_loadimm_n_w. apply decompose_int_wf; omega.
Qed.

Lemma exec_loadimm_k_x:
  forall (rd: ireg) k m l,
  wf_decomposition l ->
  forall (rs: regset) accu,
  rs#rd = Vlong (Int64.repr accu) ->
  exists rs',
     exec_straight_opt ge fn (loadimm_k X rd l k) rs m k rs' m
  /\ rs'#rd = Vlong (Int64.repr (recompose_int accu l))
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  induction 1; intros rs accu ACCU; simpl.
- exists rs; split. apply exec_straight_opt_refl. auto.
- destruct (IHwf_decomposition
                (nextinstr (rs#rd <- (insert_in_long rs#rd n p 16)))
                (Zinsert accu n p 16))
  as (rs' & P & Q & R).
  Simpl. rewrite ACCU. simpl. f_equal. apply Int64.eqm_samerepr. 
  apply Zinsert_eqmod. auto. omega. apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
  exists rs'; split.
  eapply exec_straight_opt_step_opt. simpl; eauto. auto. exact P.
  split. exact Q. intros; Simpl. rewrite R by auto. Simpl.
Qed.

Lemma exec_loadimm_z_x:
  forall rd l k rs m,
  wf_decomposition l ->
  exists rs',
     exec_straight ge fn (loadimm_z X rd l k) rs m k rs' m
  /\ rs'#rd = Vlong (Int64.repr (recompose_int 0 l))
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm_z; destruct 1.
- econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl.
  intros; Simpl.
- set (accu0 := Zinsert 0 n p 16).
  set (rs1 := nextinstr (rs#rd <- (Vlong (Int64.repr accu0)))).
  destruct (exec_loadimm_k_x rd k m l H1 rs1 accu0) as (rs2 & P & Q & R); auto.
  unfold rs1; Simpl.
  exists rs2; split.
  eapply exec_straight_opt_step; eauto.
  simpl. unfold rs1. do 5 f_equal. unfold accu0. rewrite H. apply Zinsert_0_l; omega.
  reflexivity.
  split. exact Q. 
  intros. rewrite R by auto. unfold rs1; Simpl.
Qed.

Lemma exec_loadimm_n_x:
  forall rd l k rs m,
  wf_decomposition l ->
  exists rs',
     exec_straight ge fn (loadimm_n X rd l k) rs m k rs' m
  /\ rs'#rd = Vlong (Int64.repr (Z.lnot (recompose_int 0 l)))
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm_n; destruct 1.
- econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. 
  intros; Simpl.
- set (accu0 := Z.lnot (Zinsert 0 n p 16)).
  set (rs1 := nextinstr (rs#rd <- (Vlong (Int64.repr accu0)))).
  destruct (exec_loadimm_k_x rd k m (negate_decomposition l) 
                                    (negate_decomposition_wf l H1)
                                    rs1 accu0) as (rs2 & P & Q & R).
  unfold rs1; Simpl.
  exists rs2; split.
  eapply exec_straight_opt_step; eauto.
  simpl. unfold rs1. do 5 f_equal.
  unfold accu0. f_equal. rewrite H. apply Zinsert_0_l; omega.
  reflexivity.  
  split. unfold accu0 in Q; rewrite recompose_int_negated in Q by auto. exact Q.
  intros. rewrite R by auto. unfold rs1; Simpl.
Qed.

Lemma exec_loadimm64:
  forall rd n k rs m,
  exists rs',
     exec_straight ge fn (loadimm64 rd n k) rs m k rs' m
  /\ rs'#rd = Vlong n
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadimm64, loadimm; intros.
  destruct (is_logical_imm64 n).
- econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. rewrite Int64.repr_unsigned, Int64.or_zero_l; auto.
  intros; Simpl.
- set (dz := decompose_int 4%nat (Int64.unsigned n) 0).
  set (dn := decompose_int 4%nat (Z.lnot (Int64.unsigned n)) 0).
  assert (A: Int64.repr (recompose_int 0 dz) = n).
  { transitivity (Int64.repr (Int64.unsigned n)).
    apply Int64.eqm_samerepr. apply decompose_int_eqmod. 
    apply Int64.repr_unsigned. }
  assert (B: Int64.repr (Z.lnot (recompose_int 0 dn)) = n).
  { transitivity (Int64.repr (Int64.unsigned n)).
    apply Int64.eqm_samerepr. apply decompose_notint_eqmod. 
    apply Int64.repr_unsigned. }
  destruct Nat.leb.
+ rewrite <- A. apply exec_loadimm_z_x. apply decompose_int_wf; omega.
+ rewrite <- B. apply exec_loadimm_n_x. apply decompose_int_wf; omega.
Qed.

(** Add immediate *)

Lemma exec_addimm_aux_32:
  forall (insn: iregsp -> iregsp -> Z -> instruction) (sem: val -> val -> val),
  (forall rd r1 n rs m,
    exec_instr ge fn (insn rd r1 n) rs m =
      Next (nextinstr (rs#rd <- (sem rs#r1 (Vint (Int.repr n))))) m) ->
  (forall v n1 n2, sem (sem v (Vint n1)) (Vint n2) = sem v (Vint (Int.add n1 n2))) ->
  forall rd r1 n k rs m,
  exists rs',
     exec_straight ge fn (addimm_aux insn rd r1 (Int.unsigned n) k) rs m k rs' m
  /\ rs'#rd = sem rs#r1 (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros insn sem SEM ASSOC; intros. unfold addimm_aux.
  set (nlo := Zzero_ext 12 (Int.unsigned n)). set (nhi := Int.unsigned n - nlo).
  assert (E: Int.unsigned n = nhi + nlo) by (unfold nhi; omega).
  rewrite <- (Int.repr_unsigned n).
  destruct (Z.eqb_spec nhi 0); [|destruct (Z.eqb_spec nlo 0)].
- econstructor; split. apply exec_straight_one. apply SEM. Simpl. 
  split. Simpl. do 3 f_equal; omega.
  intros; Simpl.
- econstructor; split. apply exec_straight_one. apply SEM. Simpl. 
  split. Simpl. do 3 f_equal; omega.
  intros; Simpl.
- econstructor; split. eapply exec_straight_two.
  apply SEM. apply SEM. Simpl. Simpl.
  split. Simpl. rewrite ASSOC. do 2 f_equal. apply Int.eqm_samerepr.
  rewrite E. auto with ints.
  intros; Simpl.
Qed.

Lemma exec_addimm32:
  forall rd r1 n k rs m,
  r1 <> X16 ->
  exists rs',
     exec_straight ge fn (addimm32 rd r1 n k) rs m k rs' m
  /\ rs'#rd = Val.add rs#r1 (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. unfold addimm32. set (nn := Int.neg n).
  destruct (Int.eq n (Int.zero_ext 24 n)); [| destruct (Int.eq nn (Int.zero_ext 24 nn))].
- apply exec_addimm_aux_32 with (sem := Val.add). auto. intros; apply Val.add_assoc. 
- rewrite <- Val.sub_opp_add.
  apply exec_addimm_aux_32 with (sem := Val.sub). auto.
  intros. rewrite ! Val.sub_add_opp, Val.add_assoc. rewrite Int.neg_add_distr. auto.
- destruct (Int.lt n Int.zero).
+ rewrite <- Val.sub_opp_add; fold nn.
  edestruct (exec_loadimm32 X16 nn) as (rs1 & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. eapply exec_straight_one. simpl; eauto. auto.
  split. Simpl. rewrite B, C; eauto with asmgen.
  intros; Simpl.
+ edestruct (exec_loadimm32 X16 n) as (rs1 & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. eapply exec_straight_one. simpl; eauto. auto.
  split. Simpl. rewrite B, C; eauto with asmgen.
  intros; Simpl.
Qed.

Lemma exec_addimm_aux_64:
  forall (insn: iregsp -> iregsp -> Z -> instruction) (sem: val -> val -> val),
  (forall rd r1 n rs m,
    exec_instr ge fn (insn rd r1 n) rs m =
      Next (nextinstr (rs#rd <- (sem rs#r1 (Vlong (Int64.repr n))))) m) ->
  (forall v n1 n2, sem (sem v (Vlong n1)) (Vlong n2) = sem v (Vlong (Int64.add n1 n2))) ->
  forall rd r1 n k rs m,
  exists rs',
     exec_straight ge fn (addimm_aux insn rd r1 (Int64.unsigned n) k) rs m k rs' m
  /\ rs'#rd = sem rs#r1 (Vlong n)
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros insn sem SEM ASSOC; intros. unfold addimm_aux.
  set (nlo := Zzero_ext 12 (Int64.unsigned n)). set (nhi := Int64.unsigned n - nlo).
  assert (E: Int64.unsigned n = nhi + nlo) by (unfold nhi; omega).
  rewrite <- (Int64.repr_unsigned n).
  destruct (Z.eqb_spec nhi 0); [|destruct (Z.eqb_spec nlo 0)].
- econstructor; split. apply exec_straight_one. apply SEM. Simpl. 
  split. Simpl. do 3 f_equal; omega.
  intros; Simpl.
- econstructor; split. apply exec_straight_one. apply SEM. Simpl. 
  split. Simpl. do 3 f_equal; omega.
  intros; Simpl.
- econstructor; split. eapply exec_straight_two.
  apply SEM. apply SEM. Simpl. Simpl.
  split. Simpl. rewrite ASSOC. do 2 f_equal. apply Int64.eqm_samerepr.
  rewrite E. auto with ints.
  intros; Simpl.
Qed.

Lemma exec_addimm64:
  forall rd r1 n k rs m,
  preg_of_iregsp r1 <> X16 ->
  exists rs',
     exec_straight ge fn (addimm64 rd r1 n k) rs m k rs' m
  /\ rs'#rd = Val.addl rs#r1 (Vlong n)
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros. 
  unfold addimm64. set (nn := Int64.neg n).
  destruct (Int64.eq n (Int64.zero_ext 24 n)); [| destruct (Int64.eq nn (Int64.zero_ext 24 nn))].
- apply exec_addimm_aux_64 with (sem := Val.addl). auto. intros; apply Val.addl_assoc. 
- rewrite <- Val.subl_opp_addl.
  apply exec_addimm_aux_64 with (sem := Val.subl). auto.
  intros. rewrite ! Val.subl_addl_opp, Val.addl_assoc. rewrite Int64.neg_add_distr. auto.
- destruct (Int64.lt n Int64.zero).
+ rewrite <- Val.subl_opp_addl; fold nn.
  edestruct (exec_loadimm64 X16 nn) as (rs1 & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. eapply exec_straight_one. simpl; eauto. Simpl. 
  split. Simpl. rewrite B, C; eauto with asmgen. simpl. rewrite Int64.shl'_zero. auto.
  intros; Simpl.
+ edestruct (exec_loadimm64 X16 n) as (rs1 & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. eapply exec_straight_one. simpl; eauto. Simpl. 
  split. Simpl. rewrite B, C; eauto with asmgen. simpl. rewrite Int64.shl'_zero. auto.
  intros; Simpl.
Qed.

(** Logical immediate *)

Lemma exec_logicalimm32:
  forall (insn1: ireg -> ireg0 -> Z -> instruction)
         (insn2: ireg -> ireg0 -> ireg -> shift_op -> instruction)
         (sem: val -> val -> val),
  (forall rd r1 n rs m,
    exec_instr ge fn (insn1 rd r1 n) rs m =
      Next (nextinstr (rs#rd <- (sem rs##r1 (Vint (Int.repr n))))) m) ->
  (forall rd r1 r2 s rs m,
    exec_instr ge fn (insn2 rd r1 r2 s) rs m =
      Next (nextinstr (rs#rd <- (sem rs##r1 (eval_shift_op_int rs#r2 s)))) m) ->
  forall rd r1 n k rs m,
  r1 <> X16 ->
  exists rs',
     exec_straight ge fn (logicalimm32 insn1 insn2 rd r1 n k) rs m k rs' m
  /\ rs'#rd = sem rs#r1 (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until sem; intros SEM1 SEM2; intros. unfold logicalimm32.
  destruct (is_logical_imm32 n).
- econstructor; split. 
  apply exec_straight_one. apply SEM1. reflexivity. 
  split. Simpl. rewrite Int.repr_unsigned; auto. intros; Simpl.
- edestruct (exec_loadimm32 X16 n) as (rs1 & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A.  
  apply exec_straight_one. apply SEM2. reflexivity.
  split. Simpl. f_equal; auto. apply C; auto with asmgen.
  intros; Simpl. 
Qed.

Lemma exec_logicalimm64:
  forall (insn1: ireg -> ireg0 -> Z -> instruction)
         (insn2: ireg -> ireg0 -> ireg -> shift_op -> instruction)
         (sem: val -> val -> val),
  (forall rd r1 n rs m,
    exec_instr ge fn (insn1 rd r1 n) rs m =
      Next (nextinstr (rs#rd <- (sem rs###r1 (Vlong (Int64.repr n))))) m) ->
  (forall rd r1 r2 s rs m,
    exec_instr ge fn (insn2 rd r1 r2 s) rs m =
      Next (nextinstr (rs#rd <- (sem rs###r1 (eval_shift_op_long rs#r2 s)))) m) ->
  forall rd r1 n k rs m,
  r1 <> X16 ->
  exists rs',
     exec_straight ge fn (logicalimm64 insn1 insn2 rd r1 n k) rs m k rs' m
  /\ rs'#rd = sem rs#r1 (Vlong n)
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros until sem; intros SEM1 SEM2; intros. unfold logicalimm64.
  destruct (is_logical_imm64 n).
- econstructor; split. 
  apply exec_straight_one. apply SEM1. reflexivity. 
  split. Simpl. rewrite Int64.repr_unsigned. auto. intros; Simpl.
- edestruct (exec_loadimm64 X16 n) as (rs1 & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A.  
  apply exec_straight_one. apply SEM2. reflexivity.
  split. Simpl. f_equal; auto. apply C; auto with asmgen.
  intros; Simpl. 
Qed.

(** Load address of symbol *)

Lemma exec_loadsymbol: forall rd s ofs k rs m,
  rd <> X16 \/ Archi.pic_code tt = false ->
  exists rs',
     exec_straight ge fn (loadsymbol rd s ofs k) rs m k rs' m
  /\ rs'#rd = Genv.symbol_address ge s ofs
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold loadsymbol; intros. destruct (Archi.pic_code tt).
- predSpec Ptrofs.eq Ptrofs.eq_spec ofs Ptrofs.zero.
+ subst ofs. econstructor; split.
  apply exec_straight_one; [simpl; eauto | reflexivity].
  split. Simpl. intros; Simpl.
+ exploit exec_addimm64. instantiate (1 := rd). simpl. destruct H; congruence.
  intros (rs1 & A & B & C).
  econstructor; split.
  econstructor. simpl; eauto. auto. eexact A. 
  split. simpl in B; rewrite B. Simpl. 
  rewrite <- Genv.shift_symbol_address_64 by auto.
  rewrite Ptrofs.add_zero_l, Ptrofs.of_int64_to_int64 by auto. auto.
  intros. rewrite C by auto. Simpl.
- econstructor; split.
  eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto.
  split. Simpl. rewrite symbol_high_low; auto. 
  intros; Simpl.
Qed.

(** Shifted operands *)

Remark transl_shift_not_none:
  forall s a, transl_shift s a <> SOnone.
Proof.
  destruct s; intros; simpl; congruence.
Qed.

Remark or_zero_eval_shift_op_int:
  forall v s, s <> SOnone -> Val.or (Vint Int.zero) (eval_shift_op_int v s) = eval_shift_op_int v s.
Proof.
  intros; destruct s; try congruence; destruct v; auto; simpl;
  destruct (Int.ltu n Int.iwordsize); auto; rewrite Int.or_zero_l; auto.
Qed.

Remark or_zero_eval_shift_op_long:
  forall v s, s <> SOnone -> Val.orl (Vlong Int64.zero) (eval_shift_op_long v s) = eval_shift_op_long v s.
Proof.
  intros; destruct s; try congruence; destruct v; auto; simpl;
  destruct (Int.ltu n Int64.iwordsize'); auto; rewrite Int64.or_zero_l; auto.
Qed.

Remark add_zero_eval_shift_op_long:
  forall v s, s <> SOnone -> Val.addl (Vlong Int64.zero) (eval_shift_op_long v s) = eval_shift_op_long v s.
Proof.
  intros; destruct s; try congruence; destruct v; auto; simpl;
  destruct (Int.ltu n Int64.iwordsize'); auto; rewrite Int64.add_zero_l; auto.
Qed.

Lemma transl_eval_shift: forall s v (a: amount32),
  eval_shift_op_int v (transl_shift s a) = eval_shift s v a.
Proof.
  intros. destruct s; simpl; auto.
Qed.

Lemma transl_eval_shift': forall s v (a: amount32),
  Val.or (Vint Int.zero) (eval_shift_op_int v (transl_shift s a)) = eval_shift s v a.
Proof.
  intros. rewrite or_zero_eval_shift_op_int by (apply transl_shift_not_none).
  apply transl_eval_shift.
Qed.

Lemma transl_eval_shiftl: forall s v (a: amount64),
  eval_shift_op_long v (transl_shift s a) = eval_shiftl s v a.
Proof.
  intros. destruct s; simpl; auto.
Qed.

Lemma transl_eval_shiftl': forall s v (a: amount64),
  Val.orl (Vlong Int64.zero) (eval_shift_op_long v (transl_shift s a)) = eval_shiftl s v a.
Proof.
  intros. rewrite or_zero_eval_shift_op_long by (apply transl_shift_not_none).
  apply transl_eval_shiftl.
Qed.

Lemma transl_eval_shiftl'': forall s v (a: amount64),
  Val.addl (Vlong Int64.zero) (eval_shift_op_long v (transl_shift s a)) = eval_shiftl s v a.
Proof.
  intros. rewrite add_zero_eval_shift_op_long by (apply transl_shift_not_none).
  apply transl_eval_shiftl.
Qed.

(** Zero- and Sign- extensions *)

Lemma exec_move_extended_base: forall rd r1 ex k rs m,
  exists rs',
     exec_straight ge fn (move_extended_base rd r1 ex k) rs m k rs' m
  /\ rs' rd = match ex with Xsgn32 => Val.longofint rs#r1 | Xuns32 => Val.longofintu rs#r1 end
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold move_extended_base; destruct ex; econstructor;
  (split; [apply exec_straight_one; [simpl;eauto|auto] | split; [Simpl|intros;Simpl]]).
Qed.

Lemma exec_move_extended: forall rd r1 ex (a: amount64) k rs m,
  exists rs',
     exec_straight ge fn (move_extended rd r1 ex a k) rs m k rs' m
  /\ rs' rd = Op.eval_extend ex rs#r1 a
  /\ forall r, r <> PC -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold move_extended; intros. predSpec Int.eq Int.eq_spec a Int.zero.
- exploit (exec_move_extended_base rd r1 ex). intros (rs' & A & B & C).
  exists rs'; split. eexact A. split. unfold Op.eval_extend. rewrite H. rewrite B.
  destruct ex, (rs r1); simpl; auto; rewrite Int64.shl'_zero; auto.
  auto.
- Local Opaque Val.addl.
  exploit (exec_move_extended_base rd r1 ex). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one.
  unfold exec_instr. change (SOlsl a) with (transl_shift Slsl a). rewrite transl_eval_shiftl''. eauto. auto.
  split. Simpl. rewrite B. auto. 
  intros; Simpl.
Qed.

Lemma exec_arith_extended:
  forall (sem: val -> val -> val)
         (insnX: iregsp -> iregsp -> ireg -> extend_op -> instruction)
         (insnS: ireg -> ireg0 -> ireg -> shift_op -> instruction),
  (forall rd r1 r2 x rs m,
    exec_instr ge fn (insnX rd r1 r2 x) rs m =
      Next (nextinstr (rs#rd <- (sem rs#r1 (eval_extend rs#r2 x)))) m) ->
  (forall rd r1 r2 s rs m,
    exec_instr ge fn (insnS rd r1 r2 s) rs m =
      Next (nextinstr (rs#rd <- (sem rs###r1 (eval_shift_op_long rs#r2 s)))) m) ->
  forall (rd r1 r2: ireg) (ex: extension) (a: amount64) (k: code) rs m,
  r1 <> X16 ->
  exists rs',
     exec_straight ge fn (arith_extended insnX insnS rd r1 r2 ex a k) rs m k rs' m
  /\ rs'#rd = sem rs#r1 (Op.eval_extend ex rs#r2 a)
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  intros sem insnX insnS EX ES; intros. unfold arith_extended. destruct (Int.ltu a (Int.repr 5)).
- econstructor; split. 
  apply exec_straight_one. rewrite EX; eauto. auto.
  split. Simpl. f_equal. destruct ex; auto.
  intros; Simpl.
- exploit (exec_move_extended_base X16 r2 ex). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. 
  rewrite ES. eauto. auto.
  split. Simpl. unfold ir0x. rewrite C by eauto with asmgen. f_equal. 
  rewrite B. destruct ex; auto.
  intros; Simpl.
Qed. 

(** Extended right shift *)

Lemma exec_shrx32: forall (rd r1: ireg) (n: int) k v (rs: regset) m,
  Val.shrx rs#r1 (Vint n) = Some v ->
  r1 <> X16 ->
  exists rs',
     exec_straight ge fn (shrx32 rd r1 n k) rs m k rs' m
  /\ rs'#rd = v
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold shrx32; intros. apply Val.shrx_shr_2 in H.
  destruct (Int.eq n Int.zero) eqn:E.
- econstructor; split. apply exec_straight_one; [simpl;eauto|auto]. 
  split. Simpl. subst v; auto. intros; Simpl.
- econstructor; split. eapply exec_straight_three.
  unfold exec_instr. rewrite or_zero_eval_shift_op_int by congruence. eauto.
  simpl; eauto.
  unfold exec_instr. rewrite or_zero_eval_shift_op_int by congruence. eauto.
  auto. auto. auto.
  split. subst v; Simpl. intros; Simpl.
Qed.
 
Lemma exec_shrx64: forall (rd r1: ireg) (n: int) k v (rs: regset) m,
  Val.shrxl rs#r1 (Vint n) = Some v ->
  r1 <> X16 ->
  exists rs',
     exec_straight ge fn (shrx64 rd r1 n k) rs m k rs' m
  /\ rs'#rd = v
  /\ forall r, data_preg r = true -> r <> rd -> rs'#r = rs#r.
Proof.
  unfold shrx64; intros. apply Val.shrxl_shrl_2 in H.
  destruct (Int.eq n Int.zero) eqn:E.
- econstructor; split. apply exec_straight_one; [simpl;eauto|auto]. 
  split. Simpl. subst v; auto. intros; Simpl.
- econstructor; split. eapply exec_straight_three.
  unfold exec_instr. rewrite or_zero_eval_shift_op_long by congruence. eauto.
  simpl; eauto.
  unfold exec_instr. rewrite or_zero_eval_shift_op_long by congruence. eauto.
  auto. auto. auto.
  split. subst v; Simpl. intros; Simpl.
Qed.

(** Condition bits *)

Lemma compare_int_spec: forall rs v1 v2 m,
  let rs' := compare_int rs v1 v2 m in
     rs'#CN = (Val.negative (Val.sub v1 v2))
  /\ rs'#CZ = (Val.cmpu (Mem.valid_pointer m) Ceq v1 v2)
  /\ rs'#CC = (Val.cmpu (Mem.valid_pointer m) Cge v1 v2)
  /\ rs'#CV = (Val.sub_overflow v1 v2).
Proof.
  intros; unfold rs'; auto.
Qed.

Lemma eval_testcond_compare_sint: forall c v1 v2 b rs m,
  Val.cmp_bool c v1 v2 = Some b ->
  eval_testcond (cond_for_signed_cmp c) (compare_int rs v1 v2 m) = Some b.
Proof.
  intros. generalize (compare_int_spec rs v1 v2 m). 
  set (rs' := compare_int rs v1 v2 m). intros (B & C & D & E).
  unfold eval_testcond; rewrite B, C, D, E.
  destruct v1; try discriminate; destruct v2; try discriminate.
  simpl in H; inv H.
  unfold Val.cmpu; simpl. destruct c; simpl.
- destruct (Int.eq i i0); auto.
- destruct (Int.eq i i0); auto.
- rewrite Int.lt_sub_overflow. destruct (Int.lt i i0); auto.
- rewrite Int.lt_sub_overflow, Int.not_lt.
  destruct (Int.eq i i0), (Int.lt i i0); auto.
- rewrite Int.lt_sub_overflow, (Int.lt_not i). 
  destruct (Int.eq i i0), (Int.lt i i0); auto.
- rewrite Int.lt_sub_overflow. destruct (Int.lt i i0); auto.
Qed.

Lemma eval_testcond_compare_uint: forall c v1 v2 b rs m,
  Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
  eval_testcond (cond_for_unsigned_cmp c) (compare_int rs v1 v2 m) = Some b.
Proof.
  intros. generalize (compare_int_spec rs v1 v2 m). 
  set (rs' := compare_int rs v1 v2 m). intros (B & C & D & E).
  unfold eval_testcond; rewrite B, C, D, E.
  destruct v1; try discriminate; destruct v2; try discriminate.
  simpl in H; inv H.
  unfold Val.cmpu; simpl. destruct c; simpl.
- destruct (Int.eq i i0); auto.
- destruct (Int.eq i i0); auto.
- destruct (Int.ltu i i0); auto.
- rewrite (Int.not_ltu i). destruct (Int.eq i i0), (Int.ltu i i0); auto.
- rewrite (Int.ltu_not i). destruct (Int.eq i i0), (Int.ltu i i0); auto.
- destruct (Int.ltu i i0); auto.
Qed.

Lemma compare_long_spec: forall rs v1 v2 m,
  let rs' := compare_long rs v1 v2 m in
     rs'#CN = (Val.negativel (Val.subl v1 v2))
  /\ rs'#CZ = (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq v1 v2))
  /\ rs'#CC = (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cge v1 v2))
  /\ rs'#CV = (Val.subl_overflow v1 v2).
Proof.
  intros; unfold rs'; auto.
Qed.

Remark int64_sub_overflow:
  forall x y,
  Int.xor (Int.repr (Int64.unsigned (Int64.sub_overflow x y Int64.zero)))
          (Int.repr (Int64.unsigned (Int64.negative (Int64.sub x y)))) =
  (if Int64.lt x y then Int.one else Int.zero).
Proof.
  intros.
  transitivity (Int.repr (Int64.unsigned (if Int64.lt x y then Int64.one else Int64.zero))).
  rewrite <- (Int64.lt_sub_overflow x y).
  unfold Int64.sub_overflow, Int64.negative.
  set (s := Int64.signed x - Int64.signed y - Int64.signed Int64.zero).
  destruct (zle Int64.min_signed s && zle s Int64.max_signed);
  destruct (Int64.lt (Int64.sub x y) Int64.zero);
  auto.
  destruct (Int64.lt x y); auto.
Qed.

Lemma eval_testcond_compare_slong: forall c v1 v2 b rs m,
  Val.cmpl_bool c v1 v2 = Some b ->
  eval_testcond (cond_for_signed_cmp c) (compare_long rs v1 v2 m) = Some b.
Proof.
  intros. generalize (compare_long_spec rs v1 v2 m). 
  set (rs' := compare_long rs v1 v2 m). intros (B & C & D & E).
  unfold eval_testcond; rewrite B, C, D, E.
  destruct v1; try discriminate; destruct v2; try discriminate.
  simpl in H; inv H.
  unfold Val.cmplu; simpl. destruct c; simpl.
- destruct (Int64.eq i i0); auto.
- destruct (Int64.eq i i0); auto.
- rewrite int64_sub_overflow. destruct (Int64.lt i i0); auto.
- rewrite int64_sub_overflow, Int64.not_lt.
  destruct (Int64.eq i i0), (Int64.lt i i0); auto.
- rewrite int64_sub_overflow, (Int64.lt_not i). 
  destruct (Int64.eq i i0), (Int64.lt i i0); auto.
- rewrite int64_sub_overflow. destruct (Int64.lt i i0); auto.
Qed.

Lemma eval_testcond_compare_ulong: forall c v1 v2 b rs m,
  Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
  eval_testcond (cond_for_unsigned_cmp c) (compare_long rs v1 v2 m) = Some b.
Proof.
  intros. generalize (compare_long_spec rs v1 v2 m). 
  set (rs' := compare_long rs v1 v2 m). intros (B & C & D & E).
  unfold eval_testcond; rewrite B, C, D, E; unfold Val.cmplu.
  destruct v1; try discriminate; destruct v2; try discriminate; simpl in H.
- (* int-int *)
  inv H. destruct c; simpl.
+ destruct (Int64.eq i i0); auto.
+ destruct (Int64.eq i i0); auto.
+ destruct (Int64.ltu i i0); auto.
+ rewrite (Int64.not_ltu i). destruct (Int64.eq i i0), (Int64.ltu i i0); auto.
+ rewrite (Int64.ltu_not i). destruct (Int64.eq i i0), (Int64.ltu i i0); auto.
+ destruct (Int64.ltu i i0); auto.
- (* int-ptr *)
  simpl.
  destruct (Int64.eq i Int64.zero &&
            (Mem.valid_pointer m b0 (Ptrofs.unsigned i0)
              || Mem.valid_pointer m b0 (Ptrofs.unsigned i0 - 1))); try discriminate.
  destruct c; simpl in H; inv H; reflexivity.
- (* ptr-int *)
  simpl.
  destruct (Int64.eq i0 Int64.zero &&
            (Mem.valid_pointer m b0 (Ptrofs.unsigned i)
              || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1))); try discriminate.
  destruct c; simpl in H; inv H; reflexivity.
- (* ptr-ptr *)
  simpl. 
  destruct (eq_block b0 b1).
+ destruct ((Mem.valid_pointer m b0 (Ptrofs.unsigned i)
             || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1)) &&
            (Mem.valid_pointer m b1 (Ptrofs.unsigned i0)
             || Mem.valid_pointer m b1 (Ptrofs.unsigned i0 - 1)));
  inv H.
  destruct c; simpl.
* destruct (Ptrofs.eq i i0); auto.
* destruct (Ptrofs.eq i i0); auto.
* destruct (Ptrofs.ltu i i0); auto.
* rewrite (Ptrofs.not_ltu i). destruct (Ptrofs.eq i i0), (Ptrofs.ltu i i0); auto.
* rewrite (Ptrofs.ltu_not i). destruct (Ptrofs.eq i i0), (Ptrofs.ltu i i0); auto.
* destruct (Ptrofs.ltu i i0); auto.
+ destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned i) &&
            Mem.valid_pointer m b1 (Ptrofs.unsigned i0)); try discriminate.
  destruct c; simpl in H; inv H; reflexivity.
Qed.

Lemma compare_float_spec: forall rs f1 f2,
  let rs' := compare_float rs (Vfloat f1) (Vfloat f2) in
     rs'#CN = (Val.of_bool (Float.cmp Clt f1 f2))
  /\ rs'#CZ = (Val.of_bool (Float.cmp Ceq f1 f2))
  /\ rs'#CC = (Val.of_bool (negb (Float.cmp Clt f1 f2)))
  /\ rs'#CV = (Val.of_bool (negb (Float.ordered f1 f2))).
Proof.
  intros; auto.
Qed.

Lemma eval_testcond_compare_float: forall c v1 v2 b rs,
  Val.cmpf_bool c v1 v2 = Some b ->
  eval_testcond (cond_for_float_cmp c) (compare_float rs v1 v2) = Some b.
Proof.
  intros. destruct v1; try discriminate; destruct v2; simpl in H; inv H. 
  generalize (compare_float_spec rs f f0). 
  set (rs' := compare_float rs (Vfloat f) (Vfloat f0)).
  intros (B & C & D & E).
  unfold eval_testcond; rewrite B, C, D, E.
Local Transparent Float.cmp Float.ordered.
  unfold Float.cmp, Float.ordered;
  destruct c; destruct (Float.compare f f0) as [[]|]; reflexivity.
Qed.

Lemma eval_testcond_compare_not_float: forall c v1 v2 b rs,
  option_map negb (Val.cmpf_bool c v1 v2) = Some b ->
  eval_testcond (cond_for_float_not_cmp c) (compare_float rs v1 v2) = Some b.
Proof.
  intros. destruct v1; try discriminate; destruct v2; simpl in H; inv H.
  generalize (compare_float_spec rs f f0). 
  set (rs' := compare_float rs (Vfloat f) (Vfloat f0)).
  intros (B & C & D & E).
  unfold eval_testcond; rewrite B, C, D, E.
Local Transparent Float.cmp Float.ordered.
  unfold Float.cmp, Float.ordered;
  destruct c; destruct (Float.compare f f0) as [[]|]; reflexivity.
Qed.

Lemma compare_single_spec: forall rs f1 f2,
  let rs' := compare_single rs (Vsingle f1) (Vsingle f2) in
     rs'#CN = (Val.of_bool (Float32.cmp Clt f1 f2))
  /\ rs'#CZ = (Val.of_bool (Float32.cmp Ceq f1 f2))
  /\ rs'#CC = (Val.of_bool (negb (Float32.cmp Clt f1 f2)))
  /\ rs'#CV = (Val.of_bool (negb (Float32.ordered f1 f2))).
Proof.
  intros; auto.
Qed.

Lemma eval_testcond_compare_single: forall c v1 v2 b rs,
  Val.cmpfs_bool c v1 v2 = Some b ->
  eval_testcond (cond_for_float_cmp c) (compare_single rs v1 v2) = Some b.
Proof.
  intros. destruct v1; try discriminate; destruct v2; simpl in H; inv H. 
  generalize (compare_single_spec rs f f0). 
  set (rs' := compare_single rs (Vsingle f) (Vsingle f0)).
  intros (B & C & D & E).
  unfold eval_testcond; rewrite B, C, D, E.
Local Transparent Float32.cmp Float32.ordered.
  unfold Float32.cmp, Float32.ordered;
  destruct c; destruct (Float32.compare f f0) as [[]|]; reflexivity.
Qed.

Lemma eval_testcond_compare_not_single: forall c v1 v2 b rs,
  option_map negb (Val.cmpfs_bool c v1 v2) = Some b ->
  eval_testcond (cond_for_float_not_cmp c) (compare_single rs v1 v2) = Some b.
Proof.
  intros. destruct v1; try discriminate; destruct v2; simpl in H; inv H.
  generalize (compare_single_spec rs f f0). 
  set (rs' := compare_single rs (Vsingle f) (Vsingle f0)).
  intros (B & C & D & E).
  unfold eval_testcond; rewrite B, C, D, E.
Local Transparent Float32.cmp Float32.ordered.
  unfold Float32.cmp, Float32.ordered;
  destruct c; destruct (Float32.compare f f0) as [[]|]; reflexivity.
Qed.

Remark compare_float_inv: forall rs v1 v2 r,
  match r with CR _ => False | _ => True end ->
  (nextinstr (compare_float rs v1 v2))#r = (nextinstr rs)#r.
Proof.
  intros; unfold compare_float.
  destruct r; try contradiction; destruct v1; auto; destruct v2; auto.
Qed.

Remark compare_single_inv: forall rs v1 v2 r,
  match r with CR _ => False | _ => True end ->
  (nextinstr (compare_single rs v1 v2))#r = (nextinstr rs)#r.
Proof.
  intros; unfold compare_single.
  destruct r; try contradiction; destruct v1; auto; destruct v2; auto.
Qed.

(** Translation of conditionals *)

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

Lemma transl_cond_correct:
  forall cond args k c rs m,
  transl_cond cond args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ (forall b,
      eval_condition cond (map rs (map preg_of args)) m = Some b ->
      eval_testcond (cond_for_cond cond) rs' = Some b)
  /\ forall r, data_preg r = true -> rs'#r = rs#r.
Proof.
  intros until m; intros TR. destruct cond; simpl in TR; ArgsInv.
- (* Ccomp *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. apply eval_testcond_compare_sint; auto. 
  destruct r; reflexivity || discriminate.
- (* Ccompu *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. apply eval_testcond_compare_uint; auto. 
  destruct r; reflexivity || discriminate.
- (* Ccompimm *)
  destruct (is_arith_imm32 n); [|destruct (is_arith_imm32 (Int.neg n))].
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite Int.repr_unsigned. apply eval_testcond_compare_sint; auto. 
  destruct r; reflexivity || discriminate.
+ econstructor; split.
  apply exec_straight_one. simpl. rewrite Int.repr_unsigned, Int.neg_involutive. eauto. auto.
  split; intros. apply eval_testcond_compare_sint; auto. 
  destruct r; reflexivity || discriminate.
+ exploit (exec_loadimm32 X16 n). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one.
  simpl. rewrite B, C by eauto with asmgen. eauto. auto.
  split; intros. apply eval_testcond_compare_sint; auto. 
  transitivity (rs' r). destruct r; reflexivity || discriminate. auto with asmgen.
- (* Ccompuimm *)
  destruct (is_arith_imm32 n); [|destruct (is_arith_imm32 (Int.neg n))].
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite Int.repr_unsigned. apply eval_testcond_compare_uint; auto. 
  destruct r; reflexivity || discriminate.
+ econstructor; split.
  apply exec_straight_one. simpl. rewrite Int.repr_unsigned, Int.neg_involutive. eauto. auto.
  split; intros. apply eval_testcond_compare_uint; auto. 
  destruct r; reflexivity || discriminate.
+ exploit (exec_loadimm32 X16 n). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one.
  simpl. rewrite B, C by eauto with asmgen. eauto. auto.
  split; intros. apply eval_testcond_compare_uint; auto. 
  transitivity (rs' r). destruct r; reflexivity || discriminate. auto with asmgen.
- (* Ccompshift *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite transl_eval_shift. apply eval_testcond_compare_sint; auto. 
  destruct r; reflexivity || discriminate.
- (* Ccompushift *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite transl_eval_shift. apply eval_testcond_compare_uint; auto. 
  destruct r; reflexivity || discriminate.
- (* Cmaskzero *)
  destruct (is_logical_imm32 n).
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite Int.repr_unsigned. apply (eval_testcond_compare_sint Ceq); auto.
  destruct r; reflexivity || discriminate.
+ exploit (exec_loadimm32 X16 n). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl. rewrite B, C by eauto with asmgen. eauto. auto.
  split; intros. apply (eval_testcond_compare_sint Ceq); auto.
  transitivity (rs' r). destruct r; reflexivity || discriminate. auto with asmgen.
- (* Cmasknotzero *)
  destruct (is_logical_imm32 n).
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite Int.repr_unsigned. apply (eval_testcond_compare_sint Cne); auto.
  destruct r; reflexivity || discriminate.
+ exploit (exec_loadimm32 X16 n). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl. rewrite B, C by eauto with asmgen. eauto. auto.
  split; intros. apply (eval_testcond_compare_sint Cne); auto.
  transitivity (rs' r). destruct r; reflexivity || discriminate. auto with asmgen.
- (* Ccompl *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. apply eval_testcond_compare_slong; auto. 
  destruct r; reflexivity || discriminate.
- (* Ccomplu *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. apply eval_testcond_compare_ulong; auto. 
  destruct r; reflexivity || discriminate.
- (* Ccomplimm *)
  destruct (is_arith_imm64 n); [|destruct (is_arith_imm64 (Int64.neg n))].
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite Int64.repr_unsigned. apply eval_testcond_compare_slong; auto. 
  destruct r; reflexivity || discriminate.
+ econstructor; split.
  apply exec_straight_one. simpl. rewrite Int64.repr_unsigned, Int64.neg_involutive. eauto. auto.
  split; intros. apply eval_testcond_compare_slong; auto. 
  destruct r; reflexivity || discriminate.
+ exploit (exec_loadimm64 X16 n). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one.
  simpl. rewrite B, C by eauto with asmgen. eauto. auto.
  split; intros. apply eval_testcond_compare_slong; auto. 
  transitivity (rs' r). destruct r; reflexivity || discriminate. auto with asmgen.
- (* Ccompluimm *)
  destruct (is_arith_imm64 n); [|destruct (is_arith_imm64 (Int64.neg n))].
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite Int64.repr_unsigned. apply eval_testcond_compare_ulong; auto. 
  destruct r; reflexivity || discriminate.
+ econstructor; split.
  apply exec_straight_one. simpl. rewrite Int64.repr_unsigned, Int64.neg_involutive. eauto. auto.
  split; intros. apply eval_testcond_compare_ulong; auto. 
  destruct r; reflexivity || discriminate.
+ exploit (exec_loadimm64 X16 n). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one.
  simpl. rewrite B, C by eauto with asmgen. eauto. auto.
  split; intros. apply eval_testcond_compare_ulong; auto. 
  transitivity (rs' r). destruct r; reflexivity || discriminate. auto with asmgen.
- (* Ccomplshift *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite transl_eval_shiftl. apply eval_testcond_compare_slong; auto. 
  destruct r; reflexivity || discriminate.
- (* Ccomplushift *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite transl_eval_shiftl. apply eval_testcond_compare_ulong; auto. 
  destruct r; reflexivity || discriminate.
- (* Cmasklzero *)
  destruct (is_logical_imm64 n).
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite Int64.repr_unsigned. apply (eval_testcond_compare_slong Ceq); auto.
  destruct r; reflexivity || discriminate.
+ exploit (exec_loadimm64 X16 n). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl. rewrite B, C by eauto with asmgen. eauto. auto.
  split; intros. apply (eval_testcond_compare_slong Ceq); auto.
  transitivity (rs' r). destruct r; reflexivity || discriminate. auto with asmgen.
- (* Cmasknotzero *)
  destruct (is_logical_imm64 n).
+ econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split; intros. rewrite Int64.repr_unsigned. apply (eval_testcond_compare_slong Cne); auto.
  destruct r; reflexivity || discriminate.
+ exploit (exec_loadimm64 X16 n). intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl. rewrite B, C by eauto with asmgen. eauto. auto.
  split; intros. apply (eval_testcond_compare_slong Cne); auto.
  transitivity (rs' r). destruct r; reflexivity || discriminate. auto with asmgen.
- (* Ccompf *)
  econstructor; split. apply exec_straight_one. simpl; eauto.
  rewrite compare_float_inv; auto.
  split; intros. apply eval_testcond_compare_float; auto.
  destruct r; discriminate || rewrite compare_float_inv; auto.
- (* Cnotcompf *)
  econstructor; split. apply exec_straight_one. simpl; eauto.
  rewrite compare_float_inv; auto.
  split; intros. apply eval_testcond_compare_not_float; auto.
  destruct r; discriminate || rewrite compare_float_inv; auto.
- (* Ccompfzero *)
  econstructor; split. apply exec_straight_one. simpl; eauto.
  rewrite compare_float_inv; auto.
  split; intros. apply eval_testcond_compare_float; auto.
  destruct r; discriminate || rewrite compare_float_inv; auto.
- (* Cnotcompfzero *)
  econstructor; split. apply exec_straight_one. simpl; eauto.
  rewrite compare_float_inv; auto.
  split; intros. apply eval_testcond_compare_not_float; auto.
  destruct r; discriminate || rewrite compare_float_inv; auto.
- (* Ccompfs *)
  econstructor; split. apply exec_straight_one. simpl; eauto.
  rewrite compare_single_inv; auto.
  split; intros. apply eval_testcond_compare_single; auto.
  destruct r; discriminate || rewrite compare_single_inv; auto.
- (* Cnotcompfs *)
  econstructor; split. apply exec_straight_one. simpl; eauto.
  rewrite compare_single_inv; auto.
  split; intros. apply eval_testcond_compare_not_single; auto.
  destruct r; discriminate || rewrite compare_single_inv; auto.
- (* Ccompfszero *)
  econstructor; split. apply exec_straight_one. simpl; eauto.
  rewrite compare_single_inv; auto.
  split; intros. apply eval_testcond_compare_single; auto.
  destruct r; discriminate || rewrite compare_single_inv; auto.
- (* Cnotcompfszero *)
  econstructor; split. apply exec_straight_one. simpl; eauto.
  rewrite compare_single_inv; auto.
  split; intros. apply eval_testcond_compare_not_single; auto.
  destruct r; discriminate || rewrite compare_single_inv; auto.
Qed.

(** Translation of conditional branches *)

Lemma transl_cond_branch_correct:
  forall cond args lbl k c rs m b,
  transl_cond_branch cond args lbl k = OK c ->
  eval_condition cond (map rs (map preg_of args)) m = Some b ->
  exists rs' insn,
     exec_straight_opt ge fn c rs m (insn :: k) rs' m
  /\ exec_instr ge fn insn rs' m =
         (if b then goto_label fn lbl rs' m else Next (nextinstr rs') m)
  /\ forall r, data_preg r = true -> rs'#r = rs#r.
Proof.
  intros until b; intros TR EV.
  assert (DFL:
    transl_cond_branch_default cond args lbl k = OK c ->
    exists rs' insn,
       exec_straight_opt ge fn c rs m (insn :: k) rs' m
    /\ exec_instr ge fn insn rs' m =
         (if b then goto_label fn lbl rs' m else Next (nextinstr rs') m)
    /\ forall r, data_preg r = true -> rs'#r = rs#r).
  {
    unfold transl_cond_branch_default; intros.
    exploit transl_cond_correct; eauto. intros (rs' & A & B & C).
    exists rs', (Pbc (cond_for_cond cond) lbl); split.
    apply exec_straight_opt_intro. eexact A.
    split; auto. simpl. rewrite (B b) by auto. auto. 
  }
Local Opaque transl_cond transl_cond_branch_default.
  destruct args as [ | a1 args]; simpl in TR; auto.
  destruct args as [ | a2 args]; simpl in TR; auto.
  destruct cond; simpl in TR; auto.
- (* Ccompimm *)
  destruct c0; auto; destruct (Int.eq n Int.zero) eqn:N0; auto; 
  apply Int.same_if_eq in N0; subst n; ArgsInv.
+ (* Ccompimm Cne 0 *)
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. destruct (rs x); simpl in EV; inv EV. simpl. auto.
+ (* Ccompimm Ceq 0 *)
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. destruct (rs x); simpl in EV; inv EV. simpl. destruct (Int.eq i Int.zero); auto.
- (* Ccompuimm *)
  destruct c0; auto; destruct (Int.eq n Int.zero) eqn:N0; auto;
  apply Int.same_if_eq in N0; subst n; ArgsInv.
+ (* Ccompuimm Cne 0 *)
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. rewrite EV. auto.
+ (* Ccompuimm Ceq 0 *)
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. rewrite (Val.negate_cmpu_bool (Mem.valid_pointer m) Cne), EV. destruct b; auto.
- (* Cmaskzero *)
  destruct (Int.is_power2 n) as [bit|] eqn:P2; auto. ArgsInv.
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl.
  erewrite <- Int.mul_pow2, Int.mul_commut, Int.mul_one by eauto.
  rewrite (Val.negate_cmp_bool Ceq), EV. destruct b; auto.
- (* Cmasknotzero *)
  destruct (Int.is_power2 n) as [bit|] eqn:P2; auto. ArgsInv.
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl.
  erewrite <- Int.mul_pow2, Int.mul_commut, Int.mul_one by eauto.
  rewrite EV. auto.
- (* Ccomplimm *)
  destruct c0; auto; destruct (Int64.eq n Int64.zero) eqn:N0; auto; 
  apply Int64.same_if_eq in N0; subst n; ArgsInv.
+ (* Ccomplimm Cne 0 *)
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. destruct (rs x); simpl in EV; inv EV. simpl. auto.
+ (* Ccomplimm Ceq 0 *)
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. destruct (rs x); simpl in EV; inv EV. simpl. destruct (Int64.eq i Int64.zero); auto.
- (* Ccompluimm *)
  destruct c0; auto; destruct (Int64.eq n Int64.zero) eqn:N0; auto;
  apply Int64.same_if_eq in N0; subst n; ArgsInv.
+ (* Ccompluimm Cne 0 *)
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. rewrite EV. auto.
+ (* Ccompluimm Ceq 0 *)
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl. rewrite (Val.negate_cmplu_bool (Mem.valid_pointer m) Cne), EV. destruct b; auto.
- (* Cmasklzero *)
  destruct (Int64.is_power2' n) as [bit|] eqn:P2; auto. ArgsInv.
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl.
  erewrite <- Int64.mul_pow2', Int64.mul_commut, Int64.mul_one by eauto.
  rewrite (Val.negate_cmpl_bool Ceq), EV. destruct b; auto.
- (* Cmasklnotzero *)
  destruct (Int64.is_power2' n) as [bit|] eqn:P2; auto. ArgsInv.
  do 2 econstructor; split.
  apply exec_straight_opt_refl.
  split; auto. simpl.
  erewrite <- Int64.mul_pow2', Int64.mul_commut, Int64.mul_one by eauto.
  rewrite EV. auto.
Qed.

(** Translation of arithmetic operations *)

Ltac SimplEval H :=
  match type of H with
  | Some _ = None _ => discriminate
  | Some _ = Some _ => inv H
  | ?a = Some ?b => let A := fresh in assert (A: Val.maketotal a = b) by (rewrite H; reflexivity)
end.

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ rewrite ? transl_eval_shift, ? transl_eval_shiftl;
             apply Val.lessdef_same; Simpl; fail
           | intros; Simpl; fail ] ].

Ltac TranslOpBase :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ rewrite ? transl_eval_shift, ? transl_eval_shiftl; Simpl
           | intros; Simpl; fail ] ].

Lemma transl_op_correct:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
Local Opaque Int.eq Int64.eq Val.add Val.addl Int.zwordsize Int64.zwordsize.
  intros until c; intros TR EV.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; SimplEval EV; try TranslOpSimpl.
- (* move *)
  destruct (preg_of res) eqn:RR; try discriminate; destruct (preg_of m0) eqn:R1; inv TR.
+ TranslOpSimpl.
+ TranslOpSimpl.
- (* intconst *)
  exploit exec_loadimm32. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split. rewrite B; auto. intros; auto with asmgen.
- (* longconst *)
  exploit exec_loadimm64. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split. rewrite B; auto. intros; auto with asmgen.
- (* floatconst *)
  destruct (Float.eq_dec n Float.zero).
+ subst n. TranslOpSimpl. 
+ TranslOpSimpl.
- (* singleconst *)
  destruct (Float32.eq_dec n Float32.zero).
+ subst n. TranslOpSimpl. 
+ TranslOpSimpl.
- (* loadsymbol *)
  exploit (exec_loadsymbol x id ofs). eauto with asmgen. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split. rewrite B; auto. auto.
- (* addrstack *)
  exploit (exec_addimm64 x XSP (Ptrofs.to_int64 ofs)). simpl; eauto with asmgen.
  intros (rs' & A & B & C).
  exists rs'; split. eexact A. split. simpl in B; rewrite B.
Local Transparent Val.addl.
  destruct (rs SP); simpl; auto. rewrite Ptrofs.of_int64_to_int64 by auto. auto.
  auto.
- (* shift *)
  rewrite <- transl_eval_shift'. TranslOpSimpl.
- (* addimm *)
  exploit (exec_addimm32 x x0 n). eauto with asmgen. intros (rs' & A & B & C).
  exists rs'; split. eexact A. split. rewrite B; auto. auto.
- (* mul *)
  TranslOpBase.
Local Transparent Val.add.
  destruct (rs x0); auto; destruct (rs x1); auto. simpl. rewrite Int.add_zero_l; auto.
- (* andimm *)
  exploit (exec_logicalimm32 (Pandimm W) (Pand W)). 
  intros; reflexivity. intros; reflexivity. instantiate (1 := x0). eauto with asmgen.
  intros (rs' & A & B & C). 
  exists rs'; split. eexact A. split. rewrite B; auto. auto.
- (* orimm *)
  exploit (exec_logicalimm32 (Porrimm W) (Porr W)). 
  intros; reflexivity. intros; reflexivity. instantiate (1 := x0). eauto with asmgen.
  intros (rs' & A & B & C). 
  exists rs'; split. eexact A. split. rewrite B; auto. auto.
- (* xorimm *)
  exploit (exec_logicalimm32 (Peorimm W) (Peor W)). 
  intros; reflexivity. intros; reflexivity. instantiate (1 := x0). eauto with asmgen.
  intros (rs' & A & B & C). 
  exists rs'; split. eexact A. split. rewrite B; auto. auto.
- (* not *)
  TranslOpBase.
  destruct (rs x0); auto. simpl. rewrite Int.or_zero_l; auto.
- (* notshift *)
  TranslOpBase.
  destruct (eval_shift s (rs x0) a); auto. simpl. rewrite Int.or_zero_l; auto.
- (* shrx *)
  exploit (exec_shrx32 x x0 n); eauto with asmgen. intros (rs' & A & B & C).
  econstructor; split. eexact A. split. rewrite B; auto. auto.
- (* zero-ext *)
  TranslOpBase.
  destruct (rs x0); auto; simpl. rewrite Int.shl_zero. auto.
- (* sign-ext *)
  TranslOpBase.
  destruct (rs x0); auto; simpl. rewrite Int.shl_zero. auto.
- (* shlzext *)
  TranslOpBase.
  destruct (rs x0); simpl; auto. rewrite <- Int.shl_zero_ext_min; auto using a32_range.
- (* shlsext *)
  TranslOpBase.
  destruct (rs x0); simpl; auto. rewrite <- Int.shl_sign_ext_min; auto using a32_range.
- (* zextshr *)
  TranslOpBase.
  destruct (rs x0); simpl; auto. rewrite ! a32_range; simpl. rewrite <- Int.zero_ext_shru_min; auto using a32_range.
- (* sextshr *)
  TranslOpBase.
  destruct (rs x0); simpl; auto. rewrite ! a32_range; simpl. rewrite <- Int.sign_ext_shr_min; auto using a32_range.
- (* shiftl *)
  rewrite <- transl_eval_shiftl'. TranslOpSimpl.
- (* extend *)
  exploit (exec_move_extended x0 x1 x a k). intros (rs' & A & B & C).
  econstructor; split. eexact A. 
  split. rewrite B; auto. eauto with asmgen.
- (* addext *)
  exploit (exec_arith_extended Val.addl Paddext (Padd X)).
  auto. auto. instantiate (1 := x1). eauto with asmgen. intros (rs' & A & B & C).
  econstructor; split. eexact A. split. rewrite B; auto. auto.
- (* addlimm *)
  exploit (exec_addimm64 x x0 n). simpl. generalize (ireg_of_not_X16 _ _ EQ1). congruence.
  intros (rs' & A & B & C).
  exists rs'; split. eexact A. split. simpl in B; rewrite B; auto. auto.
- (* subext *)
  exploit (exec_arith_extended Val.subl Psubext (Psub X)).
  auto. auto. instantiate (1 := x1). eauto with asmgen. intros (rs' & A & B & C).
  econstructor; split. eexact A. split. rewrite B; auto. auto.
- (* mull *)
  TranslOpBase.
  destruct (rs x0); auto; destruct (rs x1); auto. simpl. rewrite Int64.add_zero_l; auto.
- (* andlimm *)
  exploit (exec_logicalimm64 (Pandimm X) (Pand X)). 
  intros; reflexivity. intros; reflexivity. instantiate (1 := x0). eauto with asmgen.
  intros (rs' & A & B & C). 
  exists rs'; split. eexact A. split. rewrite B; auto. auto.
- (* orlimm *)
  exploit (exec_logicalimm64 (Porrimm X) (Porr X)). 
  intros; reflexivity. intros; reflexivity. instantiate (1 := x0). eauto with asmgen.
  intros (rs' & A & B & C). 
  exists rs'; split. eexact A. split. rewrite B; auto. auto.
- (* xorlimm *)
  exploit (exec_logicalimm64 (Peorimm X) (Peor X)). 
  intros; reflexivity. intros; reflexivity. instantiate (1 := x0). eauto with asmgen.
  intros (rs' & A & B & C). 
  exists rs'; split. eexact A. split. rewrite B; auto. auto.
- (* notl *)
  TranslOpBase.
  destruct (rs x0); auto. simpl. rewrite Int64.or_zero_l; auto.
- (* notlshift *)
  TranslOpBase.
  destruct (eval_shiftl s (rs x0) a); auto. simpl. rewrite Int64.or_zero_l; auto.
- (* shrx *)
  exploit (exec_shrx64 x x0 n); eauto with asmgen. intros (rs' & A & B & C).
  econstructor; split. eexact A. split. rewrite B; auto. auto.
- (* zero-ext-l *)
  TranslOpBase.
  destruct (rs x0); auto; simpl. rewrite Int64.shl'_zero. auto.
- (* sign-ext-l *)
  TranslOpBase.
  destruct (rs x0); auto; simpl. rewrite Int64.shl'_zero. auto.
- (* shllzext *)
  TranslOpBase.
  destruct (rs x0); simpl; auto. rewrite <- Int64.shl'_zero_ext_min; auto using a64_range.
- (* shllsext *)
  TranslOpBase.
  destruct (rs x0); simpl; auto. rewrite <- Int64.shl'_sign_ext_min; auto using a64_range.
- (* zextshrl *)
  TranslOpBase.
  destruct (rs x0); simpl; auto. rewrite ! a64_range; simpl. rewrite <- Int64.zero_ext_shru'_min; auto using a64_range.
- (* sextshrl *)
  TranslOpBase.
  destruct (rs x0); simpl; auto. rewrite ! a64_range; simpl. rewrite <- Int64.sign_ext_shr'_min; auto using a64_range.
- (* condition *)
  exploit (transl_cond_correct cond args); eauto. intros (rs' & A & B & C).
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. destruct (eval_condition cond (map rs (map preg_of args)) m) as [b|]; simpl in *.
  rewrite (B b) by auto. auto. 
  auto.
  intros; Simpl.
- (* select *)
  destruct (preg_of res) eqn:RES; monadInv TR.
  + (* integer *)
    generalize (ireg_of_eq _ _ EQ) (ireg_of_eq _ _ EQ1); intros E1 E2; rewrite E1, E2.
    exploit (transl_cond_correct cond args); eauto. intros (rs' & A & B & C).
    econstructor; split.
    eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; eauto. auto.
    split. Simpl. destruct (eval_condition cond (map rs (map preg_of args)) m) as [b|]; simpl in *.
    rewrite (B b) by auto. rewrite !C. apply Val.lessdef_normalize.
    rewrite <- E2; auto with asmgen. rewrite <- E1; auto with asmgen.
    auto.
    intros; Simpl.
  + (* FP *)
    generalize (freg_of_eq _ _ EQ) (freg_of_eq _ _ EQ1); intros E1 E2; rewrite E1, E2.
    exploit (transl_cond_correct cond args); eauto. intros (rs' & A & B & C).
    econstructor; split.
    eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; eauto. auto.
    split. Simpl. destruct (eval_condition cond (map rs (map preg_of args)) m) as [b|]; simpl in *.
    rewrite (B b) by auto. rewrite !C. apply Val.lessdef_normalize.
    rewrite <- E2; auto with asmgen. rewrite <- E1; auto with asmgen.
    auto.
    intros; Simpl.
Qed.

(** Translation of addressing modes, loads, stores *)

Lemma transl_addressing_correct:
  forall sz addr args (insn: Asm.addressing -> instruction) k (rs: regset) m c b o,
  transl_addressing sz addr args insn k = OK c ->
  Op.eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some (Vptr b o) ->
  exists ad rs',
     exec_straight_opt ge fn c rs m (insn ad :: k) rs' m
  /\ Asm.eval_addressing ge ad rs' = Vptr b o
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  intros until o; intros TR EV.
  unfold transl_addressing in TR; destruct addr; ArgsInv; SimplEval EV.
- (* Aindexed *)
  destruct (offset_representable sz ofs); inv EQ0.
+ econstructor; econstructor; split. apply exec_straight_opt_refl.
  auto.
+ exploit (exec_loadimm64 X16 ofs). intros (rs' & A & B & C).
  econstructor; exists rs'; split. apply exec_straight_opt_intro; eexact A.
  split. simpl. rewrite B, C by eauto with asmgen. auto.
  eauto with asmgen.
- (* Aindexed2 *)
  econstructor; econstructor; split. apply exec_straight_opt_refl.
  auto.
- (* Aindexed2shift *)
  destruct (Int.eq a Int.zero) eqn:E; [|destruct (Int.eq (Int.shl Int.one a) (Int.repr sz))]; inv EQ2.
+ apply Int.same_if_eq in E. rewrite E.
  econstructor; econstructor; split. apply exec_straight_opt_refl.
  split; auto. simpl.
  rewrite Val.addl_commut in H0. destruct (rs x0); try discriminate.
  unfold Val.shll. rewrite Int64.shl'_zero. auto.
+ econstructor; econstructor; split. apply exec_straight_opt_refl.
  auto. 
+ econstructor; econstructor; split.
  apply exec_straight_opt_intro. apply exec_straight_one. simpl; eauto. auto.
  split. simpl. Simpl. rewrite H0. simpl. rewrite Ptrofs.add_zero. auto.
  intros; Simpl.
- (* Aindexed2ext *)
  destruct (Int.eq a Int.zero || Int.eq (Int.shl Int.one a) (Int.repr sz)); inv EQ2.
+ econstructor; econstructor; split. apply exec_straight_opt_refl.
  split; auto. destruct x; auto.
+ exploit (exec_arith_extended Val.addl Paddext (Padd X)); auto.
  instantiate (1 := x0). eauto with asmgen.
  intros (rs' & A & B & C).
  econstructor; exists rs'; split.
  apply exec_straight_opt_intro. eexact A. 
  split. simpl. rewrite B. rewrite Val.addl_assoc. f_equal.
  unfold Op.eval_extend; destruct x, (rs x1); simpl; auto; rewrite ! a64_range;
  simpl; rewrite Int64.add_zero; auto.
  intros. apply C; eauto with asmgen.
- (* Aglobal *)
  destruct (Ptrofs.eq (Ptrofs.modu ofs (Ptrofs.repr sz)) Ptrofs.zero && symbol_is_aligned id sz); inv TR.
+ econstructor; econstructor; split.
  apply exec_straight_opt_intro. apply exec_straight_one. simpl; eauto. auto.
  split. simpl. Simpl. rewrite symbol_high_low. simpl in EV. congruence.
  intros; Simpl.
+ exploit (exec_loadsymbol X16 id ofs). auto. intros (rs' & A & B & C).
  econstructor; exists rs'; split.
  apply exec_straight_opt_intro. eexact A.
  split. simpl. 
  rewrite B. rewrite <- Genv.shift_symbol_address_64, Ptrofs.add_zero by auto. 
  simpl in EV. congruence. 
  auto with asmgen.
- (* Ainstrack *)
  assert (E: Val.addl (rs SP) (Vlong (Ptrofs.to_int64 ofs)) = Vptr b o).
  { simpl in EV. inv EV. destruct (rs SP); simpl in H1; inv H1. simpl. 
    rewrite Ptrofs.of_int64_to_int64 by auto. auto. }   
  destruct (offset_representable sz (Ptrofs.to_int64 ofs)); inv TR.
+ econstructor; econstructor; split. apply exec_straight_opt_refl.
  auto.
+ exploit (exec_loadimm64 X16 (Ptrofs.to_int64 ofs)). intros (rs' & A & B & C).
  econstructor; exists rs'; split.
  apply exec_straight_opt_intro. eexact A.
  split. simpl. rewrite B, C by eauto with asmgen. auto.
  auto with asmgen.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m vaddr v,
  transl_load chunk addr args dst k = OK c ->
  Op.eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some vaddr ->
  Mem.loadv chunk m vaddr = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, data_preg r = true -> r <> preg_of dst -> rs' r = rs r.
Proof.
  intros. destruct vaddr; try discriminate. 
  assert (A: exists sz insn,
                transl_addressing sz addr args insn k = OK c
             /\ (forall ad rs', exec_instr ge fn (insn ad) rs' m =
                              exec_load ge chunk (fun v => v) ad (preg_of dst) rs' m)).
  {
    destruct chunk; monadInv H;
    try rewrite (ireg_of_eq _ _ EQ); try rewrite (freg_of_eq _ _ EQ);
    do 2 econstructor; (split; [eassumption|auto]).
  }
  destruct A as (sz & insn & B & C).
  exploit transl_addressing_correct. eexact B. eexact H0. intros (ad & rs' & P & Q & R).
  assert (X: exec_load ge chunk (fun v => v) ad (preg_of dst) rs' m =
             Next (nextinstr (rs'#(preg_of dst) <- v)) m).
  { unfold exec_load. rewrite Q, H1. auto. }
  econstructor; split.
  eapply exec_straight_opt_right. eexact P.
  apply exec_straight_one. rewrite C, X; eauto. Simpl. 
  split. Simpl. intros; Simpl.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m vaddr m',
  transl_store chunk addr args src k = OK c ->
  Op.eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some vaddr ->
  Mem.storev chunk m vaddr rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  intros. destruct vaddr; try discriminate. 
  set (chunk' := match chunk with Mint8signed => Mint8unsigned
                                | Mint16signed => Mint16unsigned
                                | _ => chunk end).
  assert (A: exists sz insn,
                transl_addressing sz addr args insn k = OK c
             /\ (forall ad rs', exec_instr ge fn (insn ad) rs' m =
                              exec_store ge chunk' ad rs'#(preg_of src) rs' m)).
  {
    unfold chunk'; destruct chunk; monadInv H;
    try rewrite (ireg_of_eq _ _ EQ); try rewrite (freg_of_eq _ _ EQ);
    do 2 econstructor; (split; [eassumption|auto]).
  }
  destruct A as (sz & insn & B & C).
  exploit transl_addressing_correct. eexact B. eexact H0. intros (ad & rs' & P & Q & R).
  assert (X: Mem.storev chunk' m (Vptr b i) rs#(preg_of src) = Some m').
  { rewrite <- H1. unfold chunk'. destruct chunk; auto; simpl; symmetry.
    apply Mem.store_signed_unsigned_8.
    apply Mem.store_signed_unsigned_16. }
  assert (Y: exec_store ge chunk' ad rs'#(preg_of src) rs' m =
             Next (nextinstr rs') m').
  { unfold exec_store. rewrite Q, R, X by auto with asmgen. auto. }
  econstructor; split.
  eapply exec_straight_opt_right. eexact P.
  apply exec_straight_one. rewrite C, Y; eauto. Simpl. 
  intros; Simpl.
Qed.

(** Translation of indexed memory accesses *)

Lemma indexed_memory_access_correct: forall insn sz (base: iregsp) ofs k (rs: regset) m b i,
  preg_of_iregsp base <> IR X16 ->
  Val.offset_ptr rs#base ofs = Vptr b i ->
  exists ad rs',
     exec_straight_opt ge fn (indexed_memory_access insn sz base ofs k) rs m (insn ad :: k) rs' m
  /\ Asm.eval_addressing ge ad rs' = Vptr b i
  /\ forall r, r <> PC -> r <> X16 -> rs' r = rs r.
Proof.
  unfold indexed_memory_access; intros.
  assert (Val.addl rs#base (Vlong (Ptrofs.to_int64 ofs)) = Vptr b i).
  { destruct (rs base); try discriminate. simpl in *. rewrite Ptrofs.of_int64_to_int64 by auto. auto. }
  destruct offset_representable.
- econstructor; econstructor; split. apply exec_straight_opt_refl. auto. 
- exploit (exec_loadimm64 X16); eauto. intros (rs' & A & B & C).
  econstructor; econstructor; split. apply exec_straight_opt_intro; eexact A.
  split. simpl. rewrite B, C by eauto with asmgen. auto. auto.
Qed.

Lemma loadptr_correct: forall (base: iregsp) ofs dst k m v (rs: regset),
  Mem.loadv Mint64 m (Val.offset_ptr rs#base ofs) = Some v ->
  preg_of_iregsp base <> IR X16 ->
  exists rs',
     exec_straight ge fn (loadptr base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, r <> PC -> r <> X16 -> r <> dst -> rs' r = rs r.
Proof.
  intros. 
  destruct (Val.offset_ptr rs#base ofs) eqn:V; try discriminate.
  exploit indexed_memory_access_correct; eauto. intros (ad & rs' & A & B & C). 
  econstructor; split.
  eapply exec_straight_opt_right. eexact A.
  apply exec_straight_one. simpl. unfold exec_load. rewrite B, H. eauto. auto.
  split. Simpl. intros; Simpl.
Qed.

Lemma storeptr_correct: forall (base: iregsp) ofs (src: ireg) k m m' (rs: regset),
  Mem.storev Mint64 m (Val.offset_ptr rs#base ofs) rs#src = Some m' ->
  preg_of_iregsp base <> IR X16 ->
  src <> X16 ->
  exists rs',
     exec_straight ge fn (storeptr src base ofs k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> X16 -> rs' r = rs r.
Proof.
  intros. 
  destruct (Val.offset_ptr rs#base ofs) eqn:V; try discriminate.
  exploit indexed_memory_access_correct; eauto. intros (ad & rs' & A & B & C). 
  econstructor; split.
  eapply exec_straight_opt_right. eexact A.
  apply exec_straight_one. simpl. unfold exec_store. rewrite B, C, H by eauto with asmgen. eauto. auto.
  intros; Simpl.
Qed.

Lemma loadind_correct: forall (base: iregsp) ofs ty dst k c (rs: regset) m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  preg_of_iregsp base <> IR X16 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, data_preg r = true -> r <> preg_of dst -> rs' r = rs r.
Proof.
  intros. 
  destruct (Val.offset_ptr rs#base ofs) eqn:V; try discriminate.
  assert (X: exists sz insn,
                c = indexed_memory_access insn sz base ofs k
             /\ (forall ad rs', exec_instr ge fn (insn ad) rs' m =
                              exec_load ge (chunk_of_type ty) (fun v => v) ad (preg_of dst) rs' m)).
  {
    unfold loadind in H; destruct ty; destruct (preg_of dst); inv H; do 2 econstructor; eauto.
  }
  destruct X as (sz & insn & EQ & SEM). subst c.
  exploit indexed_memory_access_correct; eauto. intros (ad & rs' & A & B & C). 
  econstructor; split.
  eapply exec_straight_opt_right. eexact A.
  apply exec_straight_one. rewrite SEM. unfold exec_load. rewrite B, H0. eauto. Simpl.
  split. Simpl. intros; Simpl.
Qed.

Lemma storeind_correct: forall (base: iregsp) ofs ty src k c (rs: regset) m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) rs#(preg_of src) = Some m' ->
  preg_of_iregsp base <> IR X16 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  intros. 
  destruct (Val.offset_ptr rs#base ofs) eqn:V; try discriminate.
  assert (X: exists sz insn,
                c = indexed_memory_access insn sz base ofs k
             /\ (forall ad rs', exec_instr ge fn (insn ad) rs' m =
                              exec_store ge (chunk_of_type ty) ad rs'#(preg_of src) rs' m)).
  {
    unfold storeind in H; destruct ty; destruct (preg_of src); inv H; do 2 econstructor; eauto.
  }
  destruct X as (sz & insn & EQ & SEM). subst c.
  exploit indexed_memory_access_correct; eauto. intros (ad & rs' & A & B & C). 
  econstructor; split.
  eapply exec_straight_opt_right. eexact A.
  apply exec_straight_one. rewrite SEM.
  unfold exec_store. rewrite B, C, H0 by eauto with asmgen. eauto.
  Simpl.
  intros; Simpl.
Qed.

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
  /\ (forall r, r <> PC -> r <> SP -> r <> X30 -> r <> X16 -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold make_epilogue. 
  exploit (loadptr_correct XSP (fn_retaddr_ofs f)).
    instantiate (2 := rs). simpl. rewrite <- (sp_val _ _ _ AG). simpl. eexact LRA'. simpl; congruence.
  intros (rs1 & A1 & B1 & C1).
  econstructor; econstructor; split.
  eapply exec_straight_trans. eexact A1. apply exec_straight_one. simpl. 
    simpl; rewrite (C1 SP) by auto with asmgen. rewrite <- (sp_val _ _ _ AG). simpl; rewrite LP'. 
    rewrite FREE'. eauto. auto. 
  split. apply agree_nextinstr. apply agree_set_other; auto.
  apply agree_change_sp with (Vptr stk soff).
  apply agree_exten with rs; auto. intros; apply C1; auto with asmgen.
  eapply parent_sp_def; eauto.
  split. auto.
  split. Simpl. 
  split. Simpl. 
  intros. Simpl.
Qed.

End CONSTRUCTORS.
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

(** Correctness proof for PPC generation: auxiliary results. *)

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

Local Transparent Archi.ptr64.

(** * Properties of low half/high half decomposition *)

Lemma low_high_u:
  forall n, Int.or (Int.shl (high_u n) (Int.repr 16)) (low_u n) = n.
Proof.
  intros. unfold high_u, low_u.
  rewrite Int.shl_rolm. rewrite Int.shru_rolm.
  rewrite Int.rolm_rolm.
  change (Int.modu (Int.add (Int.sub (Int.repr (Z.of_nat Int.wordsize)) (Int.repr 16))
                            (Int.repr 16))
                   (Int.repr (Z.of_nat Int.wordsize)))
    with (Int.zero).
  rewrite Int.rolm_zero. rewrite <- Int.and_or_distrib.
  exact (Int.and_mone n).
  apply int_wordsize_divides_modulus. reflexivity. reflexivity.
Qed.

Lemma low_high_u_xor:
  forall n, Int.xor (Int.shl (high_u n) (Int.repr 16)) (low_u n) = n.
Proof.
  intros. unfold high_u, low_u.
  rewrite Int.shl_rolm. rewrite Int.shru_rolm.
  rewrite Int.rolm_rolm.
  change (Int.modu (Int.add (Int.sub (Int.repr (Z.of_nat Int.wordsize)) (Int.repr 16))
                            (Int.repr 16))
                   (Int.repr (Z.of_nat Int.wordsize)))
    with (Int.zero).
  rewrite Int.rolm_zero. rewrite <- Int.and_xor_distrib.
  exact (Int.and_mone n).
  apply int_wordsize_divides_modulus. reflexivity. reflexivity.
Qed.

Lemma low_high_s:
  forall n, Int.add (Int.shl (high_s n) (Int.repr 16)) (low_s n) = n.
Proof.
  intros.
  rewrite Int.shl_mul_two_p.
  unfold high_s.
  rewrite <- (Int.divu_pow2 (Int.sub n (low_s n)) (Int.repr 65536) (Int.repr 16)).
  2: reflexivity.
  change (two_p (Int.unsigned (Int.repr 16))) with 65536.
  set (x := Int.sub n (low_s n)).
  assert (x = Int.add (Int.mul (Int.divu x (Int.repr 65536)) (Int.repr 65536))
                      (Int.modu x (Int.repr 65536))).
    apply Int.modu_divu_Euclid. vm_compute; congruence.
  assert (Int.modu x (Int.repr 65536) = Int.zero).
    unfold Int.modu, Int.zero. decEq.
    change 0 with (0 mod 65536).
    change (Int.unsigned (Int.repr 65536)) with 65536.
    apply Int.eqmod_mod_eq. omega.
    unfold x, low_s. eapply Int.eqmod_trans.
    apply Int.eqmod_divides with Int.modulus.
    unfold Int.sub. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
    exists 65536. compute; auto.
    replace 0 with (Int.unsigned n - Int.unsigned n) by omega.
    apply Int.eqmod_sub. apply Int.eqmod_refl. apply Int.eqmod_sign_ext'.
    compute; auto.
  rewrite H0 in H. rewrite Int.add_zero in H.
  rewrite <- H. unfold x. rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg (low_s n))). rewrite <- Int.sub_add_opp.
  rewrite Int.sub_idem. apply Int.add_zero.
Qed.

Lemma add_zero_symbol_address:
  forall (ge: genv) id ofs,
  Val.add Vzero (Genv.symbol_address ge id ofs) = Genv.symbol_address ge id ofs.
Proof.
  unfold Genv.symbol_address; intros. destruct (Genv.find_symbol ge id); auto.
  simpl. rewrite Ptrofs.add_zero; auto.
Qed.

Lemma low_high_half_zero:
  forall (ge: genv) id ofs,
  Val.add (Val.add Vzero (high_half ge id ofs)) (low_half ge id ofs) =
  Genv.symbol_address ge id ofs.
Proof.
  intros. rewrite Val.add_assoc. rewrite low_high_half. apply add_zero_symbol_address.
Qed.

(** * Useful properties of registers *)

(** [important_preg] extends [data_preg] by tracking the LR register as well.
    It is used to state that a code sequence modifies no data registers
    and does not modify LR either. *)

Definition important_preg (r: preg) : bool :=
  match r with
  | IR GPR0 => false
  | PC => false    | CTR => false
  | CR0_0 => false | CR0_1 => false | CR0_2 => false | CR0_3 => false
  | CARRY => false
  | _ => true
  end.

Lemma important_diff:
  forall r r',
  important_preg r = true -> important_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Hint Resolve important_diff: asmgen.

Lemma important_data_preg_1:
  forall r, data_preg r = true -> important_preg r = true.    
Proof.
  destruct r; simpl; auto; discriminate.
Qed.

Lemma important_data_preg_2:
  forall r, important_preg r = false -> data_preg r = false.
Proof.
  intros. destruct (data_preg r) eqn:E; auto. apply important_data_preg_1 in E. congruence.
Qed.  

Hint Resolve important_data_preg_1 important_data_preg_2: asmgen.

Lemma nextinstr_inv2:
  forall r rs, important_preg r = true -> (nextinstr rs)#r = rs#r.
Proof.
  intros. apply nextinstr_inv. red; intro; subst; discriminate.
Qed.

(** Useful properties of the GPR0 registers. *)

Lemma gpr_or_zero_not_zero:
  forall rs r, r <> GPR0 -> gpr_or_zero rs r = rs#r.
Proof.
  intros. unfold gpr_or_zero. case (ireg_eq r GPR0); tauto.
Qed.
Lemma gpr_or_zero_zero:
  forall rs, gpr_or_zero rs GPR0 = Vzero.
Proof.
  intros. reflexivity.
Qed.
Hint Resolve gpr_or_zero_not_zero gpr_or_zero_zero: asmgen.

Lemma gpr_or_zero_l_not_zero:
  forall rs r, r <> GPR0 -> gpr_or_zero_l rs r = rs#r.
Proof.
  intros. unfold gpr_or_zero_l. case (ireg_eq r GPR0); tauto.
Qed.
Lemma gpr_or_zero_l_zero:
  forall rs, gpr_or_zero_l rs GPR0 = Vlong Int64.zero.
Proof.
  intros. reflexivity.
Qed.
Hint Resolve gpr_or_zero_l_not_zero gpr_or_zero_l_zero: asmgen.

Lemma ireg_of_not_GPR0:
  forall m r, ireg_of m = OK r -> IR r <> IR GPR0.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.
Hint Resolve ireg_of_not_GPR0: asmgen.

Lemma ireg_of_not_GPR0':
  forall m r, ireg_of m = OK r -> r <> GPR0.
Proof.
  intros. generalize (ireg_of_not_GPR0 _ _ H). congruence.
Qed.
Hint Resolve ireg_of_not_GPR0': asmgen.

(** Useful properties of the LR register *)

Lemma preg_of_not_LR:
  forall r, LR <> preg_of r.
Proof.
  intros. auto using not_eq_sym with asmgen.
Qed.

Lemma preg_notin_LR:
  forall rl, preg_notin LR rl.
Proof.
  intros. rewrite preg_notin_charact. intros. apply preg_of_not_LR. 
Qed.

Hint Resolve preg_of_not_LR preg_notin_LR: asmgen.
      
(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv2 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** Useful properties of pointer addition *)

Lemma loadv_offset_ptr:
  forall chunk m a delta v,
  Mem.loadv chunk m (Val.offset_ptr a delta) = Some v ->
  Mem.loadv chunk m (Val.add a (Vint (Ptrofs.to_int delta))) = Some v.
Proof.
  intros. destruct a; try discriminate H. simpl. rewrite Ptrofs.of_int_to_int by auto. assumption.
Qed.

Lemma storev_offset_ptr:
  forall chunk m a delta v m',
  Mem.storev chunk m (Val.offset_ptr a delta) v = Some m' ->
  Mem.storev chunk m (Val.add a (Vint (Ptrofs.to_int delta))) v = Some m'.
Proof.
  intros. destruct a; try discriminate H. simpl. rewrite Ptrofs.of_int_to_int by auto. assumption.
Qed.

(** * Correctness of PowerPC constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Properties of comparisons. *)

Lemma compare_float_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_float rs v1 v2) in
     rs1#CR0_0 = Val.cmpf Clt v1 v2
  /\ rs1#CR0_1 = Val.cmpf Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmpf Ceq v1 v2
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. unfold compare_float. Simpl.
Qed.

Lemma compare_sint_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_sint rs v1 v2) in
     rs1#CR0_0 = Val.cmp Clt v1 v2
  /\ rs1#CR0_1 = Val.cmp Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmp Ceq v1 v2
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. unfold compare_sint. Simpl.
Qed.

Lemma compare_uint_spec:
  forall rs m v1 v2,
  let rs1 := nextinstr (compare_uint rs m v1 v2) in
     rs1#CR0_0 = Val.cmpu (Mem.valid_pointer m) Clt v1 v2
  /\ rs1#CR0_1 = Val.cmpu (Mem.valid_pointer m) Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmpu (Mem.valid_pointer m) Ceq v1 v2
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. unfold compare_uint. Simpl.
Qed.

Lemma compare_slong_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_slong rs v1 v2) in
     rs1#CR0_0 = Val.of_optbool (Val.cmpl_bool Clt v1 v2)
  /\ rs1#CR0_1 = Val.of_optbool (Val.cmpl_bool Cgt v1 v2)
  /\ rs1#CR0_2 = Val.of_optbool (Val.cmpl_bool Ceq v1 v2)
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1. split. reflexivity. split. reflexivity. split. reflexivity.
  intros. unfold compare_slong. Simpl.
Qed.

Lemma compare_ulong_spec:
  forall rs m v1 v2,
  let rs1 := nextinstr (compare_ulong rs m v1 v2) in
     rs1#CR0_0 = Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Clt v1 v2)
  /\ rs1#CR0_1 = Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Cgt v1 v2)
  /\ rs1#CR0_2 = Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Ceq v1 v2)
  /\ forall r', r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 -> r' <> PC -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1. split. reflexivity. split. reflexivity. split. reflexivity.
  intros. unfold compare_ulong. Simpl.
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
  case (Int.eq (high_s n) Int.zero).
  (* addi *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  rewrite Int.add_zero_l. intuition Simpl.
  (* addis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  rewrite <- H. rewrite Int.add_commut. rewrite low_high_s.
  intuition Simpl.
  (* addis + ori *)
  econstructor; split. eapply exec_straight_two.
  simpl; eauto. simpl; eauto. auto. auto.
  split. Simpl. rewrite Int.add_zero_l. unfold Val.or. rewrite low_high_u. auto.
  intros; Simpl.
Qed.

(** Add integer immediate. *)

Lemma addimm_correct:
  forall r1 r2 n k rs m,
  r1 <> GPR0 ->
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (addimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm.
  (* addi *)
  case (Int.eq (high_s n) Int.zero).
  econstructor; split. apply exec_straight_one.
  simpl. rewrite gpr_or_zero_not_zero; eauto.
  reflexivity.
  intuition Simpl.
  (* addis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  econstructor; split. apply exec_straight_one.
  simpl. rewrite gpr_or_zero_not_zero; auto. auto.
  split. Simpl.
  generalize (low_high_s n). rewrite H1. rewrite Int.add_zero. congruence.
  intros; Simpl.
  (* addis + addi *)
  econstructor; split. eapply exec_straight_two.
  simpl. rewrite gpr_or_zero_not_zero; eauto.
  simpl. rewrite gpr_or_zero_not_zero; eauto.
  auto. auto.
  split. Simpl. rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
  intros; Simpl.
Qed.

(** And integer immediate. *)

Lemma andimm_base_correct:
  forall r1 r2 n k (rs : regset) m,
  r2 <> GPR0 ->
  let v := Val.and rs#r2 (Vint n) in
  exists rs',
     exec_straight ge fn (andimm_base r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ rs'#CR0_2 = Val.cmp Ceq v Vzero
  /\ forall r', important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm_base.
  case (Int.eq (high_u n) Int.zero).
  (* andi *)
  exists (nextinstr (compare_sint (rs#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. apply exec_straight_one. reflexivity. reflexivity.
  split. rewrite D; auto with asmgen. Simpl.
  split. auto.
  intros. rewrite D; auto with asmgen. Simpl.
  (* andis *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (compare_sint (rs#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H0. rewrite Int.or_zero.
  intro. rewrite H1. reflexivity. reflexivity.
  split. rewrite D; auto with asmgen. Simpl.
  split. auto.
  intros. rewrite D; auto with asmgen. Simpl.
  (* loadimm + and *)
  generalize (loadimm_correct GPR0 n (Pand_ r1 r2 GPR0 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  exists (nextinstr (compare_sint (rs1#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs1#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. rewrite RES1.
  rewrite (OTHER1 r2). reflexivity. congruence. congruence.
  reflexivity.
  split. rewrite D; auto with asmgen. Simpl.
  split. auto.
  intros. rewrite D; auto with asmgen. Simpl.
Qed.

Lemma andimm_correct:
  forall r1 r2 n k (rs : regset) m,
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (andimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.and rs#r2 (Vint n)
  /\ forall r', important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm. destruct (is_rlw_mask n).
  (* turned into rlw *)
  econstructor; split. eapply exec_straight_one.
  simpl. rewrite Val.rolm_zero. eauto. auto.
  intuition Simpl.
  (* andimm_base *)
  destruct (andimm_base_correct r1 r2 n k rs m) as [rs' [A [B [C D]]]]; auto.
  exists rs'; auto.
Qed.

(** Or integer immediate. *)

Lemma orimm_correct:
  forall r1 (r2: ireg) n k (rs : regset) m,
  let v := Val.or rs#r2 (Vint n) in
  exists rs',
     exec_straight ge fn (orimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold orimm.
  case (Int.eq (high_u n) Int.zero).
  (* ori *)
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. reflexivity. reflexivity.
  intuition Simpl.
  (* oris *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H. rewrite Int.or_zero.
  intro. rewrite H0. reflexivity. reflexivity.
  intuition Simpl.
  (* oris + ori *)
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  intuition Simpl.
  rewrite Val.or_assoc. simpl. rewrite low_high_u. reflexivity.
Qed.

(** Xor integer immediate. *)

Lemma xorimm_correct:
  forall r1 (r2: ireg) n k (rs : regset) m,
  let v := Val.xor rs#r2 (Vint n) in
  exists rs',
     exec_straight ge fn (xorimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold xorimm.
  case (Int.eq (high_u n) Int.zero).
  (* xori *)
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. reflexivity. reflexivity.
  intuition Simpl.
  (* xoris *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H. rewrite Int.or_zero.
  intro. rewrite H0. reflexivity. reflexivity.
  intuition Simpl.
  (* xoris + xori *)
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  intuition Simpl.
  rewrite Val.xor_assoc. simpl. rewrite low_high_u_xor. reflexivity.
Qed.

(** Rotate and mask. *)

Lemma rolm_correct:
  forall r1 r2 amount mask k (rs : regset) m,
  r1 <> GPR0 ->
  exists rs',
     exec_straight ge fn (rolm r1 r2 amount mask k) rs m  k rs' m
  /\ rs'#r1 = Val.rolm rs#r2 amount mask
  /\ forall r', important_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold rolm. destruct (is_rlw_mask mask).
  (* rlwinm *)
  econstructor; split. eapply exec_straight_one; simpl; eauto.
  intuition Simpl.
  (* rlwinm ; andimm *)
  set (rs1 := nextinstr (rs#r1 <- (Val.rolm rs#r2 amount Int.mone))).
  destruct (andimm_base_correct r1 r1 mask k rs1 m) as [rs' [A [B [C D]]]]; auto.
  exists rs'.
  split. eapply exec_straight_step; eauto. auto. auto.
  split. rewrite B. unfold rs1. rewrite nextinstr_inv; auto with asmgen.
  rewrite Pregmap.gss. destruct (rs r2); simpl; auto.
  unfold Int.rolm. rewrite Int.and_assoc.
  decEq; decEq; decEq. rewrite Int.and_commut. apply Int.and_mone.
  intros. rewrite D; auto. unfold rs1; Simpl.
Qed.

(** Load int64 constant. *)

Lemma loadimm64_correct:
  forall r n k rs m,
  exists rs',
     exec_straight ge fn (loadimm64 r n k) rs m  k rs' m
  /\ rs'#r = Vlong n
  /\ forall r': preg, r' <> r -> r' <> GPR12 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm64.
  set (hi_s := Int64.sign_ext 16 (Int64.shr n (Int64.repr 16))).
  set (hi' := Int64.shl hi_s (Int64.repr 16)).
  destruct (Int64.eq n (low64_s n)).
  (* addi *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  rewrite Int64.add_zero_l. intuition Simpl.
  (* addis + ori *)
  predSpec Int64.eq Int64.eq_spec n (Int64.or hi' (low64_u n)).
  econstructor; split. eapply exec_straight_two. simpl; eauto. simpl; eauto. auto. auto.
  split. Simpl. rewrite Int64.add_zero_l. simpl; f_equal; auto.
  intros. Simpl.
  (* ldi *)
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  intuition Simpl.
Qed.

(** Add int64 immediate. *)

Lemma addimm64_correct:
  forall r1 r2 n k rs m,
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (addimm64 r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.addl rs#r2 (Vlong n)
  /\ forall r': preg, r' <> r1 -> r' <> GPR0 -> r' <> GPR12 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm64, opimm64. destruct (Int64.eq n (low64_s n)); [|destruct (ireg_eq r2 GPR12)].
- (* addi *)
  econstructor; split. apply exec_straight_one.
  simpl. rewrite gpr_or_zero_l_not_zero; eauto.
  reflexivity.
  intuition Simpl.
- (* move-loadimm-add *)
  subst r2.
  edestruct (loadimm64_correct GPR12 n) as (rs2 & A & B & C).
  econstructor; split. eapply exec_straight_step. simpl; reflexivity. auto.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; reflexivity. auto.
  split. rewrite B, C by eauto with asmgen. Simpl.
  intros. Simpl. rewrite C by auto. Simpl.
- (* loadimm-add *)
  edestruct (loadimm64_correct GPR0 n) as (rs2 & A & B & C).
  econstructor; split. eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; reflexivity. auto.
  split. rewrite B, C by eauto with asmgen. Simpl.
  intros. Simpl.
Qed.

(** Or int64 immediate. *)

Lemma orimm64_correct:
  forall r1 r2 n k rs m,
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (orimm64 r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.orl rs#r2 (Vlong n)
  /\ forall r': preg, r' <> r1 -> r' <> GPR0 -> r' <> GPR12 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold orimm64, opimm64. destruct (Int64.eq n (low64_u n)); [|destruct (ireg_eq r2 GPR12)].
- (* ori *)
  econstructor; split. apply exec_straight_one. simpl; eauto. reflexivity.
  intuition Simpl.
- (* move-loadimm-or *)
  subst r2.
  edestruct (loadimm64_correct GPR12 n) as (rs2 & A & B & C).
  econstructor; split. eapply exec_straight_step. simpl; reflexivity. auto.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; reflexivity. auto.
  split. rewrite B, C by eauto with asmgen. Simpl.
  intros. Simpl. rewrite C by auto. Simpl.
- (* loadimm-or *)
  edestruct (loadimm64_correct GPR0 n) as (rs2 & A & B & C).
  econstructor; split. eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; reflexivity. auto.
  split. rewrite B, C by eauto with asmgen. Simpl.
  intros. Simpl.
Qed.

(** Xor int64 immediate. *)

Lemma xorimm64_correct:
  forall r1 r2 n k rs m,
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (xorimm64 r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.xorl rs#r2 (Vlong n)
  /\ forall r': preg, r' <> r1 -> r' <> GPR0 -> r' <> GPR12 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold xorimm64, opimm64. destruct (Int64.eq n (low64_u n)); [|destruct (ireg_eq r2 GPR12)].
- (* xori *)
  econstructor; split. apply exec_straight_one. simpl; eauto. reflexivity.
  intuition Simpl.
- (* move-loadimm-xor *)
  subst r2.
  edestruct (loadimm64_correct GPR12 n) as (rs2 & A & B & C).
  econstructor; split. eapply exec_straight_step. simpl; reflexivity. auto.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; reflexivity. auto.
  split. rewrite B, C by eauto with asmgen. Simpl.
  intros. Simpl. rewrite C by auto. Simpl.
- (* loadimm-xor *)
  edestruct (loadimm64_correct GPR0 n) as (rs2 & A & B & C).
  econstructor; split. eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; reflexivity. auto.
  split. rewrite B, C by eauto with asmgen. Simpl.
  intros. Simpl.
Qed.

(** And int64 immediate. *)

Lemma andimm64_base_correct:
  forall r1 r2 n k rs m,
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (andimm64_base r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.andl rs#r2 (Vlong n)
  /\ forall r': preg, r' <> r1 -> r' <> GPR12 -> important_preg r' = true  -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm64_base, opimm64. destruct (Int64.eq n (low64_u n)); [|destruct (ireg_eq r2 GPR12)].
- (* andi *)
  econstructor; split. apply exec_straight_one. simpl; eauto. reflexivity.
  unfold compare_slong; intuition Simpl.
- (* move-loadimm-and *)
  subst r2.
  edestruct (loadimm64_correct GPR12 n) as (rs2 & A & B & C).
  econstructor; split. eapply exec_straight_step. simpl; reflexivity. auto.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; reflexivity. auto.
  split. rewrite B, C by eauto with asmgen. unfold compare_slong; Simpl.
  intros. unfold compare_slong; Simpl. rewrite C by auto with asmgen. Simpl.
- (* loadimm-xor *)
  edestruct (loadimm64_correct GPR0 n) as (rs2 & A & B & C).
  econstructor; split. eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; reflexivity. auto.
  split. rewrite B, C by eauto with asmgen. unfold compare_slong; Simpl.
  intros. unfold compare_slong; Simpl.
Qed.

Lemma andimm64_correct:
  forall r1 r2 n k rs m,
  r2 <> GPR0 ->
  exists rs',
     exec_straight ge fn (andimm64 r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.andl rs#r2 (Vlong n)
  /\ forall r': preg, r' <> r1 -> r' <> GPR12 -> important_preg r' = true  -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm64. destruct (is_rldl_mask n || is_rldr_mask n).
- econstructor; split. eapply exec_straight_one. simpl; reflexivity. reflexivity.
  split. Simpl. destruct (rs r2); simpl; auto. rewrite Int64.rolm_zero. auto.
  intros; Simpl.
- apply andimm64_base_correct; auto.
Qed.

(** Rotate-and-mask for int64 *)

Lemma rolm64_correct:
  forall r1 r2 amount mask k rs m,
  r1 <> GPR0 ->
  exists rs',
     exec_straight ge fn (rolm64 r1 r2 amount mask k) rs m  k rs' m
  /\ rs'#r1 = Val.rolml rs#r2 amount mask
  /\ forall r': preg, r' <> r1 -> r' <> GPR12 -> important_preg r' = true  -> rs'#r' = rs#r'.
Proof.
  intros. unfold rolm64.
  destruct (is_rldl_mask mask || is_rldr_mask mask || is_rldl_mask (Int64.shru' mask amount)).
- econstructor; split. eapply exec_straight_one. simpl; reflexivity. reflexivity.
  intuition Simpl.
- edestruct (andimm64_base_correct r1 r1 mask k) as (rs2 & A & B & C); auto.
  econstructor; split.
  eapply exec_straight_step. simpl; reflexivity. reflexivity. eexact A.
  split. rewrite B. Simpl. destruct (rs r2); simpl; auto. unfold Int64.rolm.
  rewrite Int64.and_assoc, Int64.and_mone_l; auto.
  intros; Simpl. rewrite C by auto. Simpl.
Qed.

(** Indexed memory loads. *)

Lemma accessind_load_correct:
  forall (A: Type) (inj: A -> preg)
       (instr1: A -> constant -> ireg -> instruction)
       (instr2: A -> ireg -> ireg -> instruction)
       (base: ireg) ofs rx chunk v (rs: regset) m k,
  (forall rs m r1 cst r2,
   exec_instr ge fn (instr1 r1 cst r2) rs m = load1 ge chunk (inj r1) cst r2 rs m) ->
  (forall rs m r1 r2 r3,
   exec_instr ge fn (instr2 r1 r2 r3) rs m = load2 chunk (inj r1) r2 r3 rs m) ->
  Mem.loadv chunk m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> GPR0 -> inj rx <> PC ->
  exists rs',
     exec_straight ge fn (accessind instr1 instr2 base ofs rx k) rs m k rs' m
  /\ rs'#(inj rx) = v
  /\ forall r, r <> PC -> r <> inj rx -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  intros. unfold accessind. set (ofs' := Ptrofs.to_int ofs) in *.
  assert (LD: Mem.loadv chunk m (Val.add (rs base) (Vint ofs')) = Some v)
  by (apply loadv_offset_ptr; auto).
  destruct (Int.eq (high_s ofs') Int.zero).
- econstructor; split. apply exec_straight_one.
  rewrite H. unfold load1. rewrite gpr_or_zero_not_zero by auto. simpl.
  rewrite LD. eauto. unfold nextinstr. repeat Simplif.
  split. unfold nextinstr. repeat Simplif.
  intros. repeat Simplif.
- exploit (loadimm_correct GPR0 ofs'); eauto. intros [rs' [P [Q R]]].
  econstructor; split. eapply exec_straight_trans. eexact P.
  apply exec_straight_one. rewrite H0. unfold load2.
  rewrite gpr_or_zero_not_zero by auto. simpl.
  rewrite Q, R by auto with asmgen.
  rewrite LD. reflexivity. unfold nextinstr. repeat Simplif.
  split. repeat Simplif.
  intros. repeat Simplif.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) m v c,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  base <> GPR0 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> preg_of dst -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); inv H; simpl in H0.
  apply accessind_load_correct with (inj := IR) (chunk := Mint32); auto with asmgen.
  apply accessind_load_correct with (inj := FR) (chunk := Mfloat64); auto with asmgen.
  apply accessind_load_correct with (inj := IR) (chunk := Mint64); auto with asmgen.
  apply accessind_load_correct with (inj := FR) (chunk := Mfloat32); auto with asmgen.
  apply accessind_load_correct with (inj := IR) (chunk := Many32); auto with asmgen.
  apply accessind_load_correct with (inj := IR) (chunk := Many64); auto with asmgen.
  apply accessind_load_correct with (inj := FR) (chunk := Many64); auto with asmgen.
Qed.

(** Indexed memory stores. *)

Lemma accessind_store_correct:
  forall (A: Type) (inj: A -> preg)
       (instr1: A -> constant -> ireg -> instruction)
       (instr2: A -> ireg -> ireg -> instruction)
       (base: ireg) ofs rx chunk (rs: regset) m m' k,
  (forall rs m r1 cst r2,
   exec_instr ge fn (instr1 r1 cst r2) rs m = store1 ge chunk (inj r1) cst r2 rs m) ->
  (forall rs m r1 r2 r3,
   exec_instr ge fn (instr2 r1 r2 r3) rs m = store2 chunk (inj r1) r2 r3 rs m) ->
  Mem.storev chunk m (Val.offset_ptr rs#base ofs) (rs (inj rx)) = Some m' ->
  base <> GPR0 -> inj rx <> PC -> inj rx <> GPR0 ->
  exists rs',
     exec_straight ge fn (accessind instr1 instr2 base ofs rx k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  intros. unfold accessind. set (ofs' := Ptrofs.to_int ofs) in *.
  assert (ST: Mem.storev chunk m (Val.add (rs base) (Vint ofs')) (rs (inj rx)) = Some m')
  by (apply storev_offset_ptr; auto).
  destruct (Int.eq (high_s ofs') Int.zero).
- econstructor; split. apply exec_straight_one.
  rewrite H. unfold store1. rewrite gpr_or_zero_not_zero by auto. simpl.
  rewrite ST. eauto. unfold nextinstr. repeat Simplif.
  intros. repeat Simplif.
- exploit (loadimm_correct GPR0 ofs'); eauto. intros [rs' [P [Q R]]].
  econstructor; split. eapply exec_straight_trans. eexact P.
  apply exec_straight_one. rewrite H0. unfold store2.
  rewrite gpr_or_zero_not_zero by auto.
  rewrite Q. rewrite R by auto with asmgen. rewrite R by auto.
  rewrite ST. reflexivity. unfold nextinstr. repeat Simplif.
  intros. repeat Simplif.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) m m' c,
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) (rs#(preg_of src)) = Some m' ->
  base <> GPR0 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  unfold storeind; intros.
  assert (preg_of src <> GPR0) by auto with asmgen.
  destruct ty; try discriminate; destruct (preg_of src) ; inv H; simpl in H0.
  apply accessind_store_correct with (inj := IR) (chunk := Mint32); auto with asmgen.
  apply accessind_store_correct with (inj := FR) (chunk := Mfloat64); auto with asmgen.
  apply accessind_store_correct with (inj := IR) (chunk := Mint64); auto with asmgen.
  apply accessind_store_correct with (inj := FR) (chunk := Mfloat32); auto with asmgen.
  apply accessind_store_correct with (inj := IR) (chunk := Many32); auto with asmgen.
  apply accessind_store_correct with (inj := IR) (chunk := Many64); auto with asmgen.
  apply accessind_store_correct with (inj := FR) (chunk := Many64); auto with asmgen.
Qed.

(** Float comparisons. *)

Lemma floatcomp_correct:
  forall cmp (r1 r2: freg) k rs m,
  exists rs',
     exec_straight ge fn (floatcomp cmp r1 r2 k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_fcmp cmp))) =
       (if snd (crbit_for_fcmp cmp)
        then Val.cmpf cmp rs#r1 rs#r2
        else Val.notbool (Val.cmpf cmp rs#r1 rs#r2))
  /\ forall r',
       r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> rs'#r' = rs#r'.
Proof.
  intros.
  generalize (compare_float_spec rs rs#r1 rs#r2).
  intros [A [B [C D]]].
  set (rs1 := nextinstr (compare_float rs rs#r1 rs#r2)) in *.
  assert ((cmp = Ceq \/ cmp = Cne \/ cmp = Clt \/ cmp = Cgt)
          \/ (cmp = Cle \/ cmp = Cge)).
    case cmp; tauto.
  unfold floatcomp.  elim H; intro; clear H.
  exists rs1.
  split. destruct H0 as [EQ|[EQ|[EQ|EQ]]]; subst cmp;
  apply exec_straight_one; reflexivity.
  split.
  destruct H0 as [EQ|[EQ|[EQ|EQ]]]; subst cmp; simpl; auto.
  rewrite Val.negate_cmpf_eq. auto.
  auto.
  (* two instrs *)
  exists (nextinstr (rs1#CR0_3 <- (Val.cmpf cmp rs#r1 rs#r2))).
  split. elim H0; intro; subst cmp.
  apply exec_straight_two with rs1 m.
  reflexivity. simpl.
  rewrite C; rewrite A. rewrite Val.or_commut. rewrite <- Val.cmpf_le.
  reflexivity. reflexivity. reflexivity.
  apply exec_straight_two with rs1 m.
  reflexivity. simpl.
  rewrite C; rewrite B. rewrite Val.or_commut. rewrite <- Val.cmpf_ge.
  reflexivity. reflexivity. reflexivity.
  split. elim H0; intro; subst cmp; simpl.
  reflexivity.
  reflexivity.
  intros. Simpl.
Qed.

(** Translation of conditions. *)

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

Lemma transl_cond_correct_1:
  forall cond args k rs m c,
  transl_cond cond args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) =
       (if snd (crbit_for_cond cond)
        then Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)
        else Val.notbool (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)))
  /\ forall r, important_preg r = true  -> preg_notin r (destroyed_by_cond cond) ->  rs'#r = rs#r.
Proof.
  intros.
Opaque Int.eq.
  unfold transl_cond in H; destruct cond; ArgsInv; simpl.
  (* Ccomp *)
  fold (Val.cmp c0 (rs x) (rs x0)).
  destruct (compare_sint_spec rs (rs x) (rs x0)) as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split.
  case c0; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  auto with asmgen.
  (* Ccompu *)
  fold (Val.cmpu (Mem.valid_pointer m) c0 (rs x) (rs x0)).
  destruct (compare_uint_spec rs m (rs x) (rs x0)) as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split.
  case c0; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  auto with asmgen.
  (* Ccompimm *)
  fold (Val.cmp c0 (rs x) (Vint i)).
  destruct (Int.eq (high_s i) Int.zero); inv EQ0.
  destruct (compare_sint_spec rs (rs x) (Vint i)) as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split.
  case c0; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  auto with asmgen.
  destruct (loadimm_correct GPR0 i (Pcmpw x GPR0 :: k) rs m) as [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_sint_spec rs1 (rs x) (Vint i)) as [A [B [C D]]].
  assert (SAME: rs1 x = rs x) by (apply OTH1; eauto with asmgen).
  exists (nextinstr (compare_sint rs1 (rs1 x) (Vint i))).
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. rewrite RES1; rewrite SAME; auto.
  reflexivity.
  split. rewrite SAME.
  case c0; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  intros. rewrite SAME; rewrite D; auto with asmgen.
  (* Ccompuimm *)
  fold (Val.cmpu (Mem.valid_pointer m) c0 (rs x) (Vint i)).
  destruct (Int.eq (high_u i) Int.zero); inv EQ0.
  destruct (compare_uint_spec rs m (rs x) (Vint i)) as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split.
  case c0; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  auto with asmgen.
  destruct (loadimm_correct GPR0 i (Pcmplw x GPR0 :: k) rs m) as [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_uint_spec rs1 m (rs x) (Vint i)) as [A [B [C D]]].
  assert (SAME: rs1 x = rs x) by (apply OTH1; eauto with asmgen).
  exists (nextinstr (compare_uint rs1 m (rs1 x) (Vint i))).
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. rewrite RES1; rewrite SAME; auto.
  reflexivity.
  split. rewrite SAME.
  case c0; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  intros. rewrite SAME; rewrite D; auto with asmgen.
  (* Ccompf *)
  fold (Val.cmpf c0 (rs x) (rs x0)).
  destruct (floatcomp_correct c0 x x0 k rs m) as [rs' [EX [RES OTH]]].
  exists rs'. split. auto.
  split. apply RES.
  auto with asmgen.
  (* Cnotcompf *)
  rewrite Val.notbool_negb_3. rewrite Val.notbool_idem4.
  fold (Val.cmpf c0 (rs x) (rs x0)).
  destruct (floatcomp_correct c0 x x0 k rs m) as [rs' [EX [RES OTH]]].
  exists rs'. split. auto.
  split. rewrite RES. destruct (snd (crbit_for_fcmp c0)); auto.
  auto with asmgen.
  (* Cmaskzero *)
  destruct (andimm_base_correct GPR0 x i k rs m) as [rs' [A [B [C D]]]].
  eauto with asmgen.
  exists rs'. split. assumption.
  split. rewrite C. destruct (rs x); auto.
  auto with asmgen.
  (* Cmasknotzero *)
  destruct (andimm_base_correct GPR0 x i k rs m) as [rs' [A [B [C D]]]].
  eauto with asmgen.
  exists rs'. split. assumption.
  split. rewrite C. destruct (rs x); auto.
  fold (option_map negb (Some (Int.eq (Int.and i0 i) Int.zero))).
  rewrite Val.notbool_negb_3. rewrite Val.notbool_idem4. auto.
  auto with asmgen.
- (* Ccompl *)
  destruct (compare_slong_spec rs (rs x) (rs x0)) as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  rewrite <- Val.notbool_negb_3. rewrite <- Val.negate_cmpl_bool.
  split. case c0; simpl; auto.
  auto with asmgen.
- (* Ccomplu *)
  destruct (compare_ulong_spec rs m (rs x) (rs x0)) as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  rewrite <- Val.notbool_negb_3. rewrite <- Val.negate_cmplu_bool.
  split. case c0; simpl; auto.
  auto with asmgen.
- (* Ccomplimm *)
  rewrite <- Val.notbool_negb_3. rewrite <- Val.negate_cmpl_bool.
  destruct (Int64.eq i (low64_s i)); [|destruct (ireg_eq x GPR12)]; inv EQ0.
+ destruct (compare_slong_spec rs (rs x) (Vlong i)) as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split. case c0; simpl; auto. auto with asmgen.
+ destruct (loadimm64_correct GPR12 i (Pcmpd GPR0 GPR12 :: k) (nextinstr (rs#GPR0 <- (rs#GPR12))) m) as [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_slong_spec rs1 (rs GPR12) (Vlong i)) as [A [B [C D]]].
  assert (SAME: rs1 GPR0 = rs GPR12) by (apply OTH1; eauto with asmgen).
  econstructor; split.
  eapply exec_straight_step. simpl;reflexivity. reflexivity.
  eapply exec_straight_trans. eexact EX1. eapply exec_straight_one. simpl;reflexivity. reflexivity.
  split. rewrite RES1, SAME. destruct c0; simpl; auto.
  simpl; intros. rewrite RES1, SAME. rewrite D by eauto with asmgen. rewrite OTH1 by eauto with asmgen. Simpl.
+ destruct (loadimm64_correct GPR0 i (Pcmpd x GPR0 :: k) rs m) as [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_slong_spec rs1 (rs x) (Vlong i)) as [A [B [C D]]].
  assert (SAME: rs1 x = rs x) by (apply OTH1; eauto with asmgen).
  econstructor; split.
  eapply exec_straight_trans. eexact EX1. eapply exec_straight_one. simpl;reflexivity. reflexivity.
  split. rewrite RES1, SAME. destruct c0; simpl; auto.
  simpl; intros. rewrite RES1, SAME. rewrite D; eauto with asmgen.
- (* Ccompluimm *)
  rewrite <- Val.notbool_negb_3. rewrite <- Val.negate_cmplu_bool.
  destruct (Int64.eq i (low64_u i)); [|destruct (ireg_eq x GPR12)]; inv EQ0.
+ destruct (compare_ulong_spec rs m (rs x) (Vlong i)) as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split. case c0; simpl; auto. auto with asmgen.
+ destruct (loadimm64_correct GPR12 i (Pcmpld GPR0 GPR12 :: k) (nextinstr (rs#GPR0 <- (rs#GPR12))) m) as [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_ulong_spec rs1 m (rs GPR12) (Vlong i)) as [A [B [C D]]].
  assert (SAME: rs1 GPR0 = rs GPR12) by (apply OTH1; eauto with asmgen).
  econstructor; split.
  eapply exec_straight_step. simpl;reflexivity. reflexivity.
  eapply exec_straight_trans. eexact EX1. eapply exec_straight_one. simpl;reflexivity. reflexivity.
  split. rewrite RES1, SAME. destruct c0; simpl; auto.
  simpl; intros. rewrite RES1, SAME. rewrite D by eauto with asmgen. rewrite OTH1 by eauto with asmgen. Simpl.
+ destruct (loadimm64_correct GPR0 i (Pcmpld x GPR0 :: k) rs m) as [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_ulong_spec rs1 m (rs x) (Vlong i)) as [A [B [C D]]].
  assert (SAME: rs1 x = rs x) by (apply OTH1; eauto with asmgen).
  econstructor; split.
  eapply exec_straight_trans. eexact EX1. eapply exec_straight_one. simpl;reflexivity. reflexivity.
  split. rewrite RES1, SAME. destruct c0; simpl; auto.
  simpl; intros. rewrite RES1, SAME. rewrite D; eauto with asmgen.
Qed.

Lemma transl_cond_correct_2:
  forall cond args k rs m b c,
  transl_cond cond args k = OK c ->
  eval_condition cond (map rs (map preg_of args)) m = Some b ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) =
       (if snd (crbit_for_cond cond)
        then Val.of_bool b
        else Val.notbool (Val.of_bool b))
  /\ forall r, important_preg r = true -> preg_notin r (destroyed_by_cond cond)  -> rs'#r = rs#r.
Proof.
  intros.
  replace (Val.of_bool b)
  with (Val.of_optbool (eval_condition cond rs ## (preg_of ## args) m)).
  eapply transl_cond_correct_1; eauto.
  rewrite H0; auto.
Qed.

Lemma transl_cond_correct_3:
  forall cond args k ms sp rs m b m' c,
  transl_cond cond args k = OK c ->
  agree ms sp rs ->
  eval_condition cond (map ms args) m = Some b ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) =
       (if snd (crbit_for_cond cond)
        then Val.of_bool b
        else Val.notbool (Val.of_bool b))
  /\ agree (Mach.undef_regs (destroyed_by_cond cond) ms) sp rs'.
Proof.
  intros.
  exploit transl_cond_correct_2. eauto.
    eapply eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto.
  intros [rs' [A [B C]]].
  exists rs'; split. eauto. split. auto. apply agree_undef_regs with rs; auto. intros r D.
  apply C. apply important_data_preg_1; auto.
Qed.

(** Translation of condition operators *)

Remark add_carry_eq0:
  forall i,
  Vint (Int.add (Int.add (Int.sub Int.zero i) i)
                (Int.add_carry Int.zero (Int.xor i Int.mone) Int.one)) =
  Val.of_bool (Int.eq i Int.zero).
Proof.
  intros. rewrite <- Int.sub_add_l. rewrite Int.add_zero_l.
  rewrite Int.sub_idem. rewrite Int.add_zero_l. fold (Int.not i).
  predSpec Int.eq Int.eq_spec i Int.zero.
  subst i. reflexivity.
  unfold Val.of_bool, Vfalse. decEq.
  unfold Int.add_carry. rewrite Int.unsigned_zero. rewrite Int.unsigned_one.
  apply zlt_true.
  generalize (Int.unsigned_range (Int.not i)); intro.
  assert (Int.unsigned (Int.not i) <> Int.modulus - 1).
    red; intros.
    assert (Int.repr (Int.unsigned (Int.not i)) = Int.mone).
Local Transparent Int.repr.
      rewrite H1. apply Int.mkint_eq. reflexivity.
   rewrite Int.repr_unsigned in H2.
   assert (Int.not (Int.not i) = Int.zero).
   rewrite H2. apply Int.mkint_eq; reflexivity.
  rewrite Int.not_involutive in H3.
  congruence.
  omega.
Qed.

Remark add_carry_ne0:
  forall i,
  Vint (Int.add (Int.add i (Int.xor (Int.add i Int.mone) Int.mone))
                (Int.add_carry i Int.mone Int.zero)) =
  Val.of_bool (negb (Int.eq i Int.zero)).
Proof.
  intros. fold (Int.not (Int.add i Int.mone)). rewrite Int.not_neg.
  rewrite (Int.add_commut  (Int.neg (Int.add i Int.mone))).
  rewrite <- Int.sub_add_opp. rewrite Int.sub_add_r. rewrite Int.sub_idem.
  rewrite Int.add_zero_l. rewrite Int.add_neg_zero. rewrite Int.add_zero_l.
Transparent Int.eq.
  unfold Int.add_carry, Int.eq.
  rewrite Int.unsigned_zero.  rewrite Int.unsigned_mone.
  unfold negb, Val.of_bool, Vtrue, Vfalse.
  destruct (zeq (Int.unsigned i) 0); decEq.
  apply zlt_true. omega.
  apply zlt_false. generalize (Int.unsigned_range i). omega.
Qed.

Lemma transl_cond_op_correct:
  forall cond args r k rs m c,
  transl_cond_op cond args r k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of r) = Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)
  /\ forall r', important_preg r' = true -> preg_notin r' (destroyed_by_cond cond) ->  r' <> preg_of r -> rs'#r' = rs#r'.
Proof.
  intros until args. unfold transl_cond_op.
  destruct (classify_condition cond args); intros; monadInv H; simpl;
  erewrite ! ireg_of_eq; eauto.
(* eq 0 *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. destruct (rs x0); simpl; auto.
  apply add_carry_eq0.
  intros; Simpl.
(* ne 0 *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  rewrite gpr_or_zero_not_zero; eauto with asmgen.
  split. Simpl. destruct (rs x0); simpl; auto.
  apply add_carry_ne0.
  intros; Simpl.
(* ge 0 *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. rewrite Val.rolm_ge_zero. auto.
  intros; Simpl.
(* lt 0 *)
  econstructor; split.
  apply exec_straight_one; simpl; reflexivity.
  split. Simpl. rewrite Val.rolm_lt_zero. auto.
  intros; Simpl.
(* default *)
  set (bit := fst (crbit_for_cond c)) in *.
  set (isset := snd (crbit_for_cond c)) in *.
  set (k1 :=
        Pmfcrbit x bit ::
        (if isset
         then k
         else Pxori x x (Cint Int.one) :: k)).
  generalize (transl_cond_correct_1 c rl k1 rs m c0 EQ0).
  fold bit; fold isset.
  intros [rs1 [EX1 [RES1 AG1]]].
  destruct isset.
  (* bit set *)
  econstructor; split.  eapply exec_straight_trans. eexact EX1.
  unfold k1. apply exec_straight_one; simpl; reflexivity.
  intuition Simpl.
  (* bit clear *)
  econstructor; split.  eapply exec_straight_trans. eexact EX1.
  unfold k1. eapply exec_straight_two; simpl; reflexivity.
  intuition Simpl.
  rewrite RES1. destruct (eval_condition c rs ## (preg_of ## rl) m). destruct b; auto. auto.
Qed.

(** Translation of arithmetic operations. *)

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; [ apply Val.lessdef_same; Simpl; fail | intros; Simpl; fail ] ].

Lemma transl_op_correct_aux:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#GPR1) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, important_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  assert (SAME: forall v1 v2, v1 = v2 -> Val.lessdef v2 v1). { intros; subst; auto. }
Opaque Int.eq.
  intros. unfold transl_op in H; destruct op; ArgsInv; simpl in H0; try (inv H0); try TranslOpSimpl.
- (* Omove *)
  destruct (preg_of res) eqn:RES; destruct (preg_of m0) eqn:ARG; inv H.
  TranslOpSimpl.
  TranslOpSimpl.
- (* Ointconst *)
  destruct (loadimm_correct x i k rs m) as [rs' [A [B C]]].
  exists rs'. rewrite B. auto with asmgen.
- (* Oaddrsymbol *)
  set (v' := Genv.symbol_address ge i i0).
  destruct (symbol_is_small_data i i0) eqn:SD; [ | destruct (symbol_is_rel_data i i0) ].
+ (* small data *)
Opaque Val.add.
  econstructor; split. apply exec_straight_one; simpl; reflexivity.
  split. apply SAME. Simpl. rewrite small_data_area_addressing by auto. apply add_zero_symbol_address.
  intros; Simpl.
+ (* relative data *)
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  split. apply SAME. Simpl. rewrite gpr_or_zero_not_zero by eauto with asmgen. Simpl.
  apply low_high_half_zero.
  intros; Simpl.
+ (* absolute data *)
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  split. apply SAME. Simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen. Simpl.
  apply low_high_half_zero.
  intros; Simpl.
- (* Oaddrstack *)
  destruct (addimm_correct x GPR1 (Ptrofs.to_int i) k rs m) as [rs' [EX [RES OTH]]]; eauto with asmgen.
  exists rs'; split. auto. split; auto with asmgen.
  rewrite RES. destruct (rs GPR1); simpl; auto.
Transparent Val.add.
  simpl. rewrite Ptrofs.of_int_to_int; auto.
Opaque Val.add.
- (* Oaddimm *)
  destruct (addimm_correct x0 x i k rs m) as [rs' [A [B C]]]; eauto with asmgen.
  exists rs'; auto with asmgen.
- (* Oaddsymbol *)
  destruct (symbol_is_small_data i i0) eqn:SD; [ | destruct (symbol_is_rel_data i i0) ].
+ (* small data *)
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  split. apply SAME. Simpl. rewrite (Val.add_commut (rs x)). f_equal.
  rewrite small_data_area_addressing by auto. apply add_zero_symbol_address.
  intros; Simpl.
+ (* relative data *)
  econstructor; split. eapply exec_straight_trans.
  eapply exec_straight_two; simpl; reflexivity.
  eapply exec_straight_two; simpl; reflexivity.
  split. assert (GPR0 <> x0) by (apply not_eq_sym; eauto with asmgen).
  Simpl. rewrite ! gpr_or_zero_zero. rewrite ! gpr_or_zero_not_zero by eauto with asmgen. Simpl.
  rewrite low_high_half_zero. auto.
  intros; Simpl.
+ (* absolute data *)
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. rewrite ! gpr_or_zero_not_zero by (eauto with asmgen). Simpl.
  rewrite Val.add_assoc. rewrite (Val.add_commut (rs x)). rewrite low_high_half. auto.
  intros; Simpl.
- (* Osubimm *)
  case (Int.eq (high_s i) Int.zero).
  TranslOpSimpl.
  destruct (loadimm_correct GPR0 i (Psubfc x0 x GPR0 :: k) rs m) as [rs1 [EX [RES OTH]]].
  econstructor; split.
  eapply exec_straight_trans. eexact EX. apply exec_straight_one; simpl; reflexivity.
  split. Simpl. rewrite RES. rewrite OTH; eauto with asmgen.
  intros; Simpl.
- (* Omulimm *)
  case (Int.eq (high_s i) Int.zero).
  TranslOpSimpl.
  destruct (loadimm_correct GPR0 i (Pmullw x0 x GPR0 :: k) rs m) as [rs1 [EX [RES OTH]]].
  econstructor; split.
  eapply exec_straight_trans. eexact EX. apply exec_straight_one; simpl; reflexivity.
  split. Simpl. rewrite RES. rewrite OTH; eauto with asmgen.
  intros; Simpl.
- (* Odivs *)
  replace v with (Val.maketotal (Val.divs (rs x) (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Odivu *)
  replace v with (Val.maketotal (Val.divu (rs x) (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Oand *)
  set (v' := Val.and (rs x) (rs x0)) in *.
  pose (rs1 := rs#x1 <- v').
  destruct (compare_sint_spec rs1 v' Vzero) as [A [B [C D]]].
  econstructor; split. apply exec_straight_one; simpl; reflexivity.
  split. rewrite D; auto with asmgen. unfold rs1; Simpl.
  intros. rewrite D; auto with asmgen. unfold rs1; Simpl.
- (* Oandimm *)
  destruct (andimm_correct x0 x i k rs m) as [rs' [A [B C]]]. eauto with asmgen.
  exists rs'; auto with asmgen.
- (* Oorimm *)
  destruct (orimm_correct x0 x i k rs m) as [rs' [A [B C]]].
  exists rs'; auto with asmgen.
- (* Oxorimm *)
  destruct (xorimm_correct x0 x i k rs m) as [rs' [A [B C]]].
  exists rs'; auto with asmgen.
- (* Onor *)
  replace (Val.notint (rs x))
     with (Val.notint (Val.or (rs x) (rs x))).
  TranslOpSimpl.
  destruct (rs x); simpl; auto. rewrite Int.or_idem. auto.
- (* Oshrximm *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. apply SAME. apply Val.shrx_carry. auto.
  intros; Simpl.
- (* Orolm *)
  destruct (rolm_correct x0 x i i0 k rs m) as [rs' [A [B C]]]. eauto with asmgen.
  exists rs'; auto.
- (* Olongconst *)
  destruct (loadimm64_correct x i k rs m) as [rs' [A [B C]]].
  exists rs'; auto with asmgen.
- (* Oaddlimm *)
  destruct (addimm64_correct x0 x i k rs m) as [rs' [A [B C]]]. eauto with asmgen.
  exists rs'; auto with asmgen.
- (* Odivl *)
  replace v with (Val.maketotal (Val.divls (rs x) (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Odivlu *)
  replace v with (Val.maketotal (Val.divlu (rs x) (rs x0))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Oandl *)
  set (v' := Val.andl (rs x) (rs x0)) in *.
  pose (rs1 := rs#x1 <- v').
  destruct (compare_slong_spec rs1 v' (Vlong Int64.zero)) as [A [B [C D]]].
  econstructor; split. apply exec_straight_one; simpl; reflexivity.
  split. rewrite D; auto with asmgen. unfold rs1; Simpl.
  intros. rewrite D; auto with asmgen. unfold rs1; Simpl.
- (* Oandlimm *)
  destruct (andimm64_correct x0 x i k rs m) as [rs' [A [B C]]]. eauto with asmgen.
  exists rs'; auto with asmgen.
- (* Oorlimm *)
  destruct (orimm64_correct x0 x i k rs m) as [rs' [A [B C]]]. eauto with asmgen.
  exists rs'; auto with asmgen.
- (* Oxorlimm *)
  destruct (xorimm64_correct x0 x i k rs m) as [rs' [A [B C]]]. eauto with asmgen.
  exists rs'; auto with asmgen.
- (* Onotl *)
  econstructor; split. eapply exec_straight_one; simpl; reflexivity.
  split. Simpl. destruct (rs x); simpl; auto. rewrite Int64.or_idem; auto.
  intros; Simpl.
- (* Oshrxlimm *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. apply SAME. apply Val.shrxl_carry. auto.
  intros; Simpl.
- (* Orolml *)
  destruct (rolm64_correct x0 x i i0 k rs m) as [rs' [A [B C]]]. eauto with asmgen.
  exists rs'; auto with asmgen.
- (* Olongoffloat *)
  replace v with (Val.maketotal (Val.longoffloat (rs x))).
  TranslOpSimpl.
  rewrite H1; auto.
- (* Ofloatoflong *)
  replace v with (Val.maketotal (Val.floatoflong (rs x))).
  TranslOpSimpl.
  rewrite H1; auto.
  (* Ointoffloat *)
- replace v with (Val.maketotal (Val.intoffloat (rs x))).
  TranslOpSimpl.
  rewrite H1; auto.
  (* Ointuoffloat *)
- replace v with (Val.maketotal (Val.intuoffloat (rs x))).
  TranslOpSimpl.
  rewrite H1; auto.
  (* Ofloatofint *)
- replace v with (Val.maketotal (Val.floatofint (rs x))).
  TranslOpSimpl.
  rewrite H1; auto.
  (* Ofloatofintu *)
- replace v with (Val.maketotal (Val.floatofintu (rs x))).
  TranslOpSimpl.
  rewrite H1; auto.
  (* Ocmp *)
- destruct (transl_cond_op_correct c0 args res k rs m c) as [rs' [A [B C]]]; auto.
  exists rs'; auto with asmgen.
Qed.

Lemma transl_op_correct:
  forall op args res k ms sp rs m v m' c,
  transl_op op args res k = OK c ->
  agree ms sp rs ->
  eval_operation ge sp op (map ms args) m = Some v ->
  Mem.extends m m' ->
  exists rs',
     exec_straight ge fn c rs m' k rs' m'
  /\ agree (Regmap.set res v (Mach.undef_regs (destroyed_by_op op) ms)) sp rs'
  /\ forall r, important_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  intros.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eauto.
  intros [v' [A B]].  rewrite (sp_val _ _ _ H0) in A.
  exploit transl_op_correct_aux; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eexact P.
  split. apply agree_set_undef_mreg with rs; auto with asmgen. eapply Val.lessdef_trans; eauto.
  auto.
Qed.

(** Translation of memory accesses *)

Lemma transl_memory_access_correct:
  forall (P: regset -> Prop) mk1 mk2 addr args temp k c (rs: regset) a m m',
  transl_memory_access mk1 mk2 addr args temp k = OK c ->
  eval_addressing ge (rs#GPR1) addr (map rs (map preg_of args)) = Some a ->
  temp <> GPR0 ->
  (forall cst (r1: ireg) (rs1: regset) k,
    Val.lessdef a (Val.add (gpr_or_zero rs1 r1) (const_low ge cst)) ->
    (forall r, r <> PC -> r <> temp -> r <> GPR0 -> rs1 r = rs r) ->
    exists rs',
        exec_straight ge fn (mk1 cst r1 :: k) rs1 m k rs' m' /\ P rs') ->
  (forall (r1 r2: ireg) (rs1: regset) k,
    Val.lessdef a (Val.add (gpr_or_zero rs1 r1) rs1#r2) ->
    (forall r, r <> PC -> r <> temp -> r <> GPR0 -> rs1 r = rs r) ->
    exists rs',
        exec_straight ge fn (mk2 r1 r2 :: k) rs1 m k rs' m' /\ P rs') ->
  exists rs',
      exec_straight ge fn c rs m k rs' m' /\ P rs'.
Proof.
  intros until m'; intros TR ADDR TEMP MK1 MK2.
  unfold transl_memory_access in TR; destruct addr; ArgsInv; simpl in ADDR; inv ADDR.
  (* Aindexed *)
  case (Int.eq (high_s i) Int.zero).
  (* Aindexed short *)
  apply MK1. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
  (* Aindexed long *)
  set (rs1 := nextinstr (rs#temp <- (Val.add (rs x) (Vint (Int.shl (high_s i) (Int.repr 16)))))).
  exploit (MK1 (Cint (low_s i)) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen.
    unfold rs1; Simpl. rewrite Val.add_assoc.
Transparent Val.add.
    simpl. rewrite low_high_s. auto.
    intros; unfold rs1; Simpl.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
  auto. auto.
  (* Aindexed2 *)
  apply MK2. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
  (* Aglobal *)
  destruct (symbol_is_small_data i i0) eqn:SISD; [ | destruct (symbol_is_rel_data i i0) ]; inv TR.
  (* Aglobal from small data *)
  apply MK1. unfold const_low. rewrite small_data_area_addressing by auto.
  rewrite add_zero_symbol_address. auto.
  auto.
  (* Aglobal from relative data *)
  set (rs1 := nextinstr (rs#temp <- (Val.add Vzero (high_half ge i i0)))).
  set (rs2 := nextinstr (rs1#temp <- (Genv.symbol_address ge i i0))).
  exploit (MK1 (Cint Int.zero) temp rs2).
    simpl. rewrite gpr_or_zero_not_zero by eauto with asmgen.
    unfold rs2. Simpl. rewrite Val.add_commut. rewrite add_zero_symbol_address. auto.
    intros; unfold rs2, rs1; Simpl.
  intros [rs' [EX' AG']].
  exists rs'; split. apply exec_straight_step with rs1 m; auto.
  apply exec_straight_step with rs2 m; auto. simpl. unfold rs2.
  rewrite gpr_or_zero_not_zero by eauto with asmgen. f_equal. f_equal. f_equal.
  unfold rs1; Simpl. apply low_high_half_zero.
  eexact EX'. auto.
  (* Aglobal from absolute data *)
  set (rs1 := nextinstr (rs#temp <- (Val.add Vzero (high_half ge i i0)))).
  exploit (MK1 (Csymbol_low i i0) temp rs1).
    simpl. rewrite gpr_or_zero_not_zero by eauto with asmgen.
    unfold rs1. Simpl. rewrite low_high_half_zero. auto.
    intros; unfold rs1; Simpl.
  intros [rs' [EX' AG']].
  exists rs'; split. apply exec_straight_step with rs1 m; auto.
  eexact EX'. auto.
  (* Abased *)
  destruct (symbol_is_small_data i i0) eqn:SISD; [ | destruct (symbol_is_rel_data i i0) ].
  (* Abased from small data *)
  set (rs1 := nextinstr (rs#GPR0 <- (Genv.symbol_address ge i i0))).
  exploit (MK2 x GPR0 rs1 k).
    simpl. rewrite gpr_or_zero_not_zero by eauto with asmgen.
    unfold rs1; Simpl. rewrite Val.add_commut. auto.
    intros. unfold rs1; Simpl.
  intros [rs' [EX' AG']].
  exists rs'; split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_zero. f_equal. unfold rs1. f_equal. f_equal.
  unfold const_low. rewrite small_data_area_addressing; auto.
  apply add_zero_symbol_address.
  reflexivity.
  assumption. assumption.
  (* Abased from relative data *)
  set (rs1 := nextinstr (rs#GPR0 <- (rs#x))).
  set (rs2 := nextinstr (rs1#temp <- (Val.add Vzero (high_half ge i i0)))).
  set (rs3 := nextinstr (rs2#temp <- (Genv.symbol_address ge i i0))).
  exploit (MK2 temp GPR0 rs3).
    rewrite gpr_or_zero_not_zero by eauto with asmgen.
    f_equal. unfold rs3; Simpl. unfold rs3, rs2, rs1; Simpl.
    intros. unfold rs3, rs2, rs1; Simpl.
  intros [rs' [EX' AG']].
  exists rs'. split. eapply exec_straight_trans with (rs2 := rs3) (m2 := m).
  apply exec_straight_three with rs1 m rs2 m; auto.
  simpl. unfold rs3. f_equal. f_equal. f_equal. rewrite gpr_or_zero_not_zero by auto.
  unfold rs2; Simpl. apply low_high_half_zero.
  eexact EX'. auto.
  (* Abased absolute *)
  set (rs1 := nextinstr (rs#temp <- (Val.add (rs x) (high_half ge i i0)))).
  exploit (MK1 (Csymbol_low i i0) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen.
    unfold rs1. Simpl.
    rewrite Val.add_assoc. rewrite low_high_half. rewrite Val.add_commut. auto.
    intros; unfold rs1; Simpl.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
  assumption. assumption.
  (* Ainstack *)
  set (ofs := Ptrofs.to_int i) in *.
  assert (L: Val.lessdef (Val.offset_ptr (rs GPR1) i) (Val.add (rs GPR1) (Vint ofs))).
  { destruct (rs GPR1); simpl; auto. unfold ofs; rewrite Ptrofs.of_int_to_int; auto. }
  destruct (Int.eq (high_s ofs) Int.zero); inv TR.
  apply MK1. simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
  set (rs1 := nextinstr (rs#temp <- (Val.add rs#GPR1 (Vint (Int.shl (high_s ofs) (Int.repr 16)))))).
  exploit (MK1 (Cint (low_s ofs)) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; auto.
    unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss.
    rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
    congruence.
    intros. unfold rs1. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
  assumption. assumption.
Qed.

(** Translation of loads *)

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) m a v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge (rs#GPR1) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> GPR12 -> r <> GPR0 -> r <> preg_of dst -> rs' r = rs r.
Proof.
  intros.
  assert (LD: forall v, Val.lessdef a v -> v = a).
  { intros. inv H2; auto. discriminate H1. }
  assert (BASE: forall mk1 mk2 k' chunk' v',
  transl_memory_access mk1 mk2 addr args GPR12 k' = OK c ->
  Mem.loadv chunk' m a = Some v' ->
  (forall cst (r1: ireg) (rs1: regset),
    exec_instr ge fn (mk1 cst r1) rs1 m =
    load1 ge chunk' (preg_of dst) cst r1 rs1 m) ->
  (forall (r1 r2: ireg) (rs1: regset),
    exec_instr ge fn (mk2 r1 r2) rs1 m =
    load2 chunk' (preg_of dst) r1 r2 rs1 m) ->
  exists rs',
     exec_straight ge fn c rs m k' rs' m
  /\ rs'#(preg_of dst) = v'
  /\ forall r, r <> PC -> r <> GPR12 -> r <> GPR0 -> r <> preg_of dst -> rs' r = rs r).
  {
  intros. eapply transl_memory_access_correct; eauto. congruence.
  intros. econstructor; split. apply exec_straight_one.
  rewrite H4. unfold load1. apply LD in H6. rewrite H6. rewrite H3. eauto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso; auto with asmgen.
  intuition Simpl.
  intros. econstructor; split. apply exec_straight_one.
  rewrite H5. unfold load2. apply LD in H6. rewrite H6. rewrite H3. eauto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso; auto with asmgen.
  intuition Simpl.
  }
  destruct chunk; monadInv H.
- (* Mint8signed *)
  assert (exists v1, Mem.loadv Mint8unsigned m a = Some v1 /\ v = Val.sign_ext 8 v1).
  {
    destruct a; simpl in *; try discriminate.
    rewrite Mem.load_int8_signed_unsigned in H1.
    destruct (Mem.load Mint8unsigned m b (Ptrofs.unsigned i)); simpl in H1; inv H1.
    exists v0; auto.
  }
  destruct H as [v1 [LD' SG]]. clear H1.
  exploit BASE; eauto; erewrite ireg_of_eq by eauto; auto.
  intros [rs1 [A [B C]]].
  econstructor; split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one. simpl; eauto. auto.
  split. Simpl. congruence. intros. Simpl.
- (* Mint8unsigned *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint816signed *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint16unsigned *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint32 *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint64 *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mfloat32 *)
  eapply BASE; eauto; erewrite freg_of_eq by eauto; auto.
- (* Mfloat64 *)
  eapply BASE; eauto; erewrite freg_of_eq by eauto; auto.
Qed.

(** Translation of stores *)

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs#GPR1) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a (rs (preg_of src)) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> preg_notin r (destroyed_by_store chunk addr) -> rs' r = rs r.
Proof.
Local Transparent destroyed_by_store.
  intros.
  assert (LD: forall v, Val.lessdef a v -> v = a).
  { intros. inv H2; auto. discriminate H1. }
  assert (TEMP0: int_temp_for src = GPR11 \/ int_temp_for src = GPR12).
    unfold int_temp_for. destruct (mreg_eq src R12); auto.
  assert (TEMP1: int_temp_for src <> GPR0).
    destruct TEMP0; congruence.
  assert (TEMP2: IR (int_temp_for src) <> preg_of src).
    unfold int_temp_for. destruct (mreg_eq src R12).
    subst src; simpl; congruence.
    change (IR GPR12) with (preg_of R12). red; intros; elim n.
    eapply preg_of_injective; eauto.
  assert (BASE: forall mk1 mk2 chunk',
  transl_memory_access mk1 mk2 addr args (int_temp_for src) k = OK c ->
  Mem.storev chunk' m a (rs (preg_of src)) = Some m' ->
  (forall cst (r1: ireg) (rs1: regset),
    exec_instr ge fn (mk1 cst r1) rs1 m =
    store1 ge chunk' (preg_of src) cst r1 rs1 m) ->
  (forall (r1 r2: ireg) (rs1: regset),
    exec_instr ge fn (mk2 r1 r2) rs1 m =
    store2 chunk' (preg_of src) r1 r2 rs1 m) ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> r <> GPR11 /\ r <> GPR12 -> rs' r = rs r).
  {
  intros. eapply transl_memory_access_correct; eauto.
  intros. econstructor; split. apply exec_straight_one.
  rewrite H4. unfold store1. apply LD in H6. rewrite H6. rewrite H7; auto with asmgen. rewrite H3. eauto. auto.
  intros; Simpl. apply H7; auto. destruct TEMP0; destruct H10; congruence.
  intros. econstructor; split. apply exec_straight_one.
  rewrite H5. unfold store2. apply LD in H6. rewrite H6. rewrite H7; auto with asmgen. rewrite H3. eauto. auto.
  intros; Simpl. apply H7; auto. destruct TEMP0; destruct H10; congruence.
  }
  destruct chunk; monadInv H.
- (* Mint8signed *)
  assert (Mem.storev Mint8unsigned m a (rs (preg_of src)) = Some m').
    rewrite <- H1. destruct a; simpl; auto. symmetry. apply Mem.store_signed_unsigned_8.
  clear H1. eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint8unsigned *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint16signed *)
  assert (Mem.storev Mint16unsigned m a (rs (preg_of src)) = Some m').
    rewrite <- H1. destruct a; simpl; auto. symmetry. apply Mem.store_signed_unsigned_16.
  clear H1. eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint16unsigned *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint32 *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mint64 *)
  eapply BASE; eauto; erewrite ireg_of_eq by eauto; auto.
- (* Mfloat32 *)
  eapply BASE; eauto; erewrite freg_of_eq by eauto; auto.
- (* Mfloat64 *)
  eapply BASE; eauto; erewrite freg_of_eq by eauto; auto.
Qed.

(** Translation of function epilogues *)

Lemma transl_epilogue_correct:
  forall ge0 f m stk soff cs m' ms rs k tm,
  load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp cs) ->
  load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra cs) ->
  Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
  agree ms (Vptr stk soff) rs ->
  (is_leaf_function f = true -> rs#LR = parent_ra cs) ->
  Mem.extends m tm ->
  match_stack ge0 cs ->
  exists rs', exists tm',
     exec_straight ge fn (transl_epilogue f k) rs tm k rs' tm'
  /\ agree ms (parent_sp cs) rs'
  /\ Mem.extends m' tm'
  /\ rs'#LR = parent_ra cs
  /\ rs'#SP = parent_sp cs
  /\ (forall r, r <> PC -> r <> LR -> r <> SP -> r <> GPR0 -> rs'#r = rs#r).
Proof.
  intros until tm; intros LP LRA FREE AG LEAF MEXT MCS.
  exploit Mem.loadv_extends. eauto. eexact LP. auto. simpl. intros (parent' & LP' & LDP').
  exploit Mem.loadv_extends. eauto. eexact LRA. auto. simpl. intros (ra' & LRA' & LDRA').
  exploit lessdef_parent_sp; eauto. intros EQ; subst parent'; clear LDP'.
  exploit lessdef_parent_ra; eauto. intros EQ; subst ra'; clear LDRA'.
  exploit Mem.free_parallel_extends; eauto. intros (tm' & FREE' & MEXT').
  unfold transl_epilogue. destruct (is_leaf_function f).
- (* leaf function *)
  econstructor; exists tm'.
  split. apply exec_straight_one. simpl. rewrite <- (sp_val _ _ _ AG). simpl. 
  rewrite LP'. rewrite FREE'. reflexivity. reflexivity.
  split. apply agree_nextinstr. eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  split. auto.
  split. Simpl. 
  split. Simpl.
  intros; Simpl.
- (* regular function *)
  set (rs1 := nextinstr (rs#GPR0 <- (parent_ra cs))).
  set (rs2 := nextinstr (rs1#LR  <- (parent_ra cs))).
  set (rs3 := nextinstr (rs2#GPR1 <- (parent_sp cs))).
  exists rs3; exists tm'.
  split. apply exec_straight_three with rs1 tm rs2 tm; auto.
    simpl. unfold load1. rewrite gpr_or_zero_not_zero by congruence. 
    unfold const_low. rewrite <- (sp_val _ _ _ AG).
    erewrite loadv_offset_ptr by eexact LRA'. reflexivity.
    simpl. change (rs2#GPR1) with (rs#GPR1). rewrite <- (sp_val _ _ _ AG). simpl. 
    rewrite LP'. rewrite FREE'. reflexivity.
  split. unfold rs3. apply agree_nextinstr. apply agree_change_sp with (Vptr stk soff). 
    apply agree_nextinstr. apply agree_set_other; auto. 
    apply agree_nextinstr. apply agree_set_other; auto. 
    eapply parent_sp_def; eauto.
  split. auto.
  split. reflexivity.
  split. reflexivity.
  intros. unfold rs3, rs2, rs1; Simpl. 
Qed.

End CONSTRUCTORS.

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

(** * Properties of low half/high half decomposition *)

Lemma high_half_zero:
  forall v, Val.add (high_half v) Vzero = high_half v.
Proof.
  intros. generalize (high_half_type v).
  rewrite Val.add_commut. 
  case (high_half v); simpl; intros; try contradiction.
  auto. 
  rewrite Int.add_commut; rewrite Int.add_zero; auto. 
  rewrite Int.add_zero; auto. 
Qed.

Lemma low_high_u:
  forall n, Int.or (Int.shl (high_u n) (Int.repr 16)) (low_u n) = n.
Proof.
  intros. unfold high_u, low_u.
  rewrite Int.shl_rolm. rewrite Int.shru_rolm. 
  rewrite Int.rolm_rolm. 
  change (Int.modu (Int.add (Int.sub (Int.repr (Z_of_nat Int.wordsize)) (Int.repr 16))
                            (Int.repr 16))
                   (Int.repr (Z_of_nat Int.wordsize)))
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
  change (Int.modu (Int.add (Int.sub (Int.repr (Z_of_nat Int.wordsize)) (Int.repr 16))
                            (Int.repr 16))
                   (Int.repr (Z_of_nat Int.wordsize)))
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

(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
  || (rewrite nextinstr_inv1 by eauto with asmgen)
  || (rewrite Pregmap.gss)
  || (rewrite nextinstr_pc)
  || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of PowerPC constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: code.

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
  /\ forall r', data_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
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
  /\ forall r', data_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
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
  /\ forall r', data_preg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
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

(** Indexed memory loads. *)

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) m v c,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  base <> GPR0 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> preg_of dst -> r <> GPR0 -> rs'#r = rs#r.
Proof.
Opaque Int.eq.
  unfold loadind; intros. destruct ty; monadInv H; simpl in H0.
(* integer *)
  rewrite (ireg_of_eq _ _ EQ).
  destruct (Int.eq (high_s ofs) Int.zero).
  (* one load *)
  econstructor; split. apply exec_straight_one. simpl.
  unfold load1. rewrite gpr_or_zero_not_zero; auto. simpl. rewrite H0. eauto. auto.
  intuition Simpl.
  (* loadimm + load *)
  exploit (loadimm_correct GPR0 ofs); eauto. intros [rs' [A [B C]]]. 
  exists (nextinstr (rs'#x <- v)); split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one; auto. 
  simpl. unfold load2. rewrite C; auto with asmgen. rewrite B. rewrite H0. auto. 
  intuition Simpl. 
(* float *)
  rewrite (freg_of_eq _ _ EQ).
  destruct (Int.eq (high_s ofs) Int.zero).
  (* one load *)
  econstructor; split. apply exec_straight_one. simpl.
  unfold load1. rewrite gpr_or_zero_not_zero; auto. simpl. rewrite H0. eauto. auto.
  intuition Simpl.
  (* loadimm + load *)
  exploit (loadimm_correct GPR0 ofs); eauto. intros [rs' [A [B C]]]. 
  exists (nextinstr (rs'#x <- v)); split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one; auto. 
  simpl. unfold load2. rewrite C; auto with asmgen. rewrite B. rewrite H0. auto. 
  intuition Simpl. 
Qed.

(** Indexed memory stores. *)

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) m m' c,
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  base <> GPR0 ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  unfold storeind; intros.
  assert (preg_of src <> GPR0) by auto with asmgen.
  destruct ty; monadInv H; simpl in H0.
(* integer *)
  rewrite (ireg_of_eq _ _ EQ) in *.
  destruct (Int.eq (high_s ofs) Int.zero).
  (* one store *)
  econstructor; split. apply exec_straight_one. simpl.
  unfold store1. rewrite gpr_or_zero_not_zero; auto. simpl. rewrite H0. eauto. auto.
  intros; Simpl.
  (* loadimm + store *)
  exploit (loadimm_correct GPR0 ofs); eauto. intros [rs' [A [B C]]]. 
  exists (nextinstr rs'); split.
  eapply exec_straight_trans. eexact A. apply exec_straight_one; auto. 
  simpl. unfold store2. rewrite B. rewrite ! C; auto with asmgen. rewrite H0. auto. 
  intuition Simpl. 
(* float *)
  rewrite (freg_of_eq _ _ EQ) in *.
  destruct (Int.eq (high_s ofs) Int.zero).
  (* one store *)
  econstructor; split. apply exec_straight_one. simpl.
  unfold store1. rewrite gpr_or_zero_not_zero; auto. simpl. rewrite H0. eauto. auto.
  intuition Simpl.
  (* loadimm + store *)
  exploit (loadimm_correct GPR0 ofs); eauto. intros [rs' [A [B C]]]. 
  exists (nextinstr rs'); split. 
  eapply exec_straight_trans. eexact A. apply exec_straight_one; auto. 
  simpl. unfold store2. rewrite B. rewrite ! C; auto with asmgen. rewrite H0. auto. 
  intuition Simpl. 
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
  | [ H: assertion _ = OK _ |- _ ] => monadInv H
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
  /\ forall r, data_preg r = true -> rs'#r = rs#r.
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
  /\ forall r, data_preg r = true -> rs'#r = rs#r.
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
  /\ agree ms sp rs'.
Proof.
  intros.
  exploit transl_cond_correct_2. eauto. 
    eapply eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto.
  intros [rs' [A [B C]]].
  exists rs'; split. eauto. split. auto. apply agree_exten with rs; auto.
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
  /\ forall r', data_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r'.
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
  | split; intros; Simpl; fail ].

Lemma transl_op_correct_aux:
  forall op args res k (rs: regset) m v c,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#GPR1) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r,
     match op with Omove => data_preg r = true | _ => nontemp_preg r = true end ->
     r <> preg_of res -> rs'#r = rs#r.
Proof.
Opaque Int.eq.
  intros. unfold transl_op in H; destruct op; ArgsInv; simpl in H0; try (inv H0); try TranslOpSimpl.
  (* Omove *)
  destruct (preg_of res) eqn:RES; destruct (preg_of m0) eqn:ARG; inv H.
  TranslOpSimpl.
  TranslOpSimpl.
  (* Ointconst *)
  destruct (loadimm_correct x i k rs m) as [rs' [A [B C]]]. 
  exists rs'. auto with asmgen. 
  (* Oaddrsymbol *)
  change (symbol_address ge i i0) with (symbol_offset ge i i0).
  set (v' := symbol_offset ge i i0).
  destruct (symbol_is_small_data i i0) eqn:SD.
  (* small data *)
  econstructor; split. apply exec_straight_one; simpl; reflexivity.
  split. Simpl. rewrite (small_data_area_addressing _ _ _ SD). unfold v', symbol_offset. 
  destruct (Genv.find_symbol ge i); auto. rewrite Int.add_zero; auto. 
  intros; Simpl.
  (* not small data *)
Opaque Val.add.
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  split. Simpl. rewrite gpr_or_zero_zero.
  rewrite gpr_or_zero_not_zero; eauto with asmgen. Simpl.  
  rewrite (Val.add_commut Vzero). rewrite high_half_zero. 
  rewrite Val.add_commut. rewrite low_high_half. auto.
  intros; Simpl.
  (* Oaddrstack *)
  destruct (addimm_correct x GPR1 i k rs m) as [rs' [EX [RES OTH]]]; eauto with asmgen.
  exists rs'; auto with asmgen.
  (* Oaddimm *)
  destruct (addimm_correct x0 x i k rs m) as [rs' [A [B C]]]; eauto with asmgen.
  exists rs'; auto with asmgen.
  (* Osubimm *)
  case (Int.eq (high_s i) Int.zero).
  TranslOpSimpl.
  destruct (loadimm_correct GPR0 i (Psubfc x0 x GPR0 :: k) rs m) as [rs1 [EX [RES OTH]]].
  econstructor; split.
  eapply exec_straight_trans. eexact EX. apply exec_straight_one; simpl; reflexivity.
  split. Simpl. rewrite RES. rewrite OTH; eauto with asmgen. 
  intros; Simpl.
  (* Omulimm *)
  case (Int.eq (high_s i) Int.zero).
  TranslOpSimpl.
  destruct (loadimm_correct GPR0 i (Pmullw x0 x GPR0 :: k) rs m) as [rs1 [EX [RES OTH]]].
  econstructor; split.
  eapply exec_straight_trans. eexact EX. apply exec_straight_one; simpl; reflexivity.
  split. Simpl. rewrite RES. rewrite OTH; eauto with asmgen. 
  intros; Simpl.
  (* Odivs *)
  replace v with (Val.maketotal (Val.divs (rs x) (rs x0))).
  TranslOpSimpl. 
  rewrite H1; auto.
  (* Odivu *)
  replace v with (Val.maketotal (Val.divu (rs x) (rs x0))).
  TranslOpSimpl. 
  rewrite H1; auto.
  (* Oand *)
  set (v' := Val.and (rs x) (rs x0)) in *.
  pose (rs1 := rs#x1 <- v').
  destruct (compare_sint_spec rs1 v' Vzero) as [A [B [C D]]].
  econstructor; split. apply exec_straight_one; simpl; reflexivity.
  split. rewrite D; auto with asmgen. unfold rs1; Simpl.
  intros. rewrite D; auto with asmgen. unfold rs1; Simpl.
  (* Oandimm *)
  destruct (andimm_correct x0 x i k rs m) as [rs' [A [B C]]]; eauto with asmgen.
  exists rs'; auto with asmgen.
  (* Oorimm *)
  destruct (orimm_correct x0 x i k rs m) as [rs' [A [B C]]]. 
  exists rs'; auto with asmgen.
  (* Oxorimm *)
  destruct (xorimm_correct x0 x i k rs m) as [rs' [A [B C]]]. 
  exists rs'; auto with asmgen.
  (* Onor *)
  replace (Val.notint (rs x))
     with (Val.notint (Val.or (rs x) (rs x))).
  TranslOpSimpl.
  destruct (rs x); simpl; auto. rewrite Int.or_idem. auto.
  (* Oshrximm *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity. 
  split. Simpl. apply Val.shrx_carry. auto. 
  intros; Simpl.
  (* Orolm *)
  destruct (rolm_correct x0 x i i0 k rs m) as [rs' [A [B C]]]; eauto with asmgen.
  exists rs'; auto with asmgen.
  (* Ointoffloat *)
  replace v with (Val.maketotal (Val.intoffloat (rs x))).
  TranslOpSimpl.
  rewrite H1; auto.
  (* Ocmp *)
  destruct (transl_cond_op_correct c0 args res k rs m c) as [rs' [A [B C]]]; auto.
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
  /\ agree (Regmap.set res v (undef_op op ms)) sp rs'
  /\ forall r, op = Omove -> data_preg r = true -> r <> preg_of res -> rs'#r = rs#r.
Proof.
  intros. 
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eauto. 
  intros [v' [A B]].  rewrite (sp_val _ _ _ H0) in A. 
  exploit transl_op_correct_aux; eauto. intros [rs' [P [Q R]]].
  rewrite <- Q in B.
  exists rs'; split. eexact P. 
  split. unfold undef_op. destruct op;
  (apply agree_set_undef_mreg with rs || apply agree_set_mreg with rs);
  auto.
  intros. subst op. auto.
Qed.

(** Translation of memory accesses *)

Lemma transl_memory_access_correct:
  forall (P: regset -> Prop) mk1 mk2 addr args temp k c (rs: regset) a m m',
  transl_memory_access mk1 mk2 addr args temp k = OK c ->
  eval_addressing ge (rs#GPR1) addr (map rs (map preg_of args)) = Some a ->
  temp <> GPR0 ->
  (forall cst (r1: ireg) (rs1: regset) k,
    Val.add (gpr_or_zero rs1 r1) (const_low ge cst) = a ->
    (forall r, r <> PC -> r <> temp -> rs1 r = rs r) ->
    exists rs',
        exec_straight ge fn (mk1 cst r1 :: k) rs1 m k rs' m' /\ P rs') ->
  (forall (r1 r2: ireg) (rs1: regset) k,
    Val.add rs1#r1 rs1#r2 = a ->
    (forall r, r <> PC -> r <> temp -> rs1 r = rs r) ->
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
  apply MK2; auto.
  (* Aglobal *)
  destruct (symbol_is_small_data i i0) eqn:SISD; inv TR.
  (* Aglobal from small data *)
  apply MK1. simpl. rewrite small_data_area_addressing; auto.
  unfold symbol_address, symbol_offset. 
  destruct (Genv.find_symbol ge i); auto. rewrite Int.add_zero. auto.
  auto.
  (* Aglobal general case *)
  set (rs1 := nextinstr (rs#temp <- (const_high ge (Csymbol_high i i0)))).
  exploit (MK1 (Csymbol_low i i0) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen.
    unfold rs1. Simpl. 
    unfold const_high, const_low.
    rewrite Val.add_commut. rewrite low_high_half. auto.
    intros; unfold rs1; Simpl.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_zero. 
  rewrite Val.add_commut. unfold const_high. 
  rewrite high_half_zero.
  reflexivity. reflexivity.
  assumption. assumption.
  (* Abased *)
  set (rs1 := nextinstr (rs#temp <- (Val.add (rs x) (const_high ge (Csymbol_high i i0))))).
  exploit (MK1 (Csymbol_low i i0) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen.
    unfold rs1. Simpl. 
    rewrite Val.add_assoc. 
    unfold const_high, const_low. 
    symmetry. rewrite Val.add_commut. f_equal. f_equal. 
    rewrite Val.add_commut. rewrite low_high_half. auto.
    intros; unfold rs1; Simpl.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto.
  assumption. assumption.
  (* Ainstack *)
  destruct (Int.eq (high_s i) Int.zero); inv TR.
  apply MK1. simpl. rewrite gpr_or_zero_not_zero; eauto with asmgen. auto. 
  set (rs1 := nextinstr (rs#temp <- (Val.add rs#GPR1 (Vint (Int.shl (high_s i) (Int.repr 16)))))).
  exploit (MK1 (Cint (low_s i)) temp rs1 k).
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
  /\ forall r, r <> PC -> r <> GPR12 -> r <> preg_of dst -> rs' r = rs r.
Proof.
  intros.
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
  /\ forall r, r <> PC -> r <> GPR12 -> r <> preg_of dst -> rs' r = rs r).
  {
  intros. eapply transl_memory_access_correct; eauto. congruence.
  intros. econstructor; split. apply exec_straight_one. 
  rewrite H4. unfold load1. rewrite H6. rewrite H3. eauto. 
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso; auto with asmgen.
  intuition Simpl.
  intros. econstructor; split. apply exec_straight_one. 
  rewrite H5. unfold load2. rewrite H6. rewrite H3. eauto. 
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso; auto with asmgen.
  intuition Simpl.
  }
  destruct chunk; monadInv H.
- (* Mint8signed *)
  assert (exists v1, Mem.loadv Mint8unsigned m a = Some v1 /\ v = Val.sign_ext 8 v1).
  {
    destruct a; simpl in *; try discriminate. 
    rewrite Mem.load_int8_signed_unsigned in H1. 
    destruct (Mem.load Mint8unsigned m b (Int.unsigned i)); simpl in H1; inv H1.
    exists v0; auto.
  }
  destruct H as [v1 [LD SG]]. clear H1. 
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
- (* Mfloat32 *)
  eapply BASE; eauto; erewrite freg_of_eq by eauto; auto.
- (* Mfloat64 *)
  apply Mem.loadv_float64al32 in H1. eapply BASE; eauto; erewrite freg_of_eq by eauto; auto.
- (* Mfloat64al32 *)
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
  /\ forall r, r <> PC -> r <> GPR11 -> r <> GPR12 -> r <> FPR13 -> rs' r = rs r.
Proof.
  intros.
  assert (TEMP0: int_temp_for src = GPR11 \/ int_temp_for src = GPR12).
    unfold int_temp_for. destruct (mreg_eq src IT2); auto.
  assert (TEMP1: int_temp_for src <> GPR0).
    destruct TEMP0; congruence.
  assert (TEMP2: IR (int_temp_for src) <> preg_of src).
    unfold int_temp_for. destruct (mreg_eq src IT2). 
    subst src; simpl; congruence.
    change (IR GPR12) with (preg_of IT2). red; intros; elim n. 
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
  /\ forall r, r <> PC -> r <> GPR11 -> r <> GPR12 -> r <> FPR13 -> rs' r = rs r).
  {
  intros. eapply transl_memory_access_correct; eauto.
  intros. econstructor; split. apply exec_straight_one. 
  rewrite H4. unfold store1. rewrite H6. rewrite H7; auto with asmgen. rewrite H3. eauto. auto. 
  intros; Simpl. apply H7; auto. destruct TEMP0; congruence. 
  intros. econstructor; split. apply exec_straight_one. 
  rewrite H5. unfold store2. rewrite H6. rewrite H7; auto with asmgen. rewrite H3. eauto. auto. 
  intros; Simpl. apply H7; auto. destruct TEMP0; congruence. 
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
- (* Mfloat32 *)
  rewrite (freg_of_eq _ _ EQ) in H1.
  eapply transl_memory_access_correct. eauto. eauto. eauto. 
  intros. econstructor; split. apply exec_straight_one. 
  simpl. unfold store1. rewrite H. rewrite H2; auto with asmgen. rewrite H1. eauto. auto. 
  intros. Simpl. apply H2; auto with asmgen. destruct TEMP0; congruence.
  intros. econstructor; split. apply exec_straight_one. 
  simpl. unfold store2. rewrite H. rewrite H2; auto with asmgen. rewrite H1. eauto. auto. 
  intros. Simpl. apply H2; auto with asmgen. destruct TEMP0; congruence.
- (* Mfloat64 *)
  apply Mem.storev_float64al32 in H1. eapply BASE; eauto; erewrite freg_of_eq by eauto; auto.
- (* Mfloat64al32 *)
  eapply BASE; eauto; erewrite freg_of_eq by eauto; auto.
Qed.

End CONSTRUCTORS.


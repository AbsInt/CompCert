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
  intros. rewrite Int.shl_mul_two_p. 
  unfold high_s. 
  rewrite <- (Int.divu_pow2 (Int.sub n (low_s n)) (Int.repr 65536) (Int.repr 16)).
  change (two_p (Int.unsigned (Int.repr 16))) with 65536.
  set (x := Int.sub n (low_s n)).
  assert (x = Int.add (Int.mul (Int.divu x (Int.repr 65536)) (Int.repr 65536))
                      (Int.modu x (Int.repr 65536))).
    apply Int.modu_divu_Euclid. compute; congruence.
  assert (Int.modu x (Int.repr 65536) = Int.zero).
    unfold Int.modu, Int.zero. decEq.
    change 0 with (0 mod 65536).
    change (Int.unsigned (Int.repr 65536)) with 65536.
    apply Int.eqmod_mod_eq. omega. 
    unfold x, low_s. eapply Int.eqmod_trans. 
    eapply Int.eqm_eqmod_two_p with (n := 16). compute; auto.
    unfold Int.sub. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl. 
    replace 0 with (Int.unsigned n - Int.unsigned n) by omega.
    apply Int.eqmod_sub. apply Int.eqmod_refl. apply Int.eqmod_sign_ext'. 
    compute; auto.
  rewrite H0 in H. rewrite Int.add_zero in H.
  rewrite <- H. unfold x. rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg (low_s n))). rewrite <- Int.sub_add_opp. 
  rewrite Int.sub_idem. apply Int.add_zero.
  reflexivity.
Qed.

(** * Correspondence between Mach registers and PPC registers *)

Hint Extern 2 (_ <> _) => discriminate: ppcgen.

(** Mapping from Mach registers to PPC registers. *)

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

(** Characterization of PPC registers that correspond to Mach registers. *)

Definition is_data_reg (r: preg) : bool :=
  match r with
  | IR GPR0 => false
  | PC => false    | LR => false    | CTR => false
  | CR0_0 => false | CR0_1 => false | CR0_2 => false | CR0_3 => false
  | CARRY => false
  | _ => true
  end.

Lemma ireg_of_is_data_reg:
  forall (r: mreg), is_data_reg (ireg_of r) = true.
Proof.
  destruct r; reflexivity.
Qed.

Lemma freg_of_is_data_reg:
  forall (r: mreg), is_data_reg (ireg_of r) = true.
Proof.
  destruct r; reflexivity.
Qed.

Lemma preg_of_is_data_reg:
  forall (r: mreg), is_data_reg (preg_of r) = true.
Proof.
  destruct r; reflexivity.
Qed.

Lemma data_reg_diff:
  forall r r', is_data_reg r = true -> is_data_reg r' = false -> r <> r'.
Proof.
  intros. congruence.
Qed.

Lemma ireg_diff:
  forall r r', r <> r' -> IR r <> IR r'.
Proof.
  intros. congruence.
Qed.

Lemma diff_ireg:
  forall r r', IR r <> IR r' -> r <> r'.
Proof.
  intros. congruence.
Qed.

Hint Resolve ireg_of_is_data_reg freg_of_is_data_reg preg_of_is_data_reg
             data_reg_diff ireg_diff diff_ireg: ppcgen.

Definition is_nontemp_reg (r: preg) : bool :=
  match r with
  | IR GPR0 => false | IR GPR11 => false | IR GPR12 => false
  | FR FPR0 => false | FR FPR12 => false | FR FPR13 => false
  | PC => false      | LR => false       | CTR => false
  | CR0_0 => false   | CR0_1 => false    | CR0_2 => false    | CR0_3 => false
  | CARRY => false
  | _ => true
  end.

Remark is_nontemp_is_data:
  forall r, is_nontemp_reg r = true -> is_data_reg r = true.
Proof.
  destruct r; simpl; try congruence. destruct i; congruence.
Qed.

Lemma nontemp_reg_diff:
  forall r r', is_nontemp_reg r = true -> is_nontemp_reg r' = false -> r <> r'.
Proof.
  intros. congruence.
Qed.

Hint Resolve is_nontemp_is_data nontemp_reg_diff: ppcgen.

Lemma ireg_of_not_GPR1:
  forall r, ireg_of r <> GPR1.
Proof.
  intro. case r; discriminate.
Qed.

Lemma preg_of_not_GPR1:
  forall r, preg_of r <> GPR1.
Proof.
  intro. case r; discriminate.
Qed.
Hint Resolve ireg_of_not_GPR1 preg_of_not_GPR1: ppcgen.

Lemma int_temp_for_diff:
  forall r, IR(int_temp_for r) <> preg_of r.
Proof.
  intros. unfold int_temp_for. destruct (mreg_eq r IT2).
  subst r. compute. congruence. 
  change (IR GPR12) with (preg_of IT2). red; intros; elim n.
  apply preg_of_injective; auto.
Qed.

(** Agreement between Mach register sets and PPC register sets. *)

Record agree (ms: Mach.regset) (sp: val) (rs: Asm.regset) : Prop := mkagree {
  agree_sp: rs#GPR1 = sp;
  agree_sp_def: sp <> Vundef;
  agree_mregs: forall r: mreg, Val.lessdef (ms r) (rs#(preg_of r))
}.

Lemma preg_val:
  forall ms sp rs r,
  agree ms sp rs -> Val.lessdef (ms r) rs#(preg_of r).
Proof.
  intros. eapply agree_mregs; eauto. 
Qed.

Lemma preg_vals:
  forall ms sp rs rl,
  agree ms sp rs -> Val.lessdef_list (List.map ms rl) (List.map rs (List.map preg_of rl)).
Proof.
  induction rl; intros; simpl.
  constructor.
  constructor. eapply preg_val; eauto. eauto.
Qed.

Lemma ireg_val:
  forall ms sp rs r,
  agree ms sp rs ->
  mreg_type r = Tint ->
  Val.lessdef (ms r) rs#(ireg_of r).
Proof.
  intros. replace (IR (ireg_of r)) with (preg_of r). eapply preg_val; eauto. 
  unfold preg_of. rewrite H0. auto.
Qed.

Lemma freg_val:
  forall ms sp rs r,
  agree ms sp rs ->
  mreg_type r = Tfloat ->
  Val.lessdef (ms r) rs#(freg_of r).
Proof.
  intros. replace (FR (freg_of r)) with (preg_of r). eapply preg_val; eauto. 
  unfold preg_of. rewrite H0. auto.
Qed.

Lemma sp_val:
  forall ms sp rs,
  agree ms sp rs ->
  sp = rs#GPR1.
Proof.
  intros. elim H; auto.
Qed.

Lemma agree_exten:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, is_data_reg r = true -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. inv H. constructor; auto. 
  intros. rewrite H0; auto with ppcgen.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', is_data_reg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. inv H. constructor; auto with ppcgen.
  intros. unfold Regmap.set. destruct (RegEq.eq r0 r).
  subst r0. auto.
  rewrite H1; auto with ppcgen. red; intros; elim n; apply preg_of_injective; auto.
Qed.
Hint Resolve agree_set_mreg: ppcgen.

Lemma agree_set_mireg:
  forall ms sp rs r v (rs': regset),
  agree ms sp rs ->
  Val.lessdef v (rs'#(ireg_of r)) ->
  mreg_type r = Tint ->
  (forall r', is_data_reg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. eapply agree_set_mreg; eauto.  unfold preg_of; rewrite H1; auto.
Qed.
Hint Resolve agree_set_mireg: ppcgen.

Lemma agree_set_mfreg:
  forall ms sp rs r v (rs': regset),
  agree ms sp rs ->
  Val.lessdef v (rs'#(freg_of r)) ->
  mreg_type r = Tfloat ->
  (forall r', is_data_reg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. eapply agree_set_mreg; eauto.  unfold preg_of; rewrite H1; auto.
Qed.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  is_data_reg r = false ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten with rs.
  auto. intros. apply Pregmap.gso. congruence.
Qed.
Hint Resolve agree_set_other: ppcgen.

Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_set_other. auto. auto.
Qed.
Hint Resolve agree_nextinstr: ppcgen.

Lemma agree_undef_regs:
  forall rl ms sp rs rs',
  agree ms sp rs ->
  (forall r, is_data_reg r = true -> ~In r (List.map preg_of rl) -> rs'#r = rs#r) ->
  agree (undef_regs rl ms) sp rs'.
Proof.
  induction rl; simpl; intros.
  apply agree_exten with rs; auto.
  apply IHrl with (rs#(preg_of a) <- (rs'#(preg_of a))).
  apply agree_set_mreg with rs; auto with ppcgen. 
  intros. unfold Pregmap.set. destruct (PregEq.eq r' (preg_of a)).
  congruence. auto.
  intros. unfold Pregmap.set. destruct (PregEq.eq r (preg_of a)).
  congruence. apply H0; auto. intuition congruence.
Qed.

Lemma agree_undef_temps:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, is_nontemp_reg r = true -> rs'#r = rs#r) ->
  agree (undef_temps ms) sp rs'.
Proof.
  unfold undef_temps. intros. apply agree_undef_regs with rs; auto.
  simpl. unfold preg_of; simpl. intros. intuition.
  apply H0. destruct r; simpl in *; auto.
  destruct i; intuition. destruct f; intuition.
Qed.
Hint Resolve agree_undef_temps: ppcgen.

Lemma agree_set_mreg_undef_temps:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', is_nontemp_reg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v (undef_temps ms)) sp rs'.
Proof.
  intros. apply agree_set_mreg with (rs'#(preg_of r) <- (rs#(preg_of r))).
  apply agree_undef_temps with rs; auto.
  intros. unfold Pregmap.set. destruct (PregEq.eq r0 (preg_of r)). 
  congruence. apply H1; auto. 
  auto.
  intros. rewrite Pregmap.gso; auto. 
Qed.

Lemma agree_set_twice_mireg:
  forall ms sp rs r v v1 v',
  agree (Regmap.set r v1 ms) sp rs ->
  mreg_type r = Tint ->
  Val.lessdef v v' ->
  agree (Regmap.set r v ms) sp (rs#(ireg_of r) <- v').
Proof.
  intros. inv H. 
  split. rewrite Pregmap.gso. auto. 
  generalize (ireg_of_not_GPR1 r); congruence.
  auto.
  intros. generalize (agree_mregs0 r0). 
  case (mreg_eq r0 r); intro.
  subst r0. repeat rewrite Regmap.gss. unfold preg_of; rewrite H0.
  rewrite Pregmap.gss. auto.
  repeat rewrite Regmap.gso; auto.
  rewrite Pregmap.gso. auto. 
  replace (IR (ireg_of r)) with (preg_of r).
  red; intros. elim n. apply preg_of_injective; auto.
  unfold preg_of. rewrite H0. auto.
Qed.

(** Useful properties of the PC and GPR0 registers. *)

Lemma nextinstr_inv:
  forall r rs, r <> PC -> (nextinstr rs)#r = rs#r.
Proof.
  intros. unfold nextinstr. apply Pregmap.gso. auto.
Qed.
Hint Resolve nextinstr_inv: ppcgen.

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
Hint Resolve gpr_or_zero_not_zero gpr_or_zero_zero: ppcgen.

(** Connection between Mach and Asm calling conventions for external
    functions. *)

Lemma extcall_arg_match:
  forall ms sp rs m m' l v,
  agree ms sp rs ->
  Mem.extends m m' ->
  Machsem.extcall_arg ms m sp l v ->
  exists v', Asm.extcall_arg rs m' l v' /\ Val.lessdef v v'.
Proof.
  intros. inv H1.
  exists (rs#(preg_of r)); split. constructor. eapply preg_val; eauto.
  unfold load_stack in H2.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ H) in A.
  exists v'; split; auto.
  destruct ty; econstructor.
  reflexivity. assumption.
  reflexivity. assumption.
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
  forall ms m m' sp rs sg args,
  agree ms sp rs -> Mem.extends m m' ->
  Machsem.extcall_arguments ms m sp sg args ->
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

(** * Correctness of PowerPC constructor functions *)

Ltac SIMP :=
  (rewrite nextinstr_inv || rewrite Pregmap.gss || rewrite Pregmap.gso); auto with ppcgen.

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
  intros. unfold compare_float. repeat SIMP.
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
  intros. unfold compare_sint. repeat SIMP.
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
  intros. unfold compare_uint. repeat SIMP.
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
  case (Int.eq (high_s n) Int.zero).
  (* addi *)
  exists (nextinstr (rs#r <- (Vint n))).
  split. apply exec_straight_one. 
  simpl. rewrite Int.add_zero_l. auto.
  reflexivity. 
  split. repeat SIMP. intros; repeat SIMP. 
  (* addis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  exists (nextinstr (rs#r <- (Vint n))).
  split. apply exec_straight_one. 
  simpl. rewrite Int.add_commut. 
  rewrite <- H. rewrite low_high_s. reflexivity.
  reflexivity. 
  split. repeat SIMP. intros; repeat SIMP. 
  (* addis + ori *)
  pose (rs1 := nextinstr (rs#r <- (Vint (Int.shl (high_u n) (Int.repr 16))))).
  exists (nextinstr (rs1#r <- (Vint n))).
  split. eapply exec_straight_two. 
  simpl. rewrite Int.add_zero_l. reflexivity.
  simpl. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  unfold Val.or. rewrite low_high_u. reflexivity.
  reflexivity. reflexivity.
  unfold rs1. split. repeat SIMP. intros; repeat SIMP. 
Qed.

(** Add integer immediate. *)

Lemma addimm_correct:
  forall r1 r2 n k rs m,
  r1 <> GPR0 ->
  r2 <> GPR0 ->
  exists rs',
     exec_straight (addimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm.
  (* addi *)
  case (Int.eq (high_s n) Int.zero).
  exists (nextinstr (rs#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_one. 
  simpl. rewrite gpr_or_zero_not_zero; auto.
  reflexivity. 
  split. repeat SIMP. intros. repeat SIMP.
  (* addis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_one.
  simpl. rewrite gpr_or_zero_not_zero; auto.
  generalize (low_high_s n). rewrite H1. rewrite Int.add_zero. intro.
  rewrite H2. auto.
  reflexivity.
  split. repeat SIMP. intros; repeat SIMP.
  (* addis + addi *)
  pose (rs1 := nextinstr (rs#r1 <- (Val.add rs#r2 (Vint (Int.shl (high_s n) (Int.repr 16)))))).
  exists (nextinstr (rs1#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_two with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero; auto. 
  simpl. rewrite gpr_or_zero_not_zero; auto.
  unfold rs1 at 1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss.
  rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
  reflexivity. reflexivity. 
  unfold rs1; split. repeat SIMP. intros; repeat SIMP.
Qed. 

(** And integer immediate. *)

Lemma andimm_base_correct:
  forall r1 r2 n k (rs : regset) m,
  r2 <> GPR0 ->
  let v := Val.and rs#r2 (Vint n) in
  exists rs',
     exec_straight (andimm_base r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ rs'#CR0_2 = Val.cmp Ceq v Vzero
  /\ forall r', is_data_reg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm_base.
  case (Int.eq (high_u n) Int.zero).
  (* andi *)
  exists (nextinstr (compare_sint (rs#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. apply exec_straight_one. reflexivity. reflexivity.
  split. rewrite D; auto with ppcgen. SIMP. 
  split. auto.
  intros. rewrite D; auto with ppcgen. SIMP.
  (* andis *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (compare_sint (rs#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H0. rewrite Int.or_zero. 
  intro. rewrite H1. reflexivity. reflexivity.
  split. rewrite D; auto with ppcgen. SIMP. 
  split. auto.
  intros. rewrite D; auto with ppcgen. SIMP.
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
  split. rewrite D; auto with ppcgen. SIMP. 
  split. auto.
  intros. rewrite D; auto with ppcgen. SIMP.
Qed.

Lemma andimm_correct:
  forall r1 r2 n k (rs : regset) m,
  r2 <> GPR0 ->
  exists rs',
     exec_straight (andimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.and rs#r2 (Vint n)
  /\ forall r', is_data_reg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold andimm. destruct (is_rlw_mask n).
  (* turned into rlw *)
  exists (nextinstr (rs#r1 <- (Val.and rs#r2 (Vint n)))).
  split. apply exec_straight_one. simpl. rewrite Val.rolm_zero. auto. reflexivity.
  split. SIMP. apply Pregmap.gss. 
  intros. SIMP. apply Pregmap.gso; auto with ppcgen.
  (* andimm_base *)
  destruct (andimm_base_correct r1 r2 n k rs m) as [rs' [A [B [C D]]]]; auto.
  exists rs'; auto.
Qed.

(** Or integer immediate. *)

Lemma orimm_correct:
  forall r1 (r2: ireg) n k (rs : regset) m,
  let v := Val.or rs#r2 (Vint n) in
  exists rs',
     exec_straight (orimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold orimm.
  case (Int.eq (high_u n) Int.zero).
  (* ori *)
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. reflexivity. reflexivity.
  split. repeat SIMP.
  intros. repeat SIMP.
  (* oris *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H. rewrite Int.or_zero. 
  intro. rewrite H0. reflexivity. reflexivity.
  split. repeat SIMP.
  intros. repeat SIMP.
  (* oris + ori *)
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  split. repeat rewrite nextinstr_inv; auto with ppcgen. repeat rewrite Pregmap.gss.   rewrite Val.or_assoc. simpl. rewrite low_high_u. reflexivity. 
  intros. repeat SIMP.
Qed.

(** Xor integer immediate. *)

Lemma xorimm_correct:
  forall r1 (r2: ireg) n k (rs : regset) m,
  let v := Val.xor rs#r2 (Vint n) in
  exists rs',
     exec_straight (xorimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold xorimm.
  case (Int.eq (high_u n) Int.zero).
  (* xori *)
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. reflexivity. reflexivity.
  split. repeat SIMP. intros. repeat SIMP.
  (* xoris *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. simpl.
  generalize (low_high_u_xor n). rewrite H. rewrite Int.xor_zero. 
  intro. rewrite H0. reflexivity. reflexivity.
  split. repeat SIMP. intros. repeat SIMP.
  (* xoris + xori *)
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  split. repeat rewrite nextinstr_inv; auto with ppcgen. repeat rewrite Pregmap.gss.
  rewrite Val.xor_assoc. simpl. rewrite low_high_u_xor. reflexivity. 
  intros. repeat SIMP.
Qed.

(** Rotate and mask. *)

Lemma rolm_correct:
  forall r1 r2 amount mask k (rs : regset) m,
  r1 <> GPR0 ->
  exists rs',
     exec_straight (rolm r1 r2 amount mask k) rs m  k rs' m
  /\ rs'#r1 = Val.rolm rs#r2 amount mask
  /\ forall r', is_data_reg r' = true -> r' <> r1 -> rs'#r' = rs#r'.
Proof.
  intros. unfold rolm. destruct (is_rlw_mask mask).
  (* rlwinm *)
  exists (nextinstr (rs#r1 <- (Val.rolm rs#r2 amount mask))).
  split. apply exec_straight_one; auto.
  split. SIMP. apply Pregmap.gss.
  intros. SIMP. apply Pregmap.gso; auto.
  (* rlwinm ; andimm *)
  set (rs1 := nextinstr (rs#r1 <- (Val.rolm rs#r2 amount Int.mone))).
  destruct (andimm_base_correct r1 r1 mask k rs1 m) as [rs' [A [B [C D]]]]; auto.
  exists rs'.
  split. eapply exec_straight_step; eauto. auto. auto. 
  split. rewrite B. unfold rs1. SIMP. rewrite Pregmap.gss. 
  destruct (rs r2); simpl; auto. unfold Int.rolm. rewrite Int.and_assoc. 
  decEq; decEq; decEq. rewrite Int.and_commut. apply Int.and_mone.
  intros. rewrite D; auto. unfold rs1; SIMP. apply Pregmap.gso; auto.
Qed.

(** Indexed memory loads. *)

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) m v,
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  mreg_type dst = ty ->
  base <> GPR0 ->
  exists rs',
     exec_straight (loadind base ofs ty dst k) rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> preg_of dst -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  intros. unfold loadind. destruct (Int.eq (high_s ofs) Int.zero).
(* one load *)
  exists (nextinstr (rs#(preg_of dst) <- v)); split.
  unfold preg_of. rewrite H0.
  destruct ty; apply exec_straight_one; auto with ppcgen; simpl.
  unfold load1. rewrite gpr_or_zero_not_zero; auto.
  simpl in *. rewrite H. auto.
  unfold load1. rewrite gpr_or_zero_not_zero; auto.
  simpl in *. rewrite H. auto.
  split. repeat SIMP. intros. repeat SIMP.
(* loadimm + one load *)
  exploit (loadimm_correct GPR0 ofs); eauto. intros [rs' [A [B C]]]. 
  exists (nextinstr (rs'#(preg_of dst) <- v)); split.
  eapply exec_straight_trans. eexact A.
  unfold preg_of. rewrite H0.
  destruct ty; apply exec_straight_one; auto with ppcgen; simpl.
  unfold load2. rewrite B. rewrite C; auto with ppcgen. simpl in H. rewrite H. auto.
  unfold load2. rewrite B. rewrite C; auto with ppcgen. simpl in H. rewrite H. auto.
  split. repeat SIMP.
  intros. repeat SIMP. 
Qed.

(** Indexed memory stores. *)

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) m m',
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  mreg_type src = ty ->
  base <> GPR0 ->
  exists rs',
     exec_straight (storeind src base ofs ty k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR0 -> rs'#r = rs#r.
Proof.
  intros. unfold storeind. destruct (Int.eq (high_s ofs) Int.zero).
(* one store *)
  exists (nextinstr rs); split.
  destruct ty; apply exec_straight_one; auto with ppcgen; simpl.
  unfold store1. rewrite gpr_or_zero_not_zero; auto.
  simpl in *. unfold preg_of in H; rewrite H0 in H. rewrite H. auto.
  unfold store1. rewrite gpr_or_zero_not_zero; auto.
  simpl in *. unfold preg_of in H; rewrite H0 in H. rewrite H. auto.
  intros. apply nextinstr_inv; auto.
(* loadimm + one store *)
  exploit (loadimm_correct GPR0 ofs); eauto. intros [rs' [A [B C]]]. 
  assert (rs' base = rs base). apply C; auto with ppcgen. 
  assert (rs' (preg_of src) = rs (preg_of src)). apply C; auto with ppcgen. 
  exists (nextinstr rs').
  split. eapply exec_straight_trans. eexact A. 
  destruct ty; apply exec_straight_one; auto with ppcgen; simpl.
  unfold store2. replace (IR (ireg_of src)) with (preg_of src). 
  rewrite H2; rewrite H3. rewrite B. simpl in H. rewrite H. auto.
  unfold preg_of; rewrite H0; auto.
  unfold store2. replace (FR (freg_of src)) with (preg_of src). 
  rewrite H2; rewrite H3. rewrite B. simpl in H. rewrite H. auto.
  unfold preg_of; rewrite H0; auto.
  intros. rewrite nextinstr_inv; auto. 
Qed.

(** Float comparisons. *)

Lemma floatcomp_correct:
  forall cmp (r1 r2: freg) k rs m,
  exists rs',
     exec_straight (floatcomp cmp r1 r2 k) rs m k rs' m
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
  split. generalize H0; intros [EQ|[EQ|[EQ|EQ]]]; subst cmp;
  apply exec_straight_one; reflexivity.
  split. 
  generalize H0; intros [EQ|[EQ|[EQ|EQ]]]; subst cmp; simpl; auto. 
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
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

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

Ltac UseTypeInfo :=
  match goal with
  | T: (mreg_type ?r = ?t), H: context[preg_of ?r] |- _ =>
      unfold preg_of in H; UseTypeInfo
  | T: (mreg_type ?r = ?t), H: context[mreg_type ?r] |- _ =>
      rewrite T in H; UseTypeInfo
  | T: (mreg_type ?r = ?t) |- context[preg_of ?r] =>
      unfold preg_of; UseTypeInfo
  | T: (mreg_type ?r = ?t) |- context[mreg_type ?r] =>
      rewrite T; UseTypeInfo
  | _ => idtac
  end.

(** Translation of conditions. *)

Lemma transl_cond_correct_1:
  forall cond args k rs m,
  map mreg_type args = type_of_condition cond ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) = 
       (if snd (crbit_for_cond cond)
        then Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)
        else Val.notbool (Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)))
  /\ forall r, is_data_reg r = true -> rs'#r = rs#r.
Proof.
  intros.
  destruct cond; simpl in H; TypeInv; simpl; UseTypeInfo.
  (* Ccomp *)
  fold (Val.cmp c (rs (ireg_of m0)) (rs (ireg_of m1))).
  destruct (compare_sint_spec rs (rs (ireg_of m0)) (rs (ireg_of m1)))
  as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  auto with ppcgen.
  (* Ccompu *)
  fold (Val.cmpu (Mem.valid_pointer m) c (rs (ireg_of m0)) (rs (ireg_of m1))).
  destruct (compare_uint_spec rs m (rs (ireg_of m0)) (rs (ireg_of m1)))
  as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  auto with ppcgen.
  (* Ccompimm *)
  fold (Val.cmp c (rs (ireg_of m0)) (Vint i)).
  case (Int.eq (high_s i) Int.zero).
  destruct (compare_sint_spec rs (rs (ireg_of m0)) (Vint i))
  as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl. eauto. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  auto with ppcgen.
  generalize (loadimm_correct GPR0 i (Pcmpw (ireg_of m0) GPR0 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_sint_spec rs1 (rs (ireg_of m0)) (Vint i))
  as [A [B [C D]]].
  assert (rs1 (ireg_of m0) = rs (ireg_of m0)).
    apply OTH1; auto with ppcgen. 
  exists (nextinstr (compare_sint rs1 (rs1 (ireg_of m0)) (Vint i))).
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. rewrite RES1; rewrite H; auto.
  reflexivity. 
  split. rewrite H. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  intros. rewrite H; rewrite D; auto with ppcgen.
  (* Ccompuimm *)
  fold (Val.cmpu (Mem.valid_pointer m) c (rs (ireg_of m0)) (Vint i)).
  case (Int.eq (high_u i) Int.zero).
  destruct (compare_uint_spec rs m (rs (ireg_of m0)) (Vint i))
  as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl. eauto. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  auto with ppcgen.
  generalize (loadimm_correct GPR0 i (Pcmplw (ireg_of m0) GPR0 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_uint_spec rs1 m (rs (ireg_of m0)) (Vint i))
  as [A [B [C D]]].
  assert (rs1 (ireg_of m0) = rs (ireg_of m0)). apply OTH1; auto with ppcgen.
  exists (nextinstr (compare_uint rs1 m (rs1 (ireg_of m0)) (Vint i))).
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. rewrite RES1; rewrite H; auto.
  reflexivity. 
  split. rewrite H. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  intros. rewrite H; rewrite D; auto with ppcgen.
  (* Ccompf *)
  fold (Val.cmpf c (rs (freg_of m0)) (rs (freg_of m1))).
  destruct (floatcomp_correct c (freg_of m0) (freg_of m1) k rs m)
  as [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  split. apply RES. 
  auto with ppcgen.
  (* Cnotcompf *)
  rewrite Val.notbool_negb_3. rewrite Val.notbool_idem4.
  fold (Val.cmpf c (rs (freg_of m0)) (rs (freg_of m1))).
  destruct (floatcomp_correct c (freg_of m0) (freg_of m1) k rs m)
  as [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  split. rewrite RES. destruct (snd (crbit_for_fcmp c)); auto. 
  auto with ppcgen.
  (* Cmaskzero *)
  destruct (andimm_base_correct GPR0 (ireg_of m0) i k rs m)
  as [rs' [A [B [C D]]]]. auto with ppcgen.
  exists rs'. split. assumption. 
  split. rewrite C. destruct (rs (ireg_of m0)); auto. 
  auto with ppcgen.
  (* Cmasknotzero *)
  destruct (andimm_base_correct GPR0 (ireg_of m0) i k rs m)
  as [rs' [A [B [C D]]]]. auto with ppcgen.
  exists rs'. split. assumption. 
  split. rewrite C. destruct (rs (ireg_of m0)); auto.
  fold (option_map negb (Some (Int.eq (Int.and i0 i) Int.zero))).
  rewrite Val.notbool_negb_3. rewrite Val.notbool_idem4. auto. 
  auto with ppcgen.
Qed.

Lemma transl_cond_correct_2:
  forall cond args k rs m b,
  map mreg_type args = type_of_condition cond ->
  eval_condition cond (map rs (map preg_of args)) m = Some b ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) = 
       (if snd (crbit_for_cond cond)
        then Val.of_bool b
        else Val.notbool (Val.of_bool b))
  /\ forall r, is_data_reg r = true -> rs'#r = rs#r.
Proof.
  intros.
  replace (Val.of_bool b)
  with (Val.of_optbool (eval_condition cond rs ## (preg_of ## args) m)).
  eapply transl_cond_correct_1; eauto. 
  rewrite H0; auto.
Qed.

Lemma transl_cond_correct:
  forall cond args k ms sp rs m b m',
  map mreg_type args = type_of_condition cond ->
  agree ms sp rs ->
  eval_condition cond (map ms args) m = Some b ->
  Mem.extends m m' ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m' k rs' m'
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
  unfold Int.add_carry, Int.eq. 
  rewrite Int.unsigned_zero.  rewrite Int.unsigned_mone.
  unfold negb, Val.of_bool, Vtrue, Vfalse.
  destruct (zeq (Int.unsigned i) 0); decEq.
  apply zlt_true. omega.
  apply zlt_false. generalize (Int.unsigned_range i). omega.
Qed.

Lemma transl_cond_op_correct:
  forall cond args r k rs m,
  mreg_type r = Tint ->
  map mreg_type args = type_of_condition cond ->
  exists rs',
     exec_straight (transl_cond_op cond args r k) rs m k rs' m
  /\ rs'#(ireg_of r) = Val.of_optbool (eval_condition cond (map rs (map preg_of args)) m)
  /\ forall r', is_data_reg r' = true -> r' <> ireg_of r -> rs'#r' = rs#r'.
Proof.
  intros until args. unfold transl_cond_op.
  destruct (classify_condition cond args);
  intros until m; intros TY1 TY2; simpl in TY2.
(* eq 0 *)
  inv TY2. simpl. unfold preg_of; rewrite H0. 
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. repeat SIMP. destruct (rs (ireg_of r)); simpl; auto. 
  apply add_carry_eq0.
  intros; repeat SIMP.
(* ne 0 *)
  inv TY2. simpl. unfold preg_of; rewrite H0.
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. repeat SIMP. rewrite gpr_or_zero_not_zero; auto with ppcgen.
  destruct (rs (ireg_of r)); simpl; auto.
  apply add_carry_ne0.
  intros; repeat SIMP.
(* ge 0 *)
  inv TY2. simpl. unfold preg_of; rewrite H0.
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity.
  split. repeat SIMP. rewrite Val.rolm_ge_zero. auto.  
  intros; repeat SIMP.
(* lt 0 *)
  inv TY2. simpl. unfold preg_of; rewrite H0.
  econstructor; split.
  apply exec_straight_one; simpl; reflexivity.
  split. repeat SIMP. rewrite Val.rolm_lt_zero. auto. 
  intros; repeat SIMP.
(* default *)
  set (bit := fst (crbit_for_cond c)).
  set (isset := snd (crbit_for_cond c)).
  set (k1 :=
        Pmfcrbit (ireg_of r) bit ::
        (if isset
         then k
         else Pxori (ireg_of r) (ireg_of r) (Cint Int.one) :: k)).
  generalize (transl_cond_correct_1 c rl k1 rs m TY2).
  fold bit; fold isset. 
  intros [rs1 [EX1 [RES1 AG1]]].
  destruct isset.
  (* bit set *)
  econstructor; split.  eapply exec_straight_trans. eexact EX1. 
  unfold k1. apply exec_straight_one; simpl; reflexivity. 
  split. repeat SIMP. intros; repeat SIMP.
  (* bit clear *)
  econstructor; split.  eapply exec_straight_trans. eexact EX1. 
  unfold k1. eapply exec_straight_two; simpl; reflexivity. 
  split. repeat SIMP. rewrite RES1. 
  destruct (eval_condition c rs ## (preg_of ## rl) m). destruct b; auto. auto.
  intros; repeat SIMP.
Qed.

(** Translation of arithmetic operations. *)

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | split; intros; (repeat SIMP; fail) ].

Lemma transl_op_correct_aux:
  forall op args res k (rs: regset) m v,
  wt_instr (Mop op args res) ->
  eval_operation ge (rs#GPR1) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight (transl_op op args res k) rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r,
     match op with Omove => is_data_reg r = true | _ => is_nontemp_reg r = true end ->
     r <> preg_of res -> rs'#r = rs#r.
Proof.
  intros until v; intros WT EV.
  inv WT.
  (* Omove *)
  simpl in *. inv EV. 
  exists (nextinstr (rs#(preg_of res) <- (rs#(preg_of r1)))).
  split. unfold preg_of. rewrite <- H0.
  destruct (mreg_type r1); apply exec_straight_one; auto.
  split. repeat SIMP. intros; repeat SIMP.
  (* Other instructions *)
  destruct op; simpl; simpl in H3; injection H3; clear H3; intros;
  TypeInv; simpl in *; UseTypeInfo; inv EV; try (TranslOpSimpl).
  (* Ointconst *)
  destruct (loadimm_correct (ireg_of res) i k rs m) as [rs' [A [B C]]]. 
  exists rs'. split. auto. split. auto. auto with ppcgen.
  (* Oaddrsymbol *)
  change (symbol_address ge i i0) with (symbol_offset ge i i0).
  set (v' := symbol_offset ge i i0).
  caseEq (symbol_is_small_data i i0); intro SD.
  (* small data *)
  econstructor; split. apply exec_straight_one; simpl; reflexivity.
  split. repeat SIMP.
  rewrite (small_data_area_addressing _ _ _ SD). unfold v', symbol_offset. 
  destruct (Genv.find_symbol ge i); auto. rewrite Int.add_zero; auto. 
  intros; repeat SIMP.
  (* not small data *)
Opaque Val.add.
  econstructor; split. eapply exec_straight_two; simpl; reflexivity.
  split. repeat SIMP. rewrite gpr_or_zero_zero.
  rewrite gpr_or_zero_not_zero; auto with ppcgen. repeat SIMP. 
  rewrite (Val.add_commut Vzero). rewrite high_half_zero. 
  rewrite Val.add_commut. rewrite low_high_half. auto.
  intros; repeat SIMP.
  (* Oaddrstack *)
  destruct (addimm_correct (ireg_of res) GPR1 i k rs m) as [rs' [EX [RES OTH]]].
    auto with ppcgen. congruence.
  exists rs'; auto with ppcgen.
  (* Oaddimm *)
  destruct (addimm_correct (ireg_of res) (ireg_of m0) i k rs m) as [rs' [A [B C]]]; auto with ppcgen.
  exists rs'; auto with ppcgen.
  (* Osubimm *)
  case (Int.eq (high_s i) Int.zero).
  TranslOpSimpl.
  destruct (loadimm_correct GPR0 i (Psubfc (ireg_of res) (ireg_of m0) GPR0 :: k) rs m) as [rs1 [EX [RES OTH]]].
  econstructor; split.
  eapply exec_straight_trans. eexact EX. apply exec_straight_one; simpl; reflexivity.
  split. repeat SIMP. rewrite RES. rewrite OTH; auto with ppcgen. 
  intros; repeat SIMP. 
  (* Omulimm *)
  case (Int.eq (high_s i) Int.zero).
  TranslOpSimpl.
  destruct (loadimm_correct GPR0 i (Pmullw (ireg_of res) (ireg_of m0) GPR0 :: k) rs m) as [rs1 [EX [RES OTH]]].
  econstructor; split.
  eapply exec_straight_trans. eexact EX. apply exec_straight_one; simpl; reflexivity.
  split. repeat SIMP. rewrite RES. rewrite OTH; auto with ppcgen. 
  intros; repeat SIMP.
  (* Odivs *)
  replace v with (Val.maketotal (Val.divs (rs (ireg_of m0)) (rs (ireg_of m1)))).
  TranslOpSimpl. 
  rewrite H2; auto.
  (* Odivu *)
  replace v with (Val.maketotal (Val.divu (rs (ireg_of m0)) (rs (ireg_of m1)))).
  TranslOpSimpl. 
  rewrite H2; auto.
  (* Oand *)
  set (v' := Val.and (rs (ireg_of m0)) (rs (ireg_of m1))) in *.
  pose (rs1 := rs#(ireg_of res) <- v').
  generalize (compare_sint_spec rs1 v' Vzero).
  intros [A [B [C D]]].
  econstructor; split. apply exec_straight_one; simpl; reflexivity.
  split. rewrite D; auto with ppcgen. unfold rs1. SIMP. 
  intros. rewrite D; auto with ppcgen. unfold rs1. SIMP.
  (* Oandimm *)
  destruct (andimm_correct (ireg_of res) (ireg_of m0) i k rs m) as [rs' [A [B C]]]; auto with ppcgen.
  exists rs'; auto with ppcgen.
  (* Oorimm *)
  destruct (orimm_correct (ireg_of res) (ireg_of m0) i k rs m) as [rs' [A [B C]]]. 
  exists rs'; auto with ppcgen.
  (* Oxorimm *)
  destruct (xorimm_correct (ireg_of res) (ireg_of m0) i k rs m) as [rs' [A [B C]]]. 
  exists rs'; auto with ppcgen.
  (* Onor *)
  replace (Val.notint (rs (ireg_of m0)))
     with (Val.notint (Val.or (rs (ireg_of m0)) (rs (ireg_of m0)))).
  TranslOpSimpl.
  destruct (rs (ireg_of m0)); simpl; auto. rewrite Int.or_idem. auto.
  (* Oshrximm *)
  econstructor; split.
  eapply exec_straight_two; simpl; reflexivity. 
  split. repeat SIMP. apply Val.shrx_carry. auto. 
  intros; repeat SIMP. 
  (* Orolm *)
  destruct (rolm_correct (ireg_of res) (ireg_of m0) i i0 k rs m) as [rs' [A [B C]]]; auto with ppcgen.
  exists rs'; auto with ppcgen.
  (* Oroli *)
  destruct (mreg_eq m0 res). subst m0.
  TranslOpSimpl.
  econstructor; split.
  eapply exec_straight_three; simpl; reflexivity. 
  split. repeat SIMP. intros; repeat SIMP.
  (* Ointoffloat *)
  replace v with (Val.maketotal (Val.intoffloat (rs (freg_of m0)))).
  TranslOpSimpl.
  rewrite H2; auto.
  (* Ocmp *)
  destruct (transl_cond_op_correct c args res k rs m) as [rs' [A [B C]]]; auto.
  exists rs'; auto with ppcgen.
Qed.

Lemma transl_op_correct:
  forall op args res k ms sp rs m v m',
  wt_instr (Mop op args res) ->
  agree ms sp rs ->
  eval_operation ge sp op (map ms args) m = Some v ->
  Mem.extends m m' ->
  exists rs',
     exec_straight (transl_op op args res k) rs m' k rs' m'
  /\ agree (Regmap.set res v (undef_op op ms)) sp rs'.
Proof.
  intros. 
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eauto. 
  intros [v' [A B]].  rewrite (sp_val _ _ _ H0) in A. 
  exploit transl_op_correct_aux; eauto. intros [rs' [P [Q R]]].
  rewrite <- Q in B.
  exists rs'; split. eexact P. 
  unfold undef_op. destruct op;
  (apply agree_set_mreg_undef_temps with rs || apply agree_set_mreg with rs);
  auto.
Qed.

Lemma transl_load_store_correct:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
    addr args (temp: ireg) k ms sp rs m ms' m',
  (forall cst (r1: ireg) (rs1: regset) k,
    eval_addressing ge sp addr (map rs (map preg_of args)) =
                Some(Val.add (gpr_or_zero rs1 r1) (const_low ge cst)) ->
    (forall (r: preg), r <> PC -> r <> temp -> rs1 r = rs r) ->
    exists rs',
    exec_straight (mk1 cst r1 :: k) rs1 m k rs' m' /\
    agree ms' sp rs') ->
  (forall (r1 r2: ireg) k,
    eval_addressing ge sp addr (map rs (map preg_of args)) = Some(Val.add rs#r1 rs#r2) ->
    exists rs',
    exec_straight (mk2 r1 r2 :: k) rs m k rs' m' /\
    agree ms' sp rs') ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  temp <> GPR0 ->
  exists rs',
    exec_straight (transl_load_store mk1 mk2 addr args temp k) rs m
                        k rs' m'
  /\ agree ms' sp rs'.
Proof.
  intros. destruct addr; simpl in H2; TypeInv; simpl.
  (* Aindexed *)
  case (Int.eq (high_s i) Int.zero).
  (* Aindexed short *)
  apply H. 
  simpl. UseTypeInfo. rewrite gpr_or_zero_not_zero; auto with ppcgen.
  auto.
  (* Aindexed long *)
  set (rs1 := nextinstr (rs#temp <- (Val.add (rs (ireg_of m0)) (Vint (Int.shl (high_s i) (Int.repr 16)))))).
  exploit (H (Cint (low_s i)) temp rs1 k).
    simpl. UseTypeInfo. rewrite gpr_or_zero_not_zero; auto. 
    unfold rs1; repeat SIMP. rewrite Val.add_assoc.
Transparent Val.add.
    simpl. rewrite low_high_s. auto.
    intros; unfold rs1; repeat SIMP.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero; auto with ppcgen. auto. 
  auto. auto.
  (* Aindexed2 *)
  apply H0. 
  simpl. UseTypeInfo; auto.
  (* Aglobal *)
  case_eq (symbol_is_small_data i i0); intro SISD.
  (* Aglobal from small data *)
  apply H. rewrite gpr_or_zero_zero. simpl const_low. 
  rewrite small_data_area_addressing; auto. simpl. 
  unfold symbol_address, symbol_offset. 
  destruct (Genv.find_symbol ge i); auto. rewrite Int.add_zero. auto.
  auto.
  (* Aglobal general case *)
  set (rs1 := nextinstr (rs#temp <- (const_high ge (Csymbol_high i i0)))).
  exploit (H (Csymbol_low i i0) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; auto. 
    unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss.
    unfold const_high, const_low. 
    set (v := symbol_offset ge i i0).
    symmetry. rewrite Val.add_commut. unfold v. rewrite low_high_half. auto. 
    discriminate.
    intros; unfold rs1. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_zero. 
  rewrite Val.add_commut. unfold const_high. 
  rewrite high_half_zero.
  reflexivity. reflexivity.
  assumption. assumption.
  (* Abased *)
  set (rs1 := nextinstr (rs#temp <- (Val.add (rs (ireg_of m0)) (const_high ge (Csymbol_high i i0))))).
  exploit (H (Csymbol_low i i0) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; auto. 
    unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss.
    rewrite Val.add_assoc. 
    unfold const_high, const_low. 
    set (v := symbol_offset ge i i0).
    symmetry. rewrite Val.add_commut. decEq. decEq. 
    unfold v. rewrite Val.add_commut. rewrite low_high_half. auto. 
    UseTypeInfo. auto. discriminate. 
    intros. unfold rs1. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_not_zero; auto with ppcgen. auto.
  assumption. assumption.
  (* Ainstack *)
  case (Int.eq (high_s i) Int.zero).
  apply H. simpl. rewrite gpr_or_zero_not_zero; auto with ppcgen. 
  rewrite (sp_val ms sp rs); auto. auto.
  set (rs1 := nextinstr (rs#temp <- (Val.add sp (Vint (Int.shl (high_s i) (Int.repr 16)))))).
  exploit (H (Cint (low_s i)) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; auto. 
    unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss.
    rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
    congruence.
    intros. unfold rs1. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_not_zero; auto with ppcgen.
  rewrite <- (sp_val ms sp rs); auto. auto.
  assumption. assumption.
Qed.

(** Translation of memory loads. *)

Lemma transl_load_correct:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
    chunk addr args k ms sp rs m m' dst a v,
  (forall cst (r1: ireg) (rs1: regset),
    exec_instr ge fn (mk1 cst r1) rs1 m' =
    load1 ge chunk (preg_of dst) cst r1 rs1 m') ->
  (forall (r1 r2: ireg) (rs1: regset),
    exec_instr ge fn (mk2 r1 r2) rs1 m' =
    load2 chunk (preg_of dst) r1 r2 rs1 m') ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.loadv chunk m a = Some v ->
  Mem.extends m m' ->
  exists rs',
    exec_straight (transl_load_store mk1 mk2 addr args GPR12 k) rs m'
                        k rs' m'
  /\ agree (Regmap.set dst v (undef_temps ms)) sp rs'.
Proof.
  intros.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eauto. 
  intros [a' [A B]]. 
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  apply transl_load_store_correct with ms; auto.
(* mk1 *)
  intros. exists (nextinstr (rs1#(preg_of dst) <- v')). 
  split. apply exec_straight_one. rewrite H.
  unfold load1. rewrite A in H6. inv H6. rewrite C. auto. 
  unfold nextinstr. SIMP. decEq. SIMP. apply sym_not_equal; auto with ppcgen.
  apply agree_set_mreg with rs1. 
  apply agree_undef_temps with rs; auto with ppcgen.
  repeat SIMP. 
  intros; repeat SIMP.
(* mk2 *)
  intros. exists (nextinstr (rs#(preg_of dst) <- v')). 
  split. apply exec_straight_one. rewrite H0. 
  unfold load2. rewrite A in H6. inv H6. rewrite C. auto.
  unfold nextinstr. SIMP. decEq. SIMP. apply sym_not_equal; auto with ppcgen.
  apply agree_set_mreg with rs.
  apply agree_undef_temps with rs; auto with ppcgen.
  repeat SIMP. 
  intros; repeat SIMP.
(* not GPR0 *)
  congruence.
Qed.

(** Translation of memory stores. *)

Lemma transl_store_correct:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
    chunk addr args k ms sp rs m src a m' m1,
  (forall cst (r1: ireg) (rs1 rs2: regset) (m2: mem),
    store1 ge chunk (preg_of src) cst r1 rs1 m1 = OK rs2 m2 ->
    exists rs3,
    exec_instr ge fn (mk1 cst r1) rs1 m1 = OK rs3 m2
    /\ (forall (r: preg), r <> FPR13 -> rs3 r = rs2 r)) ->
  (forall (r1 r2: ireg) (rs1 rs2: regset) (m2: mem),
    store2 chunk (preg_of src) r1 r2 rs1 m1 = OK rs2 m2 ->
    exists rs3,
    exec_instr ge fn (mk2 r1 r2) rs1 m1 = OK rs3 m2
    /\ (forall (r: preg), r <> FPR13 -> rs3 r = rs2 r)) ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.storev chunk m a (ms src) = Some m' ->
  Mem.extends m m1 ->
  exists m1',
     Mem.extends m' m1'
  /\ exists rs',
       exec_straight (transl_load_store mk1 mk2 addr args (int_temp_for src) k) rs m1
                     k rs' m1'
       /\ agree (undef_temps ms) sp rs'.
Proof.
  intros.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eauto. 
  intros [a' [A B]].
  assert (Z: Val.lessdef (ms src) (rs (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m1' [C D]].
  exists m1'; split; auto.
  apply transl_load_store_correct with ms; auto.
(* mk1 *)
  intros.
  exploit (H cst r1 rs1 (nextinstr rs1) m1').
  unfold store1. rewrite A in H6. inv H6. 
  replace (rs1 (preg_of src)) with (rs (preg_of src)).
  rewrite C. auto.
  symmetry. apply H7. auto with ppcgen. 
  apply sym_not_equal. apply int_temp_for_diff.
  intros [rs3 [U V]].
  exists rs3; split.
  apply exec_straight_one. auto. rewrite V; auto with ppcgen. 
  apply agree_undef_temps with rs. auto. 
  intros. rewrite V; auto with ppcgen. SIMP. apply H7; auto with ppcgen.
  unfold int_temp_for. destruct (mreg_eq src IT2); auto with ppcgen.
(* mk2 *)
  intros.
  exploit (H0 r1 r2 rs (nextinstr rs) m1').
  unfold store2. rewrite A in H6. inv H6. rewrite C. auto. 
  intros [rs3 [U V]].
  exists rs3; split.
  apply exec_straight_one. auto. rewrite V; auto with ppcgen. 
  eapply agree_undef_temps; eauto. intros. 
  rewrite V; auto with ppcgen. 
  unfold int_temp_for. destruct (mreg_eq src IT2); congruence.
Qed.

End STRAIGHTLINE.


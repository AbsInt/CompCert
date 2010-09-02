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
Require Import Machconcr.
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

Definition is_data_reg (r: preg) : Prop :=
  match r with
  | IR GPR0 => False
  | PC => False    | LR => False    | CTR => False
  | CR0_0 => False | CR0_1 => False | CR0_2 => False | CR0_3 => False
  | CARRY => False
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

Lemma ireg_of_not_GPR1:
  forall r, ireg_of r <> GPR1.
Proof.
  intro. case r; discriminate.
Qed.
Lemma ireg_of_not_GPR0:
  forall r, ireg_of r <> GPR0.
Proof.
  intro. case r; discriminate.
Qed.
Hint Resolve ireg_of_not_GPR1 ireg_of_not_GPR0: ppcgen.

Lemma preg_of_not:
  forall r1 r2, ~(is_data_reg r2) -> preg_of r1 <> r2.
Proof.
  intros; red; intro. subst r2. elim H. apply preg_of_is_data_reg.
Qed.
Hint Resolve preg_of_not: ppcgen.

Lemma preg_of_not_GPR1:
  forall r, preg_of r <> GPR1.
Proof.
  intro. case r; discriminate.
Qed.
Hint Resolve preg_of_not_GPR1: ppcgen.

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

Lemma agree_exten_1:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, is_data_reg r -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. inv H. constructor.
  apply H0. exact I.
  auto.
  intros. rewrite H0. auto. apply preg_of_is_data_reg.
Qed.

Lemma agree_exten_2:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r,
     r <> IR GPR0 ->
     r <> PC -> r <> LR -> r <> CTR ->
     r <> CR0_0 -> r <> CR0_1 -> r <> CR0_2 -> r <> CR0_3 ->
     r <> CARRY ->
     rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. apply agree_exten_1 with rs. auto.
  intros. apply H0; (red; intro; subst r; elim H1).
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v v',
  agree ms sp rs ->
  Val.lessdef v v' ->
  agree (Regmap.set r v ms) sp (rs#(preg_of r) <- v').
Proof.
  intros. inv H. constructor.
  rewrite Pregmap.gso. auto. apply sym_not_eq. apply preg_of_not_GPR1.
  auto.
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
  forall ms sp rs r v v' v1,
  agree ms sp rs ->
  mreg_type r = Tint ->
  Val.lessdef v v' ->
  agree (Regmap.set r v ms) sp (rs #(ireg_of r) <- v1 #(ireg_of r) <- v').
Proof.
  intros. replace (IR (ireg_of r)) with (preg_of r). inv H.
  split. repeat (rewrite Pregmap.gso; auto with ppcgen). auto.
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
  Val.lessdef v rs'#(ireg_of r) ->
  (forall r', 
     r' <> IR GPR0 ->
     r' <> PC -> r' <> LR -> r' <> CTR ->
     r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 ->
     r' <> CARRY ->
     r' <> IR (ireg_of r) -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. set (v' := rs'#(ireg_of r)). 
  apply agree_exten_2 with (rs#(ireg_of r) <- v').
  auto with ppcgen.
  intros. unfold Pregmap.set. case (PregEq.eq r0 (ireg_of r)); intro.
  subst r0. auto. apply H2; auto.
Qed.
Hint Resolve agree_set_mireg_exten: ppcgen.

Lemma agree_undef_regs:
  forall rl ms sp rs rs',
  agree ms sp rs ->
  (forall r, is_data_reg r -> ~In r (List.map preg_of rl) -> rs'#r = rs#r) ->
  agree (undef_regs rl ms) sp rs'.
Proof.
  induction rl; simpl; intros.
  apply agree_exten_1 with rs; auto.
  apply IHrl with (rs#(preg_of a) <- (rs'#(preg_of a))).
  apply agree_set_mreg; auto.
  intros. unfold Pregmap.set.
  destruct (PregEq.eq r (preg_of a)).
  congruence.
  apply H0. auto. intuition congruence.
Qed.

Lemma agree_undef_temps:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, 
     r <> IR GPR0 ->
     r <> PC -> r <> LR -> r <> CTR ->
     r <> CR0_0 -> r <> CR0_1 -> r <> CR0_2 -> r <> CR0_3 ->
     r <> CARRY ->
     r <> IR GPR11 -> r <> IR GPR12 ->
     r <> FR FPR0 -> r <> FR FPR12 -> r <> FR FPR13 ->
     rs'#r = rs#r) ->
  agree (undef_temps ms) sp rs'.
Proof.
  unfold undef_temps. intros. apply agree_undef_regs with rs; auto.
  simpl. unfold preg_of; simpl. intros. 
  apply H0; (red; intro; subst; simpl in H1; intuition congruence).
Qed.
Hint Resolve agree_undef_temps: ppcgen.

Lemma agree_undef_temps_2:
  forall ms sp rs,
  agree ms sp rs ->
  agree (undef_temps ms) sp rs.
Proof.
  intros. apply agree_undef_temps with rs; auto. 
Qed.
Hint Resolve agree_undef_temps_2: ppcgen.

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
  Machconcr.extcall_arg ms m sp l v ->
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
  Machconcr.extcall_args ms m sp ll vl ->
  exists vl', Asm.extcall_args rs m' ll vl' /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros. 
  exists (@nil val); split. constructor. constructor.
  exploit extcall_arg_match; eauto. intros [v1' [A B]].
  exploit IHextcall_args; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma extcall_arguments_match:
  forall ms m m' sp rs sg args,
  agree ms sp rs -> Mem.extends m m' ->
  Machconcr.extcall_arguments ms m sp sg args ->
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

(** * Correctness of PowerPC constructor functions *)

(** Properties of comparisons. *)

Lemma compare_float_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_float rs v1 v2) in
     rs1#CR0_0 = Val.cmpf Clt v1 v2
  /\ rs1#CR0_1 = Val.cmpf Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmpf Ceq v1 v2
  /\ forall r', r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. rewrite nextinstr_inv; auto.
  unfold compare_float. repeat (rewrite Pregmap.gso; auto).
Qed.

Lemma compare_sint_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_sint rs v1 v2) in
     rs1#CR0_0 = Val.cmp Clt v1 v2
  /\ rs1#CR0_1 = Val.cmp Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmp Ceq v1 v2
  /\ forall r', r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. rewrite nextinstr_inv; auto.
  unfold compare_sint. repeat (rewrite Pregmap.gso; auto).
Qed.

Lemma compare_uint_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_uint rs v1 v2) in
     rs1#CR0_0 = Val.cmpu Clt v1 v2
  /\ rs1#CR0_1 = Val.cmpu Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmpu Ceq v1 v2
  /\ forall r', r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. rewrite nextinstr_inv; auto.
  unfold compare_uint. repeat (rewrite Pregmap.gso; auto).
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
  simpl. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.
  reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen.
   apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* addis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  exists (nextinstr (rs#r <- (Vint n))).
  split. apply exec_straight_one. 
  simpl. rewrite Int.add_commut. 
  rewrite <- H. rewrite low_high_s. reflexivity.
  reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* addis + ori *)
  pose (rs1 := nextinstr (rs#r <- (Vint (Int.shl (high_u n) (Int.repr 16))))).
  exists (nextinstr (rs1#r <- (Vint n))).
  split. eapply exec_straight_two. 
  simpl. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.
  simpl. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  unfold Val.or. rewrite low_high_u. reflexivity.
  reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
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
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto. 
  (* addis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_one.
  simpl. rewrite gpr_or_zero_not_zero; auto.
  generalize (low_high_s n). rewrite H1. rewrite Int.add_zero. intro.
  rewrite H2. auto.
  reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* addis + addi *)
  pose (rs1 := nextinstr (rs#r1 <- (Val.add rs#r2 (Vint (Int.shl (high_s n) (Int.repr 16)))))).
  exists (nextinstr (rs1#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_two with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero; auto. 
  simpl. rewrite gpr_or_zero_not_zero; auto.
  unfold rs1 at 1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss.
  rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
  reflexivity. reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
Qed. 

(** And integer immediate. *)

Lemma andimm_correct:
  forall r1 r2 n k (rs : regset) m,
  r2 <> GPR0 ->
  let v := Val.and rs#r2 (Vint n) in
  exists rs',
     exec_straight (andimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ rs'#CR0_2 = Val.cmp Ceq v Vzero
  /\ forall r': preg,
       r' <> r1 -> r' <> GPR0 -> r' <> PC ->
       r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 ->
       rs'#r' = rs#r'.
Proof.
  intros. unfold andimm.
  case (Int.eq (high_u n) Int.zero).
  (* andi *)
  exists (nextinstr (compare_sint (rs#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. apply exec_straight_one. reflexivity. reflexivity.
  split. rewrite D; try discriminate. apply Pregmap.gss. 
  split. auto.
  intros. rewrite D; auto. apply Pregmap.gso; auto.
  (* andis *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (compare_sint (rs#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H0. rewrite Int.or_zero. 
  intro. rewrite H1. reflexivity. reflexivity.
  split. rewrite D; try discriminate. apply Pregmap.gss. 
  split. auto.
  intros. rewrite D; auto. apply Pregmap.gso; auto.
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
  split. rewrite D; try discriminate. apply Pregmap.gss. 
  split. auto.
  intros. rewrite D; auto. rewrite Pregmap.gso; auto.
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
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* oris *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H. rewrite Int.or_zero. 
  intro. rewrite H0. reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* oris + ori *)
  pose (rs1 := nextinstr (rs#r1 <- (Val.or rs#r2 (Vint (Int.shl (high_u n) (Int.repr 16)))))).
  exists (nextinstr (rs1#r1 <- v)).
  split. apply exec_straight_two with rs1 m.
  reflexivity. simpl. unfold rs1 at 1. 
  rewrite nextinstr_inv; auto with ppcgen.
  rewrite Pregmap.gss. rewrite Val.or_assoc. simpl. 
  rewrite low_high_u. reflexivity. reflexivity. reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
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
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* xoris *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. simpl.
  generalize (low_high_u_xor n). rewrite H. rewrite Int.xor_zero. 
  intro. rewrite H0. reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* xoris + xori *)
  pose (rs1 := nextinstr (rs#r1 <- (Val.xor rs#r2 (Vint (Int.shl (high_u n) (Int.repr 16)))))).
  exists (nextinstr (rs1#r1 <- v)).
  split. apply exec_straight_two with rs1 m.
  reflexivity. simpl. unfold rs1 at 1. 
  rewrite nextinstr_inv; try discriminate. 
  rewrite Pregmap.gss. rewrite Val.xor_assoc. simpl. 
  rewrite low_high_u_xor. reflexivity. reflexivity. reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen.
  apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
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
  destruct ty; apply exec_straight_one; auto with ppcgen; simpl.
  unfold load1. rewrite gpr_or_zero_not_zero; auto.
  simpl in *. rewrite H. unfold preg_of; rewrite H0. auto.
  unfold load1. rewrite gpr_or_zero_not_zero; auto.
  simpl in *. rewrite H. unfold preg_of; rewrite H0. auto.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
(* loadimm + one load *)
  exploit (loadimm_correct GPR0 ofs); eauto. intros [rs' [A [B C]]]. 
  exists (nextinstr (rs'#(preg_of dst) <- v)); split.
  eapply exec_straight_trans. eexact A.
  destruct ty; apply exec_straight_one; auto with ppcgen; simpl.
  unfold load2. rewrite B. rewrite C; auto with ppcgen. simpl in H. rewrite H. 
  unfold preg_of; rewrite H0. auto. congruence.
  unfold load2. rewrite B. rewrite C; auto with ppcgen. simpl in H. rewrite H. 
  unfold preg_of; rewrite H0. auto. congruence.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
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
  assert (rs' base = rs base). apply C; auto with ppcgen. congruence.
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

Lemma transl_cond_correct_aux:
  forall cond args k ms sp rs m,
  map mreg_type args = type_of_condition cond ->
  agree ms sp rs ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) = 
       (if snd (crbit_for_cond cond)
        then eval_condition_total cond (map rs (map preg_of args))
        else Val.notbool (eval_condition_total cond (map rs (map preg_of args))))
  /\ agree ms sp rs'.
Proof.
  intros.
  destruct cond; simpl in H; TypeInv; simpl; UseTypeInfo.
  (* Ccomp *)
  destruct (compare_sint_spec rs (rs (ireg_of m0)) (rs (ireg_of m1)))
  as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  apply agree_exten_2 with rs; auto.
  (* Ccompu *)
  destruct (compare_uint_spec rs (rs (ireg_of m0)) (rs (ireg_of m1)))
  as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  apply agree_exten_2 with rs; auto.
  (* Ccompimm *)
  case (Int.eq (high_s i) Int.zero).
  destruct (compare_sint_spec rs (rs (ireg_of m0)) (Vint i))
  as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl. eauto. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  apply agree_exten_2 with rs; auto.
  generalize (loadimm_correct GPR0 i (Pcmpw (ireg_of m0) GPR0 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_sint_spec rs1 (rs (ireg_of m0)) (Vint i))
  as [A [B [C D]]].
  assert (rs1 (ireg_of m0) = rs (ireg_of m0)).
    apply OTH1; auto with ppcgen. decEq. auto with ppcgen.
  exists (nextinstr (compare_sint rs1 (rs1 (ireg_of m0)) (Vint i))).
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. rewrite RES1; rewrite H; auto.
  reflexivity. 
  split. rewrite H. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  apply agree_exten_2 with rs; auto.
  intros. rewrite H; rewrite D; auto. 
  (* Ccompuimm *)
  case (Int.eq (high_u i) Int.zero).
  destruct (compare_uint_spec rs (rs (ireg_of m0)) (Vint i))
  as [A [B [C D]]].
  econstructor; split.
  apply exec_straight_one. simpl. eauto. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  apply agree_exten_2 with rs; auto.
  generalize (loadimm_correct GPR0 i (Pcmplw (ireg_of m0) GPR0 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTH1]]].
  destruct (compare_uint_spec rs1 (rs (ireg_of m0)) (Vint i))
  as [A [B [C D]]].
  assert (rs1 (ireg_of m0) = rs (ireg_of m0)).
    apply OTH1; auto with ppcgen. decEq. auto with ppcgen.
  exists (nextinstr (compare_uint rs1 (rs1 (ireg_of m0)) (Vint i))).
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. rewrite RES1; rewrite H; auto.
  reflexivity. 
  split. rewrite H. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  apply agree_exten_2 with rs; auto.
  intros. rewrite H; rewrite D; auto. 
  (* Ccompf *)
  destruct (floatcomp_correct c (freg_of m0) (freg_of m1) k rs m)
  as [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  split. apply RES. 
  apply agree_exten_2 with rs; auto.
  (* Cnotcompf *)
  destruct (floatcomp_correct c (freg_of m0) (freg_of m1) k rs m)
  as [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  split. rewrite RES.
  assert (forall v1 v2, Val.notbool (Val.notbool (Val.cmpf c v1 v2)) = Val.cmpf c v1 v2).
    intros v1 v2; unfold Val.cmpf; destruct v1; destruct v2; auto. 
    apply Val.notbool_idem2.
  rewrite H. case (snd (crbit_for_fcmp c)); simpl; auto.
  apply agree_exten_2 with rs; auto.
  (* Cmaskzero *)
  destruct (andimm_correct GPR0 (ireg_of m0) i k rs m (ireg_of_not_GPR0 m0))
  as [rs' [A [B [C D]]]].
  exists rs'. split. assumption. 
  split. rewrite C. auto. 
  apply agree_exten_2 with rs; auto.
  (* Cmasknotzero *)
  destruct (andimm_correct GPR0 (ireg_of m0) i k rs m (ireg_of_not_GPR0 m0))
  as [rs' [A [B [C D]]]].
  exists rs'. split. assumption. 
  split. rewrite C. rewrite Val.notbool_idem3. reflexivity. 
  apply agree_exten_2 with rs; auto.
Qed.

Lemma transl_cond_correct:
  forall cond args k ms sp rs m b,
  map mreg_type args = type_of_condition cond ->
  agree ms sp rs ->
  eval_condition cond (map ms args) = Some b ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) = 
       (if snd (crbit_for_cond cond)
        then Val.of_bool b
        else Val.notbool (Val.of_bool b))
  /\ agree ms sp rs'.
Proof.
  intros.
  assert (eval_condition_total cond rs ## (preg_of ## args) = Val.of_bool b).
    apply eval_condition_weaken. eapply eval_condition_lessdef; eauto. 
    eapply preg_vals; eauto.
  rewrite <- H2. eapply transl_cond_correct_aux; eauto.
Qed.

(** Translation of arithmetic operations. *)

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity]
  | auto 7 with ppcgen; fail ].
(*
  match goal with
  | H: (Val.lessdef ?v ?v') |-
         exists rs' : regset,
         exec_straight ?c ?rs ?m ?k rs' ?m /\
         agree (Regmap.set ?res ?v ?ms) ?sp rs'  =>

    (exists (nextinstr (rs#(ireg_of res) <- v'));
     split; 
     [ apply exec_straight_one; auto; fail
     | auto with ppcgen ])
  ||
    (exists (nextinstr (rs#(freg_of res) <- v'));
     split; 
     [ apply exec_straight_one; auto; fail
     | auto with ppcgen ])
  end.
*)

Lemma transl_op_correct:
  forall op args res k ms sp rs m v,
  wt_instr (Mop op args res) ->
  agree ms sp rs ->
  eval_operation ge sp op (map ms args) = Some v ->
  exists rs',
    exec_straight (transl_op op args res k) rs m k rs' m
  /\ agree (Regmap.set res v (undef_op op ms)) sp rs'.
Proof.
  intros.
  assert (exists v', Val.lessdef v v' /\
          eval_operation_total ge sp op (map rs (map preg_of args)) = v').
    exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. 
    intros [v' [A B]]. exists v'; split; auto.
    apply eval_operation_weaken; eauto. 
  destruct H2 as [v' [LD EQ]]. clear H1.
  inv H.
  (* Omove *)
  simpl in *. 
  exists (nextinstr (rs#(preg_of res) <- (rs#(preg_of r1)))).
  split. unfold preg_of. rewrite <- H2.
  destruct (mreg_type r1); apply exec_straight_one; auto.
  auto with ppcgen. 
  (* Other instructions *)
  destruct op; simpl; simpl in H5; injection H5; clear H5; intros;
  TypeInv; simpl in *; UseTypeInfo; try (TranslOpSimpl).
  (* Omove again *)
  congruence.
  (* Ointconst *)
  destruct (loadimm_correct (ireg_of res) i k rs m)
  as [rs' [A [B C]]]. 
  exists rs'. split. auto. 
  rewrite <- B in LD. eauto with ppcgen. 
  (* Ofloatconst *)
  exists (nextinstr (rs #GPR12 <- Vundef #(freg_of res) <- (Vfloat f))).
  split. apply exec_straight_one. reflexivity. reflexivity.
  apply agree_nextinstr. apply agree_set_mfreg; auto. apply agree_set_mreg; auto.
  eapply agree_undef_temps; eauto. 
  intros. apply Pregmap.gso; auto. 
  (* Oaddrsymbol *)
  change (find_symbol_offset ge i i0) with (symbol_offset ge i i0) in LD.
  set (v' := symbol_offset ge i i0) in *.
  pose (rs1 := nextinstr (rs#GPR12 <- (high_half v'))).
  exists (nextinstr (rs1#(ireg_of res) <- v')).
  split. apply exec_straight_two with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_zero.
  unfold const_high. rewrite Val.add_commut. 
  rewrite high_half_zero. reflexivity. 
  simpl. rewrite gpr_or_zero_not_zero. 2: congruence. 
  unfold rs1 at 1. rewrite nextinstr_inv; auto with ppcgen.
  rewrite Pregmap.gss. 
  fold v'. rewrite Val.add_commut. unfold v'. rewrite low_high_half.
  reflexivity. reflexivity. reflexivity. 
  unfold rs1. apply agree_nextinstr. apply agree_set_mireg; auto.
  apply agree_set_mreg; auto. apply agree_nextinstr.
  eapply agree_undef_temps; eauto.
  intros. apply Pregmap.gso; auto.
  (* Oaddrstack *)
  assert (GPR1 <> GPR0). discriminate.
  generalize (addimm_correct (ireg_of res) GPR1 i k rs m (ireg_of_not_GPR0 res) H1). 
  intros [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  apply agree_set_mireg_exten with rs; auto with ppcgen.
  rewrite (sp_val ms sp rs) in LD; auto. rewrite RES; auto. 
  (* Ocast8unsigned *)
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity. 
  replace (Val.zero_ext 8 (rs (ireg_of m0)))
      with (Val.rolm (rs (ireg_of m0)) Int.zero (Int.repr 255)) in LD.
  auto with ppcgen. 
  unfold Val.rolm, Val.zero_ext. destruct (rs (ireg_of m0)); auto.
  rewrite Int.rolm_zero. rewrite Int.zero_ext_and. auto. compute; auto.
  (* Ocast16unsigned *)
  econstructor; split.
  apply exec_straight_one. simpl; reflexivity. reflexivity. 
  replace (Val.zero_ext 16 (rs (ireg_of m0)))
      with (Val.rolm (rs (ireg_of m0)) Int.zero (Int.repr 65535)) in LD.
  auto with ppcgen. 
  unfold Val.rolm, Val.zero_ext. destruct (rs (ireg_of m0)); auto.
  rewrite Int.rolm_zero. rewrite Int.zero_ext_and. auto. compute; auto.
  (* Oaddimm *)
  generalize (addimm_correct (ireg_of res) (ireg_of m0) i k rs m
                            (ireg_of_not_GPR0 res) (ireg_of_not_GPR0 m0)).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto.
  rewrite <- B in LD. eauto with ppcgen.  
  (* Osubimm *)
  case (Int.eq (high_s i) Int.zero).
  econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  auto 7 with ppcgen.
  generalize (loadimm_correct GPR0 i (Psubfc (ireg_of res) (ireg_of m0) GPR0 :: k) rs m).
  intros [rs1 [EX [RES OTH]]].
  econstructor; split.
  eapply exec_straight_trans. eexact EX. 
  apply exec_straight_one. simpl; eauto. auto.
  rewrite RES. rewrite OTH; auto with ppcgen.
  assert (agree (undef_temps ms) sp rs1). eauto with ppcgen.  
  auto with ppcgen. decEq; auto with ppcgen.
  (* Omulimm *)
  case (Int.eq (high_s i) Int.zero).
  econstructor; split.
  apply exec_straight_one. simpl; eauto. auto. 
  auto with ppcgen.
  generalize (loadimm_correct GPR0 i (Pmullw (ireg_of res) (ireg_of m0) GPR0 :: k) rs m).
  intros [rs1 [EX [RES OTH]]].
  assert (agree (undef_temps ms) sp rs1). eauto with ppcgen.
  econstructor; split.
  eapply exec_straight_trans. eexact EX. 
  apply exec_straight_one. simpl; eauto. auto.
  rewrite RES. rewrite OTH; auto with ppcgen. decEq; auto with ppcgen.
  (* Oand *)
  set (v' := Val.and (rs (ireg_of m0)) (rs (ireg_of m1))) in *.
  pose (rs1 := rs#(ireg_of res) <- v').
  generalize (compare_sint_spec rs1 v' Vzero).
  intros [A [B [C D]]].
  exists (nextinstr (compare_sint rs1 v' Vzero)).
  split. apply exec_straight_one. auto. auto. 
  apply agree_exten_2 with rs1. unfold rs1; auto with ppcgen.
  auto.
  (* Oandimm *)
  generalize (andimm_correct (ireg_of res) (ireg_of m0) i k rs m
                             (ireg_of_not_GPR0 m0)).
  intros [rs' [A [B [C D]]]]. 
  exists rs'. split. auto. rewrite <- B in LD. eauto with ppcgen.
  (* Oorimm *)
  generalize (orimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. rewrite <- B in LD. eauto with ppcgen. 
  (* Oxorimm *)
  generalize (xorimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. rewrite <- B in LD. eauto with ppcgen.
  (* Oxhrximm *)
  pose (rs1 := nextinstr (rs#(ireg_of res) <- (Val.shr (rs (ireg_of m0)) (Vint i)) #CARRY <- (Val.shr_carry (rs (ireg_of m0)) (Vint i)))).
  exists (nextinstr (rs1#(ireg_of res) <- (Val.shrx (rs (ireg_of m0)) (Vint i)))).
  split. apply exec_straight_two with rs1 m.
  auto. simpl. decEq. decEq. decEq. 
  unfold rs1. repeat (rewrite nextinstr_inv; try discriminate).
  rewrite Pregmap.gss. rewrite Pregmap.gso. rewrite Pregmap.gss. 
  apply Val.shrx_carry. auto with ppcgen. auto. auto. 
  apply agree_nextinstr. unfold rs1. apply agree_nextinstr_commut. 
  apply agree_set_commut. auto with ppcgen. 
  apply agree_set_other. apply agree_set_mireg_twice; auto with ppcgen. 
  compute; auto. auto with ppcgen. 
  (* Ointoffloat *)
  econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  apply agree_nextinstr. apply agree_set_mireg; auto. apply agree_set_mreg; auto.
  apply agree_undef_temps with rs; auto. intros. 
  repeat rewrite Pregmap.gso; auto. 
  (* Ocmp *)
  revert H1 LD; case (classify_condition c args); intros.
  (* Optimization: compimm Cge 0 *)
  subst n. simpl in *. inv H1. UseTypeInfo. 
  set (rs1 := nextinstr (rs#(ireg_of res) <- (Val.rolm (rs (ireg_of r)) Int.one Int.one))).
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (Val.xor (rs1#(ireg_of res)) (Vint Int.one)))).
  exists rs2.
  split. apply exec_straight_two with rs1 m; auto.
  rewrite <- Val.rolm_ge_zero in LD.
  unfold rs2. apply agree_nextinstr.
  unfold rs1. apply agree_nextinstr_commut. fold rs1.
  replace (rs1 (ireg_of res)) with (Val.rolm (rs (ireg_of r)) Int.one Int.one).
  apply agree_set_mireg_twice; auto with ppcgen.
  unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss. auto. 
  auto with ppcgen. auto with ppcgen. 
  (* Optimization: compimm Clt 0 *)
  subst n. simpl in *. inv H1. UseTypeInfo. 
  exists (nextinstr (rs#(ireg_of res) <- (Val.rolm (rs (ireg_of r)) Int.one Int.one))).
  split. apply exec_straight_one; auto. 
  rewrite <- Val.rolm_lt_zero in LD.
  auto with ppcgen. 
  (* General case *)
  set (bit := fst (crbit_for_cond c0)).
  set (isset := snd (crbit_for_cond c0)).
  set (k1 :=
        Pmfcrbit (ireg_of res) bit ::
        (if isset
         then k
         else Pxori (ireg_of res) (ireg_of res) (Cint Int.one) :: k)).
  generalize (transl_cond_correct_aux c0 rl k1 ms sp rs m H1 H0).
  fold bit; fold isset. 
  intros [rs1 [EX1 [RES1 AG1]]].
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (rs1#(reg_of_crbit bit)))).
  destruct isset.
  exists rs2.
  split. apply exec_straight_trans with k1 rs1 m. assumption.
  unfold k1. apply exec_straight_one. 
  reflexivity. reflexivity. 
  unfold rs2. rewrite RES1. auto with ppcgen. 
  econstructor. 
  split. apply exec_straight_trans with k1 rs1 m. assumption.
  unfold k1. apply exec_straight_two with rs2 m.
  reflexivity. simpl. eauto. auto. auto. 
  apply agree_nextinstr. 
  unfold rs2 at 1. rewrite nextinstr_inv. rewrite Pregmap.gss. 
  rewrite RES1. rewrite <- Val.notbool_xor. 
  unfold rs2. auto 7 with ppcgen. 
  apply eval_condition_total_is_bool.
  auto with ppcgen. 
Qed.

Lemma transl_load_store_correct:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
    addr args (temp: ireg) k ms sp rs m ms' m',
  (forall cst (r1: ireg) (rs1: regset) k,
    eval_addressing_total ge sp addr (map rs (map preg_of args)) =
                Val.add (gpr_or_zero rs1 r1) (const_low ge cst) ->
    (forall (r: preg), r <> PC -> r <> temp -> rs1 r = rs r) ->
    exists rs',
    exec_straight (mk1 cst r1 :: k) rs1 m k rs' m' /\
    agree ms' sp rs') ->
  (forall (r1 r2: ireg) k,
    eval_addressing_total ge sp addr (map rs (map preg_of args)) = Val.add rs#r1 rs#r2 ->
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
    unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss. 
    rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
    discriminate.
  intros. unfold rs1. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
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
  unfold find_symbol_offset, symbol_offset. 
  destruct (Genv.find_symbol ge i); auto. rewrite Int.add_zero. auto.
  auto.
  (* Aglobal general case *)
  set (rs1 := nextinstr (rs#temp <- (const_high ge (Csymbol_high i i0)))).
  exploit (H (Csymbol_low i i0) temp rs1 k).
    simpl. rewrite gpr_or_zero_not_zero; auto. 
    unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss.
    unfold const_high, const_low. 
    set (v := symbol_offset ge i i0).
    symmetry. rewrite Val.add_commut. unfold v. apply low_high_half. 
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
    symmetry. rewrite Val.add_commut. decEq.
    unfold v. rewrite Val.add_commut. apply low_high_half. 
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
  exploit eval_addressing_weaken. eexact A. intro E. rewrite <- E in C.
  apply transl_load_store_correct with ms; auto.
(* mk1 *)
  intros. exists (nextinstr (rs1#(preg_of dst) <- v')). 
  split. apply exec_straight_one. rewrite H.
  unfold load1. rewrite <- H6. rewrite C. auto.
  auto with ppcgen.
  eauto with ppcgen.
(* mk2 *)
  intros. exists (nextinstr (rs#(preg_of dst) <- v')). 
  split. apply exec_straight_one. rewrite H0. 
  unfold load2. rewrite <- H6. rewrite C. auto.
  auto with ppcgen.
  eauto with ppcgen.
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
  exploit eval_addressing_weaken. eexact A. intro E. rewrite <- E in C.
  exists m1'; split; auto.
  apply transl_load_store_correct with ms; auto.
(* mk1 *)
  intros.
  exploit (H cst r1 rs1 (nextinstr rs1) m1').
  unfold store1. rewrite <- H6. 
  replace (rs1 (preg_of src)) with (rs (preg_of src)).
  rewrite C. auto.
  symmetry. apply H7. auto with ppcgen. 
  apply sym_not_equal. apply int_temp_for_diff.
  intros [rs3 [U V]].
  exists rs3; split.
  apply exec_straight_one. auto. rewrite V; auto with ppcgen. 
  eapply agree_undef_temps; eauto. intros. 
  rewrite V; auto. rewrite nextinstr_inv; auto. apply H7; auto. 
  unfold int_temp_for. destruct (mreg_eq src IT2); auto.
(* mk2 *)
  intros.
  exploit (H0 r1 r2 rs (nextinstr rs) m1').
  unfold store2. rewrite <- H6. rewrite C. auto. 
  intros [rs3 [U V]].
  exists rs3; split.
  apply exec_straight_one. auto. rewrite V; auto with ppcgen. 
  eapply agree_undef_temps; eauto. intros. 
  rewrite V; auto. rewrite nextinstr_inv; auto.
  unfold int_temp_for. destruct (mreg_eq src IT2); congruence.
Qed.

End STRAIGHTLINE.


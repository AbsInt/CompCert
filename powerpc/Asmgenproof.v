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

(** Correctness proof for PPC generation: main proof. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Mach.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenproof0.
Require Import Asmgenproof1.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = Errors.OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma functions_transl:
  forall f b tf,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge b = Some (Internal tf).
Proof.
  intros. 
  destruct (functions_translated _ _ H) as [tf' [A B]].
  rewrite A. monadInv B. f_equal. congruence.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z tf <= Int.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Int.max_unsigned (list_length_z x)); inv EQ0. 
  omega.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto. 
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H. 
  exploit exec_straight_steps_2; eauto. 
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to PPC
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ PPC instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- PPC instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that PPC constructor
  functions do not introduce new labels.
*)

Section TRANSL_LABEL.

Remark loadimm_label:
  forall r n k, tail_nolabel k (loadimm r n k).
Proof.
  intros. unfold loadimm. 
  case (Int.eq (high_s n) Int.zero). TailNoLabel.
  case (Int.eq (low_s n) Int.zero); TailNoLabel.
Qed.
Hint Resolve loadimm_label: labels.

Remark addimm_label:
  forall r1 r2 n k, tail_nolabel k (addimm r1 r2 n k).
Proof.
  intros; unfold addimm. 
  case (Int.eq (high_s n) Int.zero). TailNoLabel.
  case (Int.eq (low_s n) Int.zero); TailNoLabel.
Qed.
Hint Resolve addimm_label: labels.

Remark andimm_base_label:
  forall r1 r2 n k, tail_nolabel k (andimm_base r1 r2 n k).
Proof.
  intros; unfold andimm_base. 
  case (Int.eq (high_u n) Int.zero). TailNoLabel.
  case (Int.eq (low_u n) Int.zero). TailNoLabel.
  eapply tail_nolabel_trans; TailNoLabel.
Qed.
Hint Resolve andimm_base_label: labels.

Remark andimm_label:
  forall r1 r2 n k, tail_nolabel k (andimm r1 r2 n k).
Proof.
  intros; unfold andimm. 
  case (is_rlw_mask n); TailNoLabel.
Qed.
Hint Resolve andimm_label: labels.

Remark orimm_label:
  forall r1 r2 n k, tail_nolabel k (orimm r1 r2 n k).
Proof.
  intros; unfold orimm. 
  case (Int.eq (high_u n) Int.zero). TailNoLabel.
  case (Int.eq (low_u n) Int.zero); TailNoLabel.
Qed.
Hint Resolve orimm_label: labels.

Remark xorimm_label:
  forall r1 r2 n k, tail_nolabel k (xorimm r1 r2 n k).
Proof.
  intros; unfold xorimm. 
  case (Int.eq (high_u n) Int.zero). TailNoLabel.
  case (Int.eq (low_u n) Int.zero); TailNoLabel.
Qed.
Hint Resolve xorimm_label: labels.

Remark rolm_label:
  forall r1 r2 amount mask k, tail_nolabel k (rolm r1 r2 amount mask k).
Proof.
  intros; unfold rolm. 
  case (is_rlw_mask mask); TailNoLabel.
Qed.
Hint Resolve rolm_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c -> tail_nolabel k c.
Proof.
  unfold loadind; intros.
  destruct ty; destruct (Int.eq (high_s ofs) Int.zero);
  TailNoLabel; eapply tail_nolabel_trans; TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind base src ofs ty k = OK c -> tail_nolabel k c.
Proof.
  unfold storeind; intros.
  destruct ty; destruct (Int.eq (high_s ofs) Int.zero);
  TailNoLabel; eapply tail_nolabel_trans; TailNoLabel.
Qed.

Remark floatcomp_label:
  forall cmp r1 r2 k, tail_nolabel k (floatcomp cmp r1 r2 k).
Proof.
  intros; unfold floatcomp. destruct cmp; TailNoLabel.
Qed.
Hint Resolve floatcomp_label: labels.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c -> tail_nolabel k c.
Proof.
  unfold transl_cond; intros; destruct cond; TailNoLabel;
  eapply tail_nolabel_trans; TailNoLabel.
Qed.

Remark transl_cond_op_label:
  forall cond args r k c,
  transl_cond_op cond args r k = OK c -> tail_nolabel k c.
Proof.
  unfold transl_cond_op; intros; destruct (classify_condition cond args);
  TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto.
  destruct (snd (crbit_for_cond c0)); TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c -> tail_nolabel k c.
Proof.
Opaque Int.eq.
  unfold transl_op; intros; destruct op; TailNoLabel.
  destruct (preg_of r); try discriminate; destruct (preg_of m); inv H; TailNoLabel.
  destruct (symbol_is_small_data i i0); TailNoLabel.
  destruct (Int.eq (high_s i) Int.zero); TailNoLabel; eapply tail_nolabel_trans; TailNoLabel.
  destruct (Int.eq (high_s i) Int.zero); TailNoLabel; eapply tail_nolabel_trans; TailNoLabel.
  eapply transl_cond_op_label; eauto.
Qed.

Remark transl_memory_access_label:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
         addr args temp k c,
  transl_memory_access mk1 mk2 addr args temp k = OK c ->
  (forall c r, nolabel (mk1 c r)) ->
  (forall r1 r2, nolabel (mk2 r1 r2)) ->
  tail_nolabel k c.
Proof.
  unfold transl_memory_access; intros; destruct addr; TailNoLabel.
  destruct (Int.eq (high_s i) Int.zero); TailNoLabel.
  destruct (symbol_is_small_data i i0); TailNoLabel.
  destruct (Int.eq (high_s i) Int.zero); TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans; eapply loadind_label; eauto.
  eapply transl_op_label; eauto.
  destruct m; monadInv H; (eapply tail_nolabel_trans; [eapply transl_memory_access_label; TailNoLabel|TailNoLabel]).
  destruct m; monadInv H; eapply transl_memory_access_label; TailNoLabel.
  destruct s0; monadInv H; TailNoLabel.
  destruct s0; monadInv H; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. 
  destruct (snd (crbit_for_cond c0)); TailNoLabel.
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B). 
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a). 
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf = None
  | Some c => exists tc, find_label lbl tf = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Int.max_unsigned (list_length_z x)); inv EQ0.
  monadInv EQ. simpl. eapply transl_code_label; eauto. 
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m  
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2. 
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Int.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto. 
  rewrite Int.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmgenproof0.return_address_exists; eauto. 
- intros. exploit transl_instr_label; eauto. 
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0. 
  destruct (zlt Int.max_unsigned (list_length_z x)); inv EQ0. monadInv EQ.
  exists x; exists false; split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#GPR11 = parent_sp s),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Int.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m').

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (r11_is_parent ep i = true -> rs2#GPR11 = parent_sp s)) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7. 
  exploit H3; eauto. intros [rs2 [A [B C]]]. 
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto. 
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  r11_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto. 
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto. 
  econstructor; eauto.
  eapply find_instr_tail. eauto. 
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one PPC transition, except the
  transition from [Machsem.Returnstate] to [Machsem.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.

Remark preg_of_not_GPR11: forall r, negb (mreg_eq r IT1) = true -> IR GPR11 <> preg_of r.
Proof.
  intros. change (IR GPR11) with (preg_of IT1). red; intros. 
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
Qed.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros. 
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto. 
  split. apply agree_nextinstr; auto. simpl; congruence.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto with asmgen. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto with asmgen. congruence.
  simpl; congruence.

- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]]. 
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto with asmgen. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. change (undef_setstack rs) with rs. apply agree_exten with rs0; auto with asmgen.
  simpl; intros. rewrite Q; auto with asmgen.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *. 
  exploit Mem.loadv_extends. eauto. eexact H0. auto. 
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. 
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros.
  destruct ep; simpl in TR. 
(* GPR11 contains parent *)
  exploit loadind_correct. eexact TR.
  instantiate (2 := rs0). rewrite DXP; eauto.  congruence.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto. 
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto with asmgen.
  simpl; intros. rewrite R; auto with asmgen. 
  apply preg_of_not_GPR11; auto.
(* GPR11 does not contain parent *)
  monadInv TR.  
  exploit loadind_correct. eexact EQ0. eauto. congruence. intros [rs1 [P [Q R]]]. simpl in Q.
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto. congruence.
  intros [rs2 [S [T U]]]. 
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg. eauto. eauto.
  instantiate (1 := rs1#GPR11 <- (rs2#GPR11)). intros.
  rewrite Pregmap.gso; auto with asmgen.
  congruence. intros. unfold Pregmap.set. destruct (PregEq.eq r' GPR11). congruence. auto with asmgen. 
  simpl; intros. rewrite U; auto with asmgen. 
  apply preg_of_not_GPR11; auto.

- (* Mop *)
  assert (eval_operation tge sp op rs##args m = Some v). 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A. 
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto. split. auto. 
  simpl. destruct op; try congruence. destruct ep; simpl; try congruence. intros. 
  rewrite R; auto. apply preg_of_not_GPR11; auto.

- (* Mload *)
  assert (eval_addressing tge sp addr rs##args = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]]. 
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  intros; auto with asmgen. 
  simpl; congruence.

- (* Mstore *)
  assert (eval_addressing tge sp addr rs##args = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR. exploit transl_store_correct; eauto. intros [rs2 [P Q]]. 
  exists rs2; split. eauto.
  split. eapply agree_exten_temps; eauto. intros; auto with asmgen. 
  simpl; congruence.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Int.zero).
    exploit ireg_val; eauto. rewrite H5; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  generalize (code_tail_next_int _ _ _ _ NOOV CT1). intro CT2.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add (Int.add ofs Int.one) Int.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto.
  apply star_one. eapply exec_step_internal. Simpl. rewrite <- H2; simpl; eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto.
  traceEq.
  econstructor; eauto. 
  econstructor; eauto. 
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simpl. 
  Simpl. rewrite <- H2. auto.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c false tf x).
    econstructor; eauto. 
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. unfold symbol_offset. rewrite symbols_preserved. rewrite H. eauto.
  econstructor; eauto. 
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simpl.
  Simpl. rewrite <- H2. auto.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inversion AT; subst.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [parent' [A B]].
  exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]]. 
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Int.zero).
    exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
  set (rs2 := nextinstr (rs0#CTR <- (Vptr f' Int.zero))).
  set (rs3 := nextinstr (rs2#GPR0 <- (parent_ra s))).
  set (rs4 := nextinstr (rs3#LR <- (parent_ra s))).
  set (rs5 := nextinstr (rs4#GPR1 <- (parent_sp s))).
  set (rs6 := rs5#PC <- (rs5 CTR)).
  assert (exec_straight tge tf
            (Pmtctr x0 :: Plwz GPR0 (Cint (fn_retaddr_ofs f)) GPR1 :: Pmtlr GPR0
              :: Pfreeframe (fn_stacksize f) (fn_link_ofs f) :: Pbctr :: x)
            rs0 m'0
            (Pbctr :: x) rs5 m2').
  apply exec_straight_step with rs2 m'0. 
  simpl. rewrite H9. auto. auto.
  apply exec_straight_step with rs3 m'0.
  simpl. unfold load1. rewrite gpr_or_zero_not_zero. unfold const_low.
  change (rs2 GPR1) with (rs0 GPR1). rewrite <- (sp_val _ _ _ AG). 
  simpl. rewrite C. auto. congruence. auto.
  apply exec_straight_step with rs4 m'0.
  simpl. reflexivity. reflexivity.
  apply exec_straight_one. 
  simpl. change (rs4 GPR1) with (rs0 GPR1). rewrite <- (sp_val _ _ _ AG). 
  simpl. rewrite A.
  rewrite E. reflexivity. reflexivity.
  left; exists (State rs6 m2'); split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor.
  change (rs5 PC) with (Val.add (Val.add (Val.add (Val.add (rs0 PC) Vone) Vone) Vone) Vone).
  rewrite <- H4; simpl. eauto.
  eapply functions_transl; eauto. 
  eapply find_instr_tail.
  repeat (eapply code_tail_next_int; auto). eauto. 
  simpl. reflexivity. traceEq.
  (* match states *)
  econstructor; eauto.
Hint Resolve agree_nextinstr agree_set_other: asmgen.
  assert (AG4: agree rs (Vptr stk soff) rs4).
    unfold rs4, rs3, rs2; auto 10 with asmgen.
  assert (AG5: agree rs (parent_sp s) rs5).
    unfold rs5. apply agree_nextinstr. eapply agree_change_sp. eauto. 
    eapply parent_sp_def; eauto. 
  unfold rs6, rs5; auto 10 with asmgen.
+ (* Direct call *)
  set (rs2 := nextinstr (rs0#GPR0 <- (parent_ra s))).
  set (rs3 := nextinstr (rs2#LR <- (parent_ra s))).
  set (rs4 := nextinstr (rs3#GPR1 <- (parent_sp s))).
  set (rs5 := rs4#PC <- (Vptr f' Int.zero)).
  assert (exec_straight tge tf
            (Plwz GPR0 (Cint (fn_retaddr_ofs f)) GPR1 :: Pmtlr GPR0
             :: Pfreeframe (fn_stacksize f) (fn_link_ofs f) :: Pbs fid :: x)
            rs0 m'0
            (Pbs fid :: x) rs4 m2').
  apply exec_straight_step with rs2 m'0. 
  simpl. unfold load1. rewrite gpr_or_zero_not_zero. unfold const_low.
  rewrite <- (sp_val _ _ _ AG). simpl. rewrite C. auto. congruence. auto.
  apply exec_straight_step with rs3 m'0.
  simpl. reflexivity. reflexivity.
  apply exec_straight_one. 
  simpl. change (rs3 GPR1) with (rs0 GPR1). rewrite <- (sp_val _ _ _ AG). simpl. rewrite A. 
  rewrite E. reflexivity. reflexivity.
  left; exists (State rs5 m2'); split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor.
  change (rs4 PC) with (Val.add (Val.add (Val.add (rs0 PC) Vone) Vone) Vone).
  rewrite <- H4; simpl. eauto.
  eapply functions_transl; eauto. 
  eapply find_instr_tail.
  repeat (eapply code_tail_next_int; auto). eauto. 
  simpl. unfold symbol_offset. rewrite symbols_preserved. rewrite H. auto. traceEq.
  (* match states *)
  econstructor; eauto.
  assert (AG3: agree rs (Vptr stk soff) rs3).
    unfold rs3, rs2; auto 10 with asmgen.
  assert (AG4: agree rs (parent_sp s) rs4).
    unfold rs4. apply agree_nextinstr. eapply agree_change_sp. eauto. 
    eapply parent_sp_def; eauto. 
  unfold rs5; auto 10 with asmgen.

- (* Mbuiltin *)
  inv AT. monadInv H3. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H2); intro NOOV.
  exploit external_call_mem_extends; eauto. eapply preg_vals; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one. 
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  Simpl. rewrite <- H0. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  apply agree_nextinstr. eapply agree_set_undef_mreg; eauto. 
  rewrite Pregmap.gss. auto. 
  intros. Simpl. 
  congruence.

- (* Mannot *)
  inv AT. monadInv H4. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit annot_arguments_match; eauto. intros [vargs' [P Q]]. 
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one. 
  eapply exec_step_annot. eauto. eauto.
  eapply find_instr_tail; eauto. eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eapply match_states_intro with (ep := false); eauto with coqlib.
  unfold nextinstr. rewrite Pregmap.gss. 
  rewrite <- H1; simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto. 
  apply agree_nextinstr. auto.
  congruence.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4. 
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps_goto; eauto.
  intros. simpl in TR.
  destruct (transl_cond_correct_1 tge tf cond args _ rs0 m' _ TR) as [rs' [A [B C]]].
  rewrite EC in B.
  destruct (snd (crbit_for_cond cond)).
  (* Pbt, taken *)
  econstructor; econstructor; econstructor; split. eexact A. 
  split. eapply agree_exten_temps; eauto with asmgen.
  simpl. rewrite B. reflexivity. 
  (* Pbf, taken *)
  econstructor; econstructor; econstructor; split. eexact A. 
  split. eapply agree_exten_temps; eauto with asmgen.
  simpl. rewrite B. reflexivity. 

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  destruct (transl_cond_correct_1 tge tf cond args _ rs0 m' _ TR) as [rs' [A [B C]]].
  rewrite EC in B.
  econstructor; split.
  eapply exec_straight_trans. eexact A. 
  destruct (snd (crbit_for_cond cond)).
  apply exec_straight_one. simpl. rewrite B. reflexivity. auto.
  apply exec_straight_one. simpl. rewrite B. reflexivity. auto.
  split. eapply agree_exten_temps; eauto with asmgen.
  intros; Simpl.
  simpl. congruence.

- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label. eauto. eauto.
  instantiate (2 := rs0#GPR12 <- Vundef #CTR <- Vundef). 
  Simpl. eauto.
  eauto. 
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  eapply find_instr_tail; eauto. 
  simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
  econstructor; eauto. 
  eapply agree_exten_temps; eauto. intros. rewrite C; auto with asmgen. Simpl. 
  congruence.

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inversion AT; subst.
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto. simpl. intros [parent' [A B]]. 
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [ra' [C D]]. 
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
  monadInv H6.
  set (rs2 := nextinstr (rs0#GPR0 <- (parent_ra s))).
  set (rs3 := nextinstr (rs2#LR <- (parent_ra s))).
  set (rs4 := nextinstr (rs3#GPR1 <- (parent_sp s))).
  set (rs5 := rs4#PC <- (parent_ra s)).
  assert (exec_straight tge tf
           (Plwz GPR0 (Cint (fn_retaddr_ofs f)) GPR1
           :: Pmtlr GPR0
           :: Pfreeframe (fn_stacksize f) (fn_link_ofs f) :: Pblr :: x) rs0 m'0
           (Pblr :: x) rs4 m2').
  simpl. apply exec_straight_three with rs2 m'0 rs3 m'0.
  simpl. unfold load1. rewrite gpr_or_zero_not_zero. unfold const_low. rewrite C. auto. congruence.
  simpl. auto. 
  simpl. change (rs3 GPR1) with (rs0 GPR1). rewrite A. 
  rewrite <- (sp_val _ _ _ AG). rewrite E. auto. 
  auto. auto. auto. 
  left; exists (State rs5 m2'); split.
  (* execution *)
  apply plus_right' with E0 (State rs4 m2') E0.
  eapply exec_straight_exec; eauto.
  econstructor.
  change (rs4 PC) with (Val.add (Val.add (Val.add (rs0 PC) Vone) Vone) Vone). 
  rewrite <- H3. simpl. eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail. 
  eapply code_tail_next_int; auto.
  eapply code_tail_next_int; auto.
  eapply code_tail_next_int; eauto.
  reflexivity. traceEq.
  (* match states *)
  econstructor; eauto. 
  assert (AG3: agree rs (Vptr stk soff) rs3). 
    unfold rs3, rs2; auto 10 with asmgen.
  assert (AG4: agree rs (parent_sp s) rs4).
    unfold rs4. apply agree_nextinstr. eapply agree_change_sp; eauto. 
    eapply parent_sp_def; eauto.
  unfold rs5; auto with asmgen.

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'. 
  destruct (zlt Int.max_unsigned (list_length_z x0)); inversion EQ1. clear EQ1.
  unfold store_stack in *. 
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto. 
  intros [m2' [F G]].
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto. 
  intros [m3' [P Q]].
  (* Execution of function prologue *)
  monadInv EQ0.
  set (rs2 := nextinstr (rs0#GPR1 <- sp #GPR0 <- Vundef)).
  set (rs3 := nextinstr (rs2#GPR0 <- (rs0#LR))).
  set (rs4 := nextinstr rs3).
  assert (EXEC_PROLOGUE:
            exec_straight tge x
              x rs0 m'
              x1 rs4 m3').
  rewrite <- H5 at 2. 
  apply exec_straight_three with rs2 m2' rs3 m2'.
  unfold exec_instr. rewrite C. fold sp.
  rewrite <- (sp_val _ _ _ AG). unfold chunk_of_type in F. rewrite F. auto. 
  simpl. auto.
  simpl. unfold store1. rewrite gpr_or_zero_not_zero. 
  change (rs3 GPR1) with sp. change (rs3 GPR0) with (rs0 LR). simpl. 
  rewrite Int.add_zero_l. simpl in P. rewrite Int.add_zero_l in P. rewrite ATLR. rewrite P. auto. congruence.
  auto. auto. auto.
  left; exists (State rs4 m3'); split.
  eapply exec_straight_steps_1; eauto. unfold fn_code; omega. constructor. 
  econstructor; eauto. 
  change (rs4 PC) with (Val.add (Val.add (Val.add (rs0 PC) Vone) Vone) Vone). 
  rewrite ATPC. simpl. constructor; eauto.
  subst x. unfold fn_code. eapply code_tail_next_int. omega. 
  eapply code_tail_next_int. omega. 
  eapply code_tail_next_int. omega. 
  constructor.
  unfold rs4, rs3, rs2.
  apply agree_nextinstr. apply agree_set_other; auto. apply agree_set_other; auto. 
  apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. apply agree_exten_temps with rs0; eauto.
  unfold sp; congruence.
  congruence.

- (* external function *)
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto. 
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto. 
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  unfold loc_external_result.
  eapply agree_set_mreg; eauto. 
  rewrite Pregmap.gso; auto with asmgen. rewrite Pregmap.gss. auto. 
  intros; Simpl.

- (* return *)
  inv STACKS. simpl in *.
  right. split. omega. split. auto.
  rewrite <- ATPC in H5. 
  econstructor; eauto. congruence.
Qed.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply Genv.init_mem_transf_partial; eauto.
  replace (symbol_offset (Genv.globalenv tprog) (prog_main tprog) Int.zero)
     with (Vptr fb Int.zero).
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  split. auto. simpl. congruence. intros. rewrite Regmap.gi. auto. 
  unfold symbol_offset. 
  rewrite (transform_partial_program_main _ _ TRANSF).
  rewrite symbols_preserved. 
  unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
  auto. 
  compute in H1. 
  generalize (preg_val _ _ _ R3 AG). rewrite H1. intros LD; inv LD. auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.

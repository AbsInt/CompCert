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

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.

Local Transparent Archi.ptr64.

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z tf.(fn_code) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
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

Remark loadimm64_label:
  forall r n k, tail_nolabel k (loadimm64 r n k).
Proof.
  unfold loadimm64; intros.
  destruct Int64.eq. TailNoLabel. destruct Int64.eq; TailNoLabel.
Qed.
Hint Resolve loadimm64_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c -> tail_nolabel k c.
Proof.
  unfold loadind, accessind; intros. set (ofs' := Ptrofs.to_int ofs) in *.
  destruct ty; try discriminate;
  destruct (preg_of dst); try discriminate;
  destruct (Int.eq (high_s ofs') Int.zero);
  TailNoLabel; eapply tail_nolabel_trans; TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c -> tail_nolabel k c.
Proof.
  unfold storeind, accessind; intros. set (ofs' := Ptrofs.to_int ofs) in *.
  destruct ty; try discriminate;
  destruct (preg_of src); try discriminate;
  destruct (Int.eq (high_s ofs') Int.zero);
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
- destruct (preg_of r); try discriminate; destruct (preg_of m); inv H; TailNoLabel.
- destruct (symbol_is_small_data i i0). TailNoLabel. destruct (symbol_is_rel_data i i0); TailNoLabel.
- destruct (symbol_is_small_data i i0). TailNoLabel. destruct (symbol_is_rel_data i i0); TailNoLabel.
- destruct (Int.eq (high_s i) Int.zero); TailNoLabel; eapply tail_nolabel_trans; TailNoLabel.
- destruct (Int.eq (high_s i) Int.zero); TailNoLabel; eapply tail_nolabel_trans; TailNoLabel.
- unfold addimm64, opimm64. destruct Int64.eq. TailNoLabel.
  destruct ireg_eq; [apply tail_nolabel_cons; unfold nolabel;auto|]; eapply tail_nolabel_trans; TailNoLabel.
- unfold andimm64, andimm64_base, opimm64.
  destruct (is_rldl_mask i || is_rldr_mask i). TailNoLabel.
  destruct Int64.eq. TailNoLabel.
  destruct ireg_eq; [apply tail_nolabel_cons; unfold nolabel;auto|]; eapply tail_nolabel_trans; TailNoLabel.
- unfold orimm64, opimm64. destruct Int64.eq. TailNoLabel.
  destruct ireg_eq; [apply tail_nolabel_cons; unfold nolabel;auto|]; eapply tail_nolabel_trans; TailNoLabel.
- unfold xorimm64, opimm64. destruct Int64.eq. TailNoLabel.
  destruct ireg_eq; [apply tail_nolabel_cons; unfold nolabel;auto|]; eapply tail_nolabel_trans; TailNoLabel.
- unfold rolm64, andimm64_base, opimm64.
  destruct (is_rldl_mask i0 || is_rldr_mask i0 || is_rldl_mask (Int64.shru' i0 i)). TailNoLabel.
  apply tail_nolabel_cons; unfold nolabel; auto.
  destruct Int64.eq. TailNoLabel.
  destruct ireg_eq; [apply tail_nolabel_cons; unfold nolabel;auto|]; eapply tail_nolabel_trans; TailNoLabel.
- eapply transl_cond_op_label; eauto.
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
  destruct (symbol_is_small_data i i0). TailNoLabel. destruct (symbol_is_rel_data i i0); TailNoLabel.
  destruct (symbol_is_small_data i i0). TailNoLabel. destruct (symbol_is_rel_data i i0); TailNoLabel.
  destruct (Int.eq (high_s (Ptrofs.to_int i)) Int.zero); TailNoLabel.
Qed.

Remark transl_epilogue_label:
  forall f k, tail_nolabel k (transl_epilogue f k).
Proof.
  intros; unfold transl_epilogue; destruct (is_leaf_function f); TailNoLabel.
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
  destruct s0; monadInv H; TailNoLabel; (eapply tail_nolabel_trans; [apply transl_epilogue_label | TailNoLabel]). 
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto.
  destruct (snd (crbit_for_cond c0)); TailNoLabel.
  eapply tail_nolabel_trans; [apply transl_epilogue_label | TailNoLabel]. 
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
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0.
  simpl. eapply transl_code_label; eauto.
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
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
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
  destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0. monadInv EQ.
  rewrite transl_code'_transl_code in EQ0.
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
        (DXP: ep = true -> rs#GPR11 = parent_sp s)
        (LEAF: is_leaf_function f = true -> rs#LR = parent_ra s),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
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
  (is_leaf_function f = true -> rs1#LR = parent_ra s) ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#GPR11 = parent_sp s)
    /\ rs2#LR = rs1#LR) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H8.
  exploit H4; eauto. intros (rs2 & A & B & C & D).
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto. rewrite D; auto.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (is_leaf_function f = true -> rs1#LR = parent_ra s) ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2'
    /\ rs2#LR = rs1#LR) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H10.
  exploit H6; eauto. intros (jmp & k' & rs2 & A & B & C & D).
  generalize (functions_transl _ _ _ H8 H9); intro FN.
  generalize (transf_function_no_overflow _ _ H9); intro NOOV.
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
  intros. rewrite OTH by congruence. rewrite D. auto.
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

Remark preg_of_not_GPR11: forall r, negb (mreg_eq r R11) = true -> IR GPR11 <> preg_of r.
Proof.
  intros. change (IR GPR11) with (preg_of R11). red; intros.
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
Qed.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1') (WF: wf_state ge S1),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros.
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. apply agree_nextinstr; auto. 
  split. simpl; congruence.
  auto with asmgen.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto with asmgen. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto with asmgen. congruence.
  split. simpl; congruence.
  apply R; auto with asmgen.

- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto with asmgen. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  split. simpl; intros. rewrite Q; auto with asmgen.
  rewrite Q; auto with asmgen.

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
  split. simpl; intros. rewrite R; auto with asmgen.
  apply preg_of_not_GPR11; auto.
  apply R; auto with asmgen.
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
  split. simpl; intros. rewrite U; auto with asmgen.
  apply preg_of_not_GPR11; auto.
  rewrite U; auto with asmgen.

- (* Mop *)
  assert (eval_operation tge sp op rs##args m = Some v).
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto. split. auto.
  split. destruct op; simpl; try discriminate. intros.
  destruct (andb_prop _ _ H1); clear H1.
  rewrite R; auto. apply preg_of_not_GPR11; auto.
  change (destroyed_by_op Omove) with (@nil mreg). simpl; auto.
  apply R; auto with asmgen. 

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
  split. simpl; congruence.
  apply R; auto with asmgen.

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
  split. eapply agree_undef_regs; eauto with asmgen.
  split. simpl; congruence.
  apply Q; auto with asmgen.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H5; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  generalize (code_tail_next_int _ _ _ _ NOOV CT1). intro CT2.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add (Ptrofs.add ofs Ptrofs.one) Ptrofs.one)) fb f c false tf x).
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
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simpl.
  Simpl. rewrite <- H2. auto.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inversion AT; subst.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
  set (rs1 := nextinstr (rs0#CTR <- (Vptr f' Ptrofs.zero))).
  assert (AG1: agree rs (Vptr stk soff) rs1). { apply agree_nextinstr. apply agree_set_other; auto. }
  exploit transl_epilogue_correct; eauto. 
  intros (rs2 & m2' & A & B & C & D & E & F). 
  assert (A': exec_straight tge tf
            (Pmtctr x0 :: transl_epilogue f (Pbctr sig :: x))
            rs0 m'0
            (Pbctr sig :: x) rs2 m2').
  { apply exec_straight_step with rs1 m'0. simpl. rewrite H9. reflexivity. reflexivity. eexact A. }
  clear A.
  exploit exec_straight_steps_2; eauto using functions_transl. 
  intros (ofs' & U & V).
  set (rs3 := rs2#PC <- (rs2 CTR)).
  left; exists (State rs3 m2'); split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor; eauto using functions_transl, find_instr_tail.
  traceEq.
  (* match states *)
  econstructor; eauto. apply agree_set_other; auto. 
  unfold rs3; Simpl. rewrite F by congruence. reflexivity.
+ (* Direct call *)
  exploit transl_epilogue_correct; eauto. 
  intros (rs2 & m2' & A & B & C & D & E & F). 
  exploit exec_straight_steps_2; eauto using functions_transl. 
  intros (ofs' & U & V).
  set (rs3 := rs2#PC <- (Vptr f' Ptrofs.zero)).
  left; exists (State rs3 m2'); split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor; eauto using functions_transl, find_instr_tail.
  simpl. unfold Genv.symbol_address. rewrite symbols_preserved, H. reflexivity.
  traceEq.
  (* match states *)
  econstructor; eauto. apply agree_set_other; auto. 

- (* Mbuiltin *)
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one.
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eauto.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr. rewrite Pregmap.gss.
  rewrite set_res_other. rewrite undef_regs_other_2.
  rewrite <- H1. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  rewrite preg_notin_charact. intros. auto with asmgen.
  auto with asmgen.
  apply agree_nextinstr. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
  congruence.
  intros. Simpl. rewrite set_res_other by auto.
  rewrite undef_regs_other_2; auto with asmgen.

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
  rewrite INV by congruence; auto.

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
  split. eapply agree_undef_regs; eauto with asmgen.
  split. simpl. rewrite B. reflexivity.
  auto with asmgen.
  (* Pbf, taken *)
  econstructor; econstructor; econstructor; split. eexact A.
  split. eapply agree_undef_regs; eauto with asmgen.
  split. simpl. rewrite B. reflexivity.
  auto with asmgen.

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
  split. eapply agree_undef_regs; eauto with asmgen.
  intros; Simpl.
  split. simpl. congruence.
  Simpl. 

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
  eapply agree_undef_regs; eauto.
Local Transparent destroyed_by_jumptable.
  simpl. intros. rewrite C; auto with asmgen. Simpl.
  congruence.
  intros. rewrite C by auto with asmgen. Simpl. 

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inversion AT; subst.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  monadInv H6.
  exploit transl_epilogue_correct; eauto. 
  intros (rs2 & m2' & A & B & C & D & E & F).
  exploit exec_straight_steps_2; eauto using functions_transl. 
  intros (ofs' & U & V).
  set (rs3 := rs2#PC <- (parent_ra s)).
  left; exists (State rs3 m2'); split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor; eauto using functions_transl, find_instr_tail.
  simpl. rewrite D; reflexivity. 
  traceEq.
  (* match states *)
  econstructor; eauto. apply agree_set_other; auto. 

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x0.(fn_code))); inversion EQ1. clear EQ1. subst x0.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto.
  intros [m2' [F G]].
  simpl chunk_of_type in F.
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto.
  intros [m3' [P Q]].
  (* Execution of function prologue *)
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  set (tfbody := Pallocframe (fn_stacksize f) (fn_link_ofs f)
                      (fn_retaddr_ofs f)
                    :: Pmflr GPR0
                       :: Pstw GPR0 (Cint (Ptrofs.to_int (fn_retaddr_ofs f)))
                            GPR1
                          :: Pcfi_rel_offset
                               (Ptrofs.to_int (fn_retaddr_ofs f)) :: x0) in *.
  set (tf := {| fn_sig := Mach.fn_sig f; fn_code := tfbody |}) in *.
  set (rs2 := nextinstr (rs0#GPR1 <- sp #GPR0 <- Vundef)).
  set (rs3 := nextinstr (rs2#GPR0 <- (rs0#LR))).
  set (rs4 := nextinstr rs3).
  set (rs5 := nextinstr rs4).
  assert (EXEC_PROLOGUE:
            exec_straight tge tf
              tf.(fn_code) rs0 m'
              x0 rs5 m3').
  change (fn_code tf) with tfbody; unfold tfbody.
  apply exec_straight_step with rs2 m2'.
  unfold exec_instr. rewrite C. fold sp.
  rewrite <- (sp_val _ _ _ AG). rewrite F. auto. auto.
  apply exec_straight_step with rs3 m2'.
  simpl. auto. auto.
  apply exec_straight_two with rs4 m3'.
  simpl. unfold store1. rewrite gpr_or_zero_not_zero.
  change (rs3 GPR1) with sp. change (rs3 GPR0) with (rs0 LR).
  simpl const_low. rewrite ATLR. erewrite storev_offset_ptr by eexact P. auto. congruence.
  auto. auto. auto.
  left; exists (State rs5 m3'); split.
  eapply exec_straight_steps_1; eauto. omega. constructor.
  econstructor; eauto.
  change (rs5 PC) with (Val.offset_ptr (Val.offset_ptr (Val.offset_ptr (Val.offset_ptr (rs0 PC) Ptrofs.one) Ptrofs.one) Ptrofs.one) Ptrofs.one).
  rewrite ATPC. simpl. constructor; eauto.
  eapply code_tail_next_int. omega.
  eapply code_tail_next_int. omega.
  eapply code_tail_next_int. omega.
  eapply code_tail_next_int. omega.
  constructor.
  unfold rs5, rs4, rs3, rs2.
  apply agree_nextinstr. apply agree_nextinstr.
  apply agree_set_other; auto. apply agree_set_other; auto.
  apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. unfold sp; congruence.
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
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  unfold loc_external_result. apply agree_set_other; auto. apply agree_set_pair; auto.
  apply agree_undef_caller_save_regs; auto. 

- (* return *)
  inv STACKS. simpl in *.
  right. split. omega. split. auto.
  rewrite <- ATPC in H5.
  econstructor; eauto.
  congruence.
  inv WF. inv STACK. inv H1. congruence.
Qed.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Vptr fb Ptrofs.zero).
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  split. auto. simpl. unfold Vnullptr; simpl; congruence. intros. rewrite Regmap.gi. auto.
  unfold Genv.symbol_address.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved.
  unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. constructor. auto.
  compute in H1. inv H1.
  generalize (preg_val _ _ _ R3 AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  eapply forward_simulation_star with
     (measure := measure)
     (match_states := fun S1 S2 => match_states S1 S2 /\ wf_state ge S1).
- apply senv_preserved.
- simpl; intros. exploit transf_initial_states; eauto. intros (s2 & A & B).
  exists s2; intuition auto. apply wf_initial; auto. 
- simpl; intros. destruct H as [MS WF]. eapply transf_final_states; eauto.
- simpl; intros. destruct H0 as [MS WF]. 
  exploit step_simulation; eauto. intros [ (s2' & A & B) | (A & B & C) ].
+ left; exists s2'; intuition auto. eapply wf_step; eauto. 
+ right; intuition auto. eapply wf_step; eauto.
Qed.

End PRESERVATION.

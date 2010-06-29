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

(** Correctness proof for constant propagation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import ConstpropOp.
Require Import Constprop.
Require Import ConstpropOpproof.

(** * Correctness of the static analysis *)

Section ANALYSIS.

Variable ge: genv.

Definition regs_match_approx (a: D.t) (rs: regset) : Prop :=
  forall r, val_match_approx ge (D.get r a) rs#r.

Lemma regs_match_approx_top:
  forall rs, regs_match_approx D.top rs.
Proof.
  intros. red; intros. simpl. rewrite PTree.gempty. 
  unfold Approx.top, val_match_approx. auto.
Qed.

Lemma val_match_approx_increasing:
  forall a1 a2 v,
  Approx.ge a1 a2 -> val_match_approx ge a2 v -> val_match_approx ge a1 v.
Proof.
  intros until v.
  intros [A|[B|C]].
  subst a1. simpl. auto.
  subst a2. simpl. tauto.
  subst a2. auto.
Qed.

Lemma regs_match_approx_increasing:
  forall a1 a2 rs,
  D.ge a1 a2 -> regs_match_approx a2 rs -> regs_match_approx a1 rs.
Proof.
  unfold D.ge, regs_match_approx. intros.
  apply val_match_approx_increasing with (D.get r a2); auto.
Qed.

Lemma regs_match_approx_update:
  forall ra rs a v r,
  val_match_approx ge a v ->
  regs_match_approx ra rs ->
  regs_match_approx (D.set r a ra) (rs#r <- v).
Proof.
  intros; red; intros. rewrite Regmap.gsspec. 
  case (peq r0 r); intro.
  subst r0. rewrite D.gss. auto.
  rewrite D.gso; auto. 
Qed.

Lemma approx_regs_val_list:
  forall ra rs rl,
  regs_match_approx ra rs ->
  val_list_match_approx ge (approx_regs ra rl) rs##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. apply H. auto.
Qed.


(** The correctness of the static analysis follows from the results
  of module [ConstpropOpproof] and the fact that the result of
  the static analysis is a solution of the forward dataflow inequations. *)

Lemma analyze_correct_1:
  forall f pc rs pc' i,
  f.(fn_code)!pc = Some i ->
  In pc' (successors_instr i) ->
  regs_match_approx (transfer f pc (analyze f)!!pc) rs ->
  regs_match_approx (analyze f)!!pc' rs.
Proof.
  intros until i. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with (transfer f pc approxs!!pc).
  eapply DS.fixpoint_solution; eauto.
  unfold successors_list, successors. rewrite PTree.gmap. rewrite H0. auto.
  auto.
  intros. rewrite PMap.gi. apply regs_match_approx_top. 
Qed.

Lemma analyze_correct_3:
  forall f rs,
  regs_match_approx (analyze f)!!(f.(fn_entrypoint)) rs.
Proof.
  intros. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with D.top.
  eapply DS.fixpoint_entry; eauto. auto with coqlib.
  apply regs_match_approx_top. 
  intros. rewrite PMap.gi. apply regs_match_approx_top.
Qed.

End ANALYSIS.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Section PRESERVATION.

Variable prog: program.
Let tprog := transf_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_symbol_transf.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_var_info_transf.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.  
  intros.
  exact (Genv.find_funct_transf transf_fundef _ _ H).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf transf_fundef _ _ H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (transf_fundef f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma transf_ros_correct:
  forall ros rs f approx,
  regs_match_approx ge approx rs ->
  find_function ge ros rs = Some f ->
  find_function tge (transf_ros approx ros) rs = Some (transf_fundef f).
Proof.
  intros until approx; intro MATCH.
  destruct ros; simpl.
  intro.
  exploit functions_translated; eauto. intro FIND.  
  caseEq (D.get r approx); intros; auto.
  generalize (Int.eq_spec i0 Int.zero); case (Int.eq i0 Int.zero); intros; auto.
  generalize (MATCH r). rewrite H0. intros [b [A B]].
  rewrite <- symbols_preserved in A.
  rewrite B in FIND. rewrite H1 in FIND. 
  rewrite Genv.find_funct_find_funct_ptr in FIND.
  simpl. rewrite A. auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  intro. apply function_ptr_translated. auto.
  congruence.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the values of registers in [st1]
  must match their compile-time approximations at the current program
  point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f,
      (forall v, regs_match_approx ge (analyze f)!!pc (rs#res <- v)) ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function f) sp pc rs).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s'
           (MATCH: regs_match_approx ge (analyze f)!!pc rs)
           (STACKS: list_forall2 match_stackframes s s'),
      match_states (State s f sp pc rs m)
                   (State s' (transf_function f) sp pc rs m)
  | match_states_call:
      forall s f args m s',
      list_forall2 match_stackframes s s' ->
      match_states (Callstate s f args m)
                   (Callstate s' (transf_fundef f) args m)
  | match_states_return:
      forall s s' v m,
      list_forall2 match_stackframes s s' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v m).

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function |- _ =>
      cut ((transf_function f).(fn_code)!pc = Some(transf_instr (analyze f)!!pc instr));
      [ simpl transf_instr
      | unfold transf_function, transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS.

  (* Inop *)
  exists (State s' (transf_function f) sp pc' rs m); split.
  TransfInstr; intro. eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analyze_correct_1 with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. auto.

  (* Iop *)
  exists (State s' (transf_function f) sp pc' (rs#res <- v) m); split.
  TransfInstr. caseEq (op_strength_reduction (approx_reg (analyze f)!!pc) op args);
  intros op' args' OSR.
  assert (eval_operation tge sp op' rs##args' = Some v).
    rewrite (eval_operation_preserved _ _ symbols_preserved). 
    generalize (op_strength_reduction_correct ge (approx_reg (analyze f)!!pc) sp rs
                  MATCH op args v).
    rewrite OSR; simpl. auto.
  generalize (eval_static_operation_correct ge op sp
               (approx_regs (analyze f)!!pc args) rs##args v
               (approx_regs_val_list _ _ _ args MATCH) H0).
  case (eval_static_operation op (approx_regs (analyze f)!!pc args)); intros;
  simpl in H2;
  eapply exec_Iop; eauto; simpl.
  congruence.
  congruence.
  elim H2; intros b [A B]. rewrite symbols_preserved. 
  rewrite A; rewrite B; auto.
  econstructor; eauto. 
  eapply analyze_correct_1 with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. 
  eapply eval_static_operation_correct; eauto.
  apply approx_regs_val_list; auto.

  (* Iload *)
  caseEq (addr_strength_reduction (approx_reg (analyze f)!!pc) addr args);
  intros addr' args' ASR.
  assert (eval_addressing tge sp addr' rs##args' = Some a).
    rewrite (eval_addressing_preserved _ _ symbols_preserved). 
    generalize (addr_strength_reduction_correct ge (approx_reg (analyze f)!!pc) sp rs
                  MATCH addr args).
    rewrite ASR; simpl. congruence. 
  TransfInstr. rewrite ASR. intro.
  exists (State s' (transf_function f) sp pc' (rs#dst <- v) m); split.
  eapply exec_Iload; eauto.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. simpl; auto.

  (* Istore *)
  caseEq (addr_strength_reduction (approx_reg (analyze f)!!pc) addr args);
  intros addr' args' ASR.
  assert (eval_addressing tge sp addr' rs##args' = Some a).
    rewrite (eval_addressing_preserved _ _ symbols_preserved). 
    generalize (addr_strength_reduction_correct ge (approx_reg (analyze f)!!pc) sp rs
                  MATCH addr args).
    rewrite ASR; simpl. congruence. 
  TransfInstr. rewrite ASR. intro.
  exists (State s' (transf_function f) sp pc' rs m'); split.
  eapply exec_Istore; eauto.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. auto. 

  (* Icall *)
  exploit transf_ros_correct; eauto. intro FIND'.
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Icall; eauto. apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto. 
  intros. eapply analyze_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  apply regs_match_approx_update; auto. simpl. auto.

  (* Itailcall *)
  exploit transf_ros_correct; eauto. intros FIND'.
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  constructor; auto. 

  (* Ibuiltin *)
  TransfInstr. intro.
  exists (State s' (transf_function f) sp pc' (rs#res <- v) m'); split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. simpl; auto.

  (* Icond, true *)
  exists (State s' (transf_function f) sp ifso rs m); split. 
  caseEq (cond_strength_reduction (approx_reg (analyze f)!!pc) cond args);
  intros cond' args' CSR.
  assert (eval_condition cond' rs##args' = Some true).
    generalize (cond_strength_reduction_correct
                  ge (approx_reg (analyze f)!!pc) rs MATCH cond args).
    rewrite CSR.  intro. congruence.
  TransfInstr. rewrite CSR. 
  caseEq (eval_static_condition cond (approx_regs (analyze f)!!pc args)).
  intros b ESC. 
  generalize (eval_static_condition_correct ge cond _ _ _
               (approx_regs_val_list _ _ _ args MATCH) ESC); intro.
  replace b with true. intro; eapply exec_Inop; eauto. congruence.
  intros. eapply exec_Icond_true; eauto.
  econstructor; eauto.
  eapply analyze_correct_1; eauto.
  simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Icond, false *)
  exists (State s' (transf_function f) sp ifnot rs m); split. 
  caseEq (cond_strength_reduction (approx_reg (analyze f)!!pc) cond args);
  intros cond' args' CSR.
  assert (eval_condition cond' rs##args' = Some false).
    generalize (cond_strength_reduction_correct
                  ge (approx_reg (analyze f)!!pc) rs MATCH cond args).
    rewrite CSR.  intro. congruence.
  TransfInstr. rewrite CSR. 
  caseEq (eval_static_condition cond (approx_regs (analyze f)!!pc args)).
  intros b ESC. 
  generalize (eval_static_condition_correct ge cond _ _ _
               (approx_regs_val_list _ _ _ args MATCH) ESC); intro.
  replace b with false. intro; eapply exec_Inop; eauto. congruence.
  intros. eapply exec_Icond_false; eauto.
  econstructor; eauto.
  eapply analyze_correct_1; eauto.
  simpl; auto.
  unfold transfer; rewrite H; auto.

  (* Ijumptable *)
  exists (State s' (transf_function f) sp pc' rs m); split.
  caseEq (intval (approx_reg (analyze f)!!pc) arg); intros.
  exploit intval_correct; eauto. eexact MATCH. intro VRS.
  eapply exec_Inop; eauto. TransfInstr. rewrite H2. 
  replace i with n by congruence. rewrite H1. auto.
  eapply exec_Ijumptable; eauto. TransfInstr. rewrite H2. auto.
  constructor; auto.
  eapply analyze_correct_1; eauto.
  simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite  H; auto.

  (* Ireturn *)
  exists (Returnstate s' (regmap_optget or Vundef rs) m'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.

  (* internal function *)
  simpl. unfold transf_function.
  econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  apply analyze_correct_3; auto.

  (* external function *)
  simpl. econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.

  (* return *)
  inv H3. inv H1. 
  econstructor; split.
  eapply exec_return; eauto. 
  econstructor; eauto. 
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto.
  apply Genv.init_mem_transf; auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  reflexivity.
  rewrite <- H3. apply sig_function_translated.
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. constructor. 
Qed.

(** The preservation of the observable behavior of the program then
  follows, using the generic preservation theorem
  [Smallstep.simulation_step_preservation]. *)

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  exec_program prog beh -> exec_program tprog beh.
Proof.
  unfold exec_program; intros.
  eapply simulation_step_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct. 
Qed.

End PRESERVATION.

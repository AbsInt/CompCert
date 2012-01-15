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
Variable sp: val.

Definition regs_match_approx (a: D.t) (rs: regset) : Prop :=
  forall r, val_match_approx ge sp (D.get r a) rs#r.

Lemma regs_match_approx_top:
  forall rs, regs_match_approx D.top rs.
Proof.
  intros. red; intros. simpl. rewrite PTree.gempty. 
  unfold Approx.top, val_match_approx. auto.
Qed.

Lemma val_match_approx_increasing:
  forall a1 a2 v,
  Approx.ge a1 a2 -> val_match_approx ge sp a2 v -> val_match_approx ge sp a1 v.
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
  val_match_approx ge sp a v ->
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
  val_list_match_approx ge sp (approx_regs ra rl) rs##rl.
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
  unfold successors_list, successors. rewrite PTree.gmap1. rewrite H0. auto.
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

Definition regs_lessdef (rs1 rs2: regset) : Prop :=
  forall r, Val.lessdef (rs1#r) (rs2#r).

Lemma regs_lessdef_regs:
  forall rs1 rs2, regs_lessdef rs1 rs2 ->
  forall rl, Val.lessdef_list rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

Lemma set_reg_lessdef:
  forall r v1 v2 rs1 rs2,
  Val.lessdef v1 v2 -> regs_lessdef rs1 rs2 -> regs_lessdef (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r); auto.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

Lemma transf_ros_correct:
  forall sp ros rs rs' f approx,
  regs_match_approx ge sp approx rs ->
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function tge (transf_ros approx ros) rs' = Some (transf_fundef f).
Proof.
  intros. destruct ros; simpl in *.
  generalize (H r); intro MATCH. generalize (H1 r); intro LD.
  destruct (rs#r); simpl in H0; try discriminate.
  destruct (Int.eq_dec i Int.zero); try discriminate.
  inv LD. 
  assert (find_function tge (inl _ r) rs' = Some (transf_fundef f)).
    simpl. rewrite <- H4. simpl. rewrite dec_eq_true. apply function_ptr_translated. auto.
  destruct (D.get r approx); auto.
  predSpec Int.eq Int.eq_spec i0 Int.zero; intros; auto.
  simpl in *. unfold symbol_address in MATCH. rewrite symbols_preserved.
  destruct (Genv.find_symbol ge i); try discriminate. 
  inv MATCH. apply function_ptr_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); try discriminate.
  apply function_ptr_translated; auto.
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
      forall res sp pc rs f rs',
      regs_lessdef rs rs' ->
      (forall v, regs_match_approx ge sp (analyze f)!!pc (rs#res <- v)) ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function f) sp pc rs').

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' rs' m'
           (MATCH: regs_match_approx ge sp (analyze f)!!pc rs)
           (STACKS: list_forall2 match_stackframes s s')
           (REGS: regs_lessdef rs rs')
           (MEM: Mem.extends m m'),
      match_states (State s f sp pc rs m)
                   (State s' (transf_function f) sp pc rs' m')
  | match_states_call:
      forall s f args m s' args' m'
           (STACKS: list_forall2 match_stackframes s s')
           (ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m'),
      match_states (Callstate s f args m)
                   (Callstate s' (transf_fundef f) args' m')
  | match_states_return:
      forall s v m s' v' m'
           (STACKS: list_forall2 match_stackframes s s')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      list_forall2 match_stackframes s s' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v' m').

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
  exists (State s' (transf_function f) sp pc' rs' m'); split.
  TransfInstr; intro. eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analyze_correct_1 with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. auto.

  (* Iop *)
  assert (MATCH': regs_match_approx ge sp (analyze f) # pc' rs # res <- v).
    eapply analyze_correct_1 with (pc := pc); eauto. simpl; auto.
    unfold transfer; rewrite H. 
    apply regs_match_approx_update; auto. 
    eapply eval_static_operation_correct; eauto.
    apply approx_regs_val_list; auto.
  TransfInstr.
  exploit eval_static_operation_correct; eauto. eapply approx_regs_val_list; eauto. intros VM.
  destruct (eval_static_operation op (approx_regs (analyze f) # pc args)); intros; simpl in VM.
  (* Novalue *)
  contradiction.
  (* Unknown *)
  exploit op_strength_reduction_correct. eexact MATCH. reflexivity. eauto. 
  destruct (op_strength_reduction op args (approx_regs (analyze f) # pc args)) as [op' args'].
  intros [v' [EV' LD']].
  assert (EV'': exists v'', eval_operation ge sp op' rs'##args' m' = Some v'' /\ Val.lessdef v' v'').
    eapply eval_operation_lessdef; eauto. eapply regs_lessdef_regs; eauto.
  destruct EV'' as [v'' [EV'' LD'']].
  exists (State s' (transf_function f) sp pc' (rs'#res <- v'') m'); split.
  econstructor. eauto. rewrite <- EV''. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto. apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.
  (* I i *)
  subst v. exists (State s' (transf_function f) sp pc' (rs'#res <- (Vint i)) m'); split.
  econstructor; eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.
  (* F *)
  subst v. exists (State s' (transf_function f) sp pc' (rs'#res <- (Vfloat f0)) m'); split.
  econstructor; eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.
  (* G *)
  subst v. exists (State s' (transf_function f) sp pc' (rs'#res <- (symbol_address tge i i0)) m'); split.
  econstructor; eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.
  unfold symbol_address. rewrite symbols_preserved; auto. 
  (* S *)
  subst v. exists (State s' (transf_function f) sp pc' (rs'#res <- (Val.add sp (Vint i))) m'); split.
  econstructor; eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.

  (* Iload *)
  TransfInstr. 
  generalize (addr_strength_reduction_correct ge sp (analyze f)!!pc rs
                  MATCH addr args (approx_regs (analyze f) # pc args) (refl_equal _)).
  destruct (addr_strength_reduction addr args (approx_regs (analyze f) # pc args)) as [addr' args'].
  intros P Q. rewrite H0 in P.
  assert (ADDR': exists a', eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a').
    eapply eval_addressing_lessdef; eauto. eapply regs_lessdef_regs; eauto.
  destruct ADDR' as [a' [A B]].
  assert (C: eval_addressing tge sp addr' rs'##args' = Some a').
    rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
  exploit Mem.loadv_extends; eauto. intros [v' [D E]].
  exists (State s' (transf_function f) sp pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload; eauto.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. simpl; auto.
  apply set_reg_lessdef; auto. 

  (* Istore *)
  TransfInstr.
  generalize (addr_strength_reduction_correct ge sp (analyze f)!!pc rs
                  MATCH addr args (approx_regs (analyze f) # pc args) (refl_equal _)).
  destruct (addr_strength_reduction addr args (approx_regs (analyze f) # pc args)) as [addr' args'].
  intros P Q. rewrite H0 in P.
  assert (ADDR': exists a', eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a').
    eapply eval_addressing_lessdef; eauto. eapply regs_lessdef_regs; eauto.
  destruct ADDR' as [a' [A B]].
  assert (C: eval_addressing tge sp addr' rs'##args' = Some a').
    rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
  exploit Mem.storev_extends; eauto. intros [m2' [D E]].
  exists (State s' (transf_function f) sp pc' rs' m2'); split.
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
  apply regs_lessdef_regs; auto. 

  (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit transf_ros_correct; eauto. intros FIND'.
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  constructor; auto. apply regs_lessdef_regs; auto. 

  (* Ibuiltin *)
Opaque builtin_strength_reduction.
  destruct (builtin_strength_reduction ef args (approx_regs (analyze f)#pc args)) as [ef' args']_eqn.
  generalize (builtin_strength_reduction_correct ge sp (analyze f)!!pc rs
                  MATCH ef args (approx_regs (analyze f) # pc args) _ _ _ _ (refl_equal _) H0).
  rewrite Heqp. intros P.
  exploit external_call_mem_extends; eauto. 
  instantiate (1 := rs'##args'). apply regs_lessdef_regs; auto.
  intros [v' [m2' [A [B [C D]]]]].
  exists (State s' (transf_function f) sp pc' (rs'#res <- v') m2'); split.
  eapply exec_Ibuiltin. TransfInstr. rewrite Heqp. eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. simpl; auto.
  apply set_reg_lessdef; auto.

  (* Icond *)
  TransfInstr. 
  generalize (cond_strength_reduction_correct ge sp (analyze f)#pc rs m
                    MATCH cond args (approx_regs (analyze f) # pc args) (refl_equal _)).
  destruct (cond_strength_reduction cond args (approx_regs (analyze f) # pc args)) as [cond' args'].
  intros EV1. 
  exists (State s' (transf_function f) sp (if b then ifso else ifnot) rs' m'); split. 
  destruct (eval_static_condition cond (approx_regs (analyze f) # pc args)) as []_eqn.
  assert (eval_condition cond rs ## args m = Some b0).
    eapply eval_static_condition_correct; eauto. eapply approx_regs_val_list; eauto.
  assert (b = b0) by congruence. subst b0.
  destruct b; eapply exec_Inop; eauto. 
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef with (vl1 := rs##args'); eauto. eapply regs_lessdef_regs; eauto. congruence.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. destruct b; simpl; auto. 
  unfold transfer; rewrite H. auto. 

  (* Ijumptable *)
  assert (A: (fn_code (transf_function f))!pc = Some(Ijumptable arg tbl)
             \/ (fn_code (transf_function f))!pc = Some(Inop pc')).
  TransfInstr. destruct (approx_reg (analyze f) # pc arg) as []_eqn; auto.
  generalize (MATCH arg). unfold approx_reg in Heqt. rewrite Heqt. rewrite H0. 
  simpl. intro EQ; inv EQ. rewrite H1. auto.
  assert (B: rs'#arg = Vint n).
  generalize (REGS arg); intro LD; inv LD; congruence.
  exists (State s' (transf_function f) sp pc' rs' m'); split.
  destruct A. eapply exec_Ijumptable; eauto. eapply exec_Inop; eauto. 
  econstructor; eauto.
  eapply analyze_correct_1; eauto.
  simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite  H; auto.

  (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.
  destruct or; simpl; auto. 

  (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m2' [A B]].
  simpl. unfold transf_function.
  econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  apply analyze_correct_3; auto.
  apply init_regs_lessdef; auto.

  (* external function *)
  exploit external_call_mem_extends; eauto. 
  intros [v' [m2' [A [B [C D]]]]].
  simpl. econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.

  (* return *)
  inv H3. inv H1. 
  econstructor; split.
  eapply exec_return; eauto. 
  econstructor; eauto. apply set_reg_lessdef; auto. 
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
  constructor. constructor. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor. 
Qed.

(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct. 
Qed.

End PRESERVATION.

(** Correctness proof for code linearization *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import LTLtyping.
Require Import LTLin.
Require Import Linearize.
Require Import Lattice.

Section LINEARIZATION.

Variable prog: LTL.program.
Let tprog := transf_program prog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_transf _ _ _ transf_fundef prog).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ transf_fundef prog).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ transf_fundef prog).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = LTL.funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros ls f,
  LTL.find_function ge ros ls = Some f ->
  find_function tge ros ls = Some (transf_fundef f).
Proof.
  intros until f. destruct ros; simpl.
  intro. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

(** * Correctness of reachability analysis *)

(** The entry point of the function is reachable. *)

Lemma reachable_entrypoint:
  forall f, (reachable f)!!(f.(fn_entrypoint)) = true.
Proof.
  intros. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux; intros reach A.
  assert (LBoolean.ge reach!!(f.(fn_entrypoint)) true).
  eapply DS.fixpoint_entry. eexact A. auto with coqlib.
  unfold LBoolean.ge in H. tauto.
  intros. apply PMap.gi.
Qed.

(** The successors of a reachable instruction are reachable. *)

Lemma reachable_successors:
  forall f pc pc',
  In pc' (successors f pc) ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  intro f. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux. intro reach; intros.
  elim (LTL.fn_code_wf f pc); intro.
  assert (LBoolean.ge reach!!pc' reach!!pc).
  change (reach!!pc) with ((fun pc r => r) pc (reach!!pc)).
  eapply DS.fixpoint_solution. eexact H. auto. auto.
  elim H3; intro. congruence. auto.
  unfold successors in H0. rewrite H2 in H0. contradiction.
  intros. apply PMap.gi.
Qed.

(** * Properties of node enumeration *)

(** An enumeration of CFG nodes is correct if the following conditions hold:
- All nodes for reachable basic blocks must be in the list.
- The list is without repetition (so that no code duplication occurs).

We prove that our [enumerate] function satisfies all three. *)

Lemma enumerate_complete:
  forall f pc i,
  f.(LTL.fn_code)!pc = Some i ->
  (reachable f)!!pc = true ->
  In pc (enumerate f).
Proof.
  intros. 
  assert (forall p, 
    Plt p f.(fn_nextpc) ->
    (reachable f)!!p = true ->
    In p (enumerate f)).
  unfold enumerate. pattern (fn_nextpc f).
  apply positive_Peano_ind. 
  intros. compute in H1. destruct p; discriminate. 
  intros. rewrite positive_rec_succ. elim (Plt_succ_inv _ _ H2); intro.
  case (reachable f)!!x. apply in_cons. auto. auto.
  subst x. rewrite H3. apply in_eq. 
  elim (LTL.fn_code_wf f pc); intro. auto. congruence.
Qed. 

Lemma enumerate_norepet:
  forall f, list_norepet (enumerate f).
Proof.
  intro. 
  unfold enumerate. pattern (fn_nextpc f).
  apply positive_Peano_ind.  
  rewrite positive_rec_base. constructor.
  intros. rewrite positive_rec_succ.
  case (reachable f)!!x.
  constructor. 
  assert (forall y,
    In y (positive_rec
     (list node) nil
     (fun (pc : positive) (nodes : list node) =>
      if (reachable f) !! pc then pc :: nodes else nodes) x) ->
    Plt y x).
    pattern x. apply positive_Peano_ind. 
    rewrite positive_rec_base. intros. elim H0.
    intros until y. rewrite positive_rec_succ. 
    case (reachable f)!!x0. 
    simpl. intros [A|B].
    subst x0. apply Plt_succ.
    apply Plt_trans_succ. auto. 
    intro. apply Plt_trans_succ. auto.
  red; intro. generalize (H0 x H1). exact (Plt_strict x). auto.
  auto.
Qed.

(** * Properties related to labels *)

(** If labels are globally unique and the LTLin code [c] contains
  a subsequence [Llabel lbl :: c1], [find_label lbl c] returns [c1].
*)

Fixpoint unique_labels (c: code) : Prop :=
  match c with
  | nil => True
  | Llabel lbl :: c => ~(In (Llabel lbl) c) /\ unique_labels c
  | i :: c => unique_labels c
  end.

Lemma find_label_unique:
  forall lbl c1 c2 c3,
  is_tail (Llabel lbl :: c1) c2 ->
  unique_labels c2 ->
  find_label lbl c2 = Some c3 ->
  c1 = c3.
Proof.
  induction c2.
  simpl; intros; discriminate.
  intros c3 TAIL UNIQ. simpl.
  generalize (is_label_correct lbl a). case (is_label lbl a); intro ISLBL.
  subst a. intro. inversion TAIL. congruence. 
  elim UNIQ; intros. elim H4. apply is_tail_in with c1; auto.
  inversion TAIL. congruence. apply IHc2. auto. 
  destruct a; simpl in UNIQ; tauto.
Qed.

(** Correctness of the [starts_with] test. *)

Lemma starts_with_correct:
  forall lbl c1 c2 c3 s f sp ls m,
  is_tail c1 c2 ->
  unique_labels c2 ->
  starts_with lbl c1 = true ->
  find_label lbl c2 = Some c3 ->
  plus step tge (State s f sp c1 ls m)
             E0 (State s f sp c3 ls m).
Proof.
  induction c1.
  simpl; intros; discriminate.
  simpl starts_with. destruct a; try (intros; discriminate).
  intros. 
  apply plus_left with E0 (State s f sp c1 ls m) E0.
  simpl. constructor. 
  destruct (peq lbl l).
  subst l. replace c3 with c1. constructor.
  apply find_label_unique with lbl c2; auto.
  apply plus_star. 
  apply IHc1 with c2; auto. eapply is_tail_cons_left; eauto.
  traceEq.
Qed.

(** Connection between [find_label] and linearization. *)

Lemma find_label_add_branch:
  forall lbl k s,
  find_label lbl (add_branch s k) = find_label lbl k.
Proof.
  intros. unfold add_branch. destruct (starts_with s k); auto.
Qed.

Lemma find_label_lin_instr:
  forall lbl k b,
  find_label lbl (linearize_instr b k) = find_label lbl k.
Proof.
  intros lbl k. generalize (find_label_add_branch lbl k); intro.
  induction b; simpl; auto.
  case (starts_with n k); simpl; auto.
Qed.

Lemma find_label_lin_rec:
  forall f enum pc b,
  In pc enum ->
  f.(LTL.fn_code)!pc = Some b ->
  exists k, find_label pc (linearize_body f enum) = Some (linearize_instr b k).
Proof.
  induction enum; intros.
  elim H.
  case (peq a pc); intro.
  subst a. exists (linearize_body f enum).
  simpl. rewrite H0. simpl. rewrite peq_true. auto.
  assert (In pc enum). simpl in H. tauto.
  elim (IHenum pc b H1 H0). intros k FIND.
  exists k. simpl. destruct (LTL.fn_code f)!a. 
  simpl. rewrite peq_false. rewrite find_label_lin_instr. auto. auto.
  auto.
Qed.

Lemma find_label_lin:
  forall f pc b,
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  exists k,
  find_label pc (fn_code (transf_function f)) = Some (linearize_instr b k).
Proof.
  intros. unfold transf_function; simpl.
  rewrite find_label_add_branch. apply find_label_lin_rec.
  eapply enumerate_complete; eauto. auto.
Qed.

Lemma find_label_lin_inv:
  forall f pc b k ,
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  find_label pc (fn_code (transf_function f)) = Some k ->
  exists k', k = linearize_instr b k'.
Proof.
  intros. exploit find_label_lin; eauto. intros [k' FIND].
  exists k'. congruence.
Qed.

Lemma find_label_lin_succ:
  forall f s,
  valid_successor f s ->
  (reachable f)!!s = true ->
  exists k,
  find_label s (fn_code (transf_function f)) = Some k.
Proof.
  intros. destruct H as [i AT]. 
  exploit find_label_lin; eauto. intros [k FIND].
  exists (linearize_instr i k); auto.
Qed.

(** Unique label property for linearized code. *)

Lemma label_in_add_branch:
  forall lbl s k,
  In (Llabel lbl) (add_branch s k) -> In (Llabel lbl) k.
Proof.
  intros until k; unfold add_branch.
  destruct (starts_with s k); simpl; intuition congruence.
Qed.

Lemma label_in_lin_instr:
  forall lbl k b,
  In (Llabel lbl) (linearize_instr b k) -> In (Llabel lbl) k.
Proof.
  induction b; simpl; intros;
  try (apply label_in_add_branch with n; intuition congruence);
  try (intuition congruence).
  destruct (starts_with n k); simpl in H.
  apply label_in_add_branch with n; intuition congruence.
  apply label_in_add_branch with n0; intuition congruence.
Qed.

Lemma label_in_lin_rec:
  forall f lbl enum,
  In (Llabel lbl) (linearize_body f enum) -> In lbl enum.
Proof.
  induction enum.
  simpl; auto.
  simpl. destruct (LTL.fn_code f)!a. 
  simpl. intros [A|B]. left; congruence. 
  right. apply IHenum. eapply label_in_lin_instr; eauto.
  intro; right; auto.
Qed.

Lemma unique_labels_add_branch:
  forall lbl k,
  unique_labels k -> unique_labels (add_branch lbl k).
Proof.
  intros; unfold add_branch. 
  destruct (starts_with lbl k); simpl; intuition.
Qed.

Lemma unique_labels_lin_instr:
  forall k b,
  unique_labels k -> unique_labels (linearize_instr b k).
Proof.
  induction b; intro; simpl; auto; try (apply unique_labels_add_branch; auto).
  case (starts_with n k); simpl; apply unique_labels_add_branch; auto.
Qed.

Lemma unique_labels_lin_rec:
  forall f enum,
  list_norepet enum ->
  unique_labels (linearize_body f enum).
Proof.
  induction enum.
  simpl; auto.
  intro. simpl. destruct (LTL.fn_code f)!a. 
  simpl. split. red. intro. inversion H. elim H3.
  apply label_in_lin_rec with f. 
  apply label_in_lin_instr with i. auto.
  apply unique_labels_lin_instr. apply IHenum. inversion H; auto.
  apply IHenum. inversion H; auto.
Qed.

Lemma unique_labels_transf_function:
  forall f,
  unique_labels (fn_code (transf_function f)).
Proof.
  intros. unfold transf_function; simpl.
  apply unique_labels_add_branch. 
  apply unique_labels_lin_rec. apply enumerate_norepet. 
Qed.

(** Correctness of [add_branch]. *)

Lemma is_tail_find_label:
  forall lbl c2 c1,
  find_label lbl c1 = Some c2 -> is_tail c2 c1.
Proof.
  induction c1; simpl.
  intros; discriminate.
  case (is_label lbl a). intro. injection H; intro. subst c2.
  constructor. constructor.
  intro. constructor. auto. 
Qed.

Lemma is_tail_add_branch:
  forall lbl c1 c2, is_tail (add_branch lbl c1) c2 -> is_tail c1 c2.
Proof.
  intros until c2. unfold add_branch. destruct (starts_with lbl c1).
  auto. eauto with coqlib.
Qed.

Lemma add_branch_correct:
  forall lbl c k s f sp ls m,
  is_tail k (transf_function f).(fn_code) ->
  find_label lbl (transf_function f).(fn_code) = Some c ->
  plus step tge (State s (transf_function f) sp (add_branch lbl k) ls m)
             E0 (State s (transf_function f) sp c ls m).
Proof.
  intros. unfold add_branch.
  caseEq (starts_with lbl k); intro SW.
  eapply starts_with_correct; eauto.
  apply unique_labels_transf_function.
  apply plus_one. apply exec_Lgoto. auto.
Qed.

(** * Correctness of linearization *)

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant (horizontal lines above) is the [match_states]
  predicate defined below.  It captures the fact that the flow
  of data is the same in the source and linearized codes.
  Moreover, whenever the source state is at node [pc] in its
  control-flow graph, the transformed state is at a code
  sequence [c] that starts with the label [pc]. *)

Inductive match_stackframes: LTL.stackframe -> LTLin.stackframe -> Prop :=
  | match_stackframe_intro:
      forall res f sp pc ls c,
      (reachable f)!!pc = true ->
      valid_successor f pc ->
      is_tail c (fn_code (transf_function f)) ->
      wt_function f ->
      match_stackframes
        (LTL.Stackframe res f sp ls pc)
        (LTLin.Stackframe res (transf_function f) sp ls (add_branch pc c)).

Inductive match_states: LTL.state -> LTLin.state -> Prop :=
  | match_states_intro:
      forall s f sp pc ls m ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (REACH: (reachable f)!!pc = true)
        (AT: find_label pc (fn_code (transf_function f)) = Some c)
        (WTF: wt_function f),
      match_states (LTL.State s f sp pc ls m)
                   (LTLin.State ts (transf_function f) sp c ls m)
  | match_states_call:
      forall s f ls m ts,
      list_forall2 match_stackframes s ts ->
      wt_fundef f ->
      match_states (LTL.Callstate s f ls m)
                   (LTLin.Callstate ts (transf_fundef f) ls m)
  | match_states_return:
      forall s sig ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (LTL.Returnstate s sig ls m)
                   (LTLin.Returnstate ts sig ls m).

Remark parent_locset_match:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  parent_locset ts = LTL.parent_locset s.
Proof.
  induction 1; simpl; auto. inv H; auto. 
Qed.

Hypothesis wt_prog: wt_program prog.

Theorem transf_step_correct:
  forall s1 t s2, LTL.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', plus LTLin.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; try (inv MS);
  try (generalize (wt_instrs _ WTF _ _ H); intro WTI).
  (* Lnop *)
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto.
  unfold successors; rewrite H; auto with coqlib.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_find_label. eauto.
  econstructor; eauto. 
  (* Lop *)
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto.
  unfold successors; rewrite H; auto with coqlib.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply plus_left'.
  eapply exec_Lop with (v := v); eauto.
  rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.
  (* Lload *)
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto.
  unfold successors; rewrite H; auto with coqlib.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply plus_left'.
  eapply exec_Lload; eauto.
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.
  (* Lstore *)
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto.
  unfold successors; rewrite H; auto with coqlib.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply plus_left'.
  eapply exec_Lstore; eauto.
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.
  (* Lcall *)
  unfold rs1 in *. inv MS. fold rs1.
  generalize (wt_instrs _ WTF _ _ H); intro WTI.
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto.
  unfold successors; rewrite H; auto with coqlib.
  assert (VALID: valid_successor f pc'). inv WTI; auto.
  econstructor; split.
  apply plus_one. eapply exec_Lcall with (f' := transf_fundef f'); eauto.
  apply find_function_translated; auto.
  symmetry; apply sig_preserved.
  econstructor; eauto.
  constructor; auto. econstructor; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  destruct ros; simpl in H0.
  eapply Genv.find_funct_prop; eauto.
  destruct (Genv.find_symbol ge i); try discriminate.  
  eapply Genv.find_funct_ptr_prop; eauto.

  (* Ltailcall *)
  unfold rs2, rs1 in *. inv MS. fold rs1; fold rs2.
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  econstructor; split.
  apply plus_one. eapply exec_Ltailcall with (f' := transf_fundef f'); eauto.
  apply find_function_translated; auto.
  symmetry; apply sig_preserved.
  rewrite (parent_locset_match _ _ STACKS).
  econstructor; eauto.
  destruct ros; simpl in H0.
  eapply Genv.find_funct_prop; eauto.
  destruct (Genv.find_symbol ge i); try discriminate.  
  eapply Genv.find_funct_ptr_prop; eauto.

  (* Lalloc *)
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto.
  unfold successors; rewrite H; auto with coqlib.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply plus_left'. 
  eapply exec_Lalloc; eauto.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.
  (* Lcond true *)
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!ifso = true).
  eapply reachable_successors; eauto.
  unfold successors; rewrite H; auto with coqlib.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  destruct (starts_with ifso c').
  econstructor; split.
  eapply plus_left'.  
  eapply exec_Lcond_false; eauto.
  change false with (negb true). apply eval_negate_condition; auto.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.
  econstructor; split.
  apply plus_one. eapply exec_Lcond_true; eauto.
  econstructor; eauto.
  (* Lcond false *)
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!ifnot = true).
  eapply reachable_successors; eauto.
  unfold successors; rewrite H; auto with coqlib.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  destruct (starts_with ifso c').
  econstructor; split.
  apply plus_one. eapply exec_Lcond_true; eauto.
  change true with (negb false). apply eval_negate_condition; auto.
  econstructor; eauto.
  econstructor; split.
  eapply plus_left'. 
  eapply exec_Lcond_false; eauto.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.
  (* Lreturn *)
  destruct (find_label_lin_inv _ _ _ _ H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  econstructor; split.
  apply plus_one. eapply exec_Lreturn; eauto.
  rewrite (parent_locset_match _ _ STACKS).
  econstructor; eauto. 
  (* internal function *)
  assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true).
    apply reachable_entrypoint.
  inv H6. 
  exploit find_label_lin_succ; eauto. inv H1; auto. intros [c'' AT'].
  simpl. econstructor; split.
  eapply plus_left'.  
  eapply exec_function_internal; eauto.
  simpl. eapply add_branch_correct. 
  simpl. eapply is_tail_add_branch. constructor. eauto.
  traceEq.
  econstructor; eauto.
  (* external function *)
  simpl. econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  econstructor; eauto.
  (* return *)
  inv H4. inv H1.
  exploit find_label_lin_succ; eauto. intros [c' AT].
  econstructor; split.
  eapply plus_left'.
  eapply exec_return; eauto.
  eapply add_branch_correct; eauto. traceEq.
  econstructor; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, LTL.initial_state prog st1 ->
  exists st2, LTLin.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. 
  exists (Callstate nil (transf_fundef f) (Locmap.init Vundef) (Genv.init_mem tprog)); split.
  econstructor; eauto.
  change (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  apply function_ptr_translated; auto.
  rewrite <- H2. apply sig_preserved.
  replace (Genv.init_mem tprog) with (Genv.init_mem prog).
  constructor. constructor.
  eapply Genv.find_funct_ptr_prop; eauto.
  symmetry. unfold tprog, transf_program. apply Genv.init_mem_transf.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> LTL.final_state st1 r -> LTLin.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H6. constructor. auto. 
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior),
  LTL.exec_program prog beh -> LTLin.exec_program tprog beh.
Proof.
  unfold LTL.exec_program, exec_program; intros.
  eapply simulation_plus_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct.
Qed.

End LINEARIZATION.

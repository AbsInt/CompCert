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

(** Correctness proof for code linearization *)

Require Import Coqlib.
Require Import Maps.
Require Import Ordered.
Require Import FSets.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Errors.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import LTLtyping.
Require Import LTLin.
Require Import Linearize.
Require Import Lattice.

Module NodesetFacts := FSetFacts.Facts(Nodeset).

Section LINEARIZATION.

Variable prog: LTL.program.
Variable tprog: LTLin.program.

Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf_partial transf_fundef _ TRANSF).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (Genv.find_var_info_transf_partial transf_fundef _ TRANSF).

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  LTLin.funsig tf = LTL.funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H. monadInv EQ. reflexivity.
  inv H. reflexivity.
Qed.

Lemma stacksize_preserved:
  forall f tf,
  transf_function f = OK tf ->
  LTLin.fn_stacksize tf = LTL.fn_stacksize f.
Proof.
  intros. monadInv H. auto.
Qed.

Lemma find_function_translated:
  forall ros ls f,
  LTL.find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros ls = Some tf /\ transf_fundef f = OK tf.
Proof.
  unfold LTL.find_function; intros; destruct ros; simpl.
  apply functions_translated; auto.
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
  forall f pc pc' i,
  f.(LTL.fn_code)!pc = Some i -> In pc' (successors_instr i) ->
  (reachable f)!!pc = true ->
  (reachable f)!!pc' = true.
Proof.
  intro f. unfold reachable.
  caseEq (reachable_aux f).
  unfold reachable_aux. intro reach; intros.
  assert (LBoolean.ge reach!!pc' reach!!pc).
  change (reach!!pc) with ((fun pc r => r) pc (reach!!pc)).
  eapply DS.fixpoint_solution. eexact H.
  unfold Kildall.successors_list, successors. rewrite PTree.gmap.
  rewrite H0; auto.
  elim H3; intro. congruence. auto.
  intros. apply PMap.gi.
Qed.

(** * Properties of node enumeration *)

(** An enumeration of CFG nodes is correct if the following conditions hold:
- All nodes for reachable basic blocks must be in the list.
- The list is without repetition (so that no code duplication occurs).

We prove that the result of the [enumerate] function satisfies both
conditions. *)

Lemma nodeset_of_list_correct:
  forall l s s',
  nodeset_of_list l s = OK s' ->
  list_norepet l
  /\ (forall pc, Nodeset.In pc s' <-> Nodeset.In pc s \/ In pc l)
  /\ (forall pc, In pc l -> ~Nodeset.In pc s).
Proof.
  induction l; simpl; intros. 
  inv H. split. constructor. split. intro; tauto. intros; tauto.
  generalize H; clear H; caseEq (Nodeset.mem a s); intros.
  inv H0.
  exploit IHl; eauto. intros [A [B C]].
  split. constructor; auto. red; intro. elim (C a H1). apply Nodeset.add_1. hnf. auto.
  split. intros. rewrite B. rewrite NodesetFacts.add_iff. 
  unfold Nodeset.E.eq. unfold OrderedPositive.eq. tauto.
  intros. destruct H1. subst pc. rewrite NodesetFacts.not_mem_iff. auto.
  generalize (C pc H1). rewrite NodesetFacts.add_iff. tauto.
Qed.

Lemma check_reachable_correct:
  forall f reach s pc i,
  check_reachable f reach s = true ->
  f.(LTL.fn_code)!pc = Some i ->
  reach!!pc = true ->
  Nodeset.In pc s.
Proof.
  intros f reach s.
  assert (forall l ok, 
    List.fold_left (fun a p => check_reachable_aux reach s a (fst p) (snd p)) l ok = true ->
    ok = true /\
    (forall pc i,
     In (pc, i) l ->
     reach!!pc = true ->
     Nodeset.In pc s)).
  induction l; simpl; intros.
  split. auto. intros. destruct H0.
  destruct a as [pc1 i1]. simpl in H. 
  exploit IHl; eauto. intros [A B].
  unfold check_reachable_aux in A. 
  split. destruct (reach!!pc1). elim (andb_prop _ _ A). auto. auto.
  intros. destruct H0. inv H0. rewrite H1 in A. destruct (andb_prop _ _ A). 
  apply Nodeset.mem_2; auto.
  eauto.

  intros pc i. unfold check_reachable. rewrite PTree.fold_spec. intros.
  exploit H; eauto. intros [A B]. eapply B; eauto. 
  apply PTree.elements_correct. eauto.
Qed.

Lemma enumerate_complete:
  forall f enum pc i,
  enumerate f = OK enum ->
  f.(LTL.fn_code)!pc = Some i ->
  (reachable f)!!pc = true ->
  In pc enum.
Proof.
  intros until i. unfold enumerate. 
  set (reach := reachable f).
  intros. monadInv H. 
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit check_reachable_correct; eauto. intro.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]].
  rewrite B in H2. destruct H2. elim (Nodeset.empty_1 H2). auto.
Qed.

Lemma enumerate_norepet:
  forall f enum,
  enumerate f = OK enum ->
  list_norepet enum.
Proof.
  intros until enum. unfold enumerate. 
  set (reach := reachable f).
  intros. monadInv H. 
  generalize EQ0; clear EQ0. caseEq (check_reachable f reach x); intros; inv EQ0.
  exploit nodeset_of_list_correct; eauto. intros [A [B C]]. auto.
Qed.

(** * Properties related to labels *)

(** If labels are globally unique and the LTLin code [c] contains
  a subsequence [Llabel lbl :: c1], then [find_label lbl c] returns [c1].
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
  forall f tf pc b,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  exists k,
  find_label pc (fn_code tf) = Some (linearize_instr b k).
Proof.
  intros. monadInv H. simpl. 
  rewrite find_label_add_branch. apply find_label_lin_rec.
  eapply enumerate_complete; eauto. auto.
Qed.

Lemma find_label_lin_inv:
  forall f tf pc b k,
  transf_function f = OK tf ->
  f.(LTL.fn_code)!pc = Some b ->
  (reachable f)!!pc = true ->
  find_label pc (fn_code tf) = Some k ->
  exists k', k = linearize_instr b k'.
Proof.
  intros. exploit find_label_lin; eauto. intros [k' FIND].
  exists k'. congruence.
Qed.

Lemma find_label_lin_succ:
  forall f tf s,
  transf_function f = OK tf ->
  valid_successor f s ->
  (reachable f)!!s = true ->
  exists k,
  find_label s (fn_code tf) = Some k.
Proof.
  intros. destruct H0 as [i AT]. 
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
  forall f tf,
  transf_function f = OK tf ->
  unique_labels (fn_code tf).
Proof.
  intros. monadInv H. simpl.
  apply unique_labels_add_branch. 
  apply unique_labels_lin_rec. eapply enumerate_norepet; eauto.
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
  forall lbl c k s f tf sp ls m,
  transf_function f = OK tf ->
  is_tail k tf.(fn_code) ->
  find_label lbl tf.(fn_code) = Some c ->
  plus step tge (State s tf sp (add_branch lbl k) ls m)
             E0 (State s tf sp c ls m).
Proof.
  intros. unfold add_branch.
  caseEq (starts_with lbl k); intro SW.
  eapply starts_with_correct; eauto.
  eapply unique_labels_transf_function; eauto.
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
      forall res f sp pc ls tf c,
      transf_function f = OK tf ->
      (reachable f)!!pc = true ->
      valid_successor f pc ->
      is_tail c (fn_code tf) ->
      wt_function f ->
      match_stackframes
        (LTL.Stackframe res f sp ls pc)
        (LTLin.Stackframe res tf sp ls (add_branch pc c)).

Inductive match_states: LTL.state -> LTLin.state -> Prop :=
  | match_states_intro:
      forall s f sp pc ls m tf ts c
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: transf_function f = OK tf)
        (REACH: (reachable f)!!pc = true)
        (AT: find_label pc (fn_code tf) = Some c)
        (WTF: wt_function f),
      match_states (LTL.State s f sp pc ls m)
                   (LTLin.State ts tf sp c ls m)
  | match_states_call:
      forall s f ls m tf ts,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      wt_fundef f ->
      match_states (LTL.Callstate s f ls m)
                   (LTLin.Callstate ts tf ls m)
  | match_states_return:
      forall s ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (LTL.Returnstate s ls m)
                   (LTLin.Returnstate ts ls m).

Hypothesis wt_prog: wt_program prog.

Theorem transf_step_correct:
  forall s1 t s2, LTL.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', plus LTLin.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; try (inv MS);
  try (generalize (wt_instrs _ WTF _ _ H); intro WTI).
  (* Lnop *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto. simpl; auto.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_find_label. eauto.
  econstructor; eauto. 
  (* Lop *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto. simpl; auto.
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
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto. simpl; auto.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply plus_left'.
  apply exec_Lload with a.
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.
  (* Lstore *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto. simpl; auto.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply plus_left'.
  apply exec_Lstore with a. 
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.
  (* Lcall *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto. simpl; auto.
  assert (VALID: valid_successor f pc'). inv WTI; auto.
  exploit find_function_translated; eauto. intros [tf' [A B]].
  econstructor; split.
  apply plus_one. eapply exec_Lcall with (f' := tf'); eauto.
  symmetry; apply sig_preserved; auto.
  econstructor; eauto.
  constructor; auto. econstructor; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  destruct ros; simpl in H0.
  eapply Genv.find_funct_prop; eauto.
  destruct (Genv.find_symbol ge i); try discriminate.  
  eapply Genv.find_funct_ptr_prop; eauto.

  (* Ltailcall *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  exploit find_function_translated; eauto. intros [tf' [A B]].
  econstructor; split.
  apply plus_one. eapply exec_Ltailcall with (f' := tf'); eauto.
  symmetry; apply sig_preserved; auto.
  rewrite (stacksize_preserved _ _ TRF). eauto.
  econstructor; eauto.
  destruct ros; simpl in H0.
  eapply Genv.find_funct_prop; eauto.
  destruct (Genv.find_symbol ge i); try discriminate.  
  eapply Genv.find_funct_ptr_prop; eauto.

  (* Lbuiltin *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto. simpl; auto.
  exploit find_label_lin_succ; eauto. inv WTI; auto. intros [c'' AT'].
  econstructor; split.
  eapply plus_left'.
  eapply exec_Lbuiltin. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eapply add_branch_correct; eauto.
  eapply is_tail_add_branch. eapply is_tail_cons_left. 
  eapply is_tail_find_label. eauto.
  traceEq.
  econstructor; eauto.

  (* Lcond true *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!ifso = true).
  eapply reachable_successors; eauto. simpl; auto.
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
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!ifnot = true).
  eapply reachable_successors; eauto. simpl; auto.
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

  (* Ljumptable *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  assert (REACH': (reachable f)!!pc' = true).
  eapply reachable_successors; eauto. simpl. eapply list_nth_z_in; eauto.
  exploit find_label_lin_succ; eauto.
  inv WTI. apply H6. eapply list_nth_z_in; eauto. 
  intros [c'' AT'].
  econstructor; split.
  apply plus_one. eapply exec_Ljumptable; eauto. 
  econstructor; eauto.

  (* Lreturn *)
  destruct (find_label_lin_inv _ _ _ _ _ TRF H REACH AT) as [c' EQ].
  simpl in EQ. subst c.
  econstructor; split.
  apply plus_one. eapply exec_Lreturn; eauto.
  rewrite (stacksize_preserved _ _ TRF). eauto.
  econstructor; eauto.
 
  (* internal function *)
  assert (REACH: (reachable f)!!(LTL.fn_entrypoint f) = true).
    apply reachable_entrypoint.
  inv H7. monadInv H6.   
  exploit find_label_lin_succ; eauto. inv H1; auto. intros [c'' AT'].
  generalize EQ; intro. monadInv EQ0. econstructor; simpl; split.
  eapply plus_left'.  
  eapply exec_function_internal; eauto.
  simpl. eapply add_branch_correct. eauto.  
  simpl. eapply is_tail_add_branch. constructor. eauto.
  traceEq.
  econstructor; eauto.

  (* external function *)
  monadInv H6. econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.

  (* return *)
  inv H3. inv H1.
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
  exploit function_ptr_translated; eauto. intros [tf [A B]].  
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto. eapply Genv.init_mem_transf_partial; eauto. 
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry. apply (transform_partial_program_main transf_fundef _ TRANSF). 
  rewrite <- H3. apply sig_preserved. auto.
  constructor. constructor. auto.
  eapply Genv.find_funct_ptr_prop; eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> LTL.final_state st1 r -> LTLin.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H4. constructor.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  LTL.exec_program prog beh -> LTLin.exec_program tprog beh.
Proof.
  unfold LTL.exec_program, exec_program; intros.
  eapply simulation_plus_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct.
Qed.

End LINEARIZATION.

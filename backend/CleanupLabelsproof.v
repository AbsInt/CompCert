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

(** Correctness proof for clean-up of labels *)

Require Import FSets.
Require Import Coqlib Ordered Integers.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Linear.
Require Import CleanupLabels.

Module LabelsetFacts := FSetFacts.Facts(Labelset).

Definition match_prog (p tp: Linear.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Section CLEANUP.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma sig_function_translated:
  forall f,
  funsig (transf_fundef f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros ls f,
  find_function ge ros ls = Some f ->
  find_function tge ros ls = Some (transf_fundef f).
Proof.
  unfold find_function; intros; destruct ros; simpl.
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

(** Correctness of [labels_branched_to]. *)

Definition instr_branches_to (i: instruction) (lbl: label) : Prop :=
  match i with
  | Lgoto lbl' => lbl = lbl'
  | Lcond cond args lbl' => lbl = lbl'
  | Ljumptable arg tbl => In lbl tbl
  | _ => False
  end.

Remark add_label_branched_to_incr:
  forall ls i, Labelset.Subset ls (add_label_branched_to ls i).
Proof.
  intros; red; intros; destruct i; simpl; auto.
  apply Labelset.add_2; auto.
  apply Labelset.add_2; auto.
  revert H; induction l; simpl. auto. intros; apply Labelset.add_2; auto.
Qed.

Remark add_label_branched_to_contains:
  forall ls i lbl,
  instr_branches_to i lbl ->
  Labelset.In lbl (add_label_branched_to ls i).
Proof.
  destruct i; simpl; intros; try contradiction.
  apply Labelset.add_1; auto.
  apply Labelset.add_1; auto.
  revert H. induction l; simpl; intros.
  contradiction.
  destruct H. apply Labelset.add_1; auto. apply Labelset.add_2; auto.
Qed.

Lemma labels_branched_to_correct:
  forall c i lbl,
  In i c -> instr_branches_to i lbl -> Labelset.In lbl (labels_branched_to c).
Proof.
  intros.
  assert (forall c' bto,
             Labelset.Subset bto (fold_left add_label_branched_to c' bto)).
  induction c'; intros; simpl; red; intros.
  auto.
  apply IHc'. apply add_label_branched_to_incr; auto.

  assert (forall c' bto,
             In i c' -> Labelset.In lbl (fold_left add_label_branched_to c' bto)).
  induction c'; simpl; intros.
  contradiction.
  destruct H2.
  subst a. apply H1. apply add_label_branched_to_contains; auto.
  apply IHc'; auto.

  unfold labels_branched_to. auto.
Qed.

(** Commutation with [find_label]. *)

Lemma remove_unused_labels_cons:
  forall bto i c,
  remove_unused_labels bto (i :: c) =
  match i with
  | Llabel lbl =>
      if Labelset.mem lbl bto then i :: remove_unused_labels bto c else remove_unused_labels bto c
  | _ =>
      i :: remove_unused_labels bto c
  end.
Proof.
  unfold remove_unused_labels; intros. rewrite list_fold_right_eq. auto.
Qed.


Lemma find_label_commut:
  forall lbl bto,
  Labelset.In lbl bto ->
  forall c c',
  find_label lbl c = Some c' ->
  find_label lbl (remove_unused_labels bto c) = Some (remove_unused_labels bto c').
Proof.
  induction c; simpl; intros.
  congruence.
  rewrite remove_unused_labels_cons.
  unfold is_label in H0. destruct a; simpl; auto.
  destruct (peq lbl l). subst l. inv H0.
  rewrite Labelset.mem_1; auto.
  simpl. rewrite peq_true. auto.
  destruct (Labelset.mem l bto); auto. simpl. rewrite peq_false; auto.
Qed.

Corollary find_label_translated:
  forall f i c' lbl c,
  incl (i :: c') (fn_code f) ->
  find_label lbl (fn_code f) = Some c ->
  instr_branches_to i lbl ->
  find_label lbl (fn_code (transf_function f)) =
     Some (remove_unused_labels (labels_branched_to (fn_code f)) c).
Proof.
  intros. unfold transf_function; unfold cleanup_labels; simpl.
  apply find_label_commut. eapply labels_branched_to_correct; eauto.
  apply H; auto with coqlib.
  auto.
Qed.

Lemma find_label_incl:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl; intros.
  discriminate.
  destruct (is_label lbl a). inv H; auto with coqlib. auto with coqlib.
Qed.

(** Correctness of clean-up *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframe_intro:
      forall f sp ls c,
      incl c f.(fn_code) ->
      match_stackframes
        (Stackframe f sp ls c)
        (Stackframe (transf_function f) sp ls
          (remove_unused_labels (labels_branched_to f.(fn_code)) c)).

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s f sp c ls m ts
        (STACKS: list_forall2 match_stackframes s ts)
        (INCL: incl c f.(fn_code)),
      match_states (State s f sp c ls m)
                   (State ts (transf_function f) sp (remove_unused_labels (labels_branched_to f.(fn_code)) c) ls m)
  | match_states_call:
      forall s f ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (Callstate s f ls m)
                   (Callstate ts (transf_fundef f) ls m)
  | match_states_return:
      forall s ls m ts,
      list_forall2 match_stackframes s ts ->
      match_states (Returnstate s ls m)
                   (Returnstate ts ls m).

Definition measure (st: state) : nat :=
  match st with
  | State s f sp c ls m => List.length c
  | _ => O
  end.

Lemma match_parent_locset:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  parent_locset ts = parent_locset s.
Proof.
  induction 1; simpl. auto. inv H; auto.
Qed.

Theorem transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; try rewrite remove_unused_labels_cons.
(* Lgetstack *)
  left; econstructor; split.
  econstructor; eauto.
  econstructor; eauto with coqlib.
(* Lsetstack *)
  left; econstructor; split.
  econstructor; eauto.
  econstructor; eauto with coqlib.
(* Lop *)
  left; econstructor; split.
  econstructor; eauto. instantiate (1 := v). rewrite <- H.
  apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto with coqlib.
(* Lload *)
  assert (eval_addressing tge sp addr (LTL.reglist rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  econstructor; eauto.
  econstructor; eauto with coqlib.
(* Lstore *)
  assert (eval_addressing tge sp addr (LTL.reglist rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  econstructor; eauto.
  econstructor; eauto with coqlib.
(* Lcall *)
  left; econstructor; split.
  econstructor. eapply find_function_translated; eauto.
  symmetry; apply sig_function_translated.
  econstructor; eauto. constructor; auto. constructor; eauto with coqlib.
(* Ltailcall *)
  left; econstructor; split.
  econstructor. erewrite match_parent_locset; eauto. eapply find_function_translated; eauto.
  symmetry; apply sig_function_translated.
  simpl. eauto.
  econstructor; eauto.
(* Lbuiltin *)
  left; econstructor; split.
  econstructor.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eauto.
  econstructor; eauto with coqlib.
(* Llabel *)
  case_eq (Labelset.mem lbl (labels_branched_to (fn_code f))); intros.
  (* not eliminated *)
  left; econstructor; split.
  constructor.
  econstructor; eauto with coqlib.
  (* eliminated *)
  right. split. simpl. omega. split. auto. econstructor; eauto with coqlib.
(* Lgoto *)
  left; econstructor; split.
  econstructor. eapply find_label_translated; eauto. red; auto.
  econstructor; eauto. eapply find_label_incl; eauto.
(* Lcond taken *)
  left; econstructor; split.
  econstructor. auto. eauto. eapply find_label_translated; eauto. red; auto.
  econstructor; eauto. eapply find_label_incl; eauto.
(* Lcond not taken *)
  left; econstructor; split.
  eapply exec_Lcond_false; eauto.
  econstructor; eauto with coqlib.
(* Ljumptable *)
  left; econstructor; split.
  econstructor. eauto. eauto. eapply find_label_translated; eauto.
  red. eapply list_nth_z_in; eauto. eauto.
  econstructor; eauto. eapply find_label_incl; eauto.
(* Lreturn *)
  left; econstructor; split.
  econstructor; eauto.
  erewrite <- match_parent_locset; eauto.
  econstructor; eauto with coqlib.
(* internal function *)
  left; econstructor; split.
  econstructor; simpl; eauto.
  econstructor; eauto with coqlib.
(* external function *)
  left; econstructor; split.
  econstructor; eauto. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto with coqlib.
(* return *)
  inv H3. inv H1. left; econstructor; split.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  econstructor; split.
  eapply initial_state_intro with (f := transf_fundef f).
  eapply (Genv.init_mem_transf TRANSL); eauto.
  rewrite (match_program_main TRANSL), symbols_preserved; eauto.
  apply function_ptr_translated; auto.
  rewrite sig_function_translated. auto.
  constructor; auto. constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  eapply forward_simulation_opt.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct.
Qed.

End CLEANUP.


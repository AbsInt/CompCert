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

(** Characterization and properties of deterministic semantics *)

Require Import Classical.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.

(** This file uses classical logic (the axiom of excluded middle), as
  well as the following extensionality property over infinite
  sequences of events.  All these axioms are sound in a set-theoretic
  model of Coq's logic. *)

Axiom traceinf_extensionality:
  forall T T', traceinf_sim T T' -> T = T'.

(** * Deterministic worlds *)

(** One source of possible nondeterminism is that our semantics leave
  unspecified the results of system calls.
  Different results to e.g. a "read" operation can of
  course lead to different behaviors for the program.
  We address this issue by modeling a notion of deterministic
  external world that uniquely determines the results of external calls. *)

(** An external world is a function that, given the name of an
  external call and its arguments, returns either [None], meaning
  that this external call gets stuck, or [Some(r,w)], meaning
  that this external call succeeds, has result [r], and changes
  the world to [w]. *)

Inductive world: Type :=
  World: (ident -> list eventval -> option (eventval * world)) -> world.

Definition nextworld (w: world) (evname: ident) (evargs: list eventval) :
                     option (eventval * world) :=
  match w with World f => f evname evargs end.

(** A trace is possible in a given world if all events correspond
  to non-stuck external calls according to the given world.
  Two predicates are defined, for finite and infinite traces respectively:
- [possible_trace w t w'], where [w] is the initial state of the
  world, [t] the finite trace of interest, and [w'] the state of the
  world after performing trace [t].
- [possible_traceinf w T], where [w] is the initial state of the
  world and [T] the infinite trace of interest.
*)

Inductive possible_event: world -> event -> world -> Prop :=
  | possible_event_syscall: forall w1 evname evargs evres w2,
      nextworld w1 evname evargs = Some (evres, w2) ->
      possible_event w1 (Event_syscall evname evargs evres) w2
  | possible_event_load: forall w label,
      possible_event w (Event_load label) w
  | possible_event_store: forall w label,
      possible_event w (Event_store label) w.

Inductive possible_trace: world -> trace -> world -> Prop :=
  | possible_trace_nil: forall w,
      possible_trace w E0 w
  | possible_trace_cons: forall w1 ev w2 t w3,
      possible_event w1 ev w2 -> possible_trace w2 t w3 ->
      possible_trace w1 (ev :: t) w3.

Lemma possible_trace_app:
  forall t2 w2 w0 t1 w1,
  possible_trace w0 t1 w1 -> possible_trace w1 t2 w2 ->
  possible_trace w0 (t1 ** t2) w2.
Proof.
  induction 1; simpl; intros.
  auto.
  econstructor; eauto.
Qed.

Lemma possible_trace_app_inv:
  forall t2 w2 t1 w0,
  possible_trace w0 (t1 ** t2) w2 ->
  exists w1, possible_trace w0 t1 w1 /\ possible_trace w1 t2 w2.
Proof.
  induction t1; simpl; intros.
  exists w0; split. constructor. auto.
  inv H. exploit IHt1; eauto. intros [w1 [A B]]. 
  exists w1; split. econstructor; eauto. auto.
Qed.

Lemma possible_event_final_world:
  forall w ev w1 w2,
  possible_event w ev w1 -> possible_event w ev w2 -> w1 = w2.
Proof.
  intros. inv H; inv H0; congruence.
Qed.

Lemma possible_trace_final_world:
  forall w0 t w1, possible_trace w0 t w1 ->
  forall w2, possible_trace w0 t w2 -> w1 = w2.
Proof.
  induction 1; intros.
  inv H. auto.
  inv H1. assert (w2 = w5) by (eapply possible_event_final_world; eauto). 
  subst; eauto.
Qed.

CoInductive possible_traceinf: world -> traceinf -> Prop :=
  | possible_traceinf_cons: forall w1 ev w2 T,
      possible_event w1 ev w2 ->
      possible_traceinf w2 T ->
      possible_traceinf w1 (Econsinf ev T).

Lemma possible_traceinf_app:
  forall t2 w0 t1 w1,
  possible_trace w0 t1 w1 -> possible_traceinf w1 t2 ->
  possible_traceinf w0 (t1 *** t2).
Proof.
  induction 1; simpl; intros.
  auto.
  econstructor; eauto.
Qed.

Lemma possible_traceinf_app_inv:
  forall t2 t1 w0,
  possible_traceinf w0 (t1 *** t2) ->
  exists w1, possible_trace w0 t1 w1 /\ possible_traceinf w1 t2.
Proof.
  induction t1; simpl; intros.
  exists w0; split. constructor. auto.
  inv H. exploit IHt1; eauto. intros [w1 [A B]]. 
  exists w1; split. econstructor; eauto. auto.
Qed.

Ltac possibleTraceInv :=
  match goal with
  | [H: possible_trace _ E0 _ |- _] =>
      inversion H; clear H; subst; possibleTraceInv
  | [H: possible_trace _ (_ ** _) _ |- _] =>
      let P1 := fresh "P" in
      let w := fresh "w" in
      let P2 := fresh "P" in
      elim (possible_trace_app_inv _ _ _ _ H); clear H;
      intros w [P1 P2];
      possibleTraceInv
  | [H: possible_traceinf _ (_ *** _) |- _] =>
      let P1 := fresh "P" in
      let w := fresh "w" in
      let P2 := fresh "P" in
      elim (possible_traceinf_app_inv _ _ _ H); clear H;
      intros w [P1 P2];
      possibleTraceInv
  | [H: exists w, possible_trace _ _ w |- _] =>
      let P := fresh "P" in let w := fresh "w" in 
      destruct H as [w P]; possibleTraceInv
  | _ => idtac
  end.

Definition possible_behavior (w: world) (b: program_behavior) : Prop :=
  match b with
  | Terminates t r => exists w', possible_trace w t w'
  | Diverges t => exists w', possible_trace w t w'
  | Reacts T => possible_traceinf w T
  | Goes_wrong t => exists w', possible_trace w t w'
  end.

(** * Deterministic semantics *)

Section DETERM_SEM.

(** We assume given a transition semantics that is internally
  deterministic: the only source of non-determinism is the return
  value of system calls. *)

Variable genv: Type.
Variable state: Type.
Variable step: genv -> state -> trace -> state -> Prop.
Variable initial_state: state -> Prop.
Variable final_state: state -> int -> Prop.

Hypothesis step_internal_deterministic:
  forall ge s t1 s1 t2 s2,
  step ge s t1 s1 -> step ge s t2 s2 -> matching_traces t1 t2 -> s1 = s2 /\ t1 = t2.

Hypothesis initial_state_determ:
  forall s1 s2, initial_state s1 -> initial_state s2 -> s1 = s2.

Hypothesis final_state_determ:
  forall st r1 r2, final_state st r1 -> final_state st r2 -> r1 = r2.

Hypothesis final_state_nostep:
  forall ge st r, final_state st r -> nostep step ge st.

(** Consequently, the [step] relation is deterministic if restricted
    to traces that are possible in a deterministic world. *)

Remark matching_possible_traces:
  forall w0 t1 w1, possible_trace w0 t1 w1 ->
  forall t2 w2, possible_trace w0 t2 w2 ->
  matching_traces t1 t2.
Proof.
  induction 1; intros.
  destruct t2; simpl; auto.
  destruct t2; simpl. destruct ev; auto. inv H1.
  inv H; inv H5; auto; intros.
  subst. rewrite H in H1; inv H1. split; eauto.
  eauto.
  eauto.
Qed.

Lemma step_deterministic:
  forall ge s0 t1 s1 t2 s2 w0 w1 w2,
  step ge s0 t1 s1 -> step ge s0 t2 s2 ->
  possible_trace w0 t1 w1 -> possible_trace w0 t2 w2 ->
  s1 = s2 /\ t1 = t2 /\ w1 = w2.
Proof.
  intros. exploit step_internal_deterministic. eexact H. eexact H0.
  eapply matching_possible_traces; eauto. intuition.
  subst. eapply possible_trace_final_world; eauto. 
Qed.

Ltac use_step_deterministic :=
  match goal with
  | [ S1: step _ _ ?t1 _, P1: possible_trace _ ?t1 _,
      S2: step _ _ ?t2 _, P2: possible_trace _ ?t2 _ |- _ ] =>
    destruct (step_deterministic _ _ _ _ _ _ _ _ _ S1 S2 P1 P2)
    as [EQ1 [EQ2 EQ3]]; subst
  end.

(** Determinism for finite transition sequences. *)

Lemma star_step_diamond:
  forall ge s0 t1 s1, star step ge s0 t1 s1 -> 
  forall t2 s2 w0 w1 w2, star step ge s0 t2 s2 -> 
  possible_trace w0 t1 w1 -> possible_trace w0 t2 w2 ->
  exists t,
     (star step ge s1 t s2 /\ possible_trace w1 t w2 /\ t2 = t1 ** t)
  \/ (star step ge s2 t s1 /\ possible_trace w2 t w1 /\ t1 = t2 ** t).
Proof.
  induction 1; intros. 
  inv H0. exists t2; auto. 
  inv H2. inv H4. exists (t1 ** t2); right. 
    split. econstructor; eauto. auto.
  possibleTraceInv. use_step_deterministic.  
  exploit IHstar. eexact H6. eauto. eauto. 
  intros [t A]. exists t.
  destruct A. left; intuition. traceEq. right; intuition. traceEq. 
Qed.

Ltac use_star_step_diamond :=
  match goal with
  | [ S1: star step _ _ ?t1 _, P1: possible_trace _ ?t1 _,
      S2: star step _ _ ?t2 _, P2: possible_trace _ ?t2 _ |- _ ] =>
    let t := fresh "t" in let P := fresh "P" in let Q := fresh "Q" in let EQ := fresh "EQ" in
    destruct (star_step_diamond _ _ _ _ S1 _ _ _ _ _ S2 P1 P2)
    as [t [ [P [Q EQ]] | [P [Q EQ]] ]]; subst
  end.

Ltac use_nostep :=
  match goal with
  | [ S: step _ ?s _ _, NO: nostep step _ ?s |- _ ] => elim (NO _ _ S)
  end.

Lemma star_step_triangle:
  forall ge s0 t1 s1 t2 s2 w0 w1 w2,
  star step ge s0 t1 s1 -> 
  star step ge s0 t2 s2 -> 
  possible_trace w0 t1 w1 -> possible_trace w0 t2 w2 ->
  nostep step ge s2 ->
  exists t,
  star step ge s1 t s2 /\ possible_trace w1 t w2 /\ t2 = t1 ** t.
Proof.
  intros. use_star_step_diamond; possibleTraceInv. 
  exists t; auto.
  inv P. inv Q. exists E0. split. constructor. split. constructor. traceEq.
  use_nostep.
Qed.

Ltac use_star_step_triangle :=
  match goal with
  | [ S1: star step _ _ ?t1 _, P1: possible_trace _ ?t1 _,
      S2: star step _ _ ?t2 ?s2, P2: possible_trace _ ?t2 _,
      NO: nostep step _ ?s2 |- _ ] =>
    let t := fresh "t" in let P := fresh "P" in let Q := fresh "Q" in let EQ := fresh "EQ" in
    destruct (star_step_triangle _ _ _ _ _ _ _ _ _ S1 S2 P1 P2 NO)
    as [t [P [Q EQ]]]; subst
  end.

Lemma steps_deterministic:
  forall ge s0 t1 s1 t2 s2 w0 w1 w2,
  star step ge s0 t1 s1 -> star step ge s0 t2 s2 -> 
  nostep step ge s1 -> nostep step ge s2 ->
  possible_trace w0 t1 w1 -> possible_trace w0 t2 w2 ->
  t1 = t2 /\ s1 = s2.
Proof.
  intros. use_star_step_triangle. inv P.
  inv Q. split; auto; traceEq. use_nostep.
Qed.

Lemma terminates_not_goes_wrong:
  forall ge s t1 s1 r w w1 t2 s2 w2,
  star step ge s t1 s1 -> final_state s1 r -> possible_trace w t1 w1 ->
  star step ge s t2 s2 -> nostep step ge s2 -> possible_trace w t2 w2 ->
  (forall r, ~final_state s2 r) -> False.
Proof.
  intros.
  assert (t1 = t2 /\ s1 = s2). 
    eapply steps_deterministic; eauto. 
  destruct H6; subst. elim (H5 _ H0).
Qed.

(** Determinism for infinite transition sequences. *)

Lemma star_final_not_forever_silent:
  forall ge s t s', star step ge s t s' ->
  forall w w', possible_trace w t w' -> nostep step ge s' ->
  forever_silent step ge s -> False.
Proof.
  induction 1; intros. 
  inv H1. use_nostep. 
  inv H4. possibleTraceInv. assert (possible_trace w E0 w) by constructor. 
  use_step_deterministic. eauto.
Qed.

Lemma star2_final_not_forever_silent:
  forall ge s t1 s1 w w1 t2 s2 w2,
  star step ge s t1 s1 -> possible_trace w t1 w1 -> nostep step ge s1 ->
  star step ge s t2 s2 -> possible_trace w t2 w2 -> forever_silent step ge s2 ->
  False.
Proof.
  intros. use_star_step_triangle. possibleTraceInv. 
  eapply star_final_not_forever_silent. eexact P. eauto. auto. auto.
Qed.

Lemma star_final_not_forever_reactive:
  forall ge s t s', star step ge s t s' -> 
  forall w w' T, possible_trace w t w' -> possible_traceinf w T -> nostep step ge s' ->
  forever_reactive step ge s T -> False.
Proof.
  induction 1; intros.
  inv H2. inv H3. congruence. use_nostep. 
  inv H5. possibleTraceInv. inv H6. congruence. possibleTraceInv.
  use_step_deterministic.
  eapply IHstar with (T := t4 *** T0). eauto. 
  eapply possible_traceinf_app; eauto. auto. 
  eapply star_forever_reactive; eauto.  
Qed.

Lemma star_forever_silent_inv:
  forall ge s t s', star step ge s t s' ->
  forall w w', possible_trace w t w' ->
  forever_silent step ge s -> 
  t = E0 /\ forever_silent step ge s'.
Proof.
  induction 1; intros.
  auto.
  subst. possibleTraceInv. inv H3. assert (possible_trace w E0 w) by constructor.
  use_step_deterministic. eauto. 
Qed.

Lemma forever_silent_reactive_exclusive:
  forall ge s w T,
  forever_silent step ge s -> forever_reactive step ge s T -> 
  possible_traceinf w T -> False.
Proof.
  intros. inv H0. possibleTraceInv. exploit star_forever_silent_inv; eauto. 
  intros [A B]. contradiction.
Qed.

Lemma forever_reactive_inv2:
  forall ge s t1 s1, star step ge s t1 s1 ->
  forall t2 s2 T1 T2 w w1 w2,
  possible_trace w t1 w1 ->
  star step ge s t2 s2 -> possible_trace w t2 w2 ->
  t1 <> E0 -> t2 <> E0 ->
  forever_reactive step ge s1 T1 -> possible_traceinf w1 T1 ->
  forever_reactive step ge s2 T2 -> possible_traceinf w2 T2 ->
  exists s', exists t, exists T1', exists T2', exists w',
  t <> E0 /\
  forever_reactive step ge s' T1' /\ possible_traceinf w' T1' /\
  forever_reactive step ge s' T2' /\ possible_traceinf w' T2' /\
  t1 *** T1 = t *** T1' /\
  t2 *** T2 = t *** T2'.
Proof.
  induction 1; intros.
  congruence.
  inv H3. congruence. possibleTraceInv.
  use_step_deterministic. 
  destruct t3.
  (* inductive case *)
  simpl in *. inv P1; inv P. eapply IHstar; eauto. 
  (* base case *)
  exists s5; exists (e :: t3);
  exists (t2 *** T1); exists (t4 *** T2); exists w3.
  split. unfold E0; congruence.
  split. eapply star_forever_reactive; eauto. 
  split. eapply possible_traceinf_app; eauto. 
  split. eapply star_forever_reactive; eauto. 
  split. eapply possible_traceinf_app; eauto.
  split; traceEq. 
Qed.

Lemma forever_reactive_determ':
  forall ge s T1 T2 w,
  forever_reactive step ge s T1 -> possible_traceinf w T1 ->
  forever_reactive step ge s T2 -> possible_traceinf w T2 ->
  traceinf_sim' T1 T2.
Proof.
  cofix COINDHYP; intros.
  inv H. inv H1. possibleTraceInv.
  destruct (forever_reactive_inv2 _ _ _ _ H _ _ _ _ _ _ _ P H3 P1 H6 H4
                                  H7 P0 H5 P2)
  as [s' [t' [T1' [T2' [w' [A [B [C [D [E [G K]]]]]]]]]]].
  rewrite G; rewrite K. constructor. auto. 
  eapply COINDHYP; eauto. 
Qed.

Lemma forever_reactive_determ:
  forall ge s T1 T2 w,
  forever_reactive step ge s T1 -> possible_traceinf w T1 ->
  forever_reactive step ge s T2 -> possible_traceinf w T2 ->
  traceinf_sim T1 T2.
Proof.
  intros. apply traceinf_sim'_sim. eapply forever_reactive_determ'; eauto.
Qed.

Lemma star_forever_reactive_inv:
  forall ge s t s', star step ge s t s' ->
  forall w w' T, possible_trace w t w' -> forever_reactive step ge s T ->
  possible_traceinf w T ->
  exists T', forever_reactive step ge s' T' /\ possible_traceinf w' T' /\ T = t *** T'.
Proof.
  induction 1; intros. 
  possibleTraceInv. exists T; auto.
  inv H3. possibleTraceInv. inv H5. congruence. possibleTraceInv.
  use_step_deterministic. 
  exploit IHstar. eauto. eapply star_forever_reactive. 2: eauto. eauto.
  eapply possible_traceinf_app; eauto. 
  intros [T' [A [B C]]]. exists T'; intuition. traceEq. congruence. 
Qed.

Lemma forever_silent_reactive_exclusive2:
  forall ge s t s' w w' T,
  star step ge s t s' -> possible_trace w t w' -> forever_silent step ge s' ->
  forever_reactive step ge s T -> possible_traceinf w T ->
  False.
Proof.
  intros. exploit star_forever_reactive_inv; eauto. 
  intros [T' [A [B C]]]. subst T.
  eapply forever_silent_reactive_exclusive; eauto.
Qed.

(** Determinism for program executions *)

Ltac use_init_state :=
  match goal with
  | [ H1: (initial_state _), H2: (initial_state _) |- _ ] =>
        generalize (initial_state_determ _ _ H1 H2); intro; subst; clear H2
  | [ H1: (initial_state _), H2: (forall s, ~initial_state s) |- _ ] =>
        elim (H2 _ H1)
  | _ => idtac
  end.

Theorem program_behaves_deterministic:
  forall ge w beh1 beh2,
  program_behaves step initial_state final_state ge beh1 -> possible_behavior w beh1 ->
  program_behaves step initial_state final_state ge beh2 -> possible_behavior w beh2 ->
  beh1 = beh2.
Proof.
  intros until beh2; intros BEH1 POS1 BEH2 POS2.
  inv BEH1; inv BEH2; simpl in POS1; simpl in POS2;
  possibleTraceInv; use_init_state.
(* terminates, terminates *)
  assert (t = t0 /\ s' = s'0). eapply steps_deterministic; eauto.
  destruct H2. f_equal; auto. subst. eauto. 
(* terminates, diverges *)
  byContradiction. eapply star2_final_not_forever_silent with (s1 := s') (s2 := s'0); eauto.
(* terminates, reacts *)
  byContradiction. eapply star_final_not_forever_reactive; eauto.
(* terminates, goes_wrong *)
  byContradiction. eapply terminates_not_goes_wrong with (s1 := s') (s2 := s'0); eauto.
(* diverges, terminates *)
  byContradiction. eapply star2_final_not_forever_silent with (s2 := s') (s1 := s'0); eauto.
(* diverges, diverges *)
  f_equal. use_star_step_diamond.
  exploit star_forever_silent_inv. eexact P1. eauto. eauto.
  intros [A B]. subst; traceEq.
  exploit star_forever_silent_inv. eexact P1. eauto. eauto.
  intros [A B]. subst; traceEq.
(* diverges, reacts *)
  byContradiction. eapply forever_silent_reactive_exclusive2; eauto.
(* diverges, goes wrong *)
  byContradiction. eapply star2_final_not_forever_silent with (s1 := s'0) (s2 := s'); eauto.
(* reacts, terminates *)
  byContradiction. eapply star_final_not_forever_reactive; eauto.
(* reacts, diverges *) 
  byContradiction. eapply forever_silent_reactive_exclusive2; eauto.
(* reacts, reacts *)
  f_equal. apply traceinf_extensionality. 
  eapply forever_reactive_determ; eauto. 
(* reacts, goes wrong *)
  byContradiction. eapply star_final_not_forever_reactive; eauto.
(* goes wrong, terminate *)
  byContradiction. eapply terminates_not_goes_wrong with (s1 := s'0) (s2 := s'); eauto.
(* goes wrong, diverges *)
  byContradiction. eapply star2_final_not_forever_silent with (s1 := s') (s2 := s'0); eauto.
(* goes wrong, reacts *)
  byContradiction. eapply star_final_not_forever_reactive; eauto.
(* goes wrong, goes wrong *)
  assert (t = t0 /\ s' = s'0). eapply steps_deterministic; eauto.
  destruct H3. congruence.
(* goes initially wrong, goes initially wrong *)
  reflexivity.
Qed.

End DETERM_SEM.

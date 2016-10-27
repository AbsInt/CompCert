(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Characterization and properties of deterministic external worlds
  and deterministic semantics *)

Require Import String.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Behaviors.

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

CoInductive world: Type :=
  World (io: string -> list eventval -> option (eventval * world))
        (vload: memory_chunk -> ident -> ptrofs -> option (eventval * world))
        (vstore: memory_chunk -> ident -> ptrofs -> eventval -> option world).

Definition nextworld_io (w: world) (evname: string) (evargs: list eventval) :
                     option (eventval * world) :=
  match w with World io vl vs => io evname evargs end.

Definition nextworld_vload (w: world) (chunk: memory_chunk) (id: ident) (ofs: ptrofs) :
                     option (eventval * world) :=
  match w with World io vl vs => vl chunk id ofs end.

Definition nextworld_vstore (w: world) (chunk: memory_chunk) (id: ident) (ofs: ptrofs) (v: eventval):
                     option world :=
  match w with World io vl vs => vs chunk id ofs v end.

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
      nextworld_io w1 evname evargs = Some (evres, w2) ->
      possible_event w1 (Event_syscall evname evargs evres) w2
  | possible_event_vload: forall w1 chunk id ofs evres w2,
      nextworld_vload w1 chunk id ofs = Some (evres, w2) ->
      possible_event w1 (Event_vload chunk id ofs evres) w2
  | possible_event_vstore: forall w1 chunk id ofs evarg w2,
      nextworld_vstore w1 chunk id ofs evarg = Some w2 ->
      possible_event w1 (Event_vstore chunk id ofs evarg) w2
  | possible_event_annot: forall w1 id args,
      possible_event w1 (Event_annot id args) w1.

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

Lemma match_possible_traces:
  forall ge t1 t2 w0 w1 w2,
  match_traces ge t1 t2 -> possible_trace w0 t1 w1 -> possible_trace w0 t2 w2 ->
  t1 = t2 /\ w1 = w2.
Proof.
  intros. inv H; inv H1; inv H0.
  auto.
  inv H7; inv H6. inv H9; inv H10. split; congruence.
  inv H7; inv H6. inv H9; inv H10. split; congruence.
  inv H4; inv H3. inv H6; inv H7. split; congruence.
  inv H4; inv H3. inv H7; inv H6. auto.
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

CoInductive possible_traceinf': world -> traceinf -> Prop :=
  | possible_traceinf'_app: forall w1 t w2 T,
      possible_trace w1 t w2 -> t <> E0 ->
      possible_traceinf' w2 T ->
      possible_traceinf' w1 (t *** T).

Lemma possible_traceinf'_traceinf:
  forall w T, possible_traceinf' w T -> possible_traceinf w T.
Proof.
  cofix COINDHYP; intros. inv H. inv H0. congruence.
  simpl. econstructor. eauto. apply COINDHYP.
  inv H3. simpl. auto. econstructor; eauto. econstructor; eauto. unfold E0; congruence.
Qed.

(** * Definition and properties of deterministic semantics *)

Record sem_deterministic (L: semantics) := mk_deterministic {
  det_step: forall s0 t1 s1 t2 s2,
    Step L s0 t1 s1 -> Step L s0 t2 s2 -> s1 = s2 /\ t1 = t2;
  det_initial_state: forall s1 s2,
    initial_state L s1 -> initial_state L s2 -> s1 = s2;
  det_final_state: forall s r1 r2,
    final_state L s r1 -> final_state L s r2 -> r1 = r2;
  det_final_nostep: forall s r,
    final_state L s r -> Nostep L s
}.

Section DETERM_SEM.

Variable L: semantics.
Hypothesis DET: sem_deterministic L.

Ltac use_step_deterministic :=
  match goal with
  | [ S1: Step L _ ?t1 _, S2: Step L _ ?t2 _ |- _ ] =>
    destruct (det_step L DET _ _ _ _ _ S1 S2) as [EQ1 EQ2]; subst
  end.

(** Determinism for finite transition sequences. *)

Lemma star_step_diamond:
  forall s0 t1 s1, Star L s0 t1 s1 ->
  forall t2 s2, Star L s0 t2 s2 ->
  exists t,
     (Star L s1 t s2 /\ t2 = t1 ** t)
  \/ (Star L s2 t s1 /\ t1 = t2 ** t).
Proof.
  induction 1; intros.
  exists t2; auto.
  inv H2. exists (t1 ** t2); right.
    split. econstructor; eauto. auto.
  use_step_deterministic.
  exploit IHstar. eexact H4. intros [t A]. exists t.
  destruct A. left; intuition. traceEq. right; intuition. traceEq.
Qed.

Ltac use_star_step_diamond :=
  match goal with
  | [ S1: Star L _ ?t1 _, S2: Star L _ ?t2 _ |- _ ] =>
    let t := fresh "t" in let P := fresh "P" in let EQ := fresh "EQ" in
    destruct (star_step_diamond _ _ _ S1 _ _ S2)
    as [t [ [P EQ] | [P EQ] ]]; subst
 end.

Ltac use_nostep :=
  match goal with
  | [ S: Step L ?s _ _, NO: Nostep L ?s |- _ ] => elim (NO _ _ S)
  end.

Lemma star_step_triangle:
  forall s0 t1 s1 t2 s2,
  Star L s0 t1 s1 ->
  Star L s0 t2 s2 ->
  Nostep L s2 ->
  exists t,
  Star L s1 t s2 /\ t2 = t1 ** t.
Proof.
  intros. use_star_step_diamond.
  exists t; auto.
  inv P. exists E0. split. constructor. traceEq.
  use_nostep.
Qed.

Ltac use_star_step_triangle :=
  match goal with
  | [ S1: Star L _ ?t1 _, S2: Star L _ ?t2 ?s2, NO: Nostep L ?s2 |- _ ] =>
    let t := fresh "t" in let P := fresh "P" in let EQ := fresh "EQ" in
    destruct (star_step_triangle _ _ _ _ _ S1 S2 NO)
    as [t [P EQ]]; subst
  end.

Lemma steps_deterministic:
  forall s0 t1 s1 t2 s2,
  Star L s0 t1 s1 -> Star L s0 t2 s2 ->
  Nostep L s1 -> Nostep L s2 ->
  t1 = t2 /\ s1 = s2.
Proof.
  intros. use_star_step_triangle. inv P.
  split; auto; traceEq. use_nostep.
Qed.

Lemma terminates_not_goes_wrong:
  forall s t1 s1 r t2 s2,
  Star L s t1 s1 -> final_state L s1 r ->
  Star L s t2 s2 -> Nostep L s2 ->
  (forall r, ~final_state L s2 r) -> False.
Proof.
  intros.
  assert (t1 = t2 /\ s1 = s2).
    eapply steps_deterministic; eauto. eapply det_final_nostep; eauto.
  destruct H4; subst. elim (H3 _ H0).
Qed.

(** Determinism for infinite transition sequences. *)

Lemma star_final_not_forever_silent:
  forall s t s', Star L s t s' ->
  Nostep L s' ->
  Forever_silent L s -> False.
Proof.
  induction 1; intros.
  inv H0. use_nostep.
  inv H3. use_step_deterministic. eauto.
Qed.

Lemma star2_final_not_forever_silent:
  forall s t1 s1 t2 s2,
  Star L s t1 s1 -> Nostep L s1 ->
  Star L s t2 s2 -> Forever_silent L s2 ->
  False.
Proof.
  intros. use_star_step_triangle.
  eapply star_final_not_forever_silent. eexact P. eauto. auto.
Qed.

Lemma star_final_not_forever_reactive:
  forall s t s', Star L s t s' ->
  forall T, Nostep L s' -> Forever_reactive L s T -> False.
Proof.
  induction 1; intros.
  inv H0. inv H1. congruence. use_nostep.
  inv H3. inv H4. congruence.
  use_step_deterministic.
  eapply IHstar with (T := t4 *** T0). eauto.
  eapply star_forever_reactive; eauto.
Qed.

Lemma star_forever_silent_inv:
  forall s t s', Star L s t s' ->
  Forever_silent L s ->
  t = E0 /\ Forever_silent L s'.
Proof.
  induction 1; intros.
  auto.
  subst. inv H2. use_step_deterministic. eauto.
Qed.

Lemma forever_silent_reactive_exclusive:
  forall s T,
  Forever_silent L s -> Forever_reactive L s T -> False.
Proof.
  intros. inv H0. exploit star_forever_silent_inv; eauto.
  intros [A B]. contradiction.
Qed.

Lemma forever_reactive_inv2:
  forall s t1 s1, Star L s t1 s1 ->
  forall t2 s2 T1 T2,
  Star L s t2 s2 ->
  t1 <> E0 -> t2 <> E0 ->
  Forever_reactive L s1 T1 ->
  Forever_reactive L s2 T2 ->
  exists s', exists t, exists T1', exists T2',
  t <> E0 /\
  Forever_reactive L s' T1' /\
  Forever_reactive L s' T2' /\
  t1 *** T1 = t *** T1' /\
  t2 *** T2 = t *** T2'.
Proof.
  induction 1; intros.
  congruence.
  inv H2. congruence. use_step_deterministic.
  destruct t3.
  (* inductive case *)
  simpl in *. eapply IHstar; eauto.
  (* base case *)
  exists s5; exists (e :: t3);
  exists (t2 *** T1); exists (t4 *** T2).
  split. unfold E0; congruence.
  split. eapply star_forever_reactive; eauto.
  split. eapply star_forever_reactive; eauto.
  split; traceEq.
Qed.

Lemma forever_reactive_determ':
  forall s T1 T2,
  Forever_reactive L s T1 ->
  Forever_reactive L s T2 ->
  traceinf_sim' T1 T2.
Proof.
  cofix COINDHYP; intros.
  inv H. inv H0.
  destruct (forever_reactive_inv2 _ _ _ H t s2 T0 T)
  as [s' [t' [T1' [T2' [A [B [C [D E]]]]]]]]; auto.
  rewrite D; rewrite E. constructor. auto.
  eapply COINDHYP; eauto.
Qed.

Lemma forever_reactive_determ:
  forall s T1 T2,
  Forever_reactive L s T1 ->
  Forever_reactive L s T2 ->
  traceinf_sim T1 T2.
Proof.
  intros. apply traceinf_sim'_sim. eapply forever_reactive_determ'; eauto.
Qed.

Lemma star_forever_reactive_inv:
  forall s t s', Star L s t s' ->
  forall T, Forever_reactive L s T ->
  exists T', Forever_reactive L s' T' /\ T = t *** T'.
Proof.
  induction 1; intros.
  exists T; auto.
  inv H2. inv H3. congruence.
  use_step_deterministic.
  exploit IHstar. eapply star_forever_reactive. 2: eauto. eauto.
  intros [T' [A B]]. exists T'; intuition. traceEq. congruence.
Qed.

Lemma forever_silent_reactive_exclusive2:
  forall s t s' T,
  Star L s t s' -> Forever_silent L s' ->
  Forever_reactive L s T ->
  False.
Proof.
  intros. exploit star_forever_reactive_inv; eauto.
  intros [T' [A B]]. subst T.
  eapply forever_silent_reactive_exclusive; eauto.
Qed.

(** Determinism for program executions *)

Definition same_behaviors (beh1 beh2: program_behavior) : Prop :=
  match beh1, beh2 with
  | Terminates t1 r1, Terminates t2 r2 => t1 = t2 /\ r1 = r2
  | Diverges t1, Diverges t2 => t1 = t2
  | Reacts t1, Reacts t2 => traceinf_sim t1 t2
  | Goes_wrong t1, Goes_wrong t2 => t1 = t2
  | _, _ => False
  end.

Lemma state_behaves_deterministic:
  forall s beh1 beh2,
  state_behaves L s beh1 -> state_behaves L s beh2 -> same_behaviors beh1 beh2.
Proof.
  generalize (det_final_nostep L DET); intro dfns.
  intros until beh2; intros BEH1 BEH2.
  inv BEH1; inv BEH2; red.
(* terminates, terminates *)
  assert (t = t0 /\ s' = s'0). eapply steps_deterministic; eauto.
  destruct H3. split; auto. subst. eapply det_final_state; eauto.
(* terminates, diverges *)
  eapply star2_final_not_forever_silent with (s1 := s') (s2 := s'0); eauto.
(* terminates, reacts *)
  eapply star_final_not_forever_reactive; eauto.
(* terminates, goes_wrong *)
  eapply terminates_not_goes_wrong with (s1 := s') (s2 := s'0); eauto.
(* diverges, terminates *)
  eapply star2_final_not_forever_silent with (s2 := s') (s1 := s'0); eauto.
(* diverges, diverges *)
  use_star_step_diamond.
  exploit star_forever_silent_inv. eexact P. eauto.
  intros [A B]. subst; traceEq.
  exploit star_forever_silent_inv. eexact P. eauto.
  intros [A B]. subst; traceEq.
(* diverges, reacts *)
  eapply forever_silent_reactive_exclusive2; eauto.
(* diverges, goes wrong *)
  eapply star2_final_not_forever_silent with (s1 := s'0) (s2 := s'); eauto.
(* reacts, terminates *)
  eapply star_final_not_forever_reactive; eauto.
(* reacts, diverges *)
  eapply forever_silent_reactive_exclusive2; eauto.
(* reacts, reacts *)
  eapply forever_reactive_determ; eauto.
(* reacts, goes wrong *)
  eapply star_final_not_forever_reactive; eauto.
(* goes wrong, terminate *)
  eapply terminates_not_goes_wrong with (s1 := s'0) (s2 := s'); eauto.
(* goes wrong, diverges *)
  eapply star2_final_not_forever_silent with (s1 := s') (s2 := s'0); eauto.
(* goes wrong, reacts *)
  eapply star_final_not_forever_reactive; eauto.
(* goes wrong, goes wrong *)
  assert (t = t0 /\ s' = s'0). eapply steps_deterministic; eauto.
  tauto.
Qed.

Theorem program_behaves_deterministic:
  forall beh1 beh2,
  program_behaves L beh1 -> program_behaves L beh2 ->
  same_behaviors beh1 beh2.
Proof.
  intros until beh2; intros BEH1 BEH2. inv BEH1; inv BEH2.
(* both initial states defined *)
  assert (s = s0) by (eapply det_initial_state; eauto). subst s0.
  eapply state_behaves_deterministic; eauto.
(* one initial state defined, the other undefined *)
  elim (H1 _ H).
  elim (H _ H0).
(* both initial states undefined *)
  red; auto.
Qed.

End DETERM_SEM.

(** * Integrating an external world in a semantics. *)

(** Given a transition semantics, we can build another semantics that
  integrates an external world in its state and allows only world-possible
  transitions. *)

Section WORLD_SEM.

Variable L: semantics.
Variable initial_world: world.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.
Local Open Scope pair_scope.

Definition world_sem : semantics := @Semantics_gen
  (state L * world)%type
  (genvtype L)
  (fun ge s t s' => step L ge s#1 t s'#1 /\ possible_trace s#2 t s'#2)
  (fun s => initial_state L s#1 /\ s#2 = initial_world)
  (fun s r => final_state L s#1 r)
  (globalenv L)
  (symbolenv L).

(** If the original semantics is determinate, the world-aware semantics is deterministic. *)

Hypothesis D: determinate L.

Theorem world_sem_deterministic: sem_deterministic world_sem.
Proof.
  constructor; simpl; intros.
(* steps *)
  destruct H; destruct H0.
  exploit (sd_determ D). eexact H. eexact H0. intros [A B].
  exploit match_possible_traces; eauto. intros [EQ1 EQ2]. subst t2.
  split; auto.
  rewrite (surjective_pairing s1). rewrite (surjective_pairing s2). intuition congruence.
(* initial states *)
  destruct H; destruct H0.
  rewrite (surjective_pairing s1). rewrite (surjective_pairing s2). decEq.
  eapply (sd_initial_determ D); eauto.
  congruence.
(* final states *)
  eapply (sd_final_determ D); eauto.
(* final no step *)
  red; simpl; intros. red; intros [A B]. exploit (sd_final_nostep D); eauto.
Qed.

End WORLD_SEM.



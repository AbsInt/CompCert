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
Require Import Behaviors.

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
  World (io: ident -> list eventval -> option (eventval * world))
        (vload: memory_chunk -> ident -> int -> option (eventval * world))
        (vstore: memory_chunk -> ident -> int -> eventval -> option world).

Definition nextworld_io (w: world) (evname: ident) (evargs: list eventval) :
                     option (eventval * world) :=
  match w with World io vl vs => io evname evargs end.

Definition nextworld_vload (w: world) (chunk: memory_chunk) (id: ident) (ofs: int) :
                     option (eventval * world) :=
  match w with World io vl vs => vl chunk id ofs end.

Definition nextworld_vstore (w: world) (chunk: memory_chunk) (id: ident) (ofs: int) (v: eventval):
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
  forall (F V: Type) (ge: Genv.t F V) t1 t2 w0 w1 w2,
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

(*
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
*)

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
    L (genv L) s0 t1 s1 -> L (genv L) s0 t2 s2 -> s1 = s2 /\ t1 = t2;
  det_initial_state: forall s1 s2,
    initial_state L s1 -> initial_state L s2 -> s1 = s2;
  det_final_state: forall s r1 r2,
    final_state L s r1 -> final_state L s r2 -> r1 = r2;
  det_final_nostep: forall s r,
    final_state L s r -> nostep L (genv L) s
}.

Section DETERM_SEM.

Variable L: semantics.
Hypothesis DET: sem_deterministic L.

Ltac use_step_deterministic :=
  match goal with
  | [ S1: step L (genv L) _ ?t1 _, S2: step L (genv L) _ ?t2 _ |- _ ] =>
    destruct (det_step L DET _ _ _ _ _ S1 S2) as [EQ1 EQ2]; subst
  end.

(** Determinism for finite transition sequences. *)

Lemma star_step_diamond:
  forall s0 t1 s1, star L (genv L) s0 t1 s1 -> 
  forall t2 s2, star L (genv L) s0 t2 s2 -> 
  exists t,
     (star L (genv L) s1 t s2 /\ t2 = t1 ** t)
  \/ (star L (genv L) s2 t s1 /\ t1 = t2 ** t).
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
  | [ S1: star (step L) (genv L) _ ?t1 _, S2: star (step L) (genv L) _ ?t2 _ |- _ ] =>
    let t := fresh "t" in let P := fresh "P" in let EQ := fresh "EQ" in
    destruct (star_step_diamond _ _ _ S1 _ _ S2)
    as [t [ [P EQ] | [P EQ] ]]; subst
 end.

Ltac use_nostep :=
  match goal with
  | [ S: step L (genv L) ?s _ _, NO: nostep (step L) (genv L) ?s |- _ ] => elim (NO _ _ S)
  end.

Lemma star_step_triangle:
  forall s0 t1 s1 t2 s2,
  star L (genv L) s0 t1 s1 -> 
  star L (genv L) s0 t2 s2 -> 
  nostep L (genv L) s2 ->
  exists t,
  star L (genv L) s1 t s2 /\ t2 = t1 ** t.
Proof.
  intros. use_star_step_diamond.
  exists t; auto.
  inv P. exists E0. split. constructor. traceEq.
  use_nostep.
Qed.

Ltac use_star_step_triangle :=
  match goal with
  | [ S1: star (step L) (genv L) _ ?t1 _, S2: star (step L) (genv L) _ ?t2 ?s2,
      NO: nostep (step L) (genv L) ?s2 |- _ ] =>
    let t := fresh "t" in let P := fresh "P" in let EQ := fresh "EQ" in
    destruct (star_step_triangle _ _ _ _ _ S1 S2 NO)
    as [t [P EQ]]; subst
  end.

Lemma steps_deterministic:
  forall s0 t1 s1 t2 s2,
  star L (genv L) s0 t1 s1 -> star L (genv L) s0 t2 s2 -> 
  nostep L (genv L) s1 -> nostep L (genv L) s2 ->
  t1 = t2 /\ s1 = s2.
Proof.
  intros. use_star_step_triangle. inv P.
  split; auto; traceEq. use_nostep.
Qed.

Lemma terminates_not_goes_wrong:
  forall s t1 s1 r t2 s2,
  star L (genv L) s t1 s1 -> final_state L s1 r ->
  star L (genv L) s t2 s2 -> nostep L (genv L) s2 ->
  (forall r, ~final_state L s2 r) -> False.
Proof.
  intros.
  assert (t1 = t2 /\ s1 = s2). 
    eapply steps_deterministic; eauto. eapply det_final_nostep; eauto. 
  destruct H4; subst. elim (H3 _ H0).
Qed.

(** Determinism for infinite transition sequences. *)

Lemma star_final_not_forever_silent:
  forall s t s', star L (genv L) s t s' ->
  nostep L (genv L) s' ->
  forever_silent L (genv L) s -> False.
Proof.
  induction 1; intros. 
  inv H0. use_nostep. 
  inv H3. use_step_deterministic. eauto.
Qed.

Lemma star2_final_not_forever_silent:
  forall s t1 s1 t2 s2,
  star L (genv L) s t1 s1 -> nostep L (genv L) s1 ->
  star L (genv L) s t2 s2 -> forever_silent L (genv L) s2 ->
  False.
Proof.
  intros. use_star_step_triangle.
  eapply star_final_not_forever_silent. eexact P. eauto. auto.
Qed.

Lemma star_final_not_forever_reactive:
  forall s t s', star L (genv L) s t s' -> 
  forall T, nostep L (genv L) s' -> forever_reactive L (genv L) s T -> False.
Proof.
  induction 1; intros.
  inv H0. inv H1. congruence. use_nostep. 
  inv H3. inv H4. congruence.
  use_step_deterministic.
  eapply IHstar with (T := t4 *** T0). eauto. 
  eapply star_forever_reactive; eauto.  
Qed.

Lemma star_forever_silent_inv:
  forall s t s', star L (genv L) s t s' ->
  forever_silent L (genv L) s -> 
  t = E0 /\ forever_silent L (genv L) s'.
Proof.
  induction 1; intros.
  auto.
  subst. inv H2. use_step_deterministic. eauto. 
Qed.

Lemma forever_silent_reactive_exclusive:
  forall s T,
  forever_silent L (genv L) s -> forever_reactive L (genv L) s T -> False.
Proof.
  intros. inv H0. exploit star_forever_silent_inv; eauto. 
  intros [A B]. contradiction.
Qed.

Lemma forever_reactive_inv2:
  forall s t1 s1, star L (genv L) s t1 s1 ->
  forall t2 s2 T1 T2,
  star L (genv L) s t2 s2 ->
  t1 <> E0 -> t2 <> E0 ->
  forever_reactive L (genv L) s1 T1 ->
  forever_reactive L (genv L) s2 T2 ->
  exists s', exists t, exists T1', exists T2',
  t <> E0 /\
  forever_reactive L (genv L) s' T1' /\
  forever_reactive L (genv L) s' T2' /\
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
  forever_reactive L (genv L) s T1 ->
  forever_reactive L (genv L) s T2 ->
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
  forever_reactive L (genv L) s T1 ->
  forever_reactive L (genv L) s T2 ->
  traceinf_sim T1 T2.
Proof.
  intros. apply traceinf_sim'_sim. eapply forever_reactive_determ'; eauto.
Qed.

Lemma star_forever_reactive_inv:
  forall s t s', star L (genv L) s t s' ->
  forall T, forever_reactive L (genv L) s T ->
  exists T', forever_reactive L (genv L) s' T' /\ T = t *** T'.
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
  star L (genv L) s t s' -> forever_silent L (genv L) s' ->
  forever_reactive L (genv L) s T ->
  False.
Proof.
  intros. exploit star_forever_reactive_inv; eauto. 
  intros [T' [A B]]. subst T.
  eapply forever_silent_reactive_exclusive; eauto.
Qed.

(** Determinism for program executions *)

Lemma state_behaves_deterministic:
  forall s beh1 beh2,
  state_behaves L s beh1 -> state_behaves L s beh2 -> beh1 = beh2.
Proof.
  generalize (det_final_nostep L DET); intro dfns.
  intros until beh2; intros BEH1 BEH2.
  inv BEH1; inv BEH2.
(* terminates, terminates *)
  assert (t = t0 /\ s' = s'0). eapply steps_deterministic; eauto.
  destruct H3. f_equal; auto. subst. eapply det_final_state; eauto. 
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
  exploit star_forever_silent_inv. eexact P. eauto.  
  intros [A B]. subst; traceEq.
  exploit star_forever_silent_inv. eexact P. eauto. 
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
  destruct H5. congruence.
Qed.

Theorem program_behaves_deterministic:
  forall beh1 beh2,
  program_behaves L beh1 -> program_behaves L beh2 ->
  beh1 = beh2.
Proof.
  intros until beh2; intros BEH1 BEH2. inv BEH1; inv BEH2.
(* both initial states defined *)
  assert (s = s0) by (eapply det_initial_state; eauto). subst s0. 
  eapply state_behaves_deterministic; eauto.
(* one initial state defined, the other undefined *)
  elim (H1 _ H).
  elim (H _ H0).
(* both initial states undefined *)
  auto.
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

Definition world_sem : semantics := @mk_semantics
  (state L * world)%type
  (funtype L)
  (vartype L)
  (fun ge s t s' => L ge s#1 t s'#1 /\ possible_trace s#2 t s'#2)
  (fun s => initial_state L s#1 /\ s#2 = initial_world)
  (fun s r => final_state L s#1 r)
  (genv L).

(** If the original semantics is determinate, the world-aware semantics is deterministic. *)

Hypothesis D: sem_determinate L.

Theorem world_sem_deterministic: sem_deterministic world_sem.
Proof.
  constructor; simpl; intros.
(* steps *)
  destruct H; destruct H0.
  exploit (sd_match D). eexact H. eexact H0. intros MT.
  exploit match_possible_traces; eauto. intros [EQ1 EQ2]. subst t2.
  exploit (sd_determ D). eexact H. eexact H0. intros EQ3. 
  split; auto. rewrite (surjective_pairing s1). rewrite (surjective_pairing s2). congruence.
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



Variable genv: Type.
Variable state: Type.
Variable step: genv -> state -> trace -> state -> Prop.
Variable initial_state: state -> Prop.
Variable final_state: state -> int -> Prop.
Variable initial_world: world.

Definition wstate : Type := (state * world)%type.


Definition wstep (ge: genv) (S: wstate) (t: trace) (S': wstate) :=
  step ge S#1 t S'#1 /\ possible_trace S#2 t S'#2.

Definition winitial_state (S: wstate) :=
  initial_state S#1 /\ S#2 = initial_world.

Definition wfinal_state (S: wstate) (r: int) :=
  final_state S#1 r.

Definition wprogram_behaves (ge: genv) (beh: program_behavior) :=
  program_behaves wstep winitial_state wfinal_state ge beh.

(** We now relate sequences of transitions and behaviors between the two semantics. *)

Section TRANSITIONS.

Variable ge: genv.

Lemma inject_star:
  forall S t S', star step ge S t S' ->
  forall w w', possible_trace w t w' ->
  star wstep ge (S, w) t (S', w').
Proof.
  induction 1; intros; subst; possibleTraceInv.
  constructor.
  apply star_step with t1 (s2,w0) t2. split; auto. auto. auto.
Qed.
 
Lemma project_star:
  forall S t S', star wstep ge S t S' -> star step ge S#1 t S'#1.
Proof.
  induction 1. constructor. destruct H. econstructor; eauto.
Qed.

Lemma project_star_trace:
  forall S t S', star wstep ge S t S' -> possible_trace S#2 t S'#2.
Proof.
  induction 1. constructor. subst t. destruct H. eapply possible_trace_app. eauto. eauto.
Qed.

Lemma inject_forever_silent:
  forall S w, forever_silent step ge S -> forever_silent wstep ge (S, w).
Proof.
  cofix COINDHYP; intros. inv H.
  apply forever_silent_intro with (s2,w). 
  split. auto. constructor. apply COINDHYP; auto.
Qed.

Lemma project_forever_silent:
  forall S, forever_silent wstep ge S -> forever_silent step ge S#1.
Proof.
  cofix COINDHYP; intros. inv H. destruct H0. 
  apply forever_silent_intro with (s2#1). auto. apply COINDHYP; auto.
Qed.

Lemma inject_forever_reactive:
  forall S T w, forever_reactive step ge S T -> possible_traceinf w T ->
  forever_reactive wstep ge (S, w) T.
Proof.
  cofix COINDHYP; intros. inv H. possibleTraceInv. 
  apply forever_reactive_intro with (s2,w0).
  apply inject_star; auto. auto. apply COINDHYP; auto.
Qed.

Lemma project_forever_reactive:
  forall S T, forever_reactive wstep ge S T -> forever_reactive step ge S#1 T.
Proof.
  cofix COINDHYP; intros. inv H.
  apply forever_reactive_intro with (s2#1).
  apply project_star; auto. auto. apply COINDHYP; auto.
Qed.

Lemma project_forever_reactive_trace:
  forall S T, forever_reactive wstep ge S T -> possible_traceinf S#2 T.
Proof.
  intros. apply possible_traceinf'_traceinf. revert S T H. 
  cofix COINDHYP; intros. inv H. econstructor.
  apply project_star_trace. eauto. auto. apply COINDHYP; auto. 
Qed.

Lemma inject_behaviors:
  forall beh,
  program_behaves step initial_state final_state ge beh ->
  possible_behavior initial_world beh ->
  wprogram_behaves ge beh.
Proof.
  intros. inv H; simpl in H0.
(* terminates *)
  destruct H0 as [w' A]. econstructor.
    instantiate (1 := (s, initial_world)). red; eauto.
    apply inject_star; eauto. 
    red; auto.
(* diverges silently *)
  destruct H0 as [w' A]. econstructor.
    instantiate (1 := (s, initial_world)). red; eauto.
    apply inject_star; eauto. apply inject_forever_silent; auto. 
(* diverges reactively *)
  econstructor.
    instantiate (1 := (s, initial_world)). red; eauto.
    apply inject_forever_reactive; auto.
(* goes wrong *)
  destruct H0 as [w' A]. red in H3.
  econstructor. 
    instantiate (1 := (s, initial_world)). red; eauto.
    apply inject_star; eauto. 
    red. intros. red; intros [C D]. elim (H3 t0 s'0#1); auto.
    unfold wfinal_state; simpl. auto. 
(* goes initially wrong *)
  apply program_goes_initially_wrong. intros; red; intros. destruct H. 
  elim (H1 s#1); auto.
Qed.

Lemma project_behaviors_trace:
  forall beh,
  wprogram_behaves ge beh ->
  possible_behavior initial_world beh.
Proof.
  intros. inv H; simpl.
  destruct H0. rewrite <- H0. exists (s'#2); apply project_star_trace; auto. 
  destruct H0. rewrite <- H0. exists (s'#2); apply project_star_trace; auto. 
  destruct H0. rewrite <- H0. apply project_forever_reactive_trace; auto.
  destruct H0. rewrite <- H0. exists (s'#2); apply project_star_trace; auto. 
  exists initial_world; constructor.
Qed.

Lemma project_behaviors:
  forall beh,
  wprogram_behaves ge beh ->
  program_behaves step initial_state final_state ge beh
  \/ exists S, exists t, exists S', exists w', exists S'', exists t',
     beh = Goes_wrong t /\     
     initial_state S /\ star step ge S t S' /\ possible_trace initial_world t w' /\
     step ge S' t' S'' /\ forall w'', ~(possible_trace w' t' w'').
Proof.
  intros. inv H.
(* terminates *)
  destruct H0.
  left. econstructor; eauto. apply project_star; auto. 
(* diverges silently *)
  destruct H0.
  left. econstructor; eauto. apply project_star; eauto. apply project_forever_silent; auto.
(* diverges reactively *)
  destruct H0.
  left. econstructor; eauto. apply project_forever_reactive; auto. 
(* goes wrong *)
  destruct H0.
  red in H2. 
  destruct (classic (forall t s'', ~step ge s'#1 t s'')). 
  left. econstructor; eauto. apply project_star; eauto.
  destruct (not_all_ex_not _ _ H4) as [t' A]. clear H4.
  destruct (not_all_ex_not _ _ A) as [s'' B]. clear A.
  assert (C: step ge s'#1 t' s''). apply NNPP; auto. clear B.
  right. do 6 econstructor. split. eauto. split. eauto. 
  split. apply project_star; eauto.
  split. rewrite <- H0. apply project_star_trace; eauto. 
  split. eauto. 
  intros; red; intros. elim (H2 t' (s'',w'')). split; auto.
(* goes initially wrong *)
  left. apply program_goes_initially_wrong. intros; red; intros. 
  elim (H0 (s, initial_world)). split; auto.
Qed.

End TRANSITIONS.

Section INTERNAL_DET_TO_DET.

(** We assume given a transition semantics that is internally
  deterministic: the only source of non-determinism is the return
  value of system calls.   Under this assumption, the world-aware semantics
  is deterministic. *)

Hypothesis step_internal_deterministic:
  forall ge s t1 s1 t2 s2,
  step ge s t1 s1 -> step ge s t2 s2 -> matching_traces t1 t2 -> s1 = s2 /\ t1 = t2.

Hypothesis initial_state_determ:
  forall s1 s2, initial_state s1 -> initial_state s2 -> s1 = s2.

Hypothesis final_state_determ:
  forall st r1 r2, final_state st r1 -> final_state st r2 -> r1 = r2.

Hypothesis final_state_nostep:
  forall ge st r, final_state st r -> nostep step ge st.

Remark matching_possible_traces:
  forall w0 t1 w1, possible_trace w0 t1 w1 ->
  forall t2 w2, possible_trace w0 t2 w2 ->
  matching_traces t1 t2.
Proof.
  induction 1; intros.
  destruct t2; simpl; auto.
  destruct t2; simpl. destruct ev; auto. inv H1.
  inv H; inv H5; auto; intros.
  destruct H2. subst. rewrite H in H1; inv H1. split; eauto.
  destruct H2. destruct H3. subst. rewrite H in H1; inv H1. split; eauto.
  destruct H2. destruct H3. destruct H4. subst. rewrite H in H1; inv H1. eauto.
Qed.

Lemma wstep_deterministic:
  forall ge S0 t1 S1 t2 S2,
  wstep ge S0 t1 S1 -> wstep ge S0 t2 S2 -> S1 = S2 /\ t1 = t2.
Proof.
  intros. destruct H; destruct H0. 
  exploit step_internal_deterministic. eexact H. eexact H0. 
  eapply matching_possible_traces; eauto. 
  intros [A B]. split. apply injective_projections. auto.
  subst t2. eapply possible_trace_final_world; eauto.
  auto.
Qed.

Lemma winitial_state_determ:
  forall s1 s2, winitial_state s1 -> winitial_state s2 -> s1 = s2.
Proof.
  intros. destruct H; destruct H0. apply injective_projections. eauto. congruence.
Qed. 

Lemma wfinal_state_determ:
  forall st r1 r2, wfinal_state st r1 -> wfinal_state st r2 -> r1 = r2.
Proof. 
  unfold wfinal_state. eauto.
Qed. 

Lemma wfinal_state_nostep:
  forall ge st r, wfinal_state st r -> nostep wstep ge st.
Proof.
  unfold wfinal_state. intros; red; intros; red; intros [A B]. 
  eapply final_state_nostep; eauto. 
Qed.

Theorem program_behaves_world_deterministic:
  forall ge beh1 beh2,
  program_behaves step initial_state final_state ge beh1 -> possible_behavior initial_world beh1 ->
  program_behaves step initial_state final_state ge beh2 -> possible_behavior initial_world beh2 ->
  beh1 = beh2.
Proof.
  intros. 
  apply program_behaves_deterministic with
    (step := wstep) (initial_state := winitial_state) (final_state := wfinal_state) (ge := ge).
  exact wstep_deterministic.
  exact winitial_state_determ.
  exact wfinal_state_determ.
  exact wfinal_state_nostep. 
  apply inject_behaviors; auto.
  apply inject_behaviors; auto.
Qed.

End INTERNAL_DET_TO_DET.

End WORLD_SEM.



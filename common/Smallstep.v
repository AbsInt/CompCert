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

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.

Require Import Values. (*for meminj, compose_meminj,...*)

Set Implicit Arguments.

(** * Closures of transitions relations *)

Section CLOSURES.

Variable genv: Type.
Variable state: Type.

(** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

Variable step: genv -> state -> trace -> state -> Prop.

(** No transitions: stuck state *)

Definition nostep (ge: genv) (s: state) : Prop :=
  forall t s', ~(step ge s t s').

(** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)

Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.

Lemma star_one:
  forall ge s1 t s2, step ge s1 t s2 -> star ge s1 t s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl. traceEq.
Qed.

Lemma star_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto.
Qed.

Lemma star_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  star ge s1 t s4.
Proof.
  intros. eapply star_step; eauto. eapply star_two; eauto.
Qed.

Lemma star_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  star ge s1 t s5.
Proof.
  intros. eapply star_step; eauto. eapply star_three; eauto.
Qed.

Lemma star_trans:
  forall ge s1 t1 s2, star ge s1 t1 s2 ->
  forall t2 s3 t, star ge s2 t2 s3 -> t = t1 ** t2 -> star ge s1 t s3.
Proof.
  induction 1; intros.
  rewrite H0. simpl. auto.
  eapply star_step; eauto. traceEq.
Qed.

Lemma star_left:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof star_step.

Lemma star_right:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto. auto.
Qed.

Lemma star_E0_ind:
  forall ge (P: state -> state -> Prop),
  (forall s, P s s) ->
  (forall s1 s2 s3, step ge s1 E0 s2 -> P s2 s3 -> P s1 s3) ->
  forall s1 s2, star ge s1 E0 s2 -> P s1 s2.
Proof.
  intros ge P BASE REC.
  assert (forall s1 t s2, star ge s1 t s2 -> t = E0 -> P s1 s2).
    induction 1; intros; subst.
    auto.
    destruct (Eapp_E0_inv _ _ H2). subst. eauto.
  eauto.
Qed.

(** One or several transitions.  Also known as the transitive closure. *)

Inductive plus (ge: genv): state -> trace -> state -> Prop :=
  | plus_left: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.

Lemma plus_one:
  forall ge s1 t s2,
  step ge s1 t s2 -> plus ge s1 t s2.
Proof.
  intros. econstructor; eauto. apply star_refl. traceEq.
Qed.

Lemma plus_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply star_one; auto.
Qed.

Lemma plus_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  plus ge s1 t s4.
Proof.
  intros. eapply plus_left; eauto. eapply star_two; eauto.
Qed.

Lemma plus_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  plus ge s1 t s5.
Proof.
  intros. eapply plus_left; eauto. eapply star_three; eauto.
Qed.

Lemma plus_star:
  forall ge s1 t s2, plus ge s1 t s2 -> star ge s1 t s2.
Proof.
  intros. inversion H; subst.
  eapply star_step; eauto.
Qed.

Lemma plus_right:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. inversion H; subst. simpl. apply plus_one. auto.
  rewrite Eapp_assoc. eapply plus_left; eauto.
  eapply star_right; eauto.
Qed.

Lemma plus_left':
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply plus_star; auto.
Qed.

Lemma plus_right':
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_right; eauto. apply plus_star; auto.
Qed.

Lemma plus_star_trans:
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. inversion H; subst.
  econstructor; eauto. eapply star_trans; eauto.
  traceEq.
Qed.

Lemma star_plus_trans:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. inversion H; subst.
  simpl; auto.
  rewrite Eapp_assoc.
  econstructor. eauto. eapply star_trans. eauto.
  apply plus_star. eauto. eauto. auto.
Qed.

Lemma plus_trans:
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. eapply plus_star_trans. eauto. apply plus_star. eauto. auto.
Qed.

Lemma plus_inv:
  forall ge s1 t s2,
  plus ge s1 t s2 ->
  step ge s1 t s2 \/ exists s', exists t1, exists t2, step ge s1 t1 s' /\ plus ge s' t2 s2 /\ t = t1 ** t2.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  left. rewrite E0_right. auto.
  right. exists s3; exists t1; exists (t0 ** t3); split. auto.
  split. econstructor; eauto. auto.
Qed.

Lemma star_inv:
  forall ge s1 t s2,
  star ge s1 t s2 ->
  (s2 = s1 /\ t = E0) \/ plus ge s1 t s2.
Proof.
  intros. inv H. left; auto. right; econstructor; eauto.
Qed.

Lemma plus_ind2:
  forall ge (P: state -> trace -> state -> Prop),
  (forall s1 t s2, step ge s1 t s2 -> P s1 t s2) ->
  (forall s1 t1 s2 t2 s3 t,
   step ge s1 t1 s2 -> plus ge s2 t2 s3 -> P s2 t2 s3 -> t = t1 ** t2 ->
   P s1 t s3) ->
  forall s1 t s2, plus ge s1 t s2 -> P s1 t s2.
Proof.
  intros ge P BASE IND.
  assert (forall s1 t s2, star ge s1 t s2 ->
         forall s0 t0, step ge s0 t0 s1 ->
         P s0 (t0 ** t) s2).
  induction 1; intros.
  rewrite E0_right. apply BASE; auto.
  eapply IND. eauto. econstructor; eauto. subst t. eapply IHstar; eauto. auto.

  intros. inv H0. eauto.
Qed.

Lemma plus_E0_ind:
  forall ge (P: state -> state -> Prop),
  (forall s1 s2 s3, step ge s1 E0 s2 -> star ge s2 E0 s3 -> P s1 s3) ->
  forall s1 s2, plus ge s1 E0 s2 -> P s1 s2.
Proof.
  intros. inv H0. exploit Eapp_E0_inv; eauto. intros [A B]; subst. eauto.
Qed.

(** Counted sequences of transitions *)

Inductive starN (ge: genv): nat -> state -> trace -> state -> Prop :=
  | starN_refl: forall s,
      starN ge O s E0 s
  | starN_step: forall n s t t1 s' t2 s'',
      step ge s t1 s' -> starN ge n s' t2 s'' -> t = t1 ** t2 ->
      starN ge (S n) s t s''.

Remark starN_star:
  forall ge n s t s', starN ge n s t s' -> star ge s t s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark star_starN:
  forall ge s t s', star ge s t s' -> exists n, starN ge n s t s'.
Proof.
  induction 1.
  exists O; constructor.
  destruct IHstar as [n P]. exists (S n); econstructor; eauto.
Qed.

(** Infinitely many transitions *)

CoInductive forever (ge: genv): state -> traceinf -> Prop :=
  | forever_intro: forall s1 t s2 T,
      step ge s1 t s2 -> forever ge s2 T ->
      forever ge s1 (t *** T).

Lemma star_forever:
  forall ge s1 t s2, star ge s1 t s2 ->
  forall T, forever ge s2 T ->
  forever ge s1 (t *** T).
Proof.
  induction 1; intros. simpl. auto.
  subst t. rewrite Eappinf_assoc.
  econstructor; eauto.
Qed.

(** An alternate, equivalent definition of [forever] that is useful
    for coinductive reasoning. *)

Variable A: Type.
Variable order: A -> A -> Prop.

CoInductive forever_N (ge: genv) : A -> state -> traceinf -> Prop :=
  | forever_N_star: forall s1 t s2 a1 a2 T1 T2,
      star ge s1 t s2 ->
      order a2 a1 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1
  | forever_N_plus: forall s1 t s2 a1 a2 T1 T2,
      plus ge s1 t s2 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1.

Hypothesis order_wf: well_founded order.

Lemma forever_N_inv:
  forall ge a s T,
  forever_N ge a s T ->
  exists t, exists s', exists a', exists T',
  step ge s t s' /\ forever_N ge a' s' T' /\ T = t *** T'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  change (E0 *** T2) with T2. apply H with a2. auto. auto.
  (* at least one transition *)
  exists t1; exists s0; exists x; exists (t2 *** T2).
  split. auto. split. eapply forever_N_star; eauto.
  apply Eappinf_assoc.
  (* plus case *)
  inv H1.
  exists t1; exists s0; exists a2; exists (t2 *** T2).
  split. auto.
  split. inv H3. auto.
  eapply forever_N_plus. econstructor; eauto. eauto. auto.
  apply Eappinf_assoc.
Qed.

Lemma forever_N_forever:
  forall ge a s T, forever_N ge a s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_N_inv H) as [t [s' [a' [T' [P [Q R]]]]]].
  rewrite R. apply forever_intro with s'. auto.
  apply COINDHYP with a'; auto.
Qed.

(** Yet another alternative definition of [forever]. *)

CoInductive forever_plus (ge: genv) : state -> traceinf -> Prop :=
  | forever_plus_intro: forall s1 t s2 T1 T2,
      plus ge s1 t s2 ->
      forever_plus ge s2 T2 ->
      T1 = t *** T2 ->
      forever_plus ge s1 T1.

Lemma forever_plus_inv:
  forall ge s T,
  forever_plus ge s T ->
  exists s', exists t, exists T',
  step ge s t s' /\ forever_plus ge s' T' /\ T = t *** T'.
Proof.
  intros. inv H. inv H0. exists s0; exists t1; exists (t2 *** T2).
  split. auto.
  split. exploit star_inv; eauto. intros [[P Q] | R].
    subst. simpl. auto. econstructor; eauto.
  traceEq.
Qed.

Lemma forever_plus_forever:
  forall ge s T, forever_plus ge s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_plus_inv H) as [s' [t [T' [P [Q R]]]]].
  subst. econstructor; eauto.
Qed.

(** Infinitely many silent transitions *)

CoInductive forever_silent (ge: genv): state -> Prop :=
  | forever_silent_intro: forall s1 s2,
      step ge s1 E0 s2 -> forever_silent ge s2 ->
      forever_silent ge s1.

(** An alternate definition. *)

CoInductive forever_silent_N (ge: genv) : A -> state -> Prop :=
  | forever_silent_N_star: forall s1 s2 a1 a2,
      star ge s1 E0 s2 ->
      order a2 a1 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1
  | forever_silent_N_plus: forall s1 s2 a1 a2,
      plus ge s1 E0 s2 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1.

Lemma forever_silent_N_inv:
  forall ge a s,
  forever_silent_N ge a s ->
  exists s', exists a',
  step ge s E0 s' /\ forever_silent_N ge a' s'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  apply H with a2. auto. auto.
  (* at least one transition *)
  exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
  exists s0; exists x.
  split. auto. eapply forever_silent_N_star; eauto.
  (* plus case *)
  inv H1. exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
  exists s0; exists a2.
  split. auto. inv H3. auto.
  eapply forever_silent_N_plus. econstructor; eauto. eauto.
Qed.

Lemma forever_silent_N_forever:
  forall ge a s, forever_silent_N ge a s -> forever_silent ge s.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_silent_N_inv H) as [s' [a' [P Q]]].
  apply forever_silent_intro with s'. auto.
  apply COINDHYP with a'; auto.
Qed.

(** Infinitely many non-silent transitions *)

CoInductive forever_reactive (ge: genv): state -> traceinf -> Prop :=
  | forever_reactive_intro: forall s1 s2 t T,
      star ge s1 t s2 -> t <> E0 -> forever_reactive ge s2 T ->
      forever_reactive ge s1 (t *** T).

Lemma star_forever_reactive:
  forall ge s1 t s2 T,
  star ge s1 t s2 -> forever_reactive ge s2 T ->
  forever_reactive ge s1 (t *** T).
Proof.
  intros. inv H0. rewrite <- Eappinf_assoc. econstructor.
  eapply star_trans; eauto.
  red; intro. exploit Eapp_E0_inv; eauto. intros [P Q]. contradiction.
  auto.
Qed.

End CLOSURES.

(** * Transition semantics *)

(** The general form of a transition semantics. *)
Require Import compcert.common.Memory.
Record semantics : Type := Semantics_gen {
  state: Type;
  genvtype: Type;
  step : genvtype -> (state * mem) -> trace -> (state * mem) -> Prop;
  initial_state: (state * mem) -> Prop;
  final_state: (state * mem) -> int -> Prop;
  globalenv: genvtype;
  symbolenv: Senv.t
}.

(** The form used in earlier CompCert versions, for backward compatibility. *)

Definition Semantics {state funtype vartype: Type}
                     (step: Genv.t funtype vartype -> (state * mem) -> trace -> (state * mem) -> Prop)
                     (initial_state: (state * mem) -> Prop)
                     (final_state: (state * mem) -> int -> Prop)
                     (globalenv: Genv.t funtype vartype) :=
  {| state := state;
     genvtype := Genv.t funtype vartype;
     step := step;
     initial_state := initial_state;
     final_state := final_state;
     globalenv := globalenv;
     symbolenv := Genv.to_senv globalenv |}.

(** Handy notations. *)

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : smallstep_scope.

Open Scope smallstep_scope.

(** * Forward simulations between two transition semantics. *)

(** The general form of a forward simulation. *)

Record fsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> meminj -> (state L1 * mem) -> (state L2 * mem) -> Prop) : Prop :=
  {
    fsim_order_wf: well_founded order;
    fsim_match_meminj: forall i f s1 s2, match_states i f s1 s2 ->  Mem.inject f (snd s1) (snd s2);
(*    fsim_match_initial_states:
      forall s1 m1 f m2, initial_state L1 (s1,m1) -> Mem.inject f m1 m2 ->
      exists i, exists s2, initial_state L2 (s2,m2) /\ match_states i f (s1,m1) (s2,m2);*)
    fsim_match_initial_states:
      forall s1 m1, initial_state L1 (s1,m1) -> 
      exists i f s2 m2, initial_state L2 (s2,m2) /\ match_states i f (s1,m1) (s2,m2) /\ Mem.inject f m1 m2;
    fsim_match_final_states:
      forall i s1 m1 s2 m2 r f,
      match_states i f (s1,m1) (s2 ,m2) -> final_state L1 (s1,m1) r -> (final_state L2 (s2,m2) r /\ (*include this term???*) Mem.inject f m1 m2);
    fsim_simulation:
      forall s1 t s1' f, Step L1 s1 t s1' ->
      forall i s2, match_states i f s1 s2 ->
      exists i', exists s2' f' t',
         (Plus L2 s2 t' s2' \/ (Star L2 s2 t' s2' /\ order i' i))
         /\ match_states i' f' s1' s2' /\
         Values.inject_incr f f' /\
         inject_trace f' t t';
    fsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

Arguments fsim_properties: clear implicits.

Inductive forward_simulation (L1 L2: semantics) : Prop :=
  Forward_simulation (index: Type)
                     (order: index -> index -> Prop)
                     (match_states: index -> meminj -> (state L1 * mem) -> (state L2 * mem) -> Prop)
                     (props: fsim_properties L1 L2 index order match_states).

Arguments Forward_simulation {L1 L2 index} order match_states props.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
  forall i s1 t s1' f, Step L1 s1 t s1' ->
  forall s2, match_states i f s1 s2 ->
        (exists i', exists s2' f' t', Plus L2 s2 t' s2' /\
                            match_states i' f' s1' s2'
                            /\ inject_incr f f' /\ inject_trace f' t t')
  \/ (exists i' f', order i' i /\ t = E0 /\ match_states i' f' s1' s2 /\ inject_incr f f').
Proof.
  intros. exploit fsim_simulation; eauto.
  intros [i' [s2' [f' [t'[A [B [C D]]]]]]]. intuition.
  left; exists i'; exists s2'; auto. exists f', t'; eauto.
  inv H3. inversion D; subst.
  right; exists i', f'; eauto.
  left; exists i'; exists s2',f', (t1 ** t2); split; auto. econstructor; eauto.
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)

Section FORWARD_SIMU_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id.

Variable match_states: meminj -> (state L1 * mem) -> (state L2 * mem) -> Prop.
(*
Hypothesis match_initial_states:
  forall s1 m1 f m2, initial_state L1 (s1,m1) -> Mem.inject f m1 m2 ->
  exists s2, initial_state L2 (s2,m2) /\ match_states f (s1,m1) (s2,m2).*)
Hypothesis match_initial_states:
  forall s1 m1, initial_state L1 (s1,m1) ->
  exists s2 f m2, initial_state L2 (s2,m2) /\ match_states f (s1,m1) (s2,m2) /\  Mem.inject f m1 m2.

Hypothesis match_final_states:
  forall f s1 s2 r,
  match_states f s1 s2 ->
  final_state L1 s1 r ->
  final_state L2 s2 r  /\ Mem.inject f (snd s1) (snd s2).

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state L1 -> state L1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 f, match_states f s1 s2 ->
  exists s2' f' t',
  (Plus L2 s2 t' s2' \/ (Star L2 s2 t' s2' /\ order (fst s1') (fst s1)))
  /\ match_states f' s1' s2' /\ inject_incr f f' /\ inject_trace f' t t'.

Hypothesis match_meminj : forall (f : meminj) (s1 : state L1 * mem) (s2 : state L2 * mem),
                        match_states f s1 s2 -> Mem.inject f (snd s1) (snd s2).

Lemma forward_simulation_star_wf: forward_simulation L1 L2.
Proof.
  eapply Forward_simulation with order (fun idx f s1 s2 => idx = fst s1 /\ match_states f s1 s2);
  constructor.
  - auto.
  - intros ? ? ? ? [? ?].
    eapply match_meminj; eauto.

  - intros. exploit match_initial_states; eauto. (*intros [s2 [A B]].
    exists s1; exists s2; auto.*)
    intros [s2 [f [m2 [A [B C]]]]]. exists s1; exists f; exists s2, m2; auto.
- intros. destruct H. exploit match_final_states; eauto.
- intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [f' [t' [A [B C]]]]].
  exists (fst s1'); exists s2'; exists f',t' ; intuition auto.
- auto.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 f, match_states f s1 s2 -> exists f' t',
      (exists s2', Plus L2 s2 t' s2' /\ match_states f' s1' s2'
             /\ inject_incr f f'
             /\ inject_trace f' t t')
      \/ (measure (fst s1') < measure (fst s1) /\ t = E0 /\ match_states f' s1' s2
             /\ inject_incr f f'
         /\ inject_trace f' t t')%nat.

Hypothesis match_meminj : forall (f : meminj) (s1 : state L1 * mem) (s2 : state L2 * mem),
                        match_states f s1 s2 -> Mem.inject f (snd s1) (snd s2).

Lemma forward_simulation_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star_wf with (ltof _ measure).
  apply well_founded_ltof.
  intros. exploit simulation; eauto. intros [f' [t' [[s2' [A [B [C D]]]] | [A [B [C [D E]]]]]]].
  exists s2', f', t'; auto.
  subst; inversion E; subst.
  exists s2, f', nil; split. 
  right; split. 
  apply star_refl. auto. auto.
  eapply match_meminj.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 f, match_states f s1 s2 ->
          exists s2' f' t', Plus L2 s2 t' s2' /\ match_states f' s1' s2'
             /\ inject_incr f f'
         /\ inject_trace f' t t'.


Hypothesis match_meminj : forall (f : meminj) (s1 : state L1 * mem) (s2 : state L2 * mem),
                        match_states f s1 s2 -> Mem.inject f (snd s1) (snd s2).

Lemma forward_simulation_plus: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with (measure := fun _ => O).
  intros. exploit simulation; eauto. intros [s2' [f' [X]]]. exists f'. eauto.
  eapply match_meminj.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 f, match_states f s1 s2 ->
          exists s2' f' t', Step L2 s2 t' s2' /\ match_states f' s1' s2'
                       /\ inject_incr f f'
         /\ inject_trace f' t t'.


Hypothesis match_meminj : forall (f : meminj) (s1 : state L1 * mem) (s2 : state L2 * mem),
                        match_states f s1 s2 -> Mem.inject f (snd s1) (snd s2).

Lemma forward_simulation_step: forward_simulation L1 L2.
Proof.
  apply forward_simulation_plus.
  intros. exploit simulation; eauto. intros [s2' [f' [t' [A [B [C D]]]]]].
  exists s2', f' ,t' ; split; auto. apply plus_one; auto.
  
  eapply match_meminj.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state L1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 f, match_states f s1 s2 -> exists f' t',
  (exists s2', Step L2 s2 t' s2' /\ match_states f' s1' s2'
             /\ inject_incr f f' /\ inject_trace f' t t')
  \/ (measure (fst s1') < measure (fst s1) /\ t = E0 /\ match_states f' s1' s2
     /\ inject_incr f f'
     /\ inject_trace f' t t')%nat.

Hypothesis match_meminj : forall (f : meminj) (s1 : state L1 * mem) (s2 : state L2 * mem),
                        match_states f s1 s2 -> Mem.inject f (snd s1) (snd s2).

Lemma forward_simulation_opt: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with measure.
  intros. exploit simulation; eauto. intros [f' [t' [[s2' [A [B [C D]]]] | [A [B [C [D E]]]]]]].
  exists f', t'. left; exists s2'; split; auto. apply plus_one; auto.
  exists f', t'. right; auto.
  eapply match_meminj.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.

(** ** Forward simulation of transition sequences *)

Section SIMULATION_SEQUENCES.

Context L1 L2 index order match_states (S: fsim_properties L1 L2 index order match_states).

Lemma simulation_star:
  forall s1 t s1', Star L1 s1 t s1' ->
  forall i f s2, match_states i f s1 s2 ->
  exists i' f', exists s2' t', Star L2 s2 t' s2' /\ match_states i' f' s1' s2'
             /\ inject_incr f f' /\ inject_trace f' t t'.
Proof.
  induction 1; intros.
  exists i, f; exists s2 , nil; split; auto. apply star_refl.
  split; auto; constructor.
  apply inject_incr_refl. constructor.
  exploit fsim_simulation; eauto. intros [i' [s2' [f'[t' [A [B [C D]]]]]]].
  exploit IHstar; eauto. intros [i'' [f'' [s2'' [t'' [E [F [G HH]]]]]]].
  exists i'';exists f''; exists s2'', (t' ** t''); split; auto. eapply star_trans; eauto.
  intuition auto. apply plus_star; auto.
  split; auto. subst t.
  split; auto.
  eapply inject_incr_trans; eauto.
  (*Some properties about inject_trace*)
Admitted.

Lemma simulation_plus:
  forall s1 t s1', Plus L1 s1 t s1' ->
  forall i f s2, match_states i f s1 s2 -> 
            (exists i', exists f', exists s2' t', Plus L2 s2 t' s2' /\ match_states i' f' s1' s2'
            /\ inject_incr f f' /\ inject_trace f' t t')
            \/ (exists i', exists f', clos_trans _ order i' i /\ t = E0 /\ match_states i' f' s1' s2
              /\ inject_incr f f').
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [f' [t' [A [B [C D]]]]]]] | [i' [f' [t' A]]]].
  left. exists i', f', s2', t'; auto.
  right; exists i', f' ; intuition.
(* inductive case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [f' [t' [A [B [C D]]]]]]] | [i' [f' [A [B [C D]]]]]].
  exploit simulation_star. apply plus_star; eauto. eauto.
  intros [i'' [f'' [s2'' [t'' [P [Q [R SS]]]]]]].
  left; exists i''; exists f''; exists s2'', (t'**t''); split; auto. eapply plus_star_trans; eauto.
  repeat split; auto.
  eapply inject_incr_trans; eauto.
  (*Some properties about inject_trace*)
  admit.
  
  exploit IHplus; eauto. intros [[i'' [f'' [s2'' [t' [P [Q [R SS]]]]]]] | [i'' [f'' [P [Q R]]]]].
  subst. simpl. left; exists i''; exists f''; exists s2'', (t'); auto.
  repeat split; eauto.
  eapply inject_incr_trans; eauto.
  subst. simpl. right; exists i''; exists f''; intuition auto.
  eapply t_trans; eauto. eapply t_step; eauto.
  eapply inject_incr_trans; eauto.
Admitted.

Lemma simulation_forever_silent:
  forall i f s1 s2,
  Forever_silent L1 s1 -> match_states i f s1 s2 ->
  Forever_silent L2 s2.
Proof.
  assert (forall i f s1 s2,
          Forever_silent L1 s1 -> match_states i f s1 s2 ->
          forever_silent_N (step L2) order (globalenv L2) i s2).
    cofix COINDHYP; intros.
    inv H. destruct (fsim_simulation S _ _ _ f H1 _ _ H0) as [i' [s2' [f' [t' [A [B [C D]]]]]]].
    inversion D; subst.
    destruct A as [E | [E F]]. 
    eapply forever_silent_N_plus; eauto.
    eapply forever_silent_N_star; eauto.
    intros.
    eapply forever_silent_N_forever; eauto. eapply fsim_order_wf; eauto.
Qed.

Lemma simulation_forever_reactive:
  forall i f s1 s2 T,
  Forever_reactive L1 s1 T -> match_states i f s1 s2 ->
  Forever_reactive L2 s2 T.
Proof.
  cofix COINDHYP; intros.
  inv H.
  edestruct simulation_star as [f' [t' [st2' [t'' [A [B [C D]]]]]]]; eauto.
  econstructor; eauto.
  (*Need to extend the concept of inject_trace to traceinf*)
Admitted.

End SIMULATION_SEQUENCES.

(** ** Composing two forward simulations *)

Lemma compose_forward_simulations:
  forall L1 L2 L3, forward_simulation L1 L2 -> forward_simulation L2 L3 -> forward_simulation L1 L3.
Proof.
  intros L1 L2 L3 S12 S23.
  destruct S12 as [index order match_states props].
  destruct S23 as [index' order' match_states' props'].

  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states := fun (i: ff_index) f (s1: state L1 * mem) (s3: state L3 * mem) =>
                             exists s2 f1 f2, match_states (snd i) f1 s1 s2 /\ match_states' (fst i) f2 s2 s3 /\
                             compose_meminj f1 f2=f).
  apply Forward_simulation with ff_order ff_match_states; constructor.
- (* well founded *)
  unfold ff_order. apply wf_lex_ord. apply wf_clos_trans.
  eapply fsim_order_wf; eauto. eapply fsim_order_wf; eauto.
- (* Mem.inject *) (*The alternative def of fsim fails here*)
  intros.
  unfold ff_match_states in H.
  destruct H as [s3 [f1 [f2 [MS1 [MS2 compF]]]]].
  rewrite <- compF.
  eapply 
    Mem.inject_compose; first [eapply props;eassumption | eapply props';eassumption].
- (* initial states *) (*The alternative def of fsim fails here*)
  intros. exploit (fsim_match_initial_states props); eauto.
  intros [i [f [s2 [m2 [A [B BB]]]]]].
  exploit (fsim_match_initial_states props'); eauto. intros [i' [f' [s3 [m3 [C [D DD]]]]]].
  exists (i', i), (compose_meminj f f'); exists s3, m3; split; auto.
  split. exists (s2, m2), f, f'; auto.
  eapply Mem.inject_compose; eauto.
- (* final states *)
  intros i s1 m1 s3 m3 r f H FS1. destruct H as [[s2 m2] [f1 [f2 [A [B C]]]]].
  assert (final_state L2 (s2, m2) r /\ Mem.inject f1 m1 m2).
    { eapply (fsim_match_final_states props); eauto. }
  destruct H as [FS2 INJ12].
  assert (final_state L3 (s3, m3) r /\ Mem.inject f2 m2 m3).
  { eapply (fsim_match_final_states props'); eauto. }
  destruct H as [FS3 INJ23].
  split; trivial. subst; eapply Mem.inject_compose; eauto.
- (* simulation *)
  intros. rename s2 into s3. destruct H0 as [s2 [f1 [f2 [A [B C]]]]]; subst. destruct i as [i2 i1]; simpl in *.
  exploit (fsim_simulation' props); eauto. intros [[i1' [s2' [g1 [t2' [C [D [F G]]]]]]] | [i1' [g1 [C [D [E F]]]]]].
+ (* L2 makes one or several steps. *)
  exploit simulation_plus; eauto. intros [[i2' [g2 [s3' [t3' [P [Q [R S]]]]]]] | [i2' [g2 [P [Q [R S]]]]]].
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s3', (compose_meminj g1 g2), t3'; split. auto.
  split. 
  exists s2', g1, g2; auto.
  admit.
* (* L3 makes no step *)
  exists (i2', i1'); exists s3, (compose_meminj g1 g2), nil; split.
  right; split. apply star_refl. red. left. auto.
  split. exists s2', g1, g2; auto.
  admit.
  
+ (* L2 makes no step *)
  exists (i2, i1'); exists s3, (compose_meminj g1 f2), nil; split.
  right; split. subst t; apply star_refl. red. right. auto.
  split. exists s2, g1, f2; auto.
  admit.
- (* symbols *)
  intros. transitivity (Senv.public_symbol (symbolenv L2) id); eapply fsim_public_preserved; eauto.
Admitted.

(** * Receptiveness and determinacy *)

Definition single_events (L: semantics) : Prop :=
  forall s t s', Step L s t s' -> (length t <= 1)%nat.

Record receptive (L: semantics) : Prop :=
  Receptive {
    sr_receptive: forall s t1 s1 t2,
      Step L s t1 s1 -> match_traces (symbolenv L) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces:
      single_events L
  }.

Record determinate (L: semantics) : Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall s1 s2,
      initial_state L s1 -> initial_state L s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.

Section DETERMINACY.

Variable L: semantics.
Hypothesis DET: determinate L.

Lemma sd_determ_1:
  forall s t1 s1 t2 s2,
  Step L s t1 s1 -> Step L s t2 s2 -> match_traces (symbolenv L) t1 t2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma sd_determ_2:
  forall s t s1 s2,
  Step L s t s1 -> Step L s t s2 -> s1 = s2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma star_determinacy:
  forall s t s', Star L s t s' ->
  forall s'', Star L s t s'' -> Star L s' E0 s'' \/ Star L s'' E0 s'.
Proof.
  induction 1; intros.
  auto.
  inv H2.
  right. eapply star_step; eauto.
  exploit sd_determ_1. eexact H. eexact H3. intros MT.
  exploit (sd_traces DET). eexact H. intros L1.
  exploit (sd_traces DET). eexact H3. intros L2.
  assert (t1 = t0 /\ t2 = t3).
    destruct t1. inv MT. auto.
    destruct t1; simpl in L1; try omegaContradiction.
    destruct t0. inv MT. destruct t0; simpl in L2; try omegaContradiction.
    simpl in H5. split. congruence. congruence.
  destruct H1; subst.
  assert (s2 = s4) by (eapply sd_determ_2; eauto). subst s4.
  auto.
Qed.

End DETERMINACY.
 
(** * Backward simulations between two transition semantics. *)

Definition safe (L: semantics) (s: state L * mem) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists t, exists s'', Step L s' t s'').

Lemma star_safe:
  forall (L: semantics) s s',
  Star L s E0 s' -> safe L s -> safe L s'.
Proof.
  intros; red; intros. apply H0. eapply star_trans; eauto.
Qed.

(** The general form of a backward simulation. *)

Record bsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> meminj -> state L1 * mem -> state L2 * mem -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    bsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', exists f, initial_state L1 s1' /\ match_states i f s1' s2 /\ Mem.inject f (snd s1') (snd s2);
    bsim_match_final_states:
      forall i s1 s2 r f,
      match_states i f s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    bsim_progress:
      forall i s1 s2 f,
      match_states i f s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1 f, match_states i f s1 s2 -> safe L1 s1 ->
      exists i', exists f', exists s1', exists t',
         (Plus L1 s1 t' s1' \/ (Star L1 s1 t' s1' /\ order i' i))
         /\ match_states i' f' s1' s2' /\
         Values.inject_incr f f' /\
         inject_trace f' t t';
    bsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

Arguments bsim_properties: clear implicits.

Inductive backward_simulation (L1 L2: semantics) : Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (match_states: index -> meminj -> state L1 * mem -> state L2 * mem -> Prop)
                      (props: bsim_properties L1 L2 index order match_states).

Arguments Backward_simulation {L1 L2 index} order match_states props.

(** An alternate form of the simulation diagram *)

Lemma bsim_simulation':
  forall L1 L2 index order match_states, bsim_properties L1 L2 index order match_states ->
  forall i s2 t s2', Step L2 s2 t s2' ->
  forall f s1, match_states i f s1 s2 -> safe L1 s1 -> 
          (exists i', exists s1', exists f', exists t',Plus L1 s1 t' s1' /\ match_states i' f' s1' s2'
          /\ Values.inject_incr f f' /\ inject_trace f' t t')
  \/ (exists i', exists f', order i' i /\ t = E0 /\ match_states i' f' s1 s2').
Proof.
  intros. exploit bsim_simulation; eauto.
  intros [i' [f' [s1' [t' [A [B C]]]]]]. intuition.
  left; exists i'; exists s1', f', t'; auto.
  
  inv H6.
  inversion H4.
  right; exists i', f'; auto.
  
  left; exists i'; exists s1', f', (t1 ** t2); split; auto. econstructor; eauto.
Qed.

(** ** Backward simulation diagrams. *)

(** Various simulation diagrams that imply backward simulation. *)

Section BACKWARD_SIMU_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id.

Variable match_states: meminj -> state L1 * mem -> state L2 * mem -> Prop.

Hypothesis initial_states_exist:
  forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2.

Hypothesis match_initial_states:
  forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
  exists s1' f, initial_state L1 s1' /\ match_states f s1' s2 /\ Mem.inject f (snd s1') (snd s2).

Hypothesis match_final_states:
  forall s1 s2 r f,
  match_states f s1 s2 -> final_state L2 s2 r -> final_state L1 s1 r /\ (*include this term???*) Mem.inject f (snd s1) (snd s2).

Hypothesis progress:
  forall s1 s2 f,
  match_states f s1 s2 -> safe L1 s1 ->
  (exists r, final_state L2 s2 r) \/
  (exists t, exists s2', Step L2 s2 t s2').

Section BACKWARD_SIMULATION_PLUS.

Hypothesis simulation:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall s1 f, match_states f s1 s2 -> safe L1 s1 ->
  exists s1' f' t', Plus L1 s1 t' s1' /\ match_states f' s1' s2' /\
         Values.inject_incr f f' /\
         inject_trace f' t t'.

Lemma backward_simulation_plus: backward_simulation L1 L2.
Proof.
  apply Backward_simulation with
    (fun (x y: unit) => False)
    (fun (i: unit) f s1 s2 => match_states f s1 s2);
  constructor; auto.
- red; intros; constructor; intros. contradiction.
- intros. exists tt; eauto.
- intros. exists s1; split. apply star_refl. eapply match_final_states; eauto.
- intros. exploit simulation; eauto. intros [s1' [f' [t' [A [B C]]]]].
  exists tt; exists f'; exists s1'; exists t'; auto.
  
Qed.

End BACKWARD_SIMULATION_PLUS.

End BACKWARD_SIMU_DIAGRAMS.

(** ** Backward simulation of transition sequences *)

Section BACKWARD_SIMULATION_SEQUENCES.

Context L1 L2 index order match_states (S: bsim_properties L1 L2 index order match_states).

Lemma bsim_E0_star:
  forall s2 s2', Star L2 s2 E0 s2' ->
  forall i s1 f, match_states i f s1 s2 -> safe L1 s1 ->
  exists i', exists s1' f', Star L1 s1 E0 s1' /\ match_states i' f' s1' s2'.
Proof.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
- (* base case *)
  intros. exists i; exists s1, f; split; auto. apply star_refl.
- (* inductive case *)
  intros. exploit bsim_simulation; eauto. intros [i' [f' [s1' [t' [A [B [C D]]]]]]].
  inv D.
  assert (Star L1 s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. inv A; auto; eapply star_safe; eauto.
  intros [i'' [s1'' [f'' [E F]]]].
  exists i''; exists s1'', f''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_safe:
  forall i s1 s2 f,
  match_states i f s1 s2 -> safe L1 s1 -> safe L2 s2.
Proof.
  intros; red; intros.
  exploit bsim_E0_star; eauto. intros [i' [s1' [f' [A B]]]].
  eapply bsim_progress; eauto. eapply star_safe; eauto.
Qed.

Lemma bsim_E0_plus:
  forall s2 t s2', Plus L2 s2 t s2' -> t = E0 ->
  forall i s1 f, match_states i f s1 s2 -> safe L1 s1 ->
     (exists i' f', exists s1', Plus L1 s1 E0 s1' /\ match_states i' f' s1' s2')
  \/ (exists i' f', clos_trans _ order i' i /\ match_states i' f' s1 s2').
Proof.
  induction 1 using plus_ind2; intros; subst t.
- (* base case *)
  exploit bsim_simulation'; eauto. intros [[i' [s1' [f' [t' [A [B [C D]]]]]]] | [i' [f' [A [B C]]]]].
+ inv D. left; exists i', f'; exists s1'; auto.
+ right; exists i', f'; intuition.
- (* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit bsim_simulation'; eauto. intros [[i' [s1' [f' [t' [A [B [C D]]]]]]] | [i' [f' [A [B C]]]]].
+ inv D. exploit bsim_E0_star. apply plus_star; eauto. eauto. eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [f'' [P Q]]]].
  left; exists i'', f''; exists s1''; intuition. eapply plus_star_trans; eauto.
+ exploit IHplus; eauto. intros [P | [i'' [f'' [P Q]]]].
  left; auto.
  right; exists i'', f''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.

Lemma star_non_E0_split:
  forall s2 t s2', Star L2 s2 t s2' -> (length t = 1)%nat ->
  exists s2x, exists s2y, Star L2 s2 E0 s2x /\ Step L2 s2x t s2y /\ Star L2 s2y E0 s2'.
Proof.
  induction 1; intros.
  simpl in H; discriminate.
  subst t.
  assert (EITHER: t1 = E0 \/ t2 = E0).
    unfold Eapp in H2; rewrite app_length in H2.
    destruct t1; auto. destruct t2; auto. simpl in H2; omegaContradiction.
  destruct EITHER; subst.
  exploit IHstar; eauto. intros [s2x [s2y [A [B C]]]].
  exists s2x; exists s2y; intuition. eapply star_left; eauto.
  rewrite E0_right. exists s1; exists s2; intuition. apply star_refl.
Qed.

End BACKWARD_SIMULATION_SEQUENCES.

(** ** Composing two backward simulations *)

Section COMPOSE_BACKWARD_SIMULATIONS.

Variable L1: semantics.
Variable L2: semantics.
Variable L3: semantics.
Hypothesis L3_single_events: single_events L3.
Context index order match_states (S12: bsim_properties L1 L2 index order match_states).
Context index' order' match_states' (S23: bsim_properties L2 L3 index' order' match_states').

Let bb_index : Type := (index * index')%type.

Definition bb_order : bb_index -> bb_index -> Prop := lex_ord (clos_trans _ order) order'.

Inductive bb_match_states: bb_index -> meminj -> state L1 * mem -> state L3 * mem -> Prop :=
  | bb_match_later: forall i1 i2 f s1 s3 s2x s2y f1 f2,
      match_states i1 f1 s1 s2x -> Star L2 s2x E0 s2y -> match_states' i2 f2 s2y s3 ->
      compose_meminj f1 f2=f ->
      bb_match_states (i1, i2) f s1 s3.

Lemma bb_match_at: forall i1 i2 s1 s3 s2 f1 f2,
  match_states i1 f1 s1 s2 -> match_states' i2 f2 s2 s3 ->
  bb_match_states (i1, i2) (compose_meminj f1 f2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.

Lemma bb_simulation_base:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i1 s1 i2 s2 f1 f2, match_states i1 f1 s1 s2 -> match_states' i2 f2 s2 s3 -> safe L1 s1 ->
  exists i', exists s1', exists f', exists t',
    (Plus L1 s1 t' s1' \/ (Star L1 s1 t' s1' /\ bb_order i' (i1, i2)))
    /\ bb_match_states i' f' s1' s3' /\
    inject_incr (compose_meminj f1 f2) f' /\
    inject_trace f' t t'.
Proof.
  intros.
  exploit (bsim_simulation' S23); eauto. eapply bsim_safe; eauto.
  intros [ [i2' [s2' [f2' [t' [PLUS2 [MATCH2 [? ?]]]]]]] | [i2' [f2' [ORD2 [EQ MATCH2]]]]].
- (* 1 L2 makes one or several transitions *)
  assert (EITHER: t = E0 \/ (length t = 1)%nat).
  { exploit L3_single_events; eauto.
    destruct t; auto. destruct t; auto. simpl. intros. omegaContradiction. }
  destruct EITHER.
+ (* 1.1 these are silent transitions *)
  subst t. inv H4. exploit (bsim_E0_plus S12); eauto.
  intros [ [i1' [f1' [s1' [PLUS1 MATCH1]]]] | [i1' [f1' [ORD1 MATCH1]]]].
* (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1', (compose_meminj f1' f2'), E0; split. auto. split.
  eapply bb_match_at; eauto.
  admit.
* (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1, (compose_meminj f1' f2'), E0; split.
  right; split. apply star_refl. left; auto. split.
  eapply bb_match_at; eauto.
  admit.
+ (* 1.2 non-silent transitions *)
  exploit star_non_E0_split. apply plus_star; eauto.
  do 2 match goal with
  | [ H: inject_trace _ _ _  |- _ ] => inv H; auto 
  end. inv H5.
  inv H4; auto; simpl in *. inv H5; auto; inversion H5.
  intros [s2x [s2y [P [Q R]]]].
  exploit (bsim_E0_star S12). eexact P. eauto. auto. intros [i1' [s1x [g1 [X Y]]]].
  exploit (bsim_simulation' S12). eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [g1'' [t'' [U [V [? ?]]]]]]] | [i1'' [g1'' [U [V W]]]]]; try (subst t; discriminate); try discriminate.
  exists (i1'', i2'); exists s1y. exists (compose_meminj g1'' f2'), t''. split.
  left. eapply star_plus_trans; eauto. split.
  eapply bb_match_later; eauto.
  admit.
- (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1, (compose_meminj f1 f2'), E0; split.
  right; split. apply star_refl. right; auto. split.
  eapply bb_match_at; eauto.
  admit.
Admitted.

Lemma bb_simulation:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i s1 f, bb_match_states i f s1 s3 -> safe L1 s1 ->
  exists i', exists s1', exists f' t',
    (Plus L1 s1 t' s1' \/ (Star L1 s1 t' s1' /\ bb_order i' i))
    /\ bb_match_states i' f' s1' s3' /\
    inject_incr f f' /\
    inject_trace f' t t'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
- (* 1. match at *)
  subst. eapply bb_simulation_base; eauto.
- (* 2. match later *)
  exploit (bsim_E0_plus S12); eauto.
  intros [[i1' [f1' [s1' [A B]]]] | [i1' [f1' [A B]]]].
+ (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [f'' [ t'' [C [D [E F]]]]]]].
  exists i''; exists s1'', f'', t''; repeat split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
  admit.
+ (* 2.2 no silent transition *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto. auto.
  intros [i'' [s1'' [f'' [t'' [C [D [E F]]]]]]].
  exists i''; exists s1'', f'', t''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Admitted.

End COMPOSE_BACKWARD_SIMULATIONS.

Lemma compose_backward_simulation:
  forall L1 L2 L3,
  single_events L3 -> backward_simulation L1 L2 -> backward_simulation L2 L3 ->
  backward_simulation L1 L3.
Proof.
  intros L1 L2 L3 L3single S12 S23.
  destruct S12 as [index order match_states props].
  destruct S23 as [index' order' match_states' props'].
  apply Backward_simulation with (bb_order order order') (bb_match_states L1 L2 L3 match_states match_states');
  constructor.
- (* well founded *)
  unfold bb_order. apply wf_lex_ord. apply wf_clos_trans. eapply bsim_order_wf; eauto. eapply bsim_order_wf; eauto.
- (* initial states exist *)
  intros. exploit (bsim_initial_states_exist props); eauto. intros [s2 A].
  eapply (bsim_initial_states_exist props'); eauto.
- (* match initial states *)
  intros s1 s3 INIT1 INIT3.
  exploit (bsim_initial_states_exist props); eauto. intros [s2 INIT2].
  exploit (bsim_match_initial_states props'); eauto. intros [i2 [s2' [f2 [INIT2' M2]]]].
  exploit (bsim_match_initial_states props); eauto. intros [i1 [s1' [f1 [INIT1' M1]]]].
  exists (i1, i2); exists s1', (compose_meminj f1 f2); intuition auto. eapply bb_match_at; eauto.
  eapply Mem.inject_compose; eauto.
- (* match final states *)
  intros i s1 s3 r f MS SAFE FIN. inv MS.
  exploit (bsim_match_final_states props'); eauto.
    eapply star_safe; eauto. eapply bsim_safe; eauto.
  intros [s2' [A B]].
  exploit (bsim_E0_star props). eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
  intros [i1' [s1' [f [C D]]]].
  exploit (bsim_match_final_states props); eauto. eapply star_safe; eauto.
  intros [s1'' [P Q]].
  exists s1''; split; auto. eapply star_trans; eauto.
- (* progress *)
  intros i s1 s3 f MS SAFE. inv MS.
  eapply (bsim_progress props'). eauto. eapply star_safe; eauto. eapply bsim_safe; eauto.
- (* simulation *)
  intros s3 t s3'; intros.
  destruct (@bb_simulation L1 L2 _ L3single _ _ _ props _ _ _ props' _ _ _ H _ _ _ H0 H1)
  as [i' [s1' [f' [t' [A [B [C D]]]]]]]. exists i', f', s1', t'; repeat (split; auto). 
- (* symbols *)
  intros. transitivity (Senv.public_symbol (symbolenv L2) id); eapply bsim_public_preserved; eauto.
Qed.

(** ** Converting a forward simulation to a backward simulation *)

Section FORWARD_TO_BACKWARD.

Context L1 L2 index order match_states (FS: fsim_properties L1 L2 index order match_states).
Hypothesis L1_receptive: receptive L1.
Hypothesis L2_determinate: determinate L2.

(** Exploiting forward simulation *)

Inductive f2b_transitions: state L1 * mem -> state L2 * mem -> Prop :=
  | f2b_trans_final: forall s1 s2 s1' r,
      Star L1 s1 E0 s1' ->
      final_state L1 s1' r ->
      final_state L2 s2 r ->
      f2b_transitions s1 s2
  | f2b_trans_step: forall s1 s2 s1' t t' s1'' s2' i' i'' f' f'',
      Star L1 s1 E0 s1' ->
      Step L1 s1' t s1'' ->
      Plus L2 s2 t' s2' ->
      inject_trace f'' t t' ->
      match_states i' f' s1' s2 ->
      match_states i'' f'' s1'' s2' ->
      f2b_transitions s1 s2.

Lemma f2b_progress:
  forall i f s1 s2, match_states i f s1 s2 -> safe L1 s1 -> f2b_transitions s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := order).
  eapply fsim_order_wf; eauto.
  intros i REC f s1 s2 MATCH SAFE.
  destruct (SAFE s1) as [[r FINAL] | [t [s1' STEP1]]]. apply star_refl.
- (* final state reached *)
  eapply f2b_trans_final; eauto.
  apply star_refl. destruct s1 as [s1 m1]. destruct s2 as [s2 m2].
  exploit fsim_match_final_states. apply FS. apply MATCH. simpl; apply FINAL. intros X; apply X.
- (* L1 can make one step *)
  exploit (fsim_simulation FS); eauto. intros [i' [s2' [f2' [t' [A [MATCH' [B C]]]]]]].
  assert (D: Plus L2 s2 t' s2' \/ (s2' = s2 /\ t = E0 /\ order i' i)).
  intuition auto.
  destruct (star_inv H0); intuition auto.
  subst; inversion C; intuition.
    clear A. destruct D as [PLUS2 | [EQ1 [EQ2 ORDER]]].
  + eapply f2b_trans_step; eauto. apply star_refl.
  + subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
    intros TRANS; inv TRANS.
    * eapply f2b_trans_final; eauto. eapply star_left; eauto.
    * eapply f2b_trans_step; eauto. eapply star_left; eauto.
Qed.

Lemma fsim_simulation_not_E0:
  forall s1 t s1', Step L1 s1 t s1' -> t <> E0 ->
  forall i s2 f, match_states i f s1 s2 ->
  exists i', exists s2' f' t', Plus L2 s2 t' s2' /\ match_states i' f' s1' s2' /\ inject_incr f f' /\ inject_trace f' t t'.
Proof.
  intros. exploit (fsim_simulation FS); eauto. intros [i' [s2' [f2 [t' [A [B [C D]]]]]]].
  exists i'; exists s2', f2, t'; split; auto.
  destruct A. auto. destruct H2. exploit star_inv; eauto. intros [[EQ1 EQ2] | P]; auto.
  subst.
  inversion D; subst.
  unfold E0 in *; congruence.
Qed.

(** Exploiting determinacy *)

Remark silent_or_not_silent:
  forall t, t = E0 \/ t <> E0.
Proof.
  intros; unfold E0; destruct t; auto; right; congruence.
Qed.

Remark not_silent_length:
  forall t1 t2, (length (t1 ** t2) <= 1)%nat -> t1 = E0 \/ t2 = E0.
Proof.
  unfold Eapp, E0; intros. rewrite app_length in H.
  destruct t1; destruct t2; auto. simpl in H. omegaContradiction.
Qed.

Lemma f2b_determinacy_inv:
  forall s2 t' s2' t'' s2'',
  Step L2 s2 t' s2' -> Step L2 s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces (symbolenv L1) t' t'').
Proof.
  intros.
  assert (match_traces (symbolenv L2) t' t'').
    eapply sd_determ_1; eauto.
  destruct (silent_or_not_silent t').
  subst. inv H1.
  left; intuition. eapply sd_determ_2; eauto.
  destruct (silent_or_not_silent t'').
  subst. inv H1. elim H2; auto.
  right; intuition.
  eapply match_traces_preserved with (ge1 := (symbolenv L2)); auto.
  intros; symmetry; apply (fsim_public_preserved FS).
Qed.

Lemma f2b_determinacy_star:
  forall s s1, Star L2 s E0 s1 ->
  forall t s2 s3,
  Step L2 s1 t s2 -> t <> E0 ->
  Star L2 s t s3 ->
  Star L2 s1 t s3.
Proof.
  intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence.
  exploit f2b_determinacy_inv. eexact H. eexact H4.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto.
  congruence.
Qed.

(** Orders *)

Inductive f2b_index : Type :=
  | F2BI_before (n: nat)
  | F2BI_after (n: nat).

Inductive f2b_order: f2b_index -> f2b_index -> Prop :=
  | f2b_order_before: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_before n') (F2BI_before n)
  | f2b_order_after: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_after n') (F2BI_after n)
  | f2b_order_switch: forall n n',
      f2b_order (F2BI_before n') (F2BI_after n).

Lemma wf_f2b_order:
  well_founded f2b_order.
Proof.
  assert (ACC1: forall n, Acc f2b_order (F2BI_before n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  assert (ACC2: forall n, Acc f2b_order (F2BI_after n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto. auto.
  red; intros. destruct a; auto.
Qed.

(** Constructing the backward simulation *)

Inductive f2b_match_states: f2b_index -> (*omit???*)meminj -> state L1 * mem -> state L2 * mem -> Prop :=
  | f2b_match_at: forall i s1 s2 f,
      match_states i f s1 s2 ->
      f2b_match_states (F2BI_after O) f s1 s2
  | f2b_match_before: forall s1 t s1' s2b s2 n s2a i f,
      Step L1 s1 t s1' ->  t <> E0 ->
      Star L2 s2b E0 s2 ->
      starN (step L2) (globalenv L2) n s2 t s2a ->
      match_states i f s1 s2b ->
      f2b_match_states (F2BI_before n) f s1 s2
  | f2b_match_after: forall n s2 s2a s1 i f,
      starN (step L2) (globalenv L2) (S n) s2 E0 s2a ->
      match_states i f s1 s2a ->
      f2b_match_states (F2BI_after (S n)) f s1 s2.

Remark f2b_match_after':
  forall n s2 s2a s1 i f,
  starN (step L2) (globalenv L2) n s2 E0 s2a ->
  match_states i f s1 s2a ->
  f2b_match_states (F2BI_after n) f s1 s2.
Proof.
  intros. inv H.
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

(** Backward simulation of L2 steps *)

Lemma f2b_simulation_step:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall i s1 f, f2b_match_states i f s1 s2 -> safe L1 s1 ->
  exists i', exists s1' f' t',
    (Plus L1 s1 t' s1' \/ (Star L1 s1 t' s1' /\ f2b_order i' i))
     /\ f2b_match_states i' f' s1' s2' /\ inject_incr f f' /\ inject_trace f' t t'.
Proof.
(*
  intros s2 t s2' STEP2 i s1 f MATCH SAFE.
  inv MATCH.
- (* 1. At matching states *)
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
+ (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
  exploit (sd_final_nostep L2_determinate); eauto. contradiction.
+ (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
  inv H2.
  exploit f2b_determinacy_inv. eexact H6. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
* (* 1.2.1  L2 makes a silent transition *)
  destruct (silent_or_not_silent t2).
  (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
  subst. simpl in *. destruct (star_starN H7) as [n STEPS2].
  exists (F2BI_after n); exists s1'' ; eexists; exists E0. split.
  left. eapply plus_right; eauto.
  simpl. inversion H3; auto.
  split.
  eapply f2b_match_after'; eauto.
  split; auto.
  (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_before n); exists s1'; eexists; split.
  right; split. auto. constructor.
  econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
* (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst t2. rewrite E0_right in H1.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [f''' [P Q]]]]. inv P.
  (* Exploit determinacy *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst t0. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H8. auto.
  subst t2. rewrite E0_right in *.
  assert (s4 = s2'). eapply sd_determ_2; eauto. subst s4.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H7) as [n STEPS2]. exists (F2BI_after n); exists s1'''; eexists; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.

- (* 2. Before *)
  inv H2. congruence.
  exploit f2b_determinacy_inv. eexact H4. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
+ (* 2.1 L2 makes a silent transition: remain in "before" state *)
  subst. simpl in *. exists (F2BI_before n0); exists s1; eexists; split.
  right; split. apply star_refl. constructor. omega.
  econstructor; eauto. eapply star_right; eauto.
+ (* 2.2 L2 make a non-silent transition *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst. rewrite E0_right in *.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [f''' [P Q]]]].
  (* Exploit determinacy *)
  exploit f2b_determinacy_star. eauto. eexact STEP2. auto. apply plus_star; eauto.
  intro R. inv R. congruence.
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H7; auto.
  subst. rewrite E0_right in *.
  assert (s3 = s2'). eapply sd_determ_2; eauto. subst s3.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H6) as [n STEPS2]. exists (F2BI_after n); exists s1'''; eexists; split.
  left. apply plus_one; auto.
  eapply f2b_match_after'; eauto.

- (* 3. After *)
  inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit f2b_determinacy_inv. eexact H2. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (F2BI_after n); exists s1; eexists; split.
  right; split. apply star_refl. constructor; omega.
  eapply f2b_match_after'; eauto.
  congruence.
Qed.*)
  
  Admitted. (*NEED TO CHANGE THE MATCH RELATION*)

End FORWARD_TO_BACKWARD.

(** The backward simulation *)

Lemma forward_to_backward_simulation:
  forall L1 L2,
  forward_simulation L1 L2 -> receptive L1 -> determinate L2 ->
  backward_simulation L1 L2.
Proof.
(*  intros L1 L2 FS L1_receptive L2_determinate.
  destruct FS as [index order match_states FS].
  apply Backward_simulation with f2b_order (f2b_match_states L1 L2 match_states); constructor.
- (* well founded *)
  apply wf_f2b_order.
- (* initial states exist *)
  intros [s1 m1] H. exploit (fsim_match_initial_states FS); eauto. intros [i [f [s2 [m2 [A [B C]]]]]].
  exists (s2,m2); auto.
- (* initial states *)
  intros. destruct s1 as [s1 m1]. destruct s2 as [s2 m2]. exploit (fsim_match_initial_states FS); eauto. intros [i [f [s2' [m2' [A [B C]]]]]].
  assert ((s2,m2) = (s2',m2')) by (eapply sd_initial_determ; eauto). inv H1. (* subst s2'.*)
  exists (F2BI_after O); exists (s1, m1); eexists; split; auto. split. econstructor; eauto. simpl; trivial.
- (* final states *)
  intros. inv H.
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  assert (r0 = r) by (eapply (sd_final_determ L2_determinate); eauto). subst r0.
  exists s1'; auto.
  inv H4. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H5. congruence. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H2. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
- (* progress *)
  intros. inv H.
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  left; exists r; auto.
  inv H3. right; econstructor; econstructor; eauto.
  inv H4. congruence. right; econstructor; econstructor; eauto.
  inv H1. right; econstructor; econstructor; eauto.
- (* simulation *)
  intros. destruct (f2b_simulation_step FS L1_receptive L2_determinate _ _ H H0 H1)
  as [i' [s1' [f' [t' [A [B C]]]]]]. exists i', f', s1'; trivial. 
  (*eapply f2b_simulation_step; eauto.*)
- (* symbols preserved *)
  exact (fsim_public_preserved FS).

Qed. *)
Admitted. (*Need to change backwards simulation *)


(** * Transforming a semantics into a single-event, equivalent semantics *)

Definition well_behaved_traces (L: semantics) : Prop :=
  forall s t s', Step L s t s' ->
  match t with nil => True | ev :: t' => output_trace t' end.

Section ATOMIC.

Variable L: semantics.

Hypothesis Lwb: well_behaved_traces L.

Inductive atomic_step (ge: genvtype L): (trace * state L * mem) -> trace -> (trace * state L * mem) -> Prop :=
  | atomic_step_silent: forall s s' m m',
      Step L (s,m) E0 (s',m') ->
      atomic_step ge (E0, s, m) E0 (E0, s', m')
  | atomic_step_start: forall s ev t s' m m',
      Step L (s,m) (ev :: t) (s',m') ->
      atomic_step ge (E0, s, m) (ev :: nil) (t, s', m')
  | atomic_step_continue: forall ev t s m,
      output_trace (ev :: t) ->
      atomic_step ge (ev :: t, s, m) (ev :: nil) (t, s, m).

Definition atomic : semantics := {|
  state := (trace * state L)%type;
  genvtype := genvtype L;
  step := atomic_step;
  initial_state := fun s => initial_state L (snd (fst s), snd s) /\ fst (fst s) = E0;
  final_state := fun s r => final_state L (snd (fst s), snd s) r /\ fst (fst s) = E0;
  globalenv := globalenv L;
  symbolenv := symbolenv L
|}.

End ATOMIC.

(** A forward simulation from a semantics [L1] to a single-event semantics [L2]
  can be "factored" into a forward simulation from [atomic L1] to [L2]. *)

Section FACTOR_FORWARD_SIMULATION.

Variable L1: semantics.
Variable L2: semantics.
Context index order match_states (sim: fsim_properties L1 L2 index order match_states).
Hypothesis L2single: single_events L2.

Inductive ffs_match: index -> meminj -> (trace * state L1 * mem) -> state L2 * mem -> Prop :=
  | ffs_match_at: forall i f s1 s2 m1,
      match_states i f (s1,m1) s2 ->
      ffs_match i f (E0, s1, m1) s2
  | ffs_match_buffer: forall i f ev t s1 s2 s2' m1,
      Star L2 s2 (ev :: t) s2' -> match_states i f (s1,m1) s2' ->
      ffs_match i f (ev :: t, s1, m1) s2.

Lemma star_non_E0_split':
  forall s2 t s2', Star L2 s2 t s2' ->
  match t with
  | nil => True
  | ev :: t' => exists s2x, Plus L2 s2 (ev :: nil) s2x /\ Star L2 s2x t' s2'
  end.
Proof.
  induction 1. simpl. auto.
  exploit L2single; eauto. intros LEN.
  destruct t1. simpl in *. subst. destruct t2. auto.
  destruct IHstar as [s2x [A B]]. exists s2x; split; auto.
  eapply plus_left. eauto. apply plus_star; eauto. auto.
  destruct t1. simpl in *. subst t. exists s2; split; auto. apply plus_one; auto.
  simpl in LEN. omegaContradiction.
Qed.

Lemma ffs_simulation:
  forall s1 t s1', Step (atomic L1) s1 t s1' ->
  forall i f s2, ffs_match i f s1 s2 ->
  exists i', exists s2' f',
     (Plus L2 s2 t s2' \/ (Star L2 s2 t s2') /\ order i' i)
  /\ ffs_match i' f' s1' s2'.
Proof.
  (*
  induction 1; intros.
- (* silent step *)
  inv H0.
  exploit (fsim_simulation sim); eauto.
  intros [i' [s2' [f' [A B]]]].
  exists i'; exists s2', f'; split. auto. constructor; auto.
- (* start step *)
  inv H0.
  exploit (fsim_simulation sim); eauto.
  intros [i' [s2' [f' [A B]]]].
  destruct t as [ | ev' t].
+ (* single event *)
  exists i'; exists s2', f'; split. auto. constructor; auto.
+ (* multiple events *)
  assert (C: Star L2 s2 (ev :: ev' :: t) s2'). intuition. apply plus_star; auto.
  exploit star_non_E0_split'. eauto. simpl. intros [s2x [P Q]].
  exists i'; exists s2x, f'; split. auto. econstructor; eauto.
- (* continue step *)
  inv H0.
  exploit star_non_E0_split'. eauto. simpl. intros [s2x [P Q]].
  destruct t.
  exists i; exists s2', f; split. left. eapply plus_star_trans; eauto. constructor; auto.
  exists i; exists s2x, f; split. auto. econstructor; eauto.
Qed.*)
Admitted. (*This factorization is weird. Need to revise it.*)

End FACTOR_FORWARD_SIMULATION.

Theorem factor_forward_simulation:
  forall L1 L2,
  forward_simulation L1 L2 -> single_events L2 ->
  forward_simulation (atomic L1) L2.
Proof.
(*
  intros L1 L2 FS L2single.
  destruct FS as [index order match_states sim].
  apply Forward_simulation with order (ffs_match L1 L2 match_states); constructor.
- (* wf *)
  eapply fsim_order_wf; eauto.
- (*Mem.inject *)
  intros.
  inversion H; subst.
  + eapply fsim_match_meminj in H0; eauto.
  + admit. (*THIS IS FALSE!!!*)
    (* Now, it is only used in COMPCERT backwards simulation proof, 
       which we might not need... *)
- (* initial states *)
  intros. destruct s1 as [t1 s1]. simpl in H. destruct H. subst.
  exploit (fsim_match_initial_states sim); eauto. intros [i [f [s2 [m2 [A [B MINJ]]]]]].
  exists i; exists f, s2, m2; split; auto. split; trivial. constructor; auto.
- (* final states *)
  intros. destruct s1 as [t1 s1]. simpl in H0; destruct H0; subst. inv H.
  eapply (fsim_match_final_states sim); eauto.
- (* simulation *)
  (*eapply ffs_simulation; eauto.*)
  intros.
  destruct (ffs_simulation sim L2single H H0) as [i' [s2' [f' [ A]]]].
  exists i', s2', f', t'; trivial.
- (* symbols preserved *)
  simpl. exact (fsim_public_preserved sim).*)
Admitted.

(** Likewise, a backward simulation from a single-event semantics [L1] to a semantics [L2]
  can be "factored" as a backward simulation from [L1] to [atomic L2]. *)

Section FACTOR_BACKWARD_SIMULATION.

Variable L1: semantics.
Variable L2: semantics.
Context index order match_states (sim: bsim_properties L1 L2 index order match_states).
Hypothesis L1single: single_events L1.
Hypothesis L2wb: well_behaved_traces L2.
(*Association (trace * (state L2 * mem)) is more awkward for proving Lemma factor_backward_simulation below.
  That's why we associate ((trace * state L2) * mem) below
Inductive fbs_match: index -> meminj -> (state L1 * mem) -> (trace * (state L2 * mem)) -> Prop :=
  | fbs_match_intro: forall i s1 t s2 s1' f,
      Star L1 s1 t s1' -> match_states i f s1' s2 ->
      t = E0 \/ output_trace t ->
      fbs_match i f s1 (t, s2).

Lemma fbs_simulation:
  forall (s2 :state (atomic L2) * mem) (t : trace) (s2' : state (atomic L2) * mem), 
  Step (atomic L2) s2 t s2' ->
  match s2, s2' with ((tr2,ss2),m2), ((tr2',ss2'),m2') =>
    forall i f s1, fbs_match i f s1 (*s2*)(tr2,(ss2,m2)) -> safe L1 s1 ->
    exists i' f', exists s1',
       (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
       /\ fbs_match i' f' s1' (*s2'*)(tr2',(ss2',m2'))
  end.
Proof.
  induction 1; intros.
- (* silent step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [f' [s1'' [A B]]]].
  exists i', f'; exists s1''; split.
  destruct A as [P | [P Q]]. left. eapply star_plus_trans; eauto. right; split; auto. eapply star_trans; eauto.
  econstructor. apply star_refl. auto. auto.
- (* start step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [f' [s1'' [A B]]]].
  assert (C: Star L1 s1 (ev :: t) s1'').
    eapply star_trans. eauto. destruct A as [P | [P Q]]. apply plus_star; eauto. eauto. auto.
  exploit star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i', f'; exists s1x; split.
  left; auto.
  econstructor; eauto.
  exploit L2wb; eauto.
- (* continue step *)
  inv H0. unfold E0 in (*H8*)H9; destruct (*H8*)H9; try congruence.
  exploit star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i, f; exists s1x; split. left; auto. econstructor; eauto. simpl in H0; tauto.
Qed.

Lemma fbs_progress:
  forall i f (s1 : state L1 * mem) (s2 : trace * (state L2 * mem)),
  fbs_match i f s1 s2 -> safe L1 s1 ->
  match s2 with (tr2,(ss2,m2)) =>
    (exists r, final_state (atomic L2) (*s2*) ((tr2,ss2),m2) r) \/
    (exists t, exists s2', Step (atomic L2) (*s2*) ((tr2,ss2),m2) t s2')
  end.
Proof.
  intros. inv H. destruct s3 as [s3 m3]. destruct t.
- (* 1. no buffered events *)
  exploit (bsim_progress sim); eauto. eapply star_safe; eauto.
  intros [[r A] | [t [s2' A]]].
+ (* final state *)
  left; exists r; simpl; auto.
+ (* L2 can step *)
  destruct s2' as [s2' m2']. destruct t. 
  right; exists E0; exists ((nil, s2'), m2'). constructor. auto.
  right; exists (e :: nil); exists ((t, s2'), m2'). constructor. auto.
- (* 2. some buffered events *)
  unfold E0 in H3; destruct H3. congruence.
  right; exists (e :: nil); exists ((t, s3), m3). constructor. auto.
Qed.
*)
Inductive fbs_match: index -> meminj -> (state L1 * mem) -> ((trace * state L2) * mem) -> Prop :=
  | fbs_match_intro: forall i s1 t s2 m2 s1' f,
      Star L1 s1 t s1' -> match_states i f s1' (s2,m2) ->
      t = E0 \/ output_trace t ->
      fbs_match i f s1 ((t, s2),m2).

Lemma fbs_simulation:
  forall (s2 :state (atomic L2) * mem) (t : trace) (s2' : state (atomic L2) * mem), 
  Step (atomic L2) s2 t s2' ->
    forall i f s1, fbs_match i f s1 s2 -> safe L1 s1 ->
    exists i' f', exists s1', exists t',
       (Plus L1 s1 t' s1' \/ (Star L1 s1 t' s1' /\ order i' i))
       /\ fbs_match i' f' s1' s2'
/\ inject_incr f f' /\ inject_trace f' t t'.
Proof.
  
  (*

  induction 1; intros.
- (* silent step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [f' [s1'' [ t''[A [B [C D]]]]]]].
  exists i', f'; exists s1'', t''; repeat split.
  inversion D; auto.

  destruct A as [P | [P Q]]. left. eapply star_plus_trans; eauto.
  right; split; auto. eapply star_trans; eauto.
  econstructor. apply star_refl. auto. auto.
  auto. auto.
- (* start step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [f' [s1'' [ t'' [A [B [C D]]]]]]].
  inv D.
  assert (E: Star L1 s1 (e':: t') s1'').
  eapply star_trans. eauto. destruct A as [P | [P Q]]. apply plus_star; eauto. eauto.
  auto.
  exploit star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i', f'; exists s1x, (e'::E0); split.
  left; auto.
  split. 
  econstructor; eauto.
  exploit L2wb; eauto.
- (* continue step *)
  inv H0. unfold E0 in (*H8*)H10; destruct (*H8*)H10; try congruence.
  exploit star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i, f; exists s1x; split. left; auto. econstructor; eauto. simpl in H0; tauto.

Qed.*)
Admitted. (*This won't work... *)
Lemma fbs_progress:
  forall i f (s1 : state L1 * mem) (s2 : (trace * state L2) * mem),
  fbs_match i f s1 s2 -> safe L1 s1 ->
    (exists r, final_state (atomic L2) s2 r) \/
    (exists t, exists s2', Step (atomic L2) s2 t s2').
Proof.
  intros. inv H. rename m2 into m3. destruct t.
- (* 1. no buffered events *)
  exploit (bsim_progress sim); eauto. eapply star_safe; eauto.
  intros [[r A] | [t [s2' A]]].
+ (* final state *)
  left; exists r; simpl; auto.
+ (* L2 can step *)
  destruct s2' as [s2' m2']. destruct t. 
  right; exists E0; exists ((nil, s2'), m2'). constructor. auto.
  right; exists (e :: nil); exists ((t, s2'), m2'). constructor. auto.
- (* 2. some buffered events *)
  unfold E0 in H3; destruct H3. congruence.
  right; exists (e :: nil); exists ((t, s3), m3). constructor. auto.
Qed.
End FACTOR_BACKWARD_SIMULATION.

Theorem factor_backward_simulation:
  forall L1 L2,
  backward_simulation L1 L2 -> single_events L1 -> well_behaved_traces L2 ->
  backward_simulation L1 (atomic L2).
Proof.
  intros L1 L2 BS L1single L2wb.
  destruct BS as [index order match_states sim].
  apply Backward_simulation with order (fbs_match L1 L2 match_states); constructor.
- (* wf *)
  eapply bsim_order_wf; eauto.
- (* initial states exist *)
  intros. exploit (bsim_initial_states_exist sim); eauto. intros [[s2 m2] A].
  exists ((E0, s2),m2). simpl; auto.
- (* initial states match *)
  intros. destruct s2 as [[t s2] m2]; simpl in H0; destruct H0; subst.
  exploit (bsim_match_initial_states sim); eauto. intros [i [s1' [f [A [B MINJ]]]]].
  exists i; exists s1'; exists f; split. auto. split. econstructor. apply star_refl. auto. auto. trivial.
- (* final states match *)
  intros. destruct s2 as [[t s2] m2]; simpl in H1; destruct H1; subst.
  inv H. exploit (bsim_match_final_states sim); eauto. eapply star_safe; eauto.
  intros [s1'' [A B]]. exists s1''; split; auto. eapply star_trans; eauto.
- (* progress *)
  (*eapply fbs_progress; eauto.*)
  intros. destruct (fbs_progress sim H H0). 
  + left; trivial.
  + right. destruct H1 as [tr [s2' A]]. exists tr, s2'. trivial.
- (* simulation *)
  (*eapply fbs_simulation; eauto.*)
  intros. destruct (fbs_simulation sim L1single L2wb H H0 H1) as [i' [f' [s1' A]]].
  exists i', f', s1'; trivial.
- (* symbols *)
  simpl. exact (bsim_public_preserved sim).
Qed.

(** Receptiveness of [atomic L]. *)

Record strongly_receptive (L: semantics) : Prop :=
  Strongly_receptive {
    ssr_receptive: forall s ev1 t1 s1 ev2,
      Step L s (ev1 :: t1) s1 ->
      match_traces (symbolenv L) (ev1 :: nil) (ev2 :: nil) ->
      exists s2, exists t2, Step L s (ev2 :: t2) s2;
    ssr_well_behaved:
      well_behaved_traces L
  }.

Theorem atomic_receptive:
  forall L, strongly_receptive L -> receptive (atomic L).
Proof.
  intros. constructor; intros.
- (* receptive *)
  inv H0.
+ (* silent step *)
  inv H1. exists ((E0, s'),m'). constructor; auto.
  (* start step *)
+ assert (exists ev2, t2 = ev2 :: nil). inv H1; econstructor; eauto.
  destruct H0 as [ev2 EQ]; subst t2.
  exploit ssr_receptive; eauto. intros [s2 [t2 P]].
  exploit ssr_well_behaved. eauto. eexact P. simpl; intros Q.
  destruct s2 as [s2 m2].
  exists ((t2, s2),m2). constructor; auto.
  (* continue step *)
+ simpl in H2; destruct H2.
  assert (t2 = ev :: nil). inv H1; simpl in H0; tauto.
  subst t2. exists ((t, s0), m). constructor; auto. simpl; auto.
(* single-event *)
- red. intros. inv H0; simpl; omega.
Qed.

(** * Connections with big-step semantics *)

(** The general form of a big-step semantics *)

Record bigstep_semantics : Type :=
  Bigstep_semantics {
    bigstep_terminates: trace -> int -> Prop;
    bigstep_diverges: traceinf -> Prop
  }.

(** Soundness with respect to a small-step semantics *)

Record bigstep_sound (B: bigstep_semantics) (L: semantics) : Prop :=
  Bigstep_sound {
    bigstep_terminates_sound:
      forall t r,
      bigstep_terminates B t r ->
      exists s1, exists s2, initial_state L s1 /\ Star L s1 t s2 /\ final_state L s2 r;
    bigstep_diverges_sound:
      forall T,
      bigstep_diverges B T ->
      exists s1, initial_state L s1 /\ forever (step L) (globalenv L) s1 T
}.


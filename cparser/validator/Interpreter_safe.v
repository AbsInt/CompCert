(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Streams.
Require Import Equality.
Require Import List.
Require Import Syntax.
Require Import Alphabet.
Require Grammar.
Require Automaton.
Require Validator_safe.
Require Interpreter.

Module Make(Import A:Automaton.T) (Import Inter:Interpreter.T A).
Module Import Valid := Validator_safe.Make A.

(** * A correct automaton does not crash **)

Section Safety_proof.

Hypothesis safe: safe.

Proposition shift_head_symbs: shift_head_symbs.
Proof. pose proof safe; unfold Valid.safe in H; intuition. Qed.
Proposition goto_head_symbs: goto_head_symbs.
Proof. pose proof safe; unfold Valid.safe in H; intuition. Qed.
Proposition shift_past_state: shift_past_state.
Proof. pose proof safe; unfold Valid.safe in H; intuition. Qed.
Proposition goto_past_state: goto_past_state.
Proof. pose proof safe; unfold Valid.safe in H; intuition. Qed.
Proposition reduce_ok: reduce_ok.
Proof. pose proof safe; unfold Valid.safe in H; intuition. Qed.

(** We prove that a correct automaton won't crash : the interpreter will
    not return [Err] **)

Variable init : initstate.

(** The stack of states of an automaton stack **)
Definition state_stack_of_stack (stack:stack) :=
  (List.map
    (fun cell:sigT noninitstate_type => singleton_state_pred (projT1 cell))
    stack ++ [singleton_state_pred init])%list.

(** The stack of symbols of an automaton stack **)
Definition symb_stack_of_stack (stack:stack) :=
  List.map
    (fun cell:sigT noninitstate_type => last_symb_of_non_init_state (projT1 cell))
    stack.

(** The stack invariant : it basically states that the assumptions on the
    states are true. **)
Inductive stack_invariant: stack -> Prop :=
  | stack_invariant_constr:
    forall stack,
      prefix      (head_symbs_of_state (state_of_stack init stack))
                  (symb_stack_of_stack stack) ->
      prefix_pred (head_states_of_state (state_of_stack init stack))
                  (state_stack_of_stack stack) ->
      stack_invariant_next stack ->
      stack_invariant stack
with stack_invariant_next: stack -> Prop :=
  | stack_invariant_next_nil:
      stack_invariant_next []
  | stack_invariant_next_cons:
    forall state_cur st stack_rec,
      stack_invariant stack_rec ->
      stack_invariant_next (existT _ state_cur st::stack_rec).

(** [pop] conserves the stack invariant and does not crash
     under the assumption that we can pop at this place.
     Moreover, after a pop, the top state of the stack is allowed. **)
Lemma pop_stack_invariant_conserved
  (symbols_to_pop:list symbol) (stack_cur:stack) A action:
  stack_invariant stack_cur ->
  prefix symbols_to_pop (head_symbs_of_state (state_of_stack init stack_cur)) ->
  match pop symbols_to_pop stack_cur (A:=A) action with
    | OK (stack_new, _) =>
      stack_invariant stack_new /\
      state_valid_after_pop
        (state_of_stack init stack_new) symbols_to_pop
        (head_states_of_state (state_of_stack init stack_cur))
    | Err => False
  end.
Proof with eauto.
  intros.
  pose proof H.
  destruct H.
  revert H H0 H1 H2 H3.
  generalize (head_symbs_of_state (state_of_stack init stack0)).
  generalize (head_states_of_state (state_of_stack init stack0)).
  revert stack0 A action.
  induction symbols_to_pop; intros.
  - split...
    destruct l; constructor.
    inversion H2; subst.
    specialize (H7 (state_of_stack init stack0)).
    destruct (f2 (state_of_stack init stack0)) as [] eqn:? ...
    destruct stack0 as [|[]]; simpl in *.
    + inversion H6; subst.
      unfold singleton_state_pred in Heqb0.
      now rewrite compare_refl in Heqb0; discriminate.
    + inversion H6; subst.
      unfold singleton_state_pred in Heqb0.
      now rewrite compare_refl in Heqb0; discriminate.
  - destruct stack0 as [|[]]; unfold pop.
    + inversion H0; subst.
      now inversion H.
    + fold pop.
      destruct (compare_eqdec (last_symb_of_non_init_state x) a).
      * inversion H0; subst. clear H0.
        inversion H; subst. clear H.
        dependent destruction H3; simpl.
        assert (prefix_pred (List.tl l) (state_stack_of_stack stack0)).
        unfold tl; destruct l; [constructor | inversion H2]...
        pose proof H. destruct H3.
        specialize (IHsymbols_to_pop stack0 A (action0 n) _ _ H4 H7 H H0 H6).
        revert IHsymbols_to_pop.
        fold (noninitstate_type x); generalize (pop symbols_to_pop stack0 (action0 n)).
        destruct r as [|[]]; intuition...
        destruct l; constructor...
      * apply n0.
        inversion H0; subst.
        inversion H; subst...
Qed.

(** [prefix] is associative **)
Lemma prefix_ass:
  forall (l1 l2 l3:list symbol), prefix l1 l2 -> prefix l2 l3 -> prefix l1 l3.
Proof.
induction l1; intros.
constructor.
inversion H; subst.
inversion H0; subst.
constructor; eauto.
Qed.

(** [prefix_pred] is associative **)
Lemma prefix_pred_ass:
  forall (l1 l2 l3:list (state->bool)),
  prefix_pred l1 l2 -> prefix_pred l2 l3 -> prefix_pred l1 l3.
Proof.
induction l1; intros.
constructor.
inversion H; subst.
inversion H0; subst.
constructor; eauto.
intro.
specialize (H3 x).
specialize (H4 x).
destruct (f0 x); simpl in *; intuition.
rewrite H4 in H3; intuition.
Qed.

(** If we have the right to reduce at this state, then the stack invariant
   is conserved by [reduce_step] and [reduce_step] does not crash. **)
Lemma reduce_step_stack_invariant_conserved stack prod buff:
  stack_invariant stack ->
  valid_for_reduce (state_of_stack init stack) prod ->
  match reduce_step init stack prod buff with
    | OK (Fail_sr | Accept_sr _ _) => True
    | OK (Progress_sr stack_new _) => stack_invariant stack_new
    | Err => False
  end.
Proof with eauto.
unfold valid_for_reduce.
intuition.
unfold reduce_step.
pose proof (pop_stack_invariant_conserved (prod_rhs_rev prod) stack _ (prod_action' prod)).
destruct (pop (prod_rhs_rev prod) stack (prod_action' prod)) as [|[]].
apply H0...
destruct H0...
pose proof (goto_head_symbs (state_of_stack init s) (prod_lhs prod)).
pose proof (goto_past_state (state_of_stack init s) (prod_lhs prod)).
unfold bind2.
destruct H0.
specialize (H2 _ H3)...
destruct (goto_table (state_of_stack init stack0) (prod_lhs prod)) as [[]|].
constructor.
simpl.
constructor.
eapply prefix_ass...
unfold state_stack_of_stack; simpl; constructor.
intro; destruct (singleton_state_pred x x0); reflexivity.
eapply prefix_pred_ass...
constructor...
constructor...
destruct stack0 as [|[]]...
destruct (compare_eqdec (prod_lhs prod) (start_nt init))...
apply n, H2, eq_refl.
apply H2, eq_refl.
Qed.

(** If the automaton is safe, then the stack invariant is conserved by
    [step] and [step] does not crash. **)
Lemma step_stack_invariant_conserved (stack:stack) buffer:
  stack_invariant stack ->
  match step init stack buffer with
    | OK (Fail_sr | Accept_sr _ _) => True
    | OK (Progress_sr stack_new _) => stack_invariant stack_new
    | Err => False
  end.
Proof with eauto.
intro.
unfold step.
pose proof (shift_head_symbs (state_of_stack init stack)).
pose proof (shift_past_state (state_of_stack init stack)).
pose proof (reduce_ok (state_of_stack init stack)).
destruct (action_table (state_of_stack init stack)).
apply reduce_step_stack_invariant_conserved...
destruct buffer as [[]]; simpl.
specialize (H0 x); specialize (H1 x); specialize (H2 x).
destruct (l x)...
destruct H.
constructor.
unfold state_of_stack.
constructor.
eapply prefix_ass...
unfold state_stack_of_stack; simpl; constructor.
intro; destruct (singleton_state_pred s0 x0)...
eapply prefix_pred_ass...
constructor...
constructor...
apply reduce_step_stack_invariant_conserved...
Qed.

(** If the automaton is safe, then it does not crash **)
Theorem parse_no_err buffer n_steps:
  parse init buffer n_steps <> Err.
Proof with eauto.
unfold parse.
assert (stack_invariant []).
constructor.
constructor.
unfold state_stack_of_stack; simpl; constructor.
intro; destruct (singleton_state_pred init x)...
constructor.
constructor.
revert H.
generalize buffer ([]:stack).
induction n_steps; simpl.
now discriminate.
intros.
pose proof (step_stack_invariant_conserved s buffer0 H).
destruct (step init s buffer0) as [|[]]; simpl...
discriminate.
discriminate.
Qed.

(** A version of [parse] that uses safeness in order to return a
   [parse_result], and not a [result parse_result] : we have proven that
   parsing does not return [Err]. **)
Definition parse_with_safe (buffer:Stream token) (n_steps:nat):
  parse_result init.
Proof with eauto.
pose proof (parse_no_err buffer n_steps).
destruct (parse init buffer n_steps)...
congruence.
Defined.

End Safety_proof.

End Make.

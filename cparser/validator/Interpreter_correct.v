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
Require Import List.
Require Import Syntax.
Require Import Equality.
Require Import Alphabet.
Require Grammar.
Require Automaton.
Require Interpreter.

Module Make(Import A:Automaton.T) (Import Inter:Interpreter.T A).

(** * Correctness of the interpreter **)

(** We prove that, in any case, if the interpreter accepts returning a
    semantic value, then this is a semantic value of the input **)

Section Init.

Variable init:initstate.

(** [word_has_stack_semantics] relates a word with a state, stating that the
    word is a concatenation of words that have the semantic values stored in
    the stack. **)
Inductive word_has_stack_semantics:
  forall (word:list token) (stack:stack), Prop :=
  | Nil_stack_whss: word_has_stack_semantics [] []
  | Cons_stack_whss:
    forall (wordq:list token) (stackq:stack),
      word_has_stack_semantics wordq stackq ->

    forall (wordt:list token) (s:noninitstate)
           (semantic_valuet:_),
      inhabited (parse_tree (last_symb_of_non_init_state s) wordt semantic_valuet) ->

    word_has_stack_semantics
       (wordq++wordt) (existT noninitstate_type s semantic_valuet::stackq).

Lemma pop_invariant_converter:
  forall A symbols_to_pop symbols_popped,
  arrows_left (map symbol_semantic_type (rev_append symbols_to_pop symbols_popped)) A =
  arrows_left (map symbol_semantic_type symbols_popped)
    (arrows_right A (map symbol_semantic_type symbols_to_pop)).
Proof.
intros.
unfold arrows_right, arrows_left.
rewrite rev_append_rev, map_app, map_rev, fold_left_app.
apply f_equal.
rewrite <- fold_left_rev_right, rev_involutive.
reflexivity.
Qed.

(** [pop] preserves the invariant **)
Lemma pop_invariant:
  forall (symbols_to_pop symbols_popped:list symbol)
         (stack_cur:stack)
         (A:Type)
         (action:arrows_left (map symbol_semantic_type (rev_append symbols_to_pop symbols_popped)) A),
  forall word_stack word_popped,
  forall sem_popped,
    word_has_stack_semantics word_stack stack_cur ->
    inhabited (parse_tree_list symbols_popped word_popped sem_popped) ->
    let action' := eq_rect _ (fun x=>x) action _ (pop_invariant_converter _ _ _) in
    match pop symbols_to_pop stack_cur (uncurry action' sem_popped) with
      | OK (stack_new, sem) =>
          exists word1res word2res sem_full,
            (word_stack = word1res ++ word2res)%list /\
            word_has_stack_semantics word1res stack_new /\
            sem = uncurry action sem_full /\
            inhabited (
              parse_tree_list (rev_append symbols_to_pop symbols_popped) (word2res++word_popped) sem_full)
      | Err => True
    end.
Proof.
induction symbols_to_pop; intros; unfold pop; fold pop.
exists word_stack, ([]:list token), sem_popped; intuition.
f_equal.
apply JMeq_eq, JMeq_eqrect with (P:=(fun x => x)).
destruct stack_cur as [|[]]; eauto.
destruct (compare_eqdec (last_symb_of_non_init_state x) a); eauto.
destruct e; simpl.
dependent destruction H.
destruct H0, H1. apply (Cons_ptl X), inhabits in X0.
specialize (IHsymbols_to_pop _ _ _ action0 _ _ _ H X0).
match goal with
  IHsymbols_to_pop:match ?p1 with Err => _ | OK _ => _ end |- match ?p2 with Err => _ | OK _ => _ end =>
    replace p2 with p1; [destruct p1 as [|[]]|]; intuition
end.
destruct IHsymbols_to_pop as [word1res [word2res [sem_full []]]]; intuition; subst.
exists word1res.
eexists.
exists sem_full.
intuition.
rewrite <- app_assoc; assumption.
simpl; f_equal; f_equal.
apply JMeq_eq.
etransitivity.
apply JMeq_eqrect with (P:=(fun x => x)).
symmetry.
apply JMeq_eqrect with (P:=(fun x => x)).
Qed.

(** [reduce_step] preserves the invariant **)
Lemma reduce_step_invariant (stack:stack) (prod:production):
  forall word buffer, word_has_stack_semantics word stack ->
  match reduce_step init stack prod buffer with
    | OK (Accept_sr sem buffer_new) =>
      buffer = buffer_new /\
      inhabited (parse_tree (NT (start_nt init)) word sem)
    | OK (Progress_sr stack_new buffer_new) =>
      buffer = buffer_new /\
      word_has_stack_semantics word stack_new
    | Err | OK Fail_sr => True
  end.
Proof with eauto.
intros.
unfold reduce_step.
pose proof (pop_invariant (prod_rhs_rev prod) [] stack (symbol_semantic_type (NT (prod_lhs prod)))).
revert H0.
generalize (pop_invariant_converter (symbol_semantic_type (NT (prod_lhs prod))) (prod_rhs_rev prod) []).
rewrite <- rev_alt.
intros.
specialize (H0 (prod_action prod) _ [] () H (inhabits Nil_ptl)).
match goal with H0:let action' := ?a in _ |- _ => replace a with (prod_action' prod) in H0 end.
simpl in H0.
destruct (pop (prod_rhs_rev prod) stack (prod_action' prod)) as [|[]]; intuition.
destruct H0 as [word1res [word2res [sem_full]]]; intuition.
destruct H4; apply Non_terminal_pt, inhabits in X.
match goal with X:inhabited (parse_tree _ _ ?u) |- _ => replace u with s0 in X end.
clear sem_full H2.
simpl; destruct (goto_table (state_of_stack init s) (prod_lhs prod)) as [[]|]; intuition; subst.
rewrite app_nil_r in X; revert s0 X; rewrite e0; intro; simpl.
constructor...
destruct s; intuition.
destruct (compare_eqdec (prod_lhs prod) (start_nt init)); intuition.
rewrite app_nil_r in X.
rewrite <- e0.
inversion H0.
destruct X; constructor...
apply JMeq_eq.
etransitivity.
apply JMeq_eqrect with (P:=(fun x => x)).
symmetry.
apply JMeq_eqrect with (P:=(fun x => x)).
Qed.

(** [step] preserves the invariant **)
Lemma step_invariant (stack:stack) (buffer:Stream token):
  forall buffer_tmp,
  (exists word_old,
    buffer = word_old ++ buffer_tmp /\
    word_has_stack_semantics word_old stack) ->
  match step init stack buffer_tmp with
    | OK (Accept_sr sem buffer_new) =>
      exists word_new,
        buffer = word_new ++ buffer_new /\
        inhabited (parse_tree (NT (start_nt init)) word_new sem)
    | OK (Progress_sr stack_new buffer_new) =>
      exists word_new,
        buffer = word_new ++ buffer_new /\
        word_has_stack_semantics word_new stack_new
    | Err | OK Fail_sr => True
  end.
Proof with eauto.
intros.
destruct H, H.
unfold step.
destruct (action_table (state_of_stack init stack)).
pose proof (reduce_step_invariant stack p x buffer_tmp).
destruct (reduce_step init stack p buffer_tmp) as [|[]]; intuition; subst...
destruct buffer_tmp.
unfold Streams.hd.
destruct t.
destruct (l x0); intuition.
exists (x ++ [existT (fun t => symbol_semantic_type (T t)) x0 s])%list.
split.
now rewrite <- app_str_app_assoc; intuition.
apply Cons_stack_whss; intuition.
destruct e; simpl.
now exact (inhabits (Terminal_pt _ _)).
match goal with |- (match reduce_step init stack p ?buff with Err => _ | OK _ => _ end) =>
  pose proof (reduce_step_invariant stack p x buff);
  destruct (reduce_step init stack p buff) as [|[]]; intuition; subst
end...
Qed.

(** The interpreter is correct : if it returns a semantic value, then the input
    word has this semantic value.
**)
Theorem parse_correct buffer n_steps:
  match parse init buffer n_steps with
    | OK (Parsed_pr sem buffer_new) =>
      exists word_new,
        buffer = word_new ++ buffer_new /\
        inhabited (parse_tree (NT (start_nt init)) word_new sem)
    | _ => True
  end.
Proof.
unfold parse.
assert (exists w, buffer = w ++ buffer /\ word_has_stack_semantics w []).
exists ([]:list token); intuition.
now apply Nil_stack_whss.
revert H.
generalize ([]:stack), buffer at 2 3.
induction n_steps; simpl; intuition.
pose proof (step_invariant _ _ _ H).
destruct (step init s buffer0); simpl; intuition.
destruct s0; intuition.
apply IHn_steps; intuition.
Qed.

End Init.

End Make.

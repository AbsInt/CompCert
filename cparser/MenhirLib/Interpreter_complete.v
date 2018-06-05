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
Require Import ProofIrrelevance.
Require Import Equality.
Require Import List.
Require Import Syntax.
Require Import Alphabet.
Require Import Arith.
Require Grammar.
Require Automaton.
Require Interpreter.
Require Validator_complete.

Module Make(Import A:Automaton.T) (Import Inter:Interpreter.T A).
Module Import Valid := Validator_complete.Make A.

(** * Completeness Proof **)

Section Completeness_Proof.

Hypothesis complete: complete.

Proposition nullable_stable: nullable_stable.
Proof. pose proof complete; unfold Valid.complete in H; intuition. Qed.
Proposition first_stable: first_stable.
Proof. pose proof complete; unfold Valid.complete in H; intuition. Qed.
Proposition start_future: start_future.
Proof. pose proof complete; unfold Valid.complete in H; intuition. Qed.
Proposition terminal_shift: terminal_shift.
Proof. pose proof complete; unfold Valid.complete in H; intuition. Qed.
Proposition end_reduce: end_reduce.
Proof. pose proof complete; unfold Valid.complete in H; intuition. Qed.
Proposition start_goto: start_goto.
Proof. pose proof complete; unfold Valid.complete in H; intuition. Qed.
Proposition non_terminal_goto: non_terminal_goto.
Proof. pose proof complete; unfold Valid.complete in H; intuition. Qed.
Proposition non_terminal_closed: non_terminal_closed.
Proof. pose proof complete; unfold Valid.complete in H; intuition. Qed.

(** If the nullable predicate has been validated, then it is correct. **)
Lemma nullable_correct:
  forall head sem word, word = [] ->
    parse_tree head word sem -> nullable_symb head = true
with nullable_correct_list:
  forall heads sems word, word = [] ->
    parse_tree_list heads word sems -> nullable_word heads = true.
Proof with eauto.
intros.
destruct X.
congruence.
apply nullable_stable...
intros.
destruct X; simpl...
apply andb_true_intro.
apply app_eq_nil in H; destruct H; split...
Qed.

(** If the first predicate has been validated, then it is correct. **)
Lemma first_correct:
  forall head sem word t q, word = t::q ->
  parse_tree head word sem ->
  TerminalSet.In (projT1 t) (first_symb_set head)
with first_correct_list:
  forall heads sems word t q, word = t::q ->
  parse_tree_list heads word sems ->
  TerminalSet.In (projT1 t) (first_word_set heads).
Proof with eauto.
intros.
destruct X.
inversion H; subst.
apply TerminalSet.singleton_2, compare_refl...
apply first_stable...
intros.
destruct X.
congruence.
simpl.
case_eq wordt; intros.
erewrite nullable_correct...
apply TerminalSet.union_3.
subst...
rewrite H0 in *; inversion H; destruct H2.
destruct (nullable_symb head_symbolt)...
apply TerminalSet.union_2...
Qed.

Variable init: initstate.
Variable full_word: list token.
Variable buffer_end: Stream token.
Variable full_sem: symbol_semantic_type (NT (start_nt init)).

Inductive pt_zipper:
  forall (hole_symb:symbol) (hole_word:list token)
         (hole_sem:symbol_semantic_type hole_symb), Type :=
| Top_ptz:
  pt_zipper (NT (start_nt init)) (full_word) (full_sem)
| Cons_ptl_ptz:
  forall {head_symbolt:symbol}
    {wordt:list token}
    {semantic_valuet:symbol_semantic_type head_symbolt},

  forall {head_symbolsq:list symbol}
    {wordq:list token}
    {semantic_valuesq:tuple (map symbol_semantic_type head_symbolsq)},
    parse_tree_list head_symbolsq wordq semantic_valuesq ->

    ptl_zipper (head_symbolt::head_symbolsq) (wordt++wordq)
      (semantic_valuet,semantic_valuesq) ->

    pt_zipper head_symbolt wordt semantic_valuet
with ptl_zipper:
  forall (hole_symbs:list symbol) (hole_word:list token)
         (hole_sems:tuple (map symbol_semantic_type hole_symbs)), Type :=
| Non_terminal_pt_ptlz:
  forall {p:production} {word:list token}
    {semantic_values:tuple (map symbol_semantic_type (rev (prod_rhs_rev p)))},
    pt_zipper (NT (prod_lhs p)) word (uncurry (prod_action p) semantic_values) ->
    ptl_zipper (rev (prod_rhs_rev p)) word semantic_values

| Cons_ptl_ptlz:
  forall {head_symbolt:symbol}
    {wordt:list token}
    {semantic_valuet:symbol_semantic_type head_symbolt},
    parse_tree head_symbolt wordt semantic_valuet ->

  forall {head_symbolsq:list symbol}
    {wordq:list token}
    {semantic_valuesq:tuple (map symbol_semantic_type head_symbolsq)},

  ptl_zipper (head_symbolt::head_symbolsq) (wordt++wordq)
    (semantic_valuet,semantic_valuesq) ->

  ptl_zipper head_symbolsq wordq semantic_valuesq.

Fixpoint ptlz_cost {hole_symbs hole_word hole_sems}
  (ptlz:ptl_zipper hole_symbs hole_word hole_sems) :=
  match ptlz with
    | Non_terminal_pt_ptlz ptz =>
      ptz_cost ptz
    | Cons_ptl_ptlz pt ptlz' =>
      ptlz_cost ptlz'
  end
with ptz_cost {hole_symb hole_word hole_sem}
  (ptz:pt_zipper hole_symb hole_word hole_sem) :=
  match ptz with
    | Top_ptz => 0
    | Cons_ptl_ptz ptl ptlz' =>
      1 + ptl_size ptl + ptlz_cost ptlz'
  end.

Inductive pt_dot: Type :=
| Reduce_ptd: ptl_zipper [] [] () -> pt_dot
| Shift_ptd:
  forall (term:terminal) (sem: symbol_semantic_type (T term))
    {symbolsq wordq semsq},
    parse_tree_list symbolsq wordq semsq ->
    ptl_zipper (T term::symbolsq) (existT (fun t => symbol_semantic_type (T t)) term sem::wordq) (sem, semsq) ->
    pt_dot.

Definition ptd_cost (ptd:pt_dot) :=
  match ptd with
    | Reduce_ptd ptlz => ptlz_cost ptlz
    | Shift_ptd _ _ ptl ptlz => 1 + ptl_size ptl + ptlz_cost ptlz
  end.

Fixpoint ptlz_buffer {hole_symbs hole_word hole_sems}
  (ptlz:ptl_zipper hole_symbs hole_word hole_sems): Stream token :=
  match ptlz with
    | Non_terminal_pt_ptlz ptz =>
      ptz_buffer ptz
    | Cons_ptl_ptlz _ ptlz' =>
      ptlz_buffer ptlz'
  end
with ptz_buffer {hole_symb hole_word hole_sem}
  (ptz:pt_zipper hole_symb hole_word hole_sem): Stream token :=
  match ptz with
    | Top_ptz => buffer_end
    | @Cons_ptl_ptz _ _ _ _ wordq _ ptl ptlz' =>
      wordq++ptlz_buffer ptlz'
  end.

Definition ptd_buffer (ptd:pt_dot) :=
  match ptd with
    | Reduce_ptd ptlz => ptlz_buffer ptlz
    | @Shift_ptd term sem _ wordq _ _ ptlz =>
      Cons (existT (fun t => symbol_semantic_type (T t)) term sem)
           (wordq ++ ptlz_buffer ptlz)
  end.

Fixpoint ptlz_prod {hole_symbs hole_word hole_sems}
  (ptlz:ptl_zipper hole_symbs hole_word hole_sems): production :=
  match ptlz with
    | @Non_terminal_pt_ptlz prod _ _ _ => prod
    | Cons_ptl_ptlz _ ptlz' =>
      ptlz_prod ptlz'
  end.

Fixpoint ptlz_past {hole_symbs hole_word hole_sems}
  (ptlz:ptl_zipper hole_symbs hole_word hole_sems): list symbol :=
  match ptlz with
    | Non_terminal_pt_ptlz _ => []
    | @Cons_ptl_ptlz s _ _ _ _ _ _ ptlz' => s::ptlz_past ptlz'
  end.

Lemma ptlz_past_ptlz_prod:
  forall hole_symbs hole_word hole_sems
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems),
  rev_append hole_symbs (ptlz_past ptlz) = prod_rhs_rev (ptlz_prod ptlz).
Proof.
fix ptlz_past_ptlz_prod 4.
destruct ptlz; simpl.
rewrite <- rev_alt, rev_involutive; reflexivity.
apply (ptlz_past_ptlz_prod _ _ _ ptlz).
Qed.

Definition ptlz_state_compat {hole_symbs hole_word hole_sems}
  (ptlz:ptl_zipper hole_symbs hole_word hole_sems)
  (state:state): Prop :=
  state_has_future state (ptlz_prod ptlz) hole_symbs
    (projT1 (Streams.hd (ptlz_buffer ptlz))).

Fixpoint ptlz_stack_compat {hole_symbs hole_word hole_sems}
  (ptlz:ptl_zipper hole_symbs hole_word hole_sems)
  (stack:stack): Prop :=
  ptlz_state_compat ptlz (state_of_stack init stack) /\
  match ptlz with
    | Non_terminal_pt_ptlz ptz =>
      ptz_stack_compat ptz stack
    | @Cons_ptl_ptlz _ _ sem _ _ _ _ ptlz' =>
      match stack with
        | [] => False
        | existT _ _ sem'::stackq =>
          ptlz_stack_compat ptlz' stackq /\
          sem ~= sem'
      end
  end
with ptz_stack_compat {hole_symb hole_word hole_sem}
  (ptz:pt_zipper hole_symb hole_word hole_sem)
  (stack:stack): Prop :=
  match ptz with
    | Top_ptz => stack = []
    | Cons_ptl_ptz _ ptlz' =>
      ptlz_stack_compat ptlz' stack
  end.

Lemma ptlz_stack_compat_ptlz_state_compat:
  forall hole_symbs hole_word hole_sems
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems)
    (stack:stack),
    ptlz_stack_compat ptlz stack -> ptlz_state_compat ptlz (state_of_stack init stack).
Proof.
destruct ptlz; simpl; intuition.
Qed.

Definition ptd_stack_compat (ptd:pt_dot) (stack:stack): Prop :=
  match ptd with
    | Reduce_ptd ptlz => ptlz_stack_compat ptlz stack
    | Shift_ptd _ _ _ ptlz => ptlz_stack_compat ptlz stack
  end.

Fixpoint build_pt_dot {hole_symbs hole_word hole_sems}
    (ptl:parse_tree_list hole_symbs hole_word hole_sems)
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems)
    :pt_dot :=
  match ptl in parse_tree_list hole_symbs hole_word hole_sems
    return ptl_zipper hole_symbs hole_word hole_sems -> _
  with
    | Nil_ptl => fun ptlz =>
      Reduce_ptd ptlz
    | Cons_ptl pt ptl' =>
      match pt in parse_tree hole_symb hole_word hole_sem
        return ptl_zipper (hole_symb::_) (hole_word++_) (hole_sem,_) -> _
      with
        | Terminal_pt term sem => fun ptlz =>
          Shift_ptd term sem ptl' ptlz
        | Non_terminal_pt ptl'' => fun ptlz =>
          build_pt_dot ptl''
            (Non_terminal_pt_ptlz (Cons_ptl_ptz ptl' ptlz))
      end
  end ptlz.

Lemma build_pt_dot_cost:
  forall hole_symbs hole_word hole_sems
    (ptl:parse_tree_list hole_symbs hole_word hole_sems)
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems),
    ptd_cost (build_pt_dot ptl ptlz) = ptl_size ptl + ptlz_cost ptlz.
Proof.
fix build_pt_dot_cost 4.
destruct ptl; intros.
reflexivity.
destruct p.
reflexivity.
simpl; rewrite build_pt_dot_cost.
simpl; rewrite <- plus_n_Sm, Nat.add_assoc; reflexivity.
Qed.

Lemma build_pt_dot_buffer:
  forall hole_symbs hole_word hole_sems
    (ptl:parse_tree_list hole_symbs hole_word hole_sems)
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems),
    ptd_buffer (build_pt_dot ptl ptlz) = hole_word ++ ptlz_buffer ptlz.
Proof.
fix build_pt_dot_buffer 4.
destruct ptl; intros.
reflexivity.
destruct p.
reflexivity.
simpl; rewrite build_pt_dot_buffer.
apply app_str_app_assoc.
Qed.

Lemma ptd_stack_compat_build_pt_dot:
  forall hole_symbs hole_word hole_sems
    (ptl:parse_tree_list hole_symbs hole_word hole_sems)
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems)
    (stack:stack),
  ptlz_stack_compat ptlz stack ->
  ptd_stack_compat (build_pt_dot ptl ptlz) stack.
Proof.
fix ptd_stack_compat_build_pt_dot 4.
destruct ptl; intros.
eauto.
destruct p.
eauto.
simpl.
apply ptd_stack_compat_build_pt_dot.
split.
apply ptlz_stack_compat_ptlz_state_compat, non_terminal_closed in H.
apply H; clear H; eauto.
destruct wordq.
right; split.
eauto.
eapply nullable_correct_list; eauto.
left.
eapply first_correct_list; eauto.
eauto.
Qed.

Program Fixpoint pop_ptlz {hole_symbs hole_word hole_sems}
  (ptl:parse_tree_list hole_symbs hole_word hole_sems)
  (ptlz:ptl_zipper hole_symbs hole_word hole_sems):
    { word:_ & { sem:_ &
      (pt_zipper (NT (prod_lhs (ptlz_prod ptlz))) word sem *
       parse_tree (NT (prod_lhs (ptlz_prod ptlz))) word sem)%type } } :=
  match ptlz in ptl_zipper hole_symbs hole_word hole_sems
    return parse_tree_list hole_symbs hole_word hole_sems ->
    { word:_ & { sem:_ &
      (pt_zipper (NT (prod_lhs (ptlz_prod ptlz))) word sem *
       parse_tree (NT (prod_lhs (ptlz_prod ptlz))) word sem)%type } }
  with
    | @Non_terminal_pt_ptlz prod word sem ptz => fun ptl =>
      let sem := uncurry (prod_action prod) sem in
      existT _ word (existT _ sem (ptz, Non_terminal_pt ptl))
    | Cons_ptl_ptlz pt ptlz' => fun ptl =>
      pop_ptlz (Cons_ptl pt ptl) ptlz'
  end ptl.

Lemma pop_ptlz_cost:
  forall hole_symbs hole_word hole_sems
    (ptl:parse_tree_list hole_symbs hole_word hole_sems)
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems),
  let 'existT _ word (existT _ sem (ptz, pt)) := pop_ptlz ptl ptlz in
  ptlz_cost ptlz = ptz_cost ptz.
Proof.
fix pop_ptlz_cost 5.
destruct ptlz.
reflexivity.
simpl; apply pop_ptlz_cost.
Qed.

Lemma pop_ptlz_buffer:
  forall hole_symbs hole_word hole_sems
    (ptl:parse_tree_list hole_symbs hole_word hole_sems)
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems),
  let 'existT _ word (existT _ sem (ptz, pt)) := pop_ptlz ptl ptlz in
  ptlz_buffer ptlz = ptz_buffer ptz.
Proof.
fix pop_ptlz_buffer 5.
destruct ptlz.
reflexivity.
simpl; apply pop_ptlz_buffer.
Qed.

Lemma pop_ptlz_pop_stack_compat_converter:
  forall A hole_symbs hole_word hole_sems (ptlz:ptl_zipper hole_symbs hole_word hole_sems),
  arrows_left (map symbol_semantic_type (rev (prod_rhs_rev (ptlz_prod ptlz)))) A =
  arrows_left (map symbol_semantic_type hole_symbs)
    (arrows_right A (map symbol_semantic_type (ptlz_past ptlz))).
Proof.
intros.
rewrite <- ptlz_past_ptlz_prod.
unfold arrows_right, arrows_left.
rewrite rev_append_rev, map_rev, map_app, map_rev, <- fold_left_rev_right, rev_involutive, fold_right_app.
rewrite fold_left_rev_right.
reflexivity.
Qed.

Lemma pop_ptlz_pop_stack_compat:
  forall hole_symbs hole_word hole_sems
    (ptl:parse_tree_list hole_symbs hole_word hole_sems)
    (ptlz:ptl_zipper hole_symbs hole_word hole_sems)
    (stack:stack),

    ptlz_stack_compat ptlz stack ->

    let action' :=
      eq_rect _ (fun x=>x) (prod_action (ptlz_prod ptlz)) _
      (pop_ptlz_pop_stack_compat_converter _ _ _ _ _)
    in
    let 'existT _ word (existT _ sem (ptz, pt)) := pop_ptlz ptl ptlz in
      match pop (ptlz_past ptlz) stack (uncurry action' hole_sems) with
        | OK (stack', sem') =>
           ptz_stack_compat ptz stack' /\ sem = sem'
        | Err => True
      end.
Proof.
Opaque AlphabetComparable AlphabetComparableUsualEq.
fix pop_ptlz_pop_stack_compat 5.
destruct ptlz. intros; simpl.
split.
apply H.
eapply (f_equal (fun X => uncurry X semantic_values)).
apply JMeq_eq, JMeq_sym, JMeq_eqrect with (P:=fun x => x).
simpl; intros; destruct stack0.
destruct (proj2 H).
simpl in H; destruct H.
destruct s as (state, sem').
destruct H0.
specialize (pop_ptlz_pop_stack_compat _ _ _ (Cons_ptl p ptl) ptlz _ H0).
destruct (pop_ptlz (Cons_ptl p ptl) ptlz) as [word [sem []]].
destruct (compare_eqdec (last_symb_of_non_init_state state) head_symbolt); intuition.
eapply JMeq_sym, JMeq_trans, JMeq_sym, JMeq_eq in H1; [|apply JMeq_eqrect with (e:=e)].
rewrite <- H1.
simpl in pop_ptlz_pop_stack_compat.
erewrite proof_irrelevance with (p1:=pop_ptlz_pop_stack_compat_converter _ _ _ _ _).
apply pop_ptlz_pop_stack_compat.
Transparent AlphabetComparable AlphabetComparableUsualEq.
Qed.

Definition next_ptd (ptd:pt_dot): option pt_dot :=
  match ptd with
    | Shift_ptd term sem ptl ptlz =>
      Some (build_pt_dot ptl (Cons_ptl_ptlz (Terminal_pt term sem) ptlz))
    | Reduce_ptd ptlz =>
      let 'existT _ _ (existT _ _ (ptz, pt)) := pop_ptlz Nil_ptl ptlz in
      match ptz in pt_zipper sym _ _ return parse_tree sym _ _ -> _ with
        | Top_ptz => fun pt => None
        | Cons_ptl_ptz ptl ptlz' =>
          fun pt => Some (build_pt_dot ptl (Cons_ptl_ptlz pt ptlz'))
      end pt
  end.

Lemma next_ptd_cost:
  forall ptd,
    match next_ptd ptd with
      | None => ptd_cost ptd = 0
      | Some ptd' => ptd_cost ptd = S (ptd_cost ptd')
    end.
Proof.
destruct ptd. unfold next_ptd.
pose proof (pop_ptlz_cost _ _ _ Nil_ptl p).
destruct (pop_ptlz Nil_ptl p) as [word[sem[[]]]].
assumption.
rewrite build_pt_dot_cost.
assumption.
simpl; rewrite build_pt_dot_cost; reflexivity.
Qed.

Lemma reduce_step_next_ptd:
  forall (ptlz:ptl_zipper [] [] ()) (stack:stack),
    ptlz_stack_compat ptlz stack ->
    match reduce_step init stack (ptlz_prod ptlz) (ptlz_buffer ptlz) with
      | OK Fail_sr =>
        False
      | OK (Accept_sr sem buffer) =>
        sem = full_sem /\ buffer = buffer_end /\ next_ptd (Reduce_ptd ptlz) = None
      | OK (Progress_sr stack buffer) =>
        match next_ptd (Reduce_ptd ptlz) with
          | None => False
          | Some ptd =>
            ptd_stack_compat ptd stack /\ buffer = ptd_buffer ptd
        end
      | Err =>
        True
    end.
Proof.
intros.
unfold reduce_step, next_ptd.
apply pop_ptlz_pop_stack_compat with (ptl:=Nil_ptl) in H.
pose proof (pop_ptlz_buffer _ _ _ Nil_ptl ptlz).
destruct (pop_ptlz Nil_ptl ptlz) as [word [sem [ptz pt]]].
rewrite H0; clear H0.
revert H.
match goal with
  |- match ?p1 with Err => _ | OK _ => _ end -> match bind2 ?p2 _ with Err => _ | OK _ => _ end =>
  replace p1 with p2; [destruct p2 as [|[]];  intros|]
end.
assumption.
simpl.
destruct H; subst.
generalize dependent s0.
generalize (prod_lhs (ptlz_prod ptlz)); clear ptlz stack0.
dependent destruction ptz; intros.
simpl in H; subst; simpl.
pose proof start_goto; unfold Valid.start_goto in H; rewrite H.
destruct (compare_eqdec (start_nt init) (start_nt init)); intuition.
apply JMeq_eq, JMeq_eqrect with (P:=fun nt => symbol_semantic_type (NT nt)).
pose proof (ptlz_stack_compat_ptlz_state_compat _ _ _ _ _ H).
apply non_terminal_goto in H0.
destruct (goto_table (state_of_stack init s) n) as [[]|]; intuition.
apply ptd_stack_compat_build_pt_dot; simpl; intuition.
symmetry; apply JMeq_eqrect with (P:=symbol_semantic_type).
symmetry; apply build_pt_dot_buffer.
destruct s; intuition.
simpl in H; apply ptlz_stack_compat_ptlz_state_compat in H.
destruct (H0 _ _ _ H eq_refl).
generalize (pop_ptlz_pop_stack_compat_converter (symbol_semantic_type (NT (prod_lhs (ptlz_prod ptlz)))) _ _ _ ptlz).
pose proof (ptlz_past_ptlz_prod _ _ _ ptlz); simpl in H.
rewrite H; clear H.
intro; f_equal; simpl.
apply JMeq_eq.
etransitivity.
apply JMeq_eqrect with (P:=fun x => x).
symmetry.
apply JMeq_eqrect with (P:=fun x => x).
Qed.

Lemma step_next_ptd:
  forall (ptd:pt_dot) (stack:stack),
    ptd_stack_compat ptd stack ->
    match step init stack (ptd_buffer ptd) with
      | OK Fail_sr =>
        False
      | OK (Accept_sr sem buffer) =>
        sem = full_sem /\ buffer = buffer_end /\ next_ptd ptd = None
      | OK (Progress_sr stack buffer) =>
        match next_ptd ptd with
          | None => False
          | Some ptd =>
            ptd_stack_compat ptd stack /\ buffer = ptd_buffer ptd
        end
      | Err =>
        True
    end.
Proof.
intros.
destruct ptd.
pose proof (ptlz_stack_compat_ptlz_state_compat _ _ _ _ _ H).
apply end_reduce in H0.
unfold step.
destruct (action_table (state_of_stack init stack0)).
rewrite H0 by reflexivity.
apply reduce_step_next_ptd; assumption.
simpl; destruct (Streams.hd (ptlz_buffer p)); simpl in H0.
destruct (l x); intuition; rewrite H1.
apply reduce_step_next_ptd; assumption.
pose proof (ptlz_stack_compat_ptlz_state_compat _ _ _ _ _ H).
apply terminal_shift in H0.
unfold step.
destruct (action_table (state_of_stack init stack0)); intuition.
simpl; destruct (Streams.hd (ptlz_buffer p0)) as [] eqn:?.
destruct (l term); intuition.
apply ptd_stack_compat_build_pt_dot; simpl; intuition.
unfold ptlz_state_compat; simpl; destruct Heqt; assumption.
symmetry; apply JMeq_eqrect with (P:=symbol_semantic_type).
rewrite build_pt_dot_buffer; reflexivity.
Qed.

Lemma parse_fix_complete:
  forall (ptd:pt_dot) (stack:stack) (n_steps:nat),
    ptd_stack_compat ptd stack ->
    match parse_fix init stack (ptd_buffer ptd) n_steps with
      | OK (Parsed_pr sem_res buffer_end_res) =>
        sem_res = full_sem /\ buffer_end_res = buffer_end /\
         S (ptd_cost ptd) <= n_steps
      | OK Fail_pr => False
      | OK Timeout_pr => n_steps < S (ptd_cost ptd)
      | Err => True
    end.
Proof.
fix parse_fix_complete 3.
destruct n_steps; intros; simpl.
apply Nat.lt_0_succ.
apply step_next_ptd in H.
pose proof (next_ptd_cost ptd).
destruct (step init stack0 (ptd_buffer ptd)) as [|[]]; simpl; intuition.
rewrite H3 in H0; rewrite H0.
apply le_n_S, Nat.le_0_l.
destruct (next_ptd ptd); intuition; subst.
eapply parse_fix_complete with (n_steps:=n_steps) in H1.
rewrite H0.
destruct (parse_fix init s (ptd_buffer p) n_steps) as [|[]]; try assumption.
apply lt_n_S; assumption.
destruct H1 as [H1 []]; split; [|split]; try assumption.
apply le_n_S; assumption.
Qed.

Variable full_pt: parse_tree (NT (start_nt init)) full_word full_sem.

Definition init_ptd :=
  match full_pt in parse_tree head full_word full_sem return
    pt_zipper head full_word full_sem ->
    match head return Type with | T _ => unit | NT _ => pt_dot end
  with
    | Terminal_pt _ _ => fun _ => ()
    | Non_terminal_pt ptl =>
      fun top => build_pt_dot ptl (Non_terminal_pt_ptlz top)
  end Top_ptz.

Lemma init_ptd_compat:
  ptd_stack_compat init_ptd [].
Proof.
unfold init_ptd.
assert (ptz_stack_compat Top_ptz []) by reflexivity.
pose proof (start_future init); revert H0.
generalize dependent Top_ptz.
generalize dependent full_word.
generalize full_sem.
generalize (start_nt init).
dependent destruction full_pt0.
intros.
apply ptd_stack_compat_build_pt_dot; simpl; intuition.
apply H0; reflexivity.
Qed.

Lemma init_ptd_cost:
  S (ptd_cost init_ptd) = pt_size full_pt.
Proof.
unfold init_ptd.
assert (ptz_cost Top_ptz = 0) by reflexivity.
generalize dependent Top_ptz.
generalize dependent full_word.
generalize full_sem.
generalize (start_nt init).
dependent destruction full_pt0.
intros.
rewrite build_pt_dot_cost; simpl.
rewrite H, Nat.add_0_r; reflexivity.
Qed.

Lemma init_ptd_buffer:
  ptd_buffer init_ptd = full_word ++ buffer_end.
Proof.
unfold init_ptd.
assert (ptz_buffer Top_ptz = buffer_end) by reflexivity.
generalize dependent Top_ptz.
generalize dependent full_word.
generalize full_sem.
generalize (start_nt init).
dependent destruction full_pt0.
intros.
rewrite build_pt_dot_buffer; simpl.
rewrite H; reflexivity.
Qed.

Theorem parse_complete n_steps:
  match parse init (full_word ++ buffer_end) n_steps with
    | OK (Parsed_pr sem_res buffer_end_res) =>
      sem_res = full_sem /\ buffer_end_res = buffer_end /\
       pt_size full_pt <= n_steps
    | OK Fail_pr => False
    | OK Timeout_pr => n_steps < pt_size full_pt
    | Err => True
  end.
Proof.
pose proof (parse_fix_complete init_ptd [] n_steps init_ptd_compat).
rewrite init_ptd_buffer, init_ptd_cost in H.
apply H.
Qed.

End Completeness_Proof.

End Make.

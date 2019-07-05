(****************************************************************************)
(*                                                                          *)
(*                                   Menhir                                 *)
(*                                                                          *)
(*           Jacques-Henri Jourdan, CNRS, LRI, Université Paris Sud         *)
(*                                                                          *)
(*  Copyright Inria. All rights reserved. This file is distributed under    *)
(*  the terms of the GNU Lesser General Public License as published by the  *)
(*  Free Software Foundation, either version 3 of the License, or (at your  *)
(*  option) any later version, as described in the file LICENSE.            *)
(*                                                                          *)
(****************************************************************************)

From Coq Require Import List Syntax Arith.
From Coq.ssr Require Import ssreflect.
Require Import Alphabet Grammar.
Require Automaton Interpreter Validator_complete.

Module Make(Import A:Automaton.T) (Import Inter:Interpreter.T A).
Module Import Valid := Validator_complete.Make A.

(** * Completeness Proof **)

Section Completeness_Proof.

Hypothesis safe: Inter.ValidSafe.safe.
Hypothesis complete: complete.

(* Properties of the automaton deduced from completeness validation. *)
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
Lemma nullable_correct head word :
  word = [] -> parse_tree head word -> nullable_symb head = true
with nullable_correct_list heads word :
  word = [] ->
  parse_tree_list heads word -> nullable_word heads = true.
Proof.
  - destruct 2=>//. assert (Hnull := nullable_stable prod).
    erewrite nullable_correct_list in Hnull; eauto.
  - intros Hword. destruct 1=>//=. destruct (app_eq_nil _ _ Hword).
    eauto using andb_true_intro.
Qed.

(** Auxiliary lemma for first_correct.  *)
Lemma first_word_set_app t word1 word2 :
  TerminalSet.In t (first_word_set (word1 ++ word2)) <->
  TerminalSet.In t (first_word_set word1) \/
  TerminalSet.In t (first_word_set word2) /\ nullable_word (rev word1) = true.
Proof.
  induction word1 as [|s word1 IH]=>/=.
  - split; [tauto|]. move=>[/TerminalSet.empty_1 ?|[? _]]//.
  - rewrite /nullable_word forallb_app /=. destruct nullable_symb=>/=.
    + rewrite Bool.andb_true_r. split.
      * move=>/TerminalSet.union_1. rewrite IH.
        move=>[?|[?|[??]]]; auto using TerminalSet.union_2, TerminalSet.union_3.
      * destruct IH.
        move=>[/TerminalSet.union_1 [?|?]|[??]];
        auto using TerminalSet.union_2, TerminalSet.union_3.
    + rewrite Bool.andb_false_r. by intuition.
Qed.

(** If the first predicate has been validated, then it is correct. **)
Lemma first_correct head word t q :
  word = t::q ->
  parse_tree head word ->
  TerminalSet.In (token_term t) (first_symb_set head)
with first_correct_list heads word t q :
  word = t::q ->
  parse_tree_list heads word ->
  TerminalSet.In (token_term t) (first_word_set (rev' heads)).
Proof.
  - intros Hword. destruct 1=>//.
    + inversion Hword. subst. apply TerminalSet.singleton_2, compare_refl.
    + eapply first_stable. eauto.
  - intros Hword. destruct 1 as [|symq wordq ptl symt wordt pt]=>//=.
    rewrite /rev' -rev_alt /= first_word_set_app /= rev_involutive rev_alt.
    destruct wordq; [right|left].
    + destruct nullable_symb; eauto using TerminalSet.union_2, nullable_correct_list.
    + inversion Hword. subst. fold (rev' symq). eauto.
Qed.

(** A PTL is compatible with a stack if the top of the stack contains
  data representing to this PTL. *)
Fixpoint ptl_stack_compat {symbs word}
         (stk0 : stack) (ptl : parse_tree_list symbs word) (stk : stack) : Prop :=
  match ptl with
  | Nil_ptl => stk0 = stk
  | @Cons_ptl _ _ ptl sym _ pt =>
    match stk with
    | [] => False
    | existT _ _ sem::stk =>
      ptl_stack_compat stk0 ptl stk /\
      exists e,
        sem = eq_rect _ symbol_semantic_type (pt_sem pt) _ e
    end
  end.

(** .. and when a PTL is compatible with a stack, then calling the pop
  function return the semantic value of this PTL. *)
Lemma pop_stack_compat_pop_spec {A symbs word}
    (ptl:parse_tree_list symbs word) (stk:stack) (stk0:stack) action :
  ptl_stack_compat stk0 ptl stk ->
  pop_spec symbs stk action stk0 (ptl_sem (A:=A) ptl action).
Proof.
  revert stk. induction ptl=>stk /= Hstk.
  - subst. constructor.
  - destruct stk as [|[st sem] stk]=>//. destruct Hstk as [Hstk [??]]. subst.
    simpl. constructor. eauto.
Qed.

Variable init: initstate.

(** In order to prove compleness, we first fix a word to be parsed
  together with the content of the parser at the end of the parsing. *)
Variable full_word: list token.
Variable buffer_end: buffer.

(** Completeness is proved by following the traversal of the parse
  tree which is performed by the parser. Each step of parsing
  correspond to one step of traversal. In order to represent the state
  of the traversal, we define the notion of "dotted" parse tree, which
  is a parse tree with one dot on one of its node. The place of the
  dot represents the place of the next action to be executed.

  Such a dotted parse tree is decomposed into two part: a "regular"
  parse tree, which is the parse tree placed under the dot, and a
  "parse tree zipper", which is the part of the parse tree placed
  above the dot. Therefore, a parse tree zipper is a parse tree with a
  hole. Moreover, for easier manipulation, a parse tree zipper is
  represented "upside down". That is, the root of the parse tree is
  actually a leaf of the zipper, while the root of the zipper is the
  hole.
 *)
Inductive pt_zipper:
  forall (hole_symb:symbol) (hole_word:list token), Type :=
| Top_ptz:
  pt_zipper (NT (start_nt init)) full_word
| Cons_ptl_ptz:
  forall {head_symbolsq:list symbol} {wordq:list token},
    parse_tree_list head_symbolsq wordq ->

  forall {head_symbolt:symbol} {wordt:list token},

    ptl_zipper (head_symbolt::head_symbolsq) (wordq++wordt) ->
    pt_zipper head_symbolt wordt
with ptl_zipper:
  forall (hole_symbs:list symbol) (hole_word:list token), Type :=
| Non_terminal_pt_ptlz:
  forall {p:production} {word:list token},
    pt_zipper (NT (prod_lhs p)) word ->
    ptl_zipper (prod_rhs_rev p) word

| Cons_ptl_ptlz:
  forall {head_symbolsq:list symbol} {wordq:list token},

  forall {head_symbolt:symbol} {wordt:list token},
    parse_tree head_symbolt wordt ->

  ptl_zipper (head_symbolt::head_symbolsq) (wordq++wordt) ->

  ptl_zipper head_symbolsq wordq.

(** A dotted parse tree is the combination of a parse tree zipper with
  a parse tree. It can be intwo flavors, depending on which is the next
  action to be executed (shift or reduce). *)
Inductive pt_dot: Type :=
| Reduce_ptd: forall {prod word},
    parse_tree_list (prod_rhs_rev prod) word ->
    pt_zipper (NT (prod_lhs prod)) word ->
    pt_dot
| Shift_ptd: forall (tok : token) {symbolsq wordq},
    parse_tree_list symbolsq wordq ->
    ptl_zipper (T (token_term tok)::symbolsq) (wordq++[tok]) ->
    pt_dot.

(** We can compute the full semantic value of a parse tree when
  represented as a dotted ptd. *)

Fixpoint ptlz_sem {hole_symbs hole_word}
         (ptlz:ptl_zipper hole_symbs hole_word) :
         (forall A, arrows_right A (map symbol_semantic_type hole_symbs) -> A) ->
         (symbol_semantic_type (NT (start_nt init))) :=
  match ptlz with
  | @Non_terminal_pt_ptlz prod _ ptz =>
    fun k => ptz_sem ptz (k _ (prod_action prod))
  | Cons_ptl_ptlz pt ptlz =>
    fun k => ptlz_sem ptlz (fun _ f => k _ (f (pt_sem pt)))
  end
with ptz_sem {hole_symb hole_word}
             (ptz:pt_zipper hole_symb hole_word):
  symbol_semantic_type hole_symb -> symbol_semantic_type (NT (start_nt init)) :=
  match ptz with
  | Top_ptz => fun sem => sem
  | Cons_ptl_ptz ptl ptlz =>
    fun sem => ptlz_sem ptlz (fun _ f => ptl_sem ptl (f sem))
  end.

Definition ptd_sem (ptd : pt_dot) :=
  match ptd with
  | @Reduce_ptd prod _ ptl ptz =>
    ptz_sem ptz (ptl_sem ptl (prod_action prod))
  | Shift_ptd tok ptl ptlz =>
    ptlz_sem ptlz (fun _ f => ptl_sem ptl (f (token_sem tok)))
  end.

(** The buffer associated with a dotted parse tree corresponds to the
  buffer left to be read by the parser when at the state represented
  by the dotted parse tree. *)
Fixpoint ptlz_buffer {hole_symbs hole_word}
         (ptlz:ptl_zipper hole_symbs hole_word): buffer :=
  match ptlz with
  | Non_terminal_pt_ptlz ptz =>
    ptz_buffer ptz
  | @Cons_ptl_ptlz _ _ _ wordt _ ptlz' =>
    wordt ++ ptlz_buffer ptlz'
  end
with ptz_buffer {hole_symb hole_word}
                (ptz:pt_zipper hole_symb hole_word): buffer :=
  match ptz with
  | Top_ptz => buffer_end
  | Cons_ptl_ptz _ ptlz =>
    ptlz_buffer ptlz
  end.

Definition ptd_buffer (ptd:pt_dot) :=
  match ptd with
  | Reduce_ptd _ ptz => ptz_buffer ptz
  | @Shift_ptd tok _ wordq _ ptlz => (tok::ptlz_buffer ptlz)%buf
  end.

(** We are now ready to define the main invariant of the proof of
  completeness: we need to specify when a stack is compatible with a
  dotted parse tree. Informally, a stack is compatible with a dotted
  parse tree when it is the concatenation stack fragments which are
  compatible with each of the partially recognized productions
  appearing in the parse tree zipper. Moreover, the head of each of
  these stack fragment contains a state which has an item predicted by
  the corresponding zipper.

  More formally, the compatibility relation first needs the following
  auxiliary definitions: *)
Fixpoint ptlz_prod {hole_symbs hole_word}
         (ptlz:ptl_zipper hole_symbs hole_word): production :=
  match ptlz with
  | @Non_terminal_pt_ptlz prod _ _ => prod
  | Cons_ptl_ptlz _ ptlz' => ptlz_prod ptlz'
  end.

Fixpoint ptlz_future {hole_symbs hole_word}
  (ptlz:ptl_zipper hole_symbs hole_word): list symbol :=
  match ptlz with
  | Non_terminal_pt_ptlz _ => []
  | @Cons_ptl_ptlz _ _ s _ _ ptlz' => s::ptlz_future ptlz'
  end.

Fixpoint ptlz_lookahead {hole_symbs hole_word}
  (ptlz:ptl_zipper hole_symbs hole_word) : terminal :=
  match ptlz with
  | Non_terminal_pt_ptlz ptz => token_term (buf_head (ptz_buffer ptz))
  | Cons_ptl_ptlz _ ptlz' => ptlz_lookahead ptlz'
  end.

Fixpoint ptz_stack_compat {hole_symb hole_word}
         (stk : stack) (ptz : pt_zipper hole_symb hole_word) : Prop :=
  match ptz with
  | Top_ptz => stk = []
  | Cons_ptl_ptz ptl ptlz =>
    exists stk0,
      state_has_future (state_of_stack init stk) (ptlz_prod ptlz)
                       (hole_symb::ptlz_future ptlz) (ptlz_lookahead ptlz) /\
      ptl_stack_compat stk0 ptl stk /\
      ptlz_stack_compat stk0 ptlz
  end
with ptlz_stack_compat {hole_symbs hole_word}
     (stk : stack) (ptlz : ptl_zipper hole_symbs hole_word) : Prop :=
  match ptlz with
  | Non_terminal_pt_ptlz ptz => ptz_stack_compat stk ptz
  | Cons_ptl_ptlz _ ptlz => ptlz_stack_compat stk ptlz
  end.

Definition ptd_stack_compat (ptd:pt_dot) (stk:stack): Prop :=
  match ptd with
  | @Reduce_ptd prod _ ptl ptz =>
    exists stk0,
      state_has_future (state_of_stack init stk) prod []
                       (token_term (buf_head (ptz_buffer ptz))) /\
      ptl_stack_compat stk0 ptl stk /\
      ptz_stack_compat stk0 ptz
  | Shift_ptd tok ptl ptlz =>
    exists stk0,
      state_has_future (state_of_stack init stk) (ptlz_prod ptlz)
                       (T (token_term tok) :: ptlz_future ptlz) (ptlz_lookahead ptlz) /\
      ptl_stack_compat stk0 ptl stk /\
      ptlz_stack_compat stk0 ptlz
  end.

Lemma ptz_stack_compat_cons_state_has_future {symbsq wordq symbt wordt} stk
      (ptl : parse_tree_list symbsq wordq)
      (ptlz : ptl_zipper (symbt :: symbsq) (wordq ++ wordt)) :
  ptz_stack_compat stk (Cons_ptl_ptz ptl ptlz) ->
  state_has_future (state_of_stack init stk) (ptlz_prod ptlz)
                   (symbt::ptlz_future ptlz) (ptlz_lookahead ptlz).
Proof. move=>[stk0 [? [? ?]]] //. Qed.

Lemma ptlz_future_ptlz_prod hole_symbs hole_word
      (ptlz:ptl_zipper hole_symbs hole_word) :
  rev_append (ptlz_future ptlz) hole_symbs = prod_rhs_rev (ptlz_prod ptlz).
Proof. induction ptlz=>//=. Qed.

Lemma ptlz_future_first {symbs word} (ptlz : ptl_zipper symbs word) :
  TerminalSet.In (token_term (buf_head (ptlz_buffer ptlz)))
    (first_word_set (ptlz_future ptlz)) \/
  token_term (buf_head (ptlz_buffer ptlz)) = ptlz_lookahead ptlz /\
  nullable_word (ptlz_future ptlz) = true.
Proof.
  induction ptlz as [|??? [|tok] pt ptlz IH]; [by auto| |]=>/=.
  - rewrite (nullable_correct _ _ eq_refl pt).
    destruct IH as [|[??]]; [left|right]=>/=; auto using TerminalSet.union_3.
  - left. destruct nullable_symb; eauto using TerminalSet.union_2, first_correct.
Qed.

(** We now want to define what is the next dotted parse tree which is
  to be handled after one action. Such dotted parse is built in two
  steps: Not only we have to perform the action by completing the
  parse tree, but we also have to prepare for the following step by
  moving the dot down to place it in front of the next action to be
  performed.
*)
Fixpoint build_pt_dot_from_pt {symb word}
         (pt : parse_tree symb word) (ptz : pt_zipper symb word)
  : pt_dot :=
  match pt in parse_tree symb word
    return pt_zipper symb word -> pt_dot
  with
  | Terminal_pt tok =>
    fun ptz =>
      let X :=
          match ptz in pt_zipper symb word
            return match symb with T term => True | NT _ => False end ->
                   { symbsq : list symbol &
                     { wordq : list token &
                       (parse_tree_list symbsq wordq *
                        ptl_zipper (symb :: symbsq) (wordq ++ word))%type } }
          with
          | Top_ptz => fun F => False_rect _ F
          | Cons_ptl_ptz ptl ptlz => fun _ =>
            existT _ _ (existT _ _ (ptl, ptlz))
          end I
      in
      Shift_ptd tok (fst (projT2 (projT2 X))) (snd (projT2 (projT2 X)))
  | Non_terminal_pt prod ptl => fun ptz =>
    let is_notnil :=
      match ptl in parse_tree_list w _
        return option (match w return Prop with [] => False | _ => True end)
      with
      | Nil_ptl => None
      | _ => Some I
      end
    in
    match is_notnil with
    | None => Reduce_ptd ptl ptz
    | Some H => build_pt_dot_from_pt_rec ptl H (Non_terminal_pt_ptlz ptz)
    end
  end ptz
with build_pt_dot_from_pt_rec {symbs word}
       (ptl : parse_tree_list symbs word)
       (Hsymbs : match symbs with [] => False | _ => True end)
       (ptlz : ptl_zipper symbs word)
  : pt_dot :=
  match ptl in parse_tree_list symbs word
    return match symbs with [] => False | _ => True end ->
           ptl_zipper symbs word ->
           pt_dot
  with
  | Nil_ptl => fun Hsymbs _ => False_rect _ Hsymbs
  | Cons_ptl ptl' pt => fun _ =>
    match ptl' in parse_tree_list symbsq wordq
      return parse_tree_list symbsq wordq ->
             ptl_zipper (_ :: symbsq) (wordq ++ _) ->
             pt_dot
    with
    | Nil_ptl => fun _ ptlz =>
      build_pt_dot_from_pt pt (Cons_ptl_ptz Nil_ptl ptlz)
    | _ => fun ptl' ptlz =>
      build_pt_dot_from_pt_rec ptl' I (Cons_ptl_ptlz pt ptlz)
    end ptl'
  end Hsymbs ptlz.

Definition build_pt_dot_from_ptl {symbs word}
         (ptl : parse_tree_list symbs word)
         (ptlz : ptl_zipper symbs word)
  : pt_dot :=
  match ptlz in ptl_zipper symbs word
    return parse_tree_list symbs word -> pt_dot
  with
  | Non_terminal_pt_ptlz ptz => fun ptl =>
    Reduce_ptd ptl ptz
  | Cons_ptl_ptlz pt ptlz => fun ptl =>
    build_pt_dot_from_pt pt (Cons_ptl_ptz ptl ptlz)
  end ptl.

Definition next_ptd (ptd:pt_dot) : option pt_dot :=
  match ptd with
  | Shift_ptd tok ptl ptlz =>
    Some (build_pt_dot_from_ptl (Cons_ptl ptl (Terminal_pt tok)) ptlz)
  | Reduce_ptd ptl ptz =>
    match ptz in pt_zipper symb word
      return parse_tree symb word -> _
    with
    | Top_ptz => fun _ => None
    | Cons_ptl_ptz ptl' ptlz => fun pt =>
      Some (build_pt_dot_from_ptl (Cons_ptl ptl' pt) ptlz)
    end (Non_terminal_pt _ ptl)
  end.

Fixpoint next_ptd_iter (ptd:pt_dot) (log_n_steps:nat) : option pt_dot :=
  match log_n_steps with
  | O => next_ptd ptd
  | S log_n_steps =>
    match next_ptd_iter ptd log_n_steps with
    | None => None
    | Some ptd => next_ptd_iter ptd log_n_steps
    end
  end.

(** We prove that these functions behave well w.r.t. semantic values. *)
Lemma sem_build_from_pt {symb word}
      (pt : parse_tree symb word) (ptz : pt_zipper symb word)  :
  ptz_sem ptz (pt_sem pt)
  = ptd_sem (build_pt_dot_from_pt pt ptz)
with sem_build_from_pt_rec {symbs word}
     (ptl : parse_tree_list symbs word) (ptlz : ptl_zipper symbs word)
     Hsymbs :
  ptlz_sem ptlz (fun _ f => ptl_sem ptl f)
  = ptd_sem (build_pt_dot_from_pt_rec ptl Hsymbs ptlz).
Proof.
  - destruct pt as [tok|prod word ptl]=>/=.
    + revert ptz. generalize [tok].
      generalize (token_sem tok). generalize I.
      change True with (match T (token_term tok) with T _ => True | NT _ => False end) at 1.
      generalize (T (token_term tok)) => symb HT sem word ptz. by destruct ptz.
    + match goal with
      | |- context [match ?X with Some H => _ | None => _ end] => destruct X=>//
      end.
      by rewrite -sem_build_from_pt_rec.
  - destruct ptl; [contradiction|].
    specialize (sem_build_from_pt_rec _ _ ptl)=>/=. destruct ptl.
    + by rewrite -sem_build_from_pt.
    + by rewrite -sem_build_from_pt_rec.
Qed.

Lemma sem_build_from_ptl {symbs word}
      (ptl : parse_tree_list symbs word) (ptlz : ptl_zipper symbs word) :
  ptlz_sem ptlz (fun _ f => ptl_sem ptl f)
  = ptd_sem (build_pt_dot_from_ptl ptl ptlz).
Proof. destruct ptlz=>//=. by rewrite -sem_build_from_pt. Qed.

Lemma sem_next_ptd (ptd : pt_dot) :
  match next_ptd ptd with
  | None => True
  | Some ptd' => ptd_sem ptd = ptd_sem ptd'
  end.
Proof.
  destruct ptd as [prod word ptl ptz|tok symbs word ptl ptlz] =>/=.
  - change (ptl_sem ptl (prod_action prod))
      with (pt_sem (Non_terminal_pt prod ptl)).
    generalize (Non_terminal_pt prod ptl). clear ptl.
    destruct ptz as [|?? ptl ?? ptlz]=>// pt. by rewrite -sem_build_from_ptl.
  - by rewrite -sem_build_from_ptl.
Qed.

Lemma sem_next_ptd_iter (ptd : pt_dot) (log_n_steps : nat) :
  match next_ptd_iter ptd log_n_steps with
  | None => True
  | Some ptd' => ptd_sem ptd = ptd_sem ptd'
  end.
Proof.
  revert ptd.
  induction log_n_steps as [|log_n_steps IH]; [by apply sem_next_ptd|]=>/= ptd.
  assert (IH1 := IH ptd). destruct next_ptd_iter as [ptd'|]=>//.
  specialize (IH ptd'). destruct next_ptd_iter=>//. congruence.
Qed.

(** We prove that these functions behave well w.r.t. xxx_buffer. *)
Lemma ptd_buffer_build_from_pt {symb word}
      (pt : parse_tree symb word) (ptz : pt_zipper symb word) :
  (word ++ ptz_buffer ptz)%buf = ptd_buffer (build_pt_dot_from_pt pt ptz)
with ptd_buffer_build_from_pt_rec {symbs word}
     (ptl : parse_tree_list symbs word) (ptlz : ptl_zipper symbs word)
     Hsymbs :
  (word ++ ptlz_buffer ptlz)%buf = ptd_buffer (build_pt_dot_from_pt_rec ptl Hsymbs ptlz).
Proof.
  - destruct pt as [tok|prod word ptl]=>/=.
    + f_equal. revert ptz. generalize [tok].
      generalize (token_sem tok). generalize I.
      change True with (match T (token_term tok) with T _ => True | NT _ => False end) at 1.
      generalize (T (token_term tok)) => symb HT sem word ptz. by destruct ptz.
    + match goal with
      | |- context [match ?X with Some H => _ | None => _ end] => destruct X eqn:EQ
      end.
      * by rewrite -ptd_buffer_build_from_pt_rec.
      * rewrite [X in (X ++ _)%buf](_ : word = []) //. clear -EQ. by destruct ptl.
  - destruct ptl as [|?? ptl ?? pt]; [contradiction|].
    specialize (ptd_buffer_build_from_pt_rec _ _ ptl).
    destruct ptl.
    + by rewrite /= -ptd_buffer_build_from_pt.
    + by rewrite -ptd_buffer_build_from_pt_rec //= app_buf_assoc.
Qed.

Lemma ptd_buffer_build_from_ptl {symbs word}
      (ptl : parse_tree_list symbs word) (ptlz : ptl_zipper symbs word) :
  ptlz_buffer ptlz = ptd_buffer (build_pt_dot_from_ptl ptl ptlz).
Proof.
  destruct ptlz as [|???? pt]=>//=. by rewrite -ptd_buffer_build_from_pt.
Qed.

(** We prove that these functions behave well w.r.t. xxx_stack_compat. *)
Lemma ptd_stack_compat_build_from_pt {symb word}
      (pt : parse_tree symb word) (ptz : pt_zipper symb word)
      (stk: stack) :
  ptz_stack_compat stk ptz ->
  ptd_stack_compat (build_pt_dot_from_pt pt ptz) stk
with ptd_stack_compat_build_from_pt_rec {symbs word}
     (ptl : parse_tree_list symbs word) (ptlz : ptl_zipper symbs word)
     (stk : stack) Hsymbs :
  ptlz_stack_compat stk ptlz ->
  state_has_future (state_of_stack init stk) (ptlz_prod ptlz)
                   (rev' (prod_rhs_rev (ptlz_prod ptlz))) (ptlz_lookahead ptlz) ->
  ptd_stack_compat (build_pt_dot_from_pt_rec ptl Hsymbs ptlz) stk.
Proof.
  - intros Hstk. destruct pt as [tok|prod word ptl]=>/=.
    + revert ptz Hstk. generalize [tok]. generalize (token_sem tok). generalize I.
      change True with (match T (token_term tok) with T _ => True | NT _ => False end) at 1.
      generalize (T (token_term tok)) => symb HT sem word ptz. by destruct ptz.
    + assert (state_has_future (state_of_stack init stk) prod
               (rev' (prod_rhs_rev prod)) (token_term (buf_head (ptz_buffer ptz)))).
      { revert ptz Hstk. remember (NT (prod_lhs prod)) eqn:EQ=>ptz.
        destruct ptz as [|?? ptl0 ?? ptlz0].
        - intros ->. apply start_future. congruence.
        - subst. intros (stk0 & Hfut & _). apply non_terminal_closed in Hfut.
          specialize (Hfut prod eq_refl).
          destruct (ptlz_future_first ptlz0) as [Hfirst|[Hfirst Hnull]].
          + destruct Hfut as [_ Hfut]. auto.
          + destruct Hfut as [Hfut _]. by rewrite Hnull -Hfirst in Hfut. }
      match goal with
      | |- context [match ?X with Some H => _ | None => _ end] => destruct X eqn:EQ
      end.
      * by apply ptd_stack_compat_build_from_pt_rec.
      * exists stk. destruct ptl=>//.
  - intros Hstk Hfut. destruct ptl as [|?? ptl ?? pt]; [contradiction|].
    specialize (ptd_stack_compat_build_from_pt_rec _ _ ptl). destruct ptl.
    + eapply ptd_stack_compat_build_from_pt=>//. exists stk.
      split; [|split]=>//; [].
      by rewrite -ptlz_future_ptlz_prod rev_append_rev /rev' -rev_alt
                 rev_app_distr rev_involutive in Hfut.
    + by apply ptd_stack_compat_build_from_pt_rec.
Qed.

Lemma ptd_stack_compat_build_from_ptl {symbs word}
      (ptl : parse_tree_list symbs word) (ptlz : ptl_zipper symbs word)
      (stk stk0: stack) :
  ptlz_stack_compat stk0 ptlz ->
  ptl_stack_compat stk0 ptl stk ->
  state_has_future (state_of_stack init stk) (ptlz_prod ptlz)
                   (ptlz_future ptlz) (ptlz_lookahead ptlz) ->
  ptd_stack_compat (build_pt_dot_from_ptl ptl ptlz) stk.
Proof.
  intros Hstk0 Hstk Hfut. destruct ptlz=>/=.
  - eauto.
  - apply ptd_stack_compat_build_from_pt=>/=. eauto.
Qed.

(** We can now proceed by proving that the invariant is preserved by
  each step of parsing. We also prove that each step of parsing
  follows next_ptd.

  We start with reduce steps: *)
Lemma reduce_step_next_ptd (prod : production) (word : list token)
      (ptl : parse_tree_list (prod_rhs_rev prod) word)
      (ptz : pt_zipper (NT (prod_lhs prod)) word)
      (stk : stack)
      Hval Hi :
  ptd_stack_compat (Reduce_ptd ptl ptz) stk ->
  match next_ptd (Reduce_ptd ptl ptz) with
  | None =>
    reduce_step init stk prod (ptz_buffer ptz) Hval Hi =
      Accept_sr (ptd_sem (Reduce_ptd ptl ptz)) buffer_end
  | Some ptd =>
    exists stk',
      reduce_step init stk prod (ptz_buffer ptz) Hval Hi =
        Progress_sr stk' (ptd_buffer ptd) /\
      ptd_stack_compat ptd stk'
  end.
Proof.
  intros (stk0 & _ & Hstk & Hstk0).
  apply pop_stack_compat_pop_spec with (action := prod_action prod) in Hstk.
  rewrite <-pop_spec_ok with (Hp := reduce_step_subproof init stk prod Hval Hi) in Hstk.
  unfold reduce_step.
  match goal with
  | |- context [pop_state_valid init ?A stk ?B ?C ?D ?E ?F] =>
    generalize (pop_state_valid init A stk B C D E F)
  end.
  rewrite Hstk /=. intros Hv.
  generalize (reduce_step_subproof1 init stk prod Hval stk0 (fun _ : True => Hv)).
  clear Hval Hstk Hi Hv stk.
  assert (Hgoto := fun fut prod' =>
    non_terminal_goto (state_of_stack init stk0) prod' (NT (prod_lhs prod)::fut)).
  simpl in Hgoto.
  destruct goto_table as [[st Hst]|] eqn:Hgoto'.
  - intros _.
    assert (match ptz with Top_ptz => False | _ => True end).
    { revert ptz Hst Hstk0 Hgoto'.
      generalize (eq_refl (NT (prod_lhs prod))).
      generalize (NT (prod_lhs prod)) at 1 3 5.
      intros nt Hnt ptz. destruct ptz=>//. injection Hnt=> <- /= Hst -> /= Hg.
      assert (Hsg := start_goto init). by rewrite Hg in Hsg. }
    clear Hgoto'.

    change (ptl_sem ptl (prod_action prod))
      with (pt_sem (Non_terminal_pt prod ptl)).
    generalize (Non_terminal_pt prod ptl). clear ptl.
    destruct ptz as [|?? ptl ? ? ptlz]=>// pt.

    subst=>/=. eexists _. split.
    + f_equal. apply ptd_buffer_build_from_ptl.
    + destruct Hstk0 as (stk0' & Hfut & Hstk0' & Hstk0).
      apply (ptd_stack_compat_build_from_ptl _ _ _ stk0'); auto; [].
      split=>//. by exists eq_refl.
  - intros Hv. generalize (reduce_step_subproof0 _ prod _ (fun _ => Hv)).
    intros EQnt. clear Hv Hgoto'.

    change (ptl_sem ptl (prod_action prod))
      with (pt_sem (Non_terminal_pt prod ptl)).
    generalize (Non_terminal_pt prod ptl). clear ptl. destruct ptz.
    + intros pt. f_equal. by rewrite cast_eq.
    + edestruct Hgoto. eapply ptz_stack_compat_cons_state_has_future, Hstk0.
Qed.

Lemma step_next_ptd (ptd : pt_dot) (stk : stack) Hi :
  ptd_stack_compat ptd stk ->
  match next_ptd ptd with
  | None =>
    step safe init stk (ptd_buffer ptd) Hi =
      Accept_sr (ptd_sem ptd) buffer_end
  | Some ptd' =>
    exists stk',
      step safe init stk (ptd_buffer ptd) Hi =
        Progress_sr stk' (ptd_buffer ptd') /\
      ptd_stack_compat ptd' stk'
  end.
Proof.
  intros Hstk. unfold step.
  generalize (reduce_ok safe (state_of_stack init stk)).
  destruct ptd as [prod word ptl ptz|tok symbs word ptl ptlz].
  - assert (Hfut : state_has_future (state_of_stack init stk) prod []
                                    (token_term (buf_head (ptz_buffer ptz)))).
    { destruct Hstk as (? & ? & ?)=>//. }
    assert (Hact := end_reduce _ _ _ _ Hfut).
    destruct action_table as [?|awt]=>Hval /=.
    + subst. by apply reduce_step_next_ptd.
    + set (term := token_term (buf_head (ptz_buffer ptz))) in *.
      generalize (Hval term). clear Hval. destruct (awt term)=>//. subst.
      intros Hval. by apply reduce_step_next_ptd.
  - destruct Hstk as (stk0 & Hfut & Hstk & Hstk0).
    assert (Hact := terminal_shift _ _ _ _ Hfut). simpl in Hact. clear Hfut.
    destruct action_table as [?|awt]=>//= /(_ (token_term tok)).
    destruct awt as [st' EQ| |]=>// _. eexists. split.
    + f_equal. rewrite -ptd_buffer_build_from_ptl //.
    + apply (ptd_stack_compat_build_from_ptl _ _ _ stk0); simpl; eauto.
Qed.

(** We prove the completeness of the parser main loop. *)
Lemma parse_fix_next_ptd_iter (ptd : pt_dot) (stk : stack) (log_n_steps : nat) Hi :
  ptd_stack_compat ptd stk ->
  match next_ptd_iter ptd log_n_steps with
  | None =>
    proj1_sig (parse_fix safe init stk (ptd_buffer ptd) log_n_steps Hi) =
      Accept_sr (ptd_sem ptd) buffer_end
  | Some ptd' =>
    exists stk',
      proj1_sig (parse_fix safe init stk (ptd_buffer ptd) log_n_steps Hi) =
        Progress_sr stk' (ptd_buffer ptd') /\
      ptd_stack_compat ptd' stk'
  end.
Proof.
  revert ptd stk Hi.
  induction log_n_steps as [|log_n_steps IH]; [by apply step_next_ptd|].
  move => /= ptd stk Hi Hstk. assert (IH1 := IH ptd stk Hi Hstk).
  assert (EQsem := sem_next_ptd_iter ptd log_n_steps).
  destruct parse_fix as [sr Hi']. simpl in IH1.
  destruct next_ptd_iter as [ptd'|].
  - rewrite EQsem. destruct IH1 as (stk' & -> & Hstk'). by apply IH.
  - by subst.
Qed.

(** The parser is defined by recursion over a fuel parameter. In the
  completeness proof, we need to predict how much fuel is going to be
  needed in order to prove that enough fuel gives rise to a successful
  parsing.

  To do so, of a dotted parse tree, which is the number of actions
  left to be executed before complete parsing when the current state
  is represented by the dotted parse tree. *)
Fixpoint ptlz_cost {hole_symbs hole_word}
         (ptlz:ptl_zipper hole_symbs hole_word) :=
  match ptlz with
  | Non_terminal_pt_ptlz ptz => ptz_cost ptz
  | Cons_ptl_ptlz pt ptlz' => pt_size pt + ptlz_cost ptlz'
  end
with ptz_cost {hole_symb hole_word} (ptz:pt_zipper hole_symb hole_word) :=
  match ptz with
  | Top_ptz => 0
  | Cons_ptl_ptz ptl ptlz' => 1 + ptlz_cost ptlz'
  end.

Definition ptd_cost (ptd:pt_dot) :=
  match ptd with
  | Reduce_ptd ptl ptz => ptz_cost ptz
  | Shift_ptd _ ptl ptlz => 1 + ptlz_cost ptlz
  end.

Lemma ptd_cost_build_from_pt {symb word}
      (pt : parse_tree symb word) (ptz : pt_zipper symb word) :
  pt_size pt + ptz_cost ptz = S (ptd_cost (build_pt_dot_from_pt pt ptz))
with ptd_cost_build_from_pt_rec {symbs word}
     (ptl : parse_tree_list symbs word) (ptlz : ptl_zipper symbs word)
     Hsymbs :
  ptl_size ptl + ptlz_cost ptlz = ptd_cost (build_pt_dot_from_pt_rec ptl Hsymbs ptlz).
Proof.
  - destruct pt as [tok|prod word ptl']=>/=.
    + revert ptz. generalize [tok]. generalize (token_sem tok). generalize I.
      change True with (match T (token_term tok) with T _ => True | NT _ => False end) at 1.
      generalize (T (token_term tok)) => symb HT sem word ptz. by destruct ptz.
    + match goal with
      | |- context [match ?X with Some H => _ | None => _ end] => destruct X eqn:EQ
      end.
      * rewrite -ptd_cost_build_from_pt_rec /= plus_n_Sm //.
      * simpl. by destruct ptl'.
  - destruct ptl as [|?? ptl ?? pt]; [contradiction|].
    specialize (ptd_cost_build_from_pt_rec _ _ ptl). destruct ptl.
    + apply eq_add_S. rewrite -ptd_cost_build_from_pt /=. ring.
    + rewrite -ptd_cost_build_from_pt_rec //=. ring.
Qed.

Lemma ptd_cost_build_from_ptl {symbs word}
      (ptl : parse_tree_list symbs word) (ptlz : ptl_zipper symbs word) :
  ptlz_cost ptlz = ptd_cost (build_pt_dot_from_ptl ptl ptlz).
Proof.
  destruct ptlz=>//. apply eq_add_S. rewrite -ptd_cost_build_from_pt /=. ring.
Qed.

Lemma next_ptd_cost ptd:
  match next_ptd ptd with
  | None => ptd_cost ptd = 0
  | Some ptd' => ptd_cost ptd = S (ptd_cost ptd')
  end.
Proof.
  destruct ptd as [prod word ptl ptz|tok symbq wordq ptl ptlz] =>/=.
  - generalize (Non_terminal_pt prod ptl). clear ptl.
    destruct ptz as [|?? ptl ?? ptlz]=>// pt. by rewrite -ptd_cost_build_from_ptl.
  - by rewrite -ptd_cost_build_from_ptl.
Qed.

Lemma next_ptd_iter_cost ptd log_n_steps :
  match next_ptd_iter ptd log_n_steps with
  | None => ptd_cost ptd < 2^log_n_steps
  | Some ptd' => ptd_cost ptd = 2^log_n_steps + ptd_cost ptd'
  end.
Proof.
  revert ptd. induction log_n_steps as [|log_n_steps IH]=>ptd /=.
  - assert (Hptd := next_ptd_cost ptd). destruct next_ptd=>//. by rewrite Hptd.
  - rewrite Nat.add_0_r. assert (IH1 := IH ptd). destruct next_ptd_iter as [ptd'|].
    + specialize (IH ptd'). destruct next_ptd_iter as [ptd''|].
      * by rewrite IH1 IH -!plus_assoc.
      * rewrite IH1. by apply plus_lt_compat_l.
    + by apply lt_plus_trans.
Qed.

(** We now prove the top-level parsing function. The only thing that
  is left to be done is the initialization. To do so, we define the
  initial dotted parse tree, depending on a full (top-level) parse tree. *)

Variable full_pt : parse_tree (NT (start_nt init)) full_word.

Theorem parse_complete log_n_steps:
  match parse safe init (full_word ++ buffer_end) log_n_steps with
  | Parsed_pr sem buff =>
    sem = pt_sem full_pt /\ buff = buffer_end /\ pt_size full_pt <= 2^log_n_steps
  | Timeout_pr => 2^log_n_steps < pt_size full_pt
  | Fail_pr => False
  end.
Proof.
  assert (Hstk : ptd_stack_compat (build_pt_dot_from_pt full_pt Top_ptz) []) by
      by apply ptd_stack_compat_build_from_pt.
  unfold parse.
  assert (Hparse := parse_fix_next_ptd_iter _ _ log_n_steps (parse_subproof init) Hstk).
  rewrite -ptd_buffer_build_from_pt -sem_build_from_pt /= in Hparse.
  assert (Hcost := next_ptd_iter_cost (build_pt_dot_from_pt full_pt Top_ptz) log_n_steps).
  destruct next_ptd_iter.
  - destruct Hparse as (? & -> & ?). apply (f_equal S) in Hcost.
    rewrite -ptd_cost_build_from_pt Nat.add_0_r in Hcost. rewrite Hcost.
    apply le_lt_n_Sm, le_plus_l.
  - rewrite Hparse. split; [|split]=>//. apply lt_le_S in Hcost.
    by rewrite -ptd_cost_build_from_pt Nat.add_0_r in Hcost.
Qed.

End Completeness_Proof.

End Make.

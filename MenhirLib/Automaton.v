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

Require Grammar.
Require Export Alphabet.
From Coq Require Import Orders.
From Coq Require Export List Syntax.

Module Type AutInit.
  (** The grammar of the automaton. **)
  Declare Module Gram:Grammar.T.
  Export Gram.

  (** The set of non initial state is considered as an alphabet. **)
  Parameter noninitstate : Type.
  Declare Instance NonInitStateAlph : Alphabet noninitstate.

  Parameter initstate : Type.
  Declare Instance InitStateAlph : Alphabet initstate.

  (** When we are at this state, we know that this symbol is the top of the
     stack. **)
  Parameter last_symb_of_non_init_state: noninitstate -> symbol.
End AutInit.

Module Types(Import Init:AutInit).
  (** In many ways, the behaviour of the initial state is different from the
     behaviour of the other states. So we have chosen to explicitaly separate
     them: the user has to provide the type of non initial states. **)
  Inductive state :=
    | Init: initstate -> state
    | Ninit: noninitstate -> state.

  Program Instance StateAlph : Alphabet state :=
    { AlphabetComparable := {| compare := fun x y =>
        match x, y return comparison with
          | Init _, Ninit _ => Lt
          | Init x, Init y => compare x y
          | Ninit _, Init _ => Gt
          | Ninit x, Ninit y => compare x y
        end |};
      AlphabetFinite := {| all_list := map Init all_list ++ map Ninit all_list |} }.
  Local Obligation Tactic := intros.
  Next Obligation.
  destruct x, y; intuition; apply compare_antisym.
  Qed.
  Next Obligation.
  destruct x, y, z; intuition.
  apply (compare_trans _ i0); intuition.
  congruence.
  congruence.
  apply (compare_trans _ n0); intuition.
  Qed.
  Next Obligation.
  intros x y.
  destruct x, y; intuition; try discriminate.
  rewrite (compare_eq i i0); intuition.
  rewrite (compare_eq n n0); intuition.
  Qed.
  Next Obligation.
  apply in_or_app; destruct x; intuition;
    [left|right]; apply in_map; apply  all_list_forall.
  Qed.

  Coercion Ninit : noninitstate >-> state.
  Coercion Init : initstate >-> state.

  (** For an LR automaton, there are four kind of actions that can be done at a
     given state:
       - Shifting, that is reading a token and putting it into the stack,
       - Reducing a production, that is popping the right hand side of the
          production from the stack, and pushing the left hand side,
       - Failing
       - Accepting the word (special case of reduction)

     As in the menhir parser generator, we do not want our parser to read after
     the end of stream. That means that once the parser has read a word in the
     grammar language, it should stop without peeking the input stream. So, for
     the automaton to be complete, the grammar must be particular: if a word is
     in its language, then it is not a prefix of an other word of the language
     (otherwise, menhir reports an end of stream conflict).

     As a consequence of that, there is two notions of action: the first one is
     an action performed before having read the stream, the second one is after
  **)

  Inductive lookahead_action (term:terminal) :=
  | Shift_act: forall s:noninitstate,
                 T term = last_symb_of_non_init_state s -> lookahead_action term
  | Reduce_act: production -> lookahead_action term
  | Fail_act: lookahead_action term.
  Arguments Shift_act {term}.
  Arguments Reduce_act {term}.
  Arguments Fail_act {term}.

  Inductive action :=
  | Default_reduce_act: production -> action
  | Lookahead_act : (forall term:terminal, lookahead_action term) -> action.

  (** Types used for the annotations of the automaton. **)

  (** An item is a part of the annotations given to the validator.
     It is acually a set of LR(1) items sharing the same core. It is needed
     to validate completeness. **)
  Record item := {
  (** The pseudo-production of the item. **)
    prod_item: production;

  (** The position of the dot. **)
    dot_pos_item: nat;

  (** The lookahead symbol of the item. We are using a list, so we can store
     together multiple LR(1) items sharing the same core. **)
    lookaheads_item: list terminal
  }.
End Types.

Module Type T.
  Include AutInit <+ Types.
  Module Export GramDefs := Grammar.Defs Gram.

  (** For each initial state, the non terminal it recognizes. **)
  Parameter start_nt: initstate -> nonterminal.

  (** The action table maps a state to either a map terminal -> action. **)
  Parameter action_table:
    state -> action.
  (** The goto table of an LR(1) automaton. **)
  Parameter goto_table: state -> forall nt:nonterminal,
    option { s:noninitstate | NT nt = last_symb_of_non_init_state s }.

  (** Some annotations on the automaton to help the validation. **)

  (** When we are at this state, we know that these symbols are just below
     the top of the stack. The list is ordered such that the head correspond
     to the (almost) top of the stack. **)
  Parameter past_symb_of_non_init_state: noninitstate -> list symbol.

  (** When we are at this state, the (strictly) previous states verify these
     predicates. **)
  Parameter past_state_of_non_init_state: noninitstate -> list (state -> bool).

  (** The items of the state. **)
  Parameter items_of_state: state -> list item.

  (** The nullable predicate for non terminals :
     true if and only if the symbol produces the empty string **)
  Parameter nullable_nterm: nonterminal -> bool.

  (** The first predicates for non terminals, symbols or words of symbols. A
     terminal is in the returned list if, and only if the parameter produces a
     word that begins with the given terminal **)
  Parameter first_nterm: nonterminal -> list terminal.
End T.

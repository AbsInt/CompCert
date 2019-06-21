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

From Coq Require Import List Syntax Derive.
From Coq.ssr Require Import ssreflect.
Require Automaton.
Require Import Alphabet Validator_classes.

Module Make(Import A:Automaton.T).

(** We instantiate some sets/map. **)
Module TerminalComparableM <: ComparableM.
  Definition t := terminal.
  Instance tComparable : Comparable t := _.
End TerminalComparableM.
Module TerminalOrderedType := OrderedType_from_ComparableM TerminalComparableM.
Module StateProdPosComparableM <: ComparableM.
  Definition t := (state*production*nat)%type.
  Instance tComparable : Comparable t := _.
End StateProdPosComparableM.
Module StateProdPosOrderedType :=
  OrderedType_from_ComparableM StateProdPosComparableM.

Module TerminalSet := FSetAVL.Make TerminalOrderedType.
Module StateProdPosMap := FMapAVL.Make StateProdPosOrderedType.

(** Nullable predicate for symbols and list of symbols. **)
Definition nullable_symb (symbol:symbol) :=
  match symbol with
  | NT nt => nullable_nterm nt
  | _ => false
  end.

Definition nullable_word (word:list symbol) :=
  forallb nullable_symb word.

(** First predicate for non terminal, symbols and list of symbols, given as FSets. **)
Definition first_nterm_set (nterm:nonterminal) :=
  fold_left (fun acc t => TerminalSet.add t acc)
    (first_nterm nterm) TerminalSet.empty.

Definition first_symb_set (symbol:symbol) :=
  match symbol with
  | NT nt => first_nterm_set nt
  | T t => TerminalSet.singleton t
  end.

Fixpoint first_word_set (word:list symbol) :=
  match word with
  | [] => TerminalSet.empty
  | t::q =>
    if nullable_symb t then
      TerminalSet.union (first_symb_set t) (first_word_set q)
    else
      first_symb_set t
  end.

(** Small helper for finding the part of an item that is after the dot. **)
Definition future_of_prod prod dot_pos : list symbol :=
  (fix loop n lst :=
    match n with
    | O => lst
    | S x => match loop x lst with [] => [] | _::q => q end
    end)
  dot_pos (rev' (prod_rhs_rev prod)).

(** We build a fast map to store all the items of all the states. **)
Definition items_map (_:unit): StateProdPosMap.t TerminalSet.t :=
  fold_left (fun acc state =>
    fold_left (fun acc item =>
      let key := (state, prod_item item, dot_pos_item item) in
        let data := fold_left (fun acc t => TerminalSet.add t acc)
          (lookaheads_item item) TerminalSet.empty
        in
        let old :=
          match StateProdPosMap.find key acc with
          | Some x => x | None => TerminalSet.empty
          end
        in
        StateProdPosMap.add key (TerminalSet.union data old) acc
    ) (items_of_state state) acc
  ) all_list (StateProdPosMap.empty TerminalSet.t).

(** We need to avoid computing items_map each time we need it. To that
  purpose, we declare a typeclass specifying that some map is equal to
  items_map. *)
Class IsItemsMap m := is_items_map : m = items_map ().

(** Accessor. **)
Definition find_items_map items_map state prod dot_pos : TerminalSet.t :=
  match StateProdPosMap.find (state, prod, dot_pos) items_map with
  | None => TerminalSet.empty
  | Some x => x
  end.

Definition state_has_future state prod (fut:list symbol) (lookahead:terminal) :=
  exists dot_pos:nat,
    fut = future_of_prod prod dot_pos /\
    TerminalSet.In lookahead (find_items_map (items_map ()) state prod dot_pos).

(** Iterator over items. **)
Definition forallb_items items_map (P:state -> production -> nat -> TerminalSet.t -> bool): bool:=
  StateProdPosMap.fold (fun key set acc =>
    match key with (st, p, pos) => (acc && P st p pos set)%bool end
  ) items_map true.

(** Typeclass instances for synthetizing the validator. *)

Instance is_validator_subset S1 S2 :
  IsValidator (TerminalSet.Subset S1 S2) (TerminalSet.subset S1 S2).
Proof. intros ?. by apply TerminalSet.subset_2. Qed.

(* While the specification of the validator always quantify over
   possible lookahead tokens individually, the validator usually
   handles lookahead sets directly instead, for better performances.

   For instance, the validator for [state_has_future], which speaks
   about one single lookahead token is a subset operation:
*)
Lemma is_validator_state_has_future_subset st prod pos lookahead lset im fut :
  TerminalSet.In lookahead lset ->
  fut = future_of_prod prod pos ->
  IsItemsMap im ->
  IsValidator (state_has_future st prod fut lookahead)
              (TerminalSet.subset lset (find_items_map im st prod pos)).
Proof.
  intros ? -> -> HSS%TerminalSet.subset_2. exists pos. split=>//. by apply HSS.
Qed.
(* We do not declare this lemma as an instance, and use [Hint Extern]
   instead, because the typeclass mechanism has trouble instantiating
   some evars if we do not explicitely call [eassumption]. *)
Hint Extern 2 (IsValidator (state_has_future _ _ _ _) _) =>
  eapply is_validator_state_has_future_subset; [eassumption|eassumption || reflexivity|]
: typeclass_instances.

(* As said previously, we manipulate lookahead terminal sets instead of
  lookahead individually. Hence, when we quantify over a lookahead set
  in the specification, we do not do anything in the executable
  validator.

  This instance is used for [non_terminal_closed]. *)
Instance is_validator_forall_lookahead_set lset P b:
  (forall lookahead, TerminalSet.In lookahead lset -> IsValidator (P lookahead) b) ->
  IsValidator (forall lookahead, TerminalSet.In lookahead lset -> P lookahead) b.
Proof. unfold IsValidator. firstorder. Qed.


(* Dually, we sometimes still need to explicitelly iterate over a
  lookahead set. This is what this lemma allows.
  Used only in [end_reduce]. *)
Lemma is_validator_iterate_lset P b lookahead lset :
  TerminalSet.In lookahead lset ->
  IsValidator P (b lookahead) ->
  IsValidator P (TerminalSet.fold (fun lookahead acc =>
    if acc then b lookahead else false) lset true).
Proof.
  intros Hlset%TerminalSet.elements_1 Hval Val. apply Hval.
  revert Val. rewrite TerminalSet.fold_1. generalize true at 1. clear -Hlset.
  induction Hlset as [? l <-%compare_eq|? l ? IH]=> /= b' Val.
  - destruct (b lookahead). by destruct b'. exfalso. by induction l; destruct b'.
  - eauto.
Qed.
Hint Extern 100 (IsValidator _ _) =>
  match goal with
  | H : TerminalSet.In ?lookahead ?lset |- _ =>
    eapply (is_validator_iterate_lset _ (fun lookahead => _) _ _ H); clear H
  end
: typeclass_instances.

(* We often quantify over all the items of all the states of the
   automaton. This lemma and the accompanying [Hint Resolve]
   declaration allow generating the corresponding executable
   validator.

   Note that it turns out that, in all the uses of this pattern, the
   first thing we do for each item is pattern-matching over the
   future. This lemma also embbed this pattern-matching, which makes
   it possible to get the hypothesis [fut' = future_of_prod prod (S pos)]
   in the non-nil branch.

   Moreover, note, again, that while the specification quantifies over
   lookahead terminals individually, the code provides lookahead sets
   instead. *)
Lemma is_validator_forall_items P1 b1 P2 b2 im :
  IsItemsMap im ->

  (forall st prod lookahead lset pos,
      TerminalSet.In lookahead lset ->
      [] = future_of_prod prod pos ->
      IsValidator (P1 st prod lookahead) (b1 st prod pos lset)) ->

  (forall st prod pos lookahead lset s fut',
      TerminalSet.In lookahead lset ->
      fut' = future_of_prod prod (S pos) ->
      IsValidator (P2 st prod lookahead s fut') (b2 st prod pos lset s fut')) ->

  IsValidator (forall st prod fut lookahead,
                  state_has_future st prod fut lookahead ->
                  match fut with
                  | [] => P1 st prod lookahead
                  | s :: fut' => P2 st prod lookahead s fut'
                  end)
              (forallb_items im (fun st prod pos lset =>
                 match future_of_prod prod pos with
                 | [] => b1 st prod pos lset
                 | s :: fut' => b2 st prod pos lset s fut'
                 end)).
Proof.
  intros -> Hval1 Hval2 Val st prod fut lookahead (pos & -> & Hlookahead).
  rewrite /forallb_items StateProdPosMap.fold_1 in Val.
  assert (match future_of_prod prod pos with
          | [] => b1 st prod pos (find_items_map (items_map ()) st prod pos)
          | s :: fut' => b2 st prod pos (find_items_map (items_map ()) st prod pos) s fut'
          end = true).
  - unfold find_items_map in *.
    assert (Hfind := @StateProdPosMap.find_2 _ (items_map ()) (st, prod, pos)).
    destruct StateProdPosMap.find as [lset|]; [|by edestruct (TerminalSet.empty_1); eauto].
    specialize (Hfind _ eq_refl). apply StateProdPosMap.elements_1 in Hfind.
    revert Val. generalize true at 1.
    induction Hfind as [[? ?] l [?%compare_eq ?]|??? IH]=>?.
    + simpl in *; subst.
      match goal with |- _ -> ?X = true => destruct X end; [done|].
      rewrite Bool.andb_false_r. clear. induction l as [|[[[??]?]?] l IH]=>//.
    + apply IH.
  - destruct future_of_prod eqn:EQ. by eapply Hval1; eauto.
    eapply Hval2 with (pos := pos); eauto; [].
    revert EQ. unfold future_of_prod=>-> //.
Qed.
(* We need a hint for expplicitely instantiating b1 and b2 with lambdas. *)
Hint Extern 0 (IsValidator
                 (forall st prod fut lookahead,
                     state_has_future st prod fut lookahead -> _)
                 _) =>
    eapply (is_validator_forall_items _ (fun st prod pos lset => _)
                                      _ (fun st prod pos lset s fut' => _))
  : typeclass_instances.

(* Used in [start_future] only. *)
Instance is_validator_forall_state_has_future im st prod :
  IsItemsMap im ->
  IsValidator
    (forall look, state_has_future st prod (rev' (prod_rhs_rev prod)) look)
    (let lookaheads := find_items_map im st prod 0 in
     forallb (fun t => TerminalSet.mem t lookaheads) all_list).
Proof.
  move=> -> /forallb_forall Val look.
  specialize (Val look (all_list_forall _)). exists 0. split=>//.
  by apply TerminalSet.mem_2.
Qed.

(** * Validation for completeness **)

(** The nullable predicate is a fixpoint : it is correct. **)
Definition nullable_stable :=
  forall p:production,
    if nullable_word (prod_rhs_rev p) then
      nullable_nterm (prod_lhs p) = true
    else True.

(** The first predicate is a fixpoint : it is correct. **)
Definition first_stable:=
  forall (p:production),
    TerminalSet.Subset (first_word_set (rev' (prod_rhs_rev p)))
                       (first_nterm_set (prod_lhs p)).

(** The initial state has all the S=>.u items, where S is the start non-terminal **)
Definition start_future :=
  forall (init:initstate) (p:production),
    prod_lhs p = start_nt init ->
  forall (t:terminal),
    state_has_future init p (rev' (prod_rhs_rev p)) t.

(** If a state contains an item of the form A->_.av[[b]], where a is a
    terminal, then reading an a does a [Shift_act], to a state containing
    an item of the form A->_.v[[b]]. **)
Definition terminal_shift :=
  forall (s1:state) prod fut lookahead,
    state_has_future s1 prod fut lookahead ->
    match fut with
    | T t::q =>
      match action_table s1 with
      | Lookahead_act awp =>
        match awp t with
        | Shift_act s2 _ =>
          state_has_future s2 prod q lookahead
        | _ => False
        end
      | _ => False
      end
    | _ => True
    end.

(** If a state contains an item of the form A->_.[[a]], then either we do a
    [Default_reduce_act] of the corresponding production, either a is a
    terminal (ie. there is a lookahead terminal), and reading a does a
    [Reduce_act] of the corresponding production. **)
Definition end_reduce :=
  forall (s:state) prod fut lookahead,
    state_has_future s prod fut lookahead ->
    match fut with
    | [] =>
      match action_table s with
      | Default_reduce_act p => p = prod
      | Lookahead_act awt =>
        match awt lookahead with
        | Reduce_act p => p = prod
        | _ => False
        end
      end
    | _ => True
    end.

Definition is_end_reduce items_map :=
  forallb_items items_map (fun s prod pos lset =>
    match future_of_prod prod pos with
    | [] =>
      match action_table s with
      | Default_reduce_act p => compare_eqb p prod
      | Lookahead_act awt =>
        TerminalSet.fold (fun lookahead acc =>
          match awt lookahead with
          | Reduce_act p => (acc && compare_eqb p prod)%bool
          | _ => false
          end) lset true
      end
    | _ => true
    end).

(** If a state contains an item of the form A->_.Bv[[b]], where B is a
    non terminal, then the goto table says we have to go to a state containing
    an item of the form A->_.v[[b]]. **)
Definition non_terminal_goto :=
  forall (s1:state) prod fut lookahead,
    state_has_future s1 prod fut lookahead ->
    match fut with
    | NT nt::q =>
      match goto_table s1 nt with
      | Some (exist _ s2 _) =>
        state_has_future s2 prod q lookahead
      | None => False
      end
    | _ => True
    end.

Definition start_goto :=
  forall (init:initstate),
    match goto_table init (start_nt init) with
    | None => True
    | Some _ => False
    end.

(** Closure property of item sets : if a state contains an item of the form
    A->_.Bv[[b]], then for each production B->u and each terminal a of
    first(vb), the state contains an item of the form B->_.u[[a]] **)
Definition non_terminal_closed :=
  forall s1 prod fut lookahead,
    state_has_future s1 prod fut lookahead ->
    match fut with
    | NT nt::q =>
      forall p, prod_lhs p = nt ->
        (if nullable_word q then
           state_has_future s1 p (future_of_prod p 0) lookahead
         else True) /\
        (forall lookahead2,
           TerminalSet.In lookahead2 (first_word_set q) ->
             state_has_future s1 p (future_of_prod p 0) lookahead2)
      | _ => True
    end.

(** The automaton is complete **)
Definition complete :=
  nullable_stable /\ first_stable /\ start_future /\ terminal_shift
  /\ end_reduce /\ non_terminal_goto /\ start_goto /\ non_terminal_closed.

Derive is_complete_0
SuchThat (forall im, IsItemsMap im -> IsValidator complete (is_complete_0 im))
As complete_0_is_validator.
Proof. intros im. subst is_complete_0. instantiate (1:=fun im => _). apply _. Qed.

Definition is_complete (_:unit) := is_complete_0 (items_map ()).
Lemma complete_is_validator : IsValidator complete (is_complete ()).
Proof. by apply complete_0_is_validator. Qed.

End Make.

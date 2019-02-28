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

Require Automaton.
Require Import Alphabet.
Require Import List.
Require Import Syntax.

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

Lemma forallb_items_spec :
  forall p, forallb_items (items_map ()) p = true ->
  forall st prod fut lookahead, state_has_future st prod fut lookahead ->
  forall P:state -> production -> list symbol -> terminal -> Prop,
  (forall st prod pos set lookahead,
    TerminalSet.In lookahead set -> p st prod pos set = true ->
      P st prod (future_of_prod prod pos) lookahead) ->
   P st prod fut lookahead.
Proof.
intros.
unfold forallb_items in H.
rewrite StateProdPosMap.fold_1 in H.
destruct H0; destruct H0.
specialize (H1 st prod x _ _ H2).
destruct H0.
apply H1.
unfold find_items_map in *.
pose proof (@StateProdPosMap.find_2 _ (items_map ()) (st, prod, x)).
destruct (StateProdPosMap.find (st, prod, x) (items_map ())); [ |destruct (TerminalSet.empty_1 H2)].
specialize (H0 _ (eq_refl _)).
pose proof (StateProdPosMap.elements_1 H0).
revert H.
generalize true at 1.
induction H3.
destruct H.
destruct y.
simpl in H3; destruct H3.
pose proof (compare_eq (st, prod, x) k H).
destruct H3.
simpl.
generalize (p st prod x t).
induction l; simpl; intros.
rewrite Bool.andb_true_iff in H3.
intuition.
destruct a; destruct k; destruct p0.
simpl in H3.
replace (b0 && b && p s p0 n t0)%bool with (b0 && p s p0 n t0 && b)%bool in H3.
apply (IHl _ _ H3).
destruct b, b0, (p s p0 n t0); reflexivity.
intro.
apply IHInA.
Qed.

(** * Validation for completeness **)

(** The nullable predicate is a fixpoint : it is correct. **)
Definition nullable_stable:=
  forall p:production,
    nullable_word (rev (prod_rhs_rev p)) = true ->
    nullable_nterm (prod_lhs p) = true.

Definition is_nullable_stable (_:unit) :=
  forallb (fun p:production =>
    implb (nullable_word (rev' (prod_rhs_rev p))) (nullable_nterm (prod_lhs p)))
    all_list.

Property is_nullable_stable_correct :
  is_nullable_stable () = true -> nullable_stable.
Proof.
unfold is_nullable_stable, nullable_stable.
intros.
rewrite forallb_forall in H.
specialize (H p (all_list_forall p)).
unfold rev' in H; rewrite <- rev_alt in H.
rewrite H0 in H; intuition.
Qed.

(** The first predicate is a fixpoint : it is correct. **)
Definition first_stable:=
  forall (p:production),
    TerminalSet.Subset (first_word_set (rev (prod_rhs_rev p)))
                       (first_nterm_set (prod_lhs p)).

Definition is_first_stable (_:unit) :=
  forallb (fun p:production =>
    TerminalSet.subset (first_word_set (rev' (prod_rhs_rev p)))
                       (first_nterm_set (prod_lhs p)))
    all_list.

Property is_first_stable_correct :
  is_first_stable () = true -> first_stable.
Proof.
unfold is_first_stable, first_stable.
intros.
rewrite forallb_forall in H.
specialize (H p (all_list_forall p)).
unfold rev' in H; rewrite <- rev_alt in H.
apply TerminalSet.subset_2; intuition.
Qed.

(** The initial state has all the S=>.u items, where S is the start non-terminal **)
Definition start_future :=
  forall (init:initstate) (t:terminal) (p:production),
    prod_lhs p = start_nt init ->
    state_has_future init p (rev (prod_rhs_rev p)) t.

Definition is_start_future items_map :=
  forallb (fun init =>
    forallb (fun prod =>
      if compare_eqb (prod_lhs prod) (start_nt init) then
        let lookaheads := find_items_map items_map init prod 0 in
          forallb (fun t => TerminalSet.mem t lookaheads) all_list
        else
          true) all_list) all_list.

Property is_start_future_correct :
  is_start_future (items_map ()) = true -> start_future.
Proof.
unfold is_start_future, start_future.
intros.
rewrite forallb_forall in H.
specialize (H init (all_list_forall _)).
rewrite forallb_forall in H.
specialize (H p (all_list_forall _)).
rewrite <- compare_eqb_iff in H0.
rewrite H0 in H.
rewrite forallb_forall in H.
specialize (H t (all_list_forall _)).
exists 0.
split.
apply rev_alt.
apply TerminalSet.mem_2; eauto.
Qed.

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

Definition is_terminal_shift items_map :=
  forallb_items items_map (fun s1 prod pos lset =>
    match future_of_prod prod pos with
      | T t::_ =>
        match action_table s1 with
          | Lookahead_act awp =>
            match awp t with
              | Shift_act s2 _ =>
                TerminalSet.subset lset (find_items_map items_map s2 prod (S pos))
              | _ => false
            end
          | _ => false
        end
      | _ => true
    end).

Property is_terminal_shift_correct :
  is_terminal_shift (items_map ()) = true -> terminal_shift.
Proof.
unfold is_terminal_shift, terminal_shift.
intros.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun _ _ fut look => _)).
intros.
destruct (future_of_prod prod0 pos) as [|[]] eqn:?; intuition.
destruct (action_table st); intuition.
destruct (l0 t); intuition.
exists (S pos).
split.
unfold future_of_prod in *.
rewrite Heql; reflexivity.
apply (TerminalSet.subset_2 H2); intuition.
Qed.

(** If a state contains an item of the form A->_.[[a]], then either we do a
    [Default_reduce_act] of the corresponding production, either a is a
    terminal (ie. there is a lookahead terminal), and reading a does a
    [Reduce_act] of the corresponding production. **)
Definition end_reduce :=
  forall (s:state) prod fut lookahead,
    state_has_future s prod fut lookahead ->
    fut = [] ->
    match action_table s with
      | Default_reduce_act p => p = prod
      | Lookahead_act awt =>
        match awt lookahead with
          | Reduce_act p => p = prod
          | _ => False
        end
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

Property is_end_reduce_correct :
  is_end_reduce (items_map ()) = true -> end_reduce.
Proof.
unfold is_end_reduce, end_reduce.
intros.
revert H1.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun st prod fut look => _ ->
                                            match action_table st with
                                              | Default_reduce_act p => p = prod
                                              | _ => _
                                            end)).
intros.
rewrite H3 in H2.
destruct (action_table st); intuition.
apply compare_eqb_iff; intuition.
rewrite TerminalSet.fold_1 in H2.
revert H2.
generalize true at 1.
pose proof (TerminalSet.elements_1 H1).
induction H2.
pose proof (compare_eq _ _ H2).
destruct H4.
simpl.
assert (fold_left
     (fun (a : bool) (e : TerminalSet.elt) =>
       match l e with
         | Shift_act _ _ => false
         | Reduce_act p => (a && compare_eqb p prod0)%bool
         | Fail_act => false
       end) l0 false = true -> False).
induction l0; intuition.
apply IHl0.
simpl in H4.
destruct (l a); intuition.
destruct (l lookahead0); intuition.
apply compare_eqb_iff.
destruct (compare_eqb p prod0); intuition.
destruct b; intuition.
simpl; intros.
eapply IHInA; eauto.
Qed.

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
          | None =>
            forall prod fut lookahead,
            state_has_future s1 prod fut lookahead ->
            match fut with
              | NT nt'::_ => nt <> nt'
              | _ => True
            end
        end
      | _ => True
    end.

Definition is_non_terminal_goto items_map :=
  forallb_items items_map (fun s1 prod pos lset =>
    match future_of_prod prod pos with
      | NT nt::_ =>
        match goto_table s1 nt with
          | Some (exist _ s2 _) =>
            TerminalSet.subset lset (find_items_map items_map s2 prod (S pos))
          | None => forallb_items items_map (fun s1' prod' pos' _ =>
            (implb (compare_eqb s1 s1')
            match future_of_prod prod' pos' with
              | NT nt' :: _ => negb (compare_eqb nt nt')
              | _ => true
            end)%bool)
        end
      | _ => true
    end).

Property is_non_terminal_goto_correct :
  is_non_terminal_goto (items_map ()) = true -> non_terminal_goto.
Proof.
unfold is_non_terminal_goto, non_terminal_goto.
intros.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun st prod fut look =>
                                            match fut with
                                              | NT nt :: q =>
                                                match goto_table st nt with
                                                  | Some _ => _
                                                  | None =>
                                                    forall p f l, state_has_future st p f l -> (_:Prop)
                                                end
                                              | _ => _
                                            end)).
intros.
destruct (future_of_prod prod0 pos) as [|[]] eqn:?; intuition.
destruct (goto_table st n) as [[]|].
exists (S pos).
split.
unfold future_of_prod in *.
rewrite Heql; reflexivity.
apply (TerminalSet.subset_2 H2); intuition.
intros.
remember st in H2; revert Heqs.
apply (forallb_items_spec _ H2 _ _ _ _ H3 (fun st' prod fut look => s = st' -> match fut return Prop with [] => _ | _ => _ end)); intros.
rewrite <- compare_eqb_iff in H6; rewrite H6 in H5.
destruct (future_of_prod prod1 pos0) as [|[]]; intuition.
rewrite <- compare_eqb_iff in H7; rewrite H7 in H5.
discriminate.
Qed.

Definition start_goto :=
  forall (init:initstate), goto_table init (start_nt init) = None.

Definition is_start_goto (_:unit) :=
  forallb (fun (init:initstate) =>
    match goto_table init (start_nt init) with
      | Some _ => false
      | None => true
    end) all_list.

Definition is_start_goto_correct:
  is_start_goto () = true -> start_goto.
Proof.
unfold is_start_goto, start_goto.
rewrite forallb_forall.
intros.
specialize (H init (all_list_forall _)).
destruct (goto_table init (start_nt init)); congruence.
Qed.

(** Closure property of item sets : if a state contains an item of the form
    A->_.Bv[[b]], then for each production B->u and each terminal a of
    first(vb), the state contains an item of the form B->_.u[[a]] **)
Definition non_terminal_closed :=
  forall (s1:state) prod fut lookahead,
    state_has_future s1 prod fut lookahead ->
    match fut with
      | NT nt::q =>
        forall (p:production) (lookahead2:terminal),
          prod_lhs p = nt ->
          TerminalSet.In lookahead2 (first_word_set q) \/
          lookahead2 = lookahead /\ nullable_word q = true ->
            state_has_future s1 p (rev (prod_rhs_rev p)) lookahead2
      | _ => True
    end.

Definition is_non_terminal_closed items_map :=
  forallb_items items_map (fun s1 prod pos lset =>
    match future_of_prod prod pos with
        | NT nt::q =>
          forallb (fun p =>
            if compare_eqb (prod_lhs p) nt then
              let lookaheads := find_items_map items_map s1 p 0 in
              (implb (nullable_word q) (TerminalSet.subset lset lookaheads)) &&
              TerminalSet.subset (first_word_set q) lookaheads
            else true
          )%bool all_list
        | _ => true
    end).

Property is_non_terminal_closed_correct:
  is_non_terminal_closed (items_map ()) = true -> non_terminal_closed.
Proof.
unfold is_non_terminal_closed, non_terminal_closed.
intros.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun st prod fut look =>
                                            match fut with
                                              | NT nt :: q => forall p l, _ -> _ -> state_has_future st _ _ _
                                              | _ => _
                                            end)).
intros.
destruct (future_of_prod prod0 pos); intuition.
destruct s; eauto; intros.
rewrite forallb_forall in H2.
specialize (H2 p (all_list_forall p)).
rewrite <- compare_eqb_iff in H3.
rewrite H3 in H2.
rewrite Bool.andb_true_iff in H2.
destruct H2.
exists 0.
split.
apply rev_alt.
destruct H4 as [|[]]; subst.
apply (TerminalSet.subset_2 H5); intuition.
rewrite H6 in H2.
apply (TerminalSet.subset_2 H2); intuition.
Qed.

(** The automaton is complete **)
Definition complete :=
  nullable_stable /\ first_stable /\ start_future /\ terminal_shift
  /\ end_reduce /\ non_terminal_goto /\ start_goto /\ non_terminal_closed.

Definition is_complete (_:unit) :=
  let items_map := items_map () in
  (is_nullable_stable () && is_first_stable () && is_start_future items_map &&
    is_terminal_shift items_map && is_end_reduce items_map && is_start_goto () &&
    is_non_terminal_goto items_map && is_non_terminal_closed items_map)%bool.

Property is_complete_correct:
  is_complete () = true -> complete.
Proof.
unfold is_complete, complete.
repeat rewrite Bool.andb_true_iff.
intuition.
apply is_nullable_stable_correct; assumption.
apply is_first_stable_correct; assumption.
apply is_start_future_correct; assumption.
apply is_terminal_shift_correct; assumption.
apply is_end_reduce_correct; assumption.
apply is_non_terminal_goto_correct; assumption.
apply is_start_goto_correct; assumption.
apply is_non_terminal_closed_correct; assumption.
Qed.

End Make.

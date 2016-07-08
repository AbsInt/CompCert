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

(** The singleton predicate for states **)
Definition singleton_state_pred (state:state) :=
  (fun state' => match compare state state' with Eq => true |_ => false end).

(** [past_state_of_non_init_state], extended for all states. **)
Definition past_state_of_state (state:state) :=
  match state with
    | Init _ => []
    | Ninit nis => past_state_of_non_init_state nis
  end.

(** Concatenations of last and past **)
Definition head_symbs_of_state (state:state) :=
  match state with
    | Init _ => []
    | Ninit s =>
      last_symb_of_non_init_state s::past_symb_of_non_init_state s
  end.
Definition head_states_of_state (state:state) :=
  singleton_state_pred state::past_state_of_state state.

(** * Validation for correctness **)

(** Prefix predicate between two lists of symbols. **)
Inductive prefix: list symbol -> list symbol -> Prop :=
  | prefix_nil: forall l, prefix [] l
  | prefix_cons: forall l1 l2 x, prefix l1 l2 -> prefix (x::l1) (x::l2).

Fixpoint is_prefix (l1 l2:list symbol):=
  match l1, l2 with
    | [], _ => true
    | t1::q1, t2::q2 => (compare_eqb t1 t2 && is_prefix q1 q2)%bool
    | _::_, [] => false
  end.

Property is_prefix_correct (l1 l2:list symbol):
  is_prefix l1 l2 = true -> prefix l1 l2.
Proof.
revert l2.
induction l1; intros.
apply prefix_nil.
unfold is_prefix in H.
destruct l2; intuition; try discriminate.
rewrite Bool.andb_true_iff in H.
destruct H.
rewrite compare_eqb_iff in H.
destruct H.
apply prefix_cons.
apply IHl1; intuition.
Qed.

(** If we shift, then the known top symbols of the destination state is
    a prefix of the known top symbols of the source state, with the new
    symbol added. **)
Definition shift_head_symbs :=
  forall s,
    match action_table s with
      | Lookahead_act awp =>
        forall t, match awp t with
          | Shift_act s2 _ =>
            prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
          | _ => True
        end
      | _ => True
    end.

Definition is_shift_head_symbs (_:unit) :=
  forallb (fun s:state =>
    match action_table s with
      | Lookahead_act awp =>
        forallb (fun t =>
          match awp t with
            | Shift_act s2 _ =>
              is_prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
            | _ => true
          end)
          all_list
      | _ => true
    end)
    all_list.

Property is_shift_head_symbs_correct:
  is_shift_head_symbs () = true -> shift_head_symbs.
Proof.
unfold is_shift_head_symbs, shift_head_symbs.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
destruct (action_table s); intuition.
rewrite forallb_forall in H.
specialize (H t (all_list_forall t)).
destruct (l t); intuition.
apply is_prefix_correct; intuition.
Qed.

(** When a goto happens, then the known top symbols of the destination state
    is a prefix of the known top symbols of the source state, with the new
    symbol added. **)
Definition goto_head_symbs :=
  forall s nt,
    match goto_table s nt with
      | Some (exist _ s2 _) =>
        prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
      | None => True
    end.

Definition is_goto_head_symbs (_:unit) :=
  forallb (fun s:state =>
    forallb (fun nt =>
      match goto_table s nt with
        | Some (exist _ s2 _) =>
          is_prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
        | None => true
      end)
      all_list)
    all_list.

Property is_goto_head_symbs_correct:
  is_goto_head_symbs () = true -> goto_head_symbs.
Proof.
unfold is_goto_head_symbs, goto_head_symbs.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
rewrite forallb_forall in H.
specialize (H nt (all_list_forall nt)).
destruct (goto_table s nt); intuition.
destruct s0.
apply is_prefix_correct; intuition.
Qed.

(** We have to say the same kind of checks for the assumptions about the
    states stack. However, theses assumptions are predicates. So we define
    a notion of "prefix" over predicates lists, that means, basically, that
    an assumption entails another **)
Inductive prefix_pred: list (state->bool) -> list (state->bool) -> Prop :=
  | prefix_pred_nil: forall l, prefix_pred [] l
  | prefix_pred_cons: forall l1 l2 f1 f2,
     (forall x, implb (f2 x) (f1 x) = true) ->
     prefix_pred l1 l2 -> prefix_pred (f1::l1) (f2::l2).

Fixpoint is_prefix_pred (l1 l2:list (state->bool)) :=
  match l1, l2 with
    | [], _ => true
    | f1::q1, f2::q2 =>
      (forallb (fun x => implb (f2 x) (f1 x)) all_list
        && is_prefix_pred q1 q2)%bool
    | _::_, [] => false
  end.

Property is_prefix_pred_correct (l1 l2:list (state->bool)) :
  is_prefix_pred l1 l2 = true -> prefix_pred l1 l2.
Proof.
revert l2.
induction l1.
intros.
apply prefix_pred_nil.
intros.
destruct l2; intuition; try discriminate.
unfold is_prefix_pred in H.
rewrite Bool.andb_true_iff in H.
rewrite forallb_forall in H.
apply prefix_pred_cons; intuition.
apply H0.
apply all_list_forall.
Qed.

(** The assumptions about state stack is conserved when we shift **)
Definition shift_past_state :=
  forall s,
    match action_table s with
      | Lookahead_act awp =>
        forall t, match awp t with
          | Shift_act s2 _ =>
            prefix_pred (past_state_of_non_init_state s2)
                        (head_states_of_state s)
          | _ => True
        end
      | _ => True
    end.

Definition is_shift_past_state (_:unit) :=
  forallb (fun s:state =>
    match action_table s with
      | Lookahead_act awp =>
        forallb (fun t =>
          match awp t with
            | Shift_act s2 _ =>
              is_prefix_pred
                (past_state_of_non_init_state s2) (head_states_of_state s)
            | _ => true
          end)
          all_list
      | _ => true
    end)
    all_list.

Property is_shift_past_state_correct:
 is_shift_past_state () = true -> shift_past_state.
Proof.
unfold is_shift_past_state, shift_past_state.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
destruct (action_table s); intuition.
rewrite forallb_forall in H.
specialize (H t (all_list_forall t)).
destruct (l t); intuition.
apply is_prefix_pred_correct; intuition.
Qed.

(** The assumptions about state stack is conserved when we do a goto **)
Definition goto_past_state :=
  forall s nt,
    match goto_table s nt with
      | Some (exist _ s2 _) =>
        prefix_pred (past_state_of_non_init_state s2)
                    (head_states_of_state s)
      | None => True
    end.

Definition is_goto_past_state (_:unit) :=
  forallb (fun s:state =>
    forallb (fun nt =>
      match goto_table s nt with
        | Some (exist _ s2 _) =>
          is_prefix_pred
            (past_state_of_non_init_state s2) (head_states_of_state s)
        | None => true
      end)
      all_list)
    all_list.

Property is_goto_past_state_correct :
  is_goto_past_state () = true -> goto_past_state.
Proof.
unfold is_goto_past_state, goto_past_state.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
rewrite forallb_forall in H.
specialize (H nt (all_list_forall nt)).
destruct (goto_table s nt); intuition.
destruct s0.
apply is_prefix_pred_correct; intuition.
Qed.

(** What states are possible after having popped these symbols from the
    stack, given the annotation of the current state ? **)
Inductive state_valid_after_pop (s:state):
  list symbol -> list (state -> bool) -> Prop :=
  | state_valid_after_pop_nil1:
    forall p pl, p s = true -> state_valid_after_pop s [] (p::pl)
  | state_valid_after_pop_nil2:
    forall sl, state_valid_after_pop s sl []
  | state_valid_after_pop_cons:
    forall st sq p pl, state_valid_after_pop s sq pl ->
      state_valid_after_pop s (st::sq) (p::pl).

Fixpoint is_state_valid_after_pop
  (state:state) (to_pop:list symbol) annot :=
  match annot, to_pop with
    | [], _ => true
    | p::_, [] => p state
    | p::pl, s::sl => is_state_valid_after_pop state sl pl
  end.

Property is_state_valid_after_pop_complete state sl pl :
  state_valid_after_pop state sl pl -> is_state_valid_after_pop state sl pl = true.
Proof.
intro.
induction H; intuition.
destruct sl; intuition.
Qed.

(** A state is valid for reducing a production when :
      - The assumptions on the state are such that we will find the right hand
        side of the production on the stack.
      - We will be able to do a goto after having popped the right hand side.
**)
Definition valid_for_reduce (state:state) prod :=
    prefix (prod_rhs_rev prod) (head_symbs_of_state state) /\
    forall state_new,
    state_valid_after_pop state_new
      (prod_rhs_rev prod) (head_states_of_state state) ->
    goto_table state_new (prod_lhs prod) = None ->
    match state_new with
      | Init i => prod_lhs prod = start_nt i
      | Ninit _ => False
    end.

Definition is_valid_for_reduce (state:state) prod:=
  (is_prefix (prod_rhs_rev prod) (head_symbs_of_state state) &&
   forallb (fun state_new =>
     if is_state_valid_after_pop state_new (prod_rhs_rev prod)
                                           (head_states_of_state state) then
       match goto_table state_new (prod_lhs prod) with
         | Some _ => true
         | None =>
           match state_new with
             | Init i => compare_eqb (prod_lhs prod) (start_nt i)
             | Ninit _ => false
           end
       end
     else
       true)
     all_list)%bool.

Property is_valid_for_reduce_correct (state:state) prod:
  is_valid_for_reduce state prod = true -> valid_for_reduce state prod.
Proof.
unfold is_valid_for_reduce, valid_for_reduce.
intros.
rewrite Bool.andb_true_iff in H.
split.
apply is_prefix_correct.
intuition.
intros.
rewrite forallb_forall in H.
destruct H.
specialize (H2 state_new (all_list_forall state_new)).
rewrite is_state_valid_after_pop_complete, H1 in H2.
destruct state_new; intuition.
rewrite compare_eqb_iff in H2; intuition.
intuition.
Qed.

(** All the states that does a reduce are valid for reduction **)
Definition reduce_ok :=
  forall s,
    match action_table s with
      | Lookahead_act awp =>
        forall t, match awp t with
          | Reduce_act p => valid_for_reduce s p
          | _ => True
        end
      | Default_reduce_act p => valid_for_reduce s p
    end.

Definition is_reduce_ok (_:unit) :=
  forallb (fun s =>
    match action_table s with
      | Lookahead_act awp =>
        forallb (fun t =>
          match awp t with
            | Reduce_act p => is_valid_for_reduce s p
            | _ => true
          end)
          all_list
      | Default_reduce_act p => is_valid_for_reduce s p
    end)
    all_list.

Property is_reduce_ok_correct :
  is_reduce_ok () = true -> reduce_ok.
Proof.
unfold is_reduce_ok, reduce_ok.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
destruct (action_table s).
apply is_valid_for_reduce_correct; intuition.
intro.
rewrite forallb_forall in H.
specialize (H t (all_list_forall t)).
destruct (l t); intuition.
apply is_valid_for_reduce_correct; intuition.
Qed.

(** The automaton is safe **)
Definition safe :=
  shift_head_symbs /\ goto_head_symbs /\ shift_past_state /\
  goto_past_state /\ reduce_ok.

Definition is_safe (_:unit) :=
  (is_shift_head_symbs () && is_goto_head_symbs () && is_shift_past_state () &&
    is_goto_past_state () && is_reduce_ok ())%bool.

Property is_safe_correct:
  is_safe () = true -> safe.
Proof.
unfold safe, is_safe.
repeat rewrite Bool.andb_true_iff.
intuition.
apply is_shift_head_symbs_correct; assumption.
apply is_goto_head_symbs_correct; assumption.
apply is_shift_past_state_correct; assumption.
apply is_goto_past_state_correct; assumption.
apply is_reduce_ok_correct; assumption.
Qed.

End Make.

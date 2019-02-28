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
Require Automaton.
Require Import Alphabet.

Module Make(Import A:Automaton.T).

(** The error monad **)
Inductive result (A:Type) :=
  | Err: result A
  | OK: A -> result A.

Arguments Err [A].
Arguments OK [A].

Definition bind {A B: Type} (f: result A) (g: A -> result B): result B :=
  match f with
    | OK x => g x
    | Err => Err
  end.

Definition bind2 {A B C: Type} (f: result (A * B)) (g: A -> B -> result C):
  result C :=
  match f with
    | OK (x, y) => g x y
    | Err => Err
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
  (at level 200, X ident, Y ident, A at level 100, B at level 200).

(** Some operations on streams **)

(** Concatenation of a list and a stream **)
Fixpoint app_str {A:Type} (l:list A) (s:Stream A) :=
  match l with
    | nil => s
    | cons t q => Cons t (app_str q s)
  end.

Infix "++" := app_str (right associativity, at level 60).

Lemma app_str_app_assoc {A:Type} (l1 l2:list A) (s:Stream A) :
  l1 ++ (l2 ++ s) = (l1 ++ l2) ++ s.
Proof.
induction l1.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.

(** The type of a non initial state: the type of semantic values associated
   with the last symbol of this state. *)
Definition noninitstate_type state :=
  symbol_semantic_type (last_symb_of_non_init_state state).

(** The stack of the automaton : it can be either nil or contains a non
    initial state, a semantic value for the symbol associted with this state,
    and a nested stack. **)
Definition stack := list (sigT noninitstate_type). (* eg. list {state & state_type state} *)

Section Init.

Variable init : initstate.

(** The top state of a stack **)
Definition state_of_stack (stack:stack): state :=
  match stack with
    | [] => init
    | existT _ s _::_ => s
  end.

(** [pop] pops some symbols from the stack. It returns the popped semantic
    values using [sem_popped] as an accumulator and discards the popped
    states.**)
Fixpoint pop (symbols_to_pop:list symbol) (stack_cur:stack):
  forall {A:Type} (action:arrows_right A (map symbol_semantic_type symbols_to_pop)),
    result (stack * A) :=
  match symbols_to_pop return forall {A:Type} (action:arrows_right A (map _ symbols_to_pop)), result (stack * A) with
    | [] => fun A action => OK (stack_cur, action)
    | t::q => fun A action =>
      match stack_cur with
        | existT _ state_cur sem::stack_rec =>
          match compare_eqdec (last_symb_of_non_init_state state_cur) t with
            | left e =>
              let sem_conv := eq_rect _ symbol_semantic_type sem _ e in
              pop q stack_rec (action sem_conv)
            | right _ => Err
          end
        | [] => Err
      end
  end.

(** [step_result] represents the result of one step of the automaton : it can
    fail, accept or progress. [Fail_sr] means that the input is incorrect.
    [Accept_sr] means that this is the last step of the automaton, and it
    returns the semantic value of the input word. [Progress_sr] means that
    some progress has been made, but new steps are needed in order to accept
    a word.

    For [Accept_sr] and [Progress_sr], the result contains the new input buffer.

    [Fail_sr] means that the input word is rejected by the automaton. It is
    different to [Err] (from the error monad), which mean that the automaton is
    bogus and has perfomed a forbidden action. **)
Inductive step_result :=
  | Fail_sr: step_result
  | Accept_sr: symbol_semantic_type (NT (start_nt init)) -> Stream token -> step_result
  | Progress_sr: stack -> Stream token -> step_result.

Program Definition prod_action':
  forall p,
    arrows_right (symbol_semantic_type (NT (prod_lhs p)))
      (map symbol_semantic_type (prod_rhs_rev p)):=
      fun p =>
        eq_rect _ (fun x => x) (prod_action p) _ _.
Next Obligation.
unfold arrows_left, arrows_right; simpl.
rewrite <- fold_left_rev_right, <- map_rev, rev_involutive.
reflexivity.
Qed.

(** [reduce_step] does a reduce action :
   - pops some elements from the stack
   - execute the action of the production
   - follows the goto for the produced non terminal symbol **)
Definition reduce_step stack_cur production buffer: result step_result :=
  do (stack_new, sem) <-
    pop (prod_rhs_rev production) stack_cur (prod_action' production);
  match goto_table (state_of_stack stack_new) (prod_lhs production) with
    | Some (exist _ state_new e) =>
      let sem := eq_rect _ _ sem _ e in
      OK (Progress_sr (existT noninitstate_type state_new sem::stack_new) buffer)
    | None =>
      match stack_new with
        | [] =>
          match compare_eqdec (prod_lhs production) (start_nt init) with
            | left e =>
              let sem := eq_rect _ (fun nt => symbol_semantic_type (NT nt)) sem _ e in
              OK (Accept_sr sem buffer)
            | right _ => Err
          end
        | _::_ => Err
      end
  end.

(** One step of parsing. **)
Definition step stack_cur buffer: result step_result :=
  match action_table (state_of_stack stack_cur) with
    | Default_reduce_act production =>
      reduce_step stack_cur production buffer
    | Lookahead_act awt =>
      match Streams.hd buffer with
        | existT _ term sem =>
          match awt term with
            | Shift_act state_new e =>
              let sem_conv := eq_rect _ symbol_semantic_type sem _ e in
              OK (Progress_sr (existT noninitstate_type state_new sem_conv::stack_cur)
                              (Streams.tl buffer))
            | Reduce_act production =>
              reduce_step stack_cur production buffer
            | Fail_action =>
              OK Fail_sr
          end
      end
  end.

(** The parsing use a [nat] parameter [n_steps], so that we do not have to prove
    terminaison, which is difficult. So the result of a parsing is either
    a failure (the automaton has rejected the input word), either a timeout
    (the automaton has spent all the given [n_steps]), either a parsed semantic
    value with a rest of the input buffer.
**)
Inductive parse_result :=
  | Fail_pr: parse_result
  | Timeout_pr: parse_result
  | Parsed_pr: symbol_semantic_type (NT (start_nt init)) -> Stream token -> parse_result.

Fixpoint parse_fix stack_cur buffer n_steps: result parse_result:=
  match n_steps with
    | O => OK Timeout_pr
    | S it =>
      do r <- step stack_cur buffer;
      match r with
        | Fail_sr => OK Fail_pr
        | Accept_sr t buffer_new => OK (Parsed_pr t buffer_new)
        | Progress_sr s buffer_new => parse_fix s buffer_new it
      end
  end.

Definition parse buffer n_steps: result parse_result :=
  parse_fix [] buffer n_steps.

End Init.

Arguments Fail_sr [init].
Arguments Accept_sr [init] _ _.
Arguments Progress_sr [init] _ _.

Arguments Fail_pr [init].
Arguments Timeout_pr [init].
Arguments Parsed_pr [init] _ _.

End Make.

Module Type T(A:Automaton.T).
  Include (Make A).
End T.

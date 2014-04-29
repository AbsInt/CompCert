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

Require Grammar.
Require Automaton.
Require Interpreter_safe.
Require Interpreter_correct.
Require Interpreter_complete.
Require Import Syntax.

Module Make(Export Aut:Automaton.T).
Export Aut.Gram.
Export Aut.GramDefs.

Module Import Inter := Interpreter.Make Aut.
Module Safe := Interpreter_safe.Make Aut Inter.
Module Correct := Interpreter_correct.Make Aut Inter.
Module Complete := Interpreter_complete.Make Aut Inter.

Definition complete_validator:unit->bool := Complete.Valid.is_complete.
Definition safe_validator:unit->bool := Safe.Valid.is_safe.
Definition parse (safe:safe_validator ()=true) init n_steps buffer : parse_result init:=
  Safe.parse_with_safe (Safe.Valid.is_safe_correct safe) init buffer n_steps.

(** Correction theorem. **)
Theorem parse_correct
  (safe:safe_validator ()= true) init n_steps buffer:
  match parse safe init n_steps buffer with
    | Parsed_pr sem buffer_new =>
      exists word,
        buffer = word ++ buffer_new /\ inhabited (parse_tree (NT (start_nt init)) word sem)
    | _ => True
  end.
Proof.
unfold parse, Safe.parse_with_safe.
pose proof (Correct.parse_correct init buffer n_steps).
generalize (Safe.parse_no_err (Safe.Valid.is_safe_correct safe) init buffer n_steps).
destruct (Inter.parse init buffer n_steps); intros.
now destruct (n (eq_refl _)).
now destruct p; trivial.
Qed.

(** Completeness theorem. **)
Theorem parse_complete
  (safe:safe_validator () = true) init n_steps word buffer_end sem:
  complete_validator () = true ->
  forall tree:parse_tree (NT (start_nt init)) word sem,
  match parse safe init n_steps (word ++ buffer_end) with
    | Fail_pr => False
    | Parsed_pr sem_res buffer_end_res =>
      sem_res = sem /\ buffer_end_res = buffer_end /\ pt_size tree <= n_steps
    | Timeout_pr => n_steps < pt_size tree
  end.
Proof.
intros.
unfold parse, Safe.parse_with_safe.
pose proof (Complete.parse_complete (Complete.Valid.is_complete_correct H) init _ buffer_end _ tree n_steps).
generalize (Safe.parse_no_err (Safe.Valid.is_safe_correct safe) init (word ++ buffer_end) n_steps).
destruct (Inter.parse init (word ++ buffer_end) n_steps); intros.
now destruct (n eq_refl).
now exact H0.
Qed.

(** Unambiguity theorem. **)
Theorem unambiguity:
  safe_validator () = true -> complete_validator () = true -> inhabited token ->
  forall init word,
  forall sem1 (tree1:parse_tree (NT (start_nt init)) word sem1),
  forall sem2 (tree2:parse_tree (NT (start_nt init)) word sem2),
  sem1 = sem2.
Proof.
intros.
destruct H1.
pose proof (parse_complete H init (pt_size tree1) word (Streams.const X) sem1) H0 tree1.
pose proof (parse_complete H init (pt_size tree1) word (Streams.const X) sem2) H0 tree2.
destruct (parse H init (pt_size tree1) (word ++ Streams.const X)); intuition.
rewrite <- H3, H1; reflexivity.
Qed.

End Make.

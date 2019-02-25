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

Require Grammar Automaton Interpreter_correct Interpreter_complete.
From Coq Require Import Syntax Arith.

Module Make(Export Aut:Automaton.T).
Export Aut.Gram.
Export Aut.GramDefs.

Module Import Inter := Interpreter.Make Aut.
Module Correct := Interpreter_correct.Make Aut Inter.
Module Complete := Interpreter_complete.Make Aut Inter.

Definition complete_validator:unit->bool := Complete.Valid.is_complete.
Definition safe_validator:unit->bool := ValidSafe.is_safe.
Definition parse (safe:safe_validator ()=true) init log_n_steps buffer :
  parse_result (symbol_semantic_type (NT (start_nt init))):=
  parse (ValidSafe.safe_is_validator safe) init buffer log_n_steps.

(** Correction theorem. **)
Theorem parse_correct
  (safe:safe_validator ()= true) init log_n_steps buffer:
  match parse safe init log_n_steps buffer with
    | Parsed_pr sem buffer_new =>
      exists word (pt : parse_tree (NT (start_nt init)) word),
        buffer = (word ++ buffer_new)%buf /\
        pt_sem pt = sem
    | _ => True
  end.
Proof. apply Correct.parse_correct. Qed.

(** Completeness theorem. **)
Theorem parse_complete
  (safe:safe_validator () = true) init log_n_steps word buffer_end:
  complete_validator () = true ->
  forall tree:parse_tree (NT (start_nt init)) word,
  match parse safe init log_n_steps (word ++ buffer_end) with
  | Fail_pr => False
  | Parsed_pr sem_res buffer_end_res =>
    sem_res = pt_sem tree /\ buffer_end_res = buffer_end /\
    pt_size tree <= 2^log_n_steps
  | Timeout_pr => 2^log_n_steps < pt_size tree
  end.
Proof.
  intros. now apply Complete.parse_complete, Complete.Valid.complete_is_validator.
Qed.

(** Unambiguity theorem. **)
Theorem unambiguity:
  safe_validator () = true -> complete_validator () = true -> inhabited token ->
  forall init word,
  forall (tree1 tree2:parse_tree (NT (start_nt init)) word),
    pt_sem tree1 = pt_sem tree2.
Proof.
  intros Hsafe Hcomp [tok] init word tree1 tree2.
  pose (buf_end := cofix buf_end := (tok :: buf_end)%buf).
  assert (Hcomp1 := parse_complete Hsafe init (pt_size tree1) word buf_end
                                   Hcomp tree1).
  assert (Hcomp2 := parse_complete Hsafe init (pt_size tree1) word buf_end
                                   Hcomp tree2).
  destruct parse.
  - destruct Hcomp1.
  - exfalso. eapply PeanoNat.Nat.lt_irrefl. etransitivity; [|apply Hcomp1].
    eapply Nat.pow_gt_lin_r. constructor.
  - destruct Hcomp1 as [-> _], Hcomp2 as [-> _]. reflexivity.
Qed.

End Make.

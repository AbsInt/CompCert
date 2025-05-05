(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Known built-in functions *)

From Coq Require Import String.
Require Import Coqlib.
Require Import AST Integers Floats Values.
Require Export Builtins0 Builtins1.

Inductive builtin_function : Type :=
  | BI_standard (b: standard_builtin)
  | BI_platform (b: platform_builtin).

Definition eq_builtin_function: forall (x y: builtin_function), {x=y} + {x<>y}.
Proof.
  generalize eq_standard_builtin eq_platform_builtin; decide equality.
Defined.
Global Opaque eq_builtin_function.

Definition builtin_function_sig (b: builtin_function) : signature :=
  match b with
  | BI_standard b => standard_builtin_sig b
  | BI_platform b => platform_builtin_sig b
  end.

Definition builtin_function_sem (b: builtin_function) : builtin_sem (sig_res (builtin_function_sig b)) :=
  match b with
  | BI_standard b => standard_builtin_sem b
  | BI_platform b => platform_builtin_sem b
  end.

Lemma builtin_function_sem_inject: forall b vargs vres f vargs',
  builtin_function_sem b vargs = Some vres ->
  Val.inject_list f vargs vargs' ->
  exists vres', builtin_function_sem b vargs' = Some vres' /\ Val.inject f vres vres'.
Proof.
  intros. exploit (bs_inject _ (builtin_function_sem b)); eauto.
  unfold val_opt_inject; rewrite H; intro J.
  destruct (builtin_function_sem b vargs') as [vres'|]; try contradiction.
  exists vres'; auto.
Qed.

Lemma builtin_function_sem_lessdef: forall b vargs vres vargs',
  builtin_function_sem b vargs = Some vres ->
  Val.lessdef_list vargs vargs' ->
  exists vres', builtin_function_sem b vargs' = Some vres' /\ Val.lessdef vres vres'.
Proof.
  intros. apply val_inject_list_lessdef in H0. 
  exploit builtin_function_sem_inject; eauto.
  intros (vres' & A & B). apply val_inject_lessdef in B.
  exists vres'; auto.
Qed.

Definition lookup_builtin_function (name: string) (sg: signature) : option builtin_function :=
  match lookup_builtin standard_builtin_sig name sg standard_builtin_table with
  | Some b => Some (BI_standard b)
  | None => 
  match lookup_builtin platform_builtin_sig name sg platform_builtin_table with
  | Some b => Some (BI_platform b)
  | None => None
  end end.

Lemma lookup_builtin_function_sig:
  forall name sg b, lookup_builtin_function name sg = Some b -> builtin_function_sig b = sg.
Proof.
  unfold lookup_builtin_function; intros.
  destruct (lookup_builtin standard_builtin_sig name sg standard_builtin_table) as [bs|] eqn:E.
  inv H. simpl. eapply lookup_builtin_sig; eauto.
  destruct (lookup_builtin platform_builtin_sig name sg platform_builtin_table) as [bp|] eqn:E'.
  inv H. simpl. eapply lookup_builtin_sig; eauto.
  discriminate.
Qed.



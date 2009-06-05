(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Error reporting and the error monad. *)

Require Import String.
Require Import Coqlib.

Close Scope string_scope.

Set Implicit Arguments.

(** * Representation of error messages. *)

(** Compile-time errors produce an error message, represented in Coq
  as a list of either substrings or positive numbers encoding
  a source-level identifier (see module AST). *)

Inductive errcode: Type :=
  | MSG: string -> errcode
  | CTX: positive -> errcode.

Definition errmsg: Type := list errcode.

Definition msg (s: string) : errmsg := MSG s :: nil.

(** * The error monad *)

(** Compilation functions that can fail have return type [res A].
  The return value is either [OK res] to indicate success,
  or [Error msg] to indicate failure. *)

Inductive res (A: Type) : Type :=
| OK: A -> res A
| Error: errmsg -> res A.

Implicit Arguments Error [A].

(** To automate the propagation of errors, we use a monadic style
  with the following [bind] operation. *)

Definition bind (A B: Type) (f: res A) (g: A -> res B) : res B :=
  match f with
  | OK x => g x
  | Error msg => Error msg
  end.

Definition bind2 (A B C: Type) (f: res (A * B)) (g: A -> B -> res C) : res C :=
  match f with
  | OK (x, y) => g x y
  | Error msg => Error msg
  end.

(** The [do] notation, inspired by Haskell's, keeps the code readable. *)

Notation "'do' X <- A ; B" := (bind A (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200)
 : error_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
 (at level 200, X ident, Y ident, A at level 100, B at level 200)
 : error_monad_scope.

Remark bind_inversion:
  forall (A B: Type) (f: res A) (g: A -> res B) (y: B),
  bind f g = OK y ->
  exists x, f = OK x /\ g x = OK y.
Proof.
  intros until y. destruct f; simpl; intros.
  exists a; auto.
  discriminate.
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: res (A*B)) (g: A -> B -> res C) (z: C),
  bind2 f g = OK z ->
  exists x, exists y, f = OK (x, y) /\ g x y = OK z.
Proof.
  intros until z. destruct f; simpl.
  destruct p; simpl; intros. exists a; exists b; auto.
  intros; discriminate.
Qed.

Open Local Scope error_monad_scope.

(** This is the familiar monadic map iterator. *)

Fixpoint mmap (A B: Type) (f: A -> res B) (l: list A) {struct l} : res (list B) :=
  match l with
  | nil => OK nil
  | hd :: tl => do hd' <- f hd; do tl' <- mmap f tl; OK (hd' :: tl')
  end.

Remark mmap_inversion:
  forall (A B: Type) (f: A -> res B) (l: list A) (l': list B),
  mmap f l = OK l' ->
  list_forall2 (fun x y => f x = OK y) l l'.
Proof.
  induction l; simpl; intros.
  inversion_clear H. constructor.
  destruct (bind_inversion _ _ H) as [hd' [P Q]].
  destruct (bind_inversion _ _ Q) as [tl' [R S]].
  inversion_clear S.
  constructor. auto. auto. 
Qed.

(** * Reasoning over monadic computations *)

(** The [monadInv H] tactic below simplifies hypotheses of the form
<<
        H: (do x <- a; b) = OK res
>>
    By definition of the bind operation, both computations [a] and
    [b] must succeed for their composition to succeed.  The tactic
    therefore generates the following hypotheses:

         x: ...
        H1: a = OK x
        H2: b x = OK res
*)

Ltac monadInv1 H :=
  match type of H with
  | (OK _ = OK _) =>
      inversion H; clear H; try subst
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInv1 EQ2)))))
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  end.

Ltac monadInv H :=
  match type of H with
  | (OK _ = OK _) => monadInv1 H
  | (Error _ = OK _) => monadInv1 H
  | (bind ?F ?G = OK ?X) => monadInv1 H
  | (bind2 ?F ?G = OK ?X) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.


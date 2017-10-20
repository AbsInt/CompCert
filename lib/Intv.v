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

(** Definitions and theorems about semi-open integer intervals *)

Require Import Coqlib.
Require Import Zwf.
Require Coq.Program.Wf.
Require Import Recdef.

Definition interv : Type := (Z * Z)%type.

(** * Membership *)

Definition In (x: Z) (i: interv) : Prop := fst i <= x < snd i.

Lemma In_dec:
  forall x i, {In x i} + {~In x i}.
Proof.
  unfold In; intros.
  case (zle (fst i) x); intros.
  case (zlt x (snd i)); intros.
  left; auto.
  right; intuition.
  right; intuition.
Qed.

Lemma notin_range:
  forall x i,
  x < fst i \/ x >= snd i -> ~In x i.
Proof.
  unfold In; intros; omega.
Qed.

Lemma range_notin:
  forall x i,
  ~In x i -> fst i < snd i -> x < fst i \/ x >= snd i.
Proof.
  unfold In; intros; omega.
Qed.

(** * Emptyness *)

Definition empty (i: interv) : Prop := fst i >= snd i.

Lemma empty_dec:
  forall i, {empty i} + {~empty i}.
Proof.
  unfold empty; intros.
  case (zle (snd i) (fst i)); intros.
  left; omega.
  right; omega.
Qed.

Lemma is_notempty:
  forall i, fst i < snd i -> ~empty i.
Proof.
  unfold empty; intros; omega.
Qed.

Lemma empty_notin:
  forall x i, empty i -> ~In x i.
Proof.
  unfold empty, In; intros. omega.
Qed.

Lemma in_notempty:
  forall x i, In x i -> ~empty i.
Proof.
  unfold empty, In; intros. omega.
Qed.

(** * Disjointness *)

Definition disjoint (i j: interv) : Prop :=
  forall x, In x i -> ~In x j.

Lemma disjoint_sym:
  forall i j, disjoint i j -> disjoint j i.
Proof.
  unfold disjoint; intros; red; intros. elim (H x); auto.
Qed.

Lemma empty_disjoint_r:
  forall i j, empty j -> disjoint i j.
Proof.
  unfold disjoint; intros. apply empty_notin; auto.
Qed.

Lemma empty_disjoint_l:
  forall i j, empty i -> disjoint i j.
Proof.
  intros. apply disjoint_sym. apply empty_disjoint_r; auto.
Qed.

Lemma disjoint_range:
  forall i j,
  snd i <= fst j \/ snd j <= fst i -> disjoint i j.
Proof.
  unfold disjoint, In; intros. omega.
Qed.

Lemma range_disjoint:
  forall i j,
  disjoint i j ->
  empty i \/ empty j \/ snd i <= fst j \/ snd j <= fst i.
Proof.
  unfold disjoint, empty; intros.
  destruct (zlt (fst i) (snd i)); auto.
  destruct (zlt (fst j) (snd j)); auto.
  right; right.
  destruct (zlt (fst i) (fst j)).
(* Case 1: i starts to the left of j. *)
  destruct (zle (snd i) (fst j)).
(* Case 1.1: i ends to the left of j, OK *)
  auto.
(* Case 1.2: i ends to the right of j's start, not disjoint. *)
  elim (H (fst j)). red; omega. red; omega.
(* Case 2: j starts to the left of i *)
  destruct (zle (snd j) (fst i)).
(* Case 2.1: j ends to the left of i, OK *)
  auto.
(* Case 2.2: j ends to the right of i's start, not disjoint. *)
  elim (H (fst i)). red; omega. red; omega.
Qed.

Lemma range_disjoint':
  forall i j,
  disjoint i j -> fst i < snd i -> fst j < snd j ->
  snd i <= fst j \/ snd j <= fst i.
Proof.
  intros. exploit range_disjoint; eauto. unfold empty; intuition omega.
Qed.

Lemma disjoint_dec:
  forall i j, {disjoint i j} + {~disjoint i j}.
Proof.
  intros.
  destruct (empty_dec i). left; apply empty_disjoint_l; auto.
  destruct (empty_dec j). left; apply empty_disjoint_r; auto.
  destruct (zle (snd i) (fst j)). left; apply disjoint_range; auto.
  destruct (zle (snd j) (fst i)). left; apply disjoint_range; auto.
  right; red; intro. exploit range_disjoint; eauto. intuition.
Qed.

(** * Shifting an interval by some amount *)

Definition shift (i: interv) (delta: Z) : interv := (fst i + delta, snd i + delta).

Lemma in_shift:
  forall x i delta,
  In x i -> In (x + delta) (shift i delta).
Proof.
  unfold shift, In; intros. simpl. omega.
Qed.

Lemma in_shift_inv:
  forall x i delta,
  In x (shift i delta) -> In (x - delta) i.
Proof.
  unfold shift, In; simpl; intros. omega.
Qed.

(** * Enumerating the elements of an interval *)

Section ELEMENTS.

Variable lo: Z.

Function elements_rec (hi: Z) {wf (Zwf lo) hi} : list Z :=
  if zlt lo hi then (hi-1) :: elements_rec (hi-1) else nil.
Proof.
  intros. red. omega.
  apply Zwf_well_founded.
Qed.

Lemma In_elements_rec:
  forall hi x,
  List.In x (elements_rec hi) <-> lo <= x < hi.
Proof.
  intros. functional induction (elements_rec hi).
  simpl; split; intros.
  destruct H. clear IHl. omega. rewrite IHl in H. clear IHl. omega.
  destruct (zeq (hi - 1) x); auto. right. rewrite IHl. clear IHl. omega.
  simpl; intuition.
Qed.

End ELEMENTS.

Definition elements (i: interv) : list Z :=
  elements_rec (fst i) (snd i).

Lemma in_elements:
  forall x i,
  In x i -> List.In x (elements i).
Proof.
  intros. unfold elements. rewrite In_elements_rec. auto.
Qed.

Lemma elements_in:
  forall x i,
  List.In x (elements i) -> In x i.
Proof.
  unfold elements; intros.
  rewrite In_elements_rec in H. auto.
Qed.

(** * Checking properties on all elements of an interval *)

Section FORALL.

Variables P Q: Z -> Prop.
Variable f: forall (x: Z), {P x} + {Q x}.
Variable lo: Z.

Program Fixpoint forall_rec (hi: Z) {wf (Zwf lo) hi}:
                 {forall x, lo <= x < hi -> P x}
                 + {exists x, lo <= x < hi /\ Q x} :=
  if zlt lo hi then
    match f (hi - 1) with
    | left _ =>
        match forall_rec (hi - 1) with
        | left _ => left _ _
        | right _ => right _ _
        end
    | right _ => right _ _
    end
  else
    left _ _
.
Next Obligation.
  red. omega.
Qed.
Next Obligation.
  assert (x = hi - 1 \/ x < hi - 1) by omega.
  destruct H2. congruence. auto.
Qed.
Next Obligation.
  exists wildcard'; split; auto. omega.
Qed.
Next Obligation.
  exists (hi - 1); split; auto. omega.
Qed.
Next Obligation.
  omegaContradiction.
Defined.

End FORALL.

Definition forall_dec
       (P Q: Z -> Prop) (f: forall (x: Z), {P x} + {Q x}) (i: interv) :
       {forall x, In x i -> P x} + {exists x, In x i /\ Q x} :=
 forall_rec P Q f (fst i) (snd i).

(** * Folding a function over all elements of an interval *)

Section FOLD.

Variable A: Type.
Variable f: Z -> A -> A.
Variable lo: Z.
Variable a: A.

Function fold_rec (hi: Z) {wf (Zwf lo) hi} : A :=
  if zlt lo hi then f (hi - 1) (fold_rec (hi - 1)) else a.
Proof.
  intros. red. omega.
  apply Zwf_well_founded.
Qed.

Lemma fold_rec_elements:
  forall hi, fold_rec hi = List.fold_right f a (elements_rec lo hi).
Proof.
  intros. functional induction (fold_rec hi).
  rewrite elements_rec_equation. rewrite zlt_true; auto.
  simpl. congruence.
  rewrite elements_rec_equation. rewrite zlt_false; auto.
Qed.

End FOLD.

Definition fold {A: Type} (f: Z -> A -> A) (a: A) (i: interv) : A :=
  fold_rec A f (fst i) a (snd i).

Lemma fold_elements:
  forall (A: Type) (f: Z -> A -> A) a i,
  fold f a i = List.fold_right f a (elements i).
Proof.
  intros. unfold fold, elements. apply fold_rec_elements.
Qed.

(** Hints *)

Hint Resolve
  notin_range range_notin
  is_notempty empty_notin in_notempty
  disjoint_sym empty_disjoint_r empty_disjoint_l
  disjoint_range
  in_shift in_shift_inv
  in_elements elements_in : intv.

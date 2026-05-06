(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
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

(** Bounded and unbounded iterators *)

From Coq Require Import ClassicalFacts ChoiceFacts Zwf.
Require Import Coqlib.

(** This modules defines several Coq encodings of a general "while" loop.
  The loop is presented in functional style as the iteration
  of a [step] function of type [A -> B + A]:
<<
        let rec iterate step a =
          match step a with
          | inl b -> b
          | inr a' -> iterate step a'
>>
  This iteration cannot be defined directly in Coq using [Fixpoint],
  because Coq is a logic of total functions, and therefore we must
  guarantee termination of the loop.
*)

(** * Terminating iteration *)

(** We first implement the case where termination is guaranteed because
  the current state [a] decreases at each iteration. *)

Module WfIter.

Section ITERATION.

Variables A B: Type.
Variable step: A -> B + A.
Variable ord: A -> A -> Prop.
Hypothesis ord_wf: well_founded ord.
Hypothesis step_decr: forall a a', step a = inr _ a' -> ord a' a.

Definition step_info (a: A) : {b | step a = inl _ b} + {a' | step a = inr _ a' & ord a' a}.
Proof.
  caseEq (step a); intros. left; exists b; auto. right; exists a0; auto.
Defined.

Fixpoint iterate_rec (a: A) (acc: Acc ord a) : B :=
  match step_info a with
  | inl (exist _ b P) => b
  | inr (exist2 _ _ a' P Q) => iterate_rec a' (Acc_inv acc Q)
  end.

Definition iterate (a: A) : B := iterate_rec a (ord_wf a).

(** We now prove an invariance property [iterate_prop], similar to the Hoare
  logic rule for "while" loops. *)

Variable P: A -> Prop.
Variable Q: B -> Prop.

Hypothesis step_prop:
  forall a : A, P a ->
  match step a with inl b => Q b | inr a' => P a' end.

Lemma iterate_prop:
  forall a, P a -> Q (iterate a).
Proof.
  assert (REC: forall a acc, P a -> Q (iterate_rec a acc)).
  { induction a using (well_founded_induction ord_wf); intros.
    destruct acc; simpl.
    generalize (step_prop a H0).
    destruct (step_info a) as [[b U] | [a' U V]]; rewrite U; intros.
    + auto.
    + apply H; auto.
  }
  intros. apply REC; auto.
Qed.

End ITERATION.

End WfIter.

(** * Bounded iteration *)

(** The presentation of iteration shown above is predicated on the existence
  of a well-founded ordering that decreases at each step of the iteration.
  In several parts of the CompCert development, it is very painful to define
  such a well-founded ordering and to prove decrease, even though we know our
  iterations always terminate.

  In the presentation below, we choose instead to bound the number of iterations
  by an arbitrary constant.  [iterate] then becomes a function that can fail,
  of type [A -> option B].  The [None] result denotes failure to reach
  a result in the number of iterations prescribed, or, in other terms,
  failure to find a solution to the dataflow problem.  The compiler
  passes that exploit dataflow analysis (the [Constprop], [CSE] and
  [Allocation] passes) will, in this case, either fail ([Allocation])
  or turn off the optimization pass ([Constprop] and [CSE]).

  Since we know (informally) that our computations terminate, we can
  take a very large constant as the maximal number of iterations.
  Failure will therefore never happen in practice, but of
  course our proofs also cover the failure case and show that
  nothing bad happens in this hypothetical case either.  *)

Module PrimIter.

Section ITERATION.

Variables A B: Type.
Variable step: A -> B + A.

Definition num_iterations := 1000000000000%positive.

(** The simple definition of bounded iteration is:
<<
Fixpoint iterate (niter: nat) (a: A) {struct niter} : option B :=
  match niter with
  | O => None
  | S niter' =>
      match step a with
      | inl b => b
      | inr a' => iterate niter' a'
      end
  end.
>>
  This function is structural recursive over the parameter [niter]
  (number of iterations), represented here as a Peano integer (type [nat]).
  However, we want to use very large values of [niter].  As Peano integers,
  these values would be much too large to fit in memory.  Therefore,
  we must express iteration counts as a binary integer (type [positive]).
  However, Peano induction over type [positive] is not structural recursion,
  so we cannot define [iterate] as a Coq fixpoint and must use
  Noetherian recursion instead. *)

Fixpoint iter (x: positive) (s: A) (acc: Acc Plt x) : option B :=
  match peq x xH with
  | left EQ => None
  | right NOTEQ =>
      match step s with
      | inl res => Some res
      | inr s'  => iter (Pos.pred x) s' (Acc_inv acc (Ppred_Plt x NOTEQ))
      end
  end.

(** The [iterate] function is defined as [iter] up to
    [num_iterations] through the loop. *)

Definition iterate (s: A) : option B := iter num_iterations s (Plt_wf num_iterations).

(** We now prove the invariance property [iterate_prop]. *)

Variable P: A -> Prop.
Variable Q: B -> Prop.

Hypothesis step_prop:
  forall a : A, P a ->
  match step a with inl b => Q b | inr a' => P a' end.

Lemma iterate_prop:
  forall a b, iterate a = Some b -> P a -> Q b.
Proof.
  assert (REC: forall x a acc b, iter x a acc = Some b -> P a -> Q b).
  { induction x using (well_founded_induction Plt_wf).
    intros. destruct acc; simpl in *. destruct (peq x 1).
  - discriminate.
  - specialize (step_prop a H1). destruct (step a) as [res | a'].
    + congruence.
    + eapply H; eauto using Ppred_Plt.
  }
  intros a b. apply REC.
Qed.

End ITERATION.

End PrimIter.

(** * General iteration *)

(* An implementation using classical logic and unbounded iteration,
  in the style of Yves Bertot's paper, "Extending the Calculus
  of Constructions with Tarski's fix-point theorem".

  As in the bounded case, the [iterate] function returns an option type.
  [None] means that iteration does not terminate.
  [Some b] means that iteration terminates with the result [b]. *)

Module GenIter.

Section ITERATION.

Hypothesis EM: excluded_middle.
Hypothesis CDD: ConstructiveDefiniteDescription.

Variables A B: Type.
Variable step: A -> B + A.

Definition B_le (x y: option B) : Prop := x = None \/ y = x.
Definition F_le (x y: A -> option B) : Prop := forall a, B_le (x a) (y a).

Definition F_iter (next: A -> option B) (a: A) : option B :=
  match step a with
  | inl b => Some b
  | inr a' => next a'
  end.

Lemma F_iter_monot:
 forall f g, F_le f g -> F_le (F_iter f) (F_iter g).
Proof.
  intros; red; intros. unfold F_iter.
  destruct (step a) as [b | a']. red; auto. apply H.
Qed.

Fixpoint iter (n: nat) : A -> option B :=
  match n with
  | O => (fun a => None)
  | S m => F_iter (iter m)
  end.

Lemma iter_monot:
  forall p q, (p <= q)%nat -> F_le (iter p) (iter q).
Proof.
  induction p; intros.
  simpl. red; intros; red; auto.
  destruct q. exfalso; lia.
  simpl. apply F_iter_monot. apply IHp. lia.
Qed.

Lemma iter_either:
  forall a,
  (exists n, exists b, iter n a = Some b) \/
  (forall n, iter n a = None).
Proof.
  intro a. destruct (EM (exists n, iter n a <> None)).
- left. destruct H as [n D]. destruct (iter n a) as [b | ] eqn:I; try congruence.
  exists n, b; auto.
- right; intros. destruct (iter n a) as [b | ] eqn:I; auto.
  elim H. exists n; congruence.
Qed.

Definition converges_to (a: A) (b: option B) : Prop :=
  exists n, forall m, (n <= m)%nat -> iter m a = b.

Lemma converges_to_Some:
  forall a n b, iter n a = Some b -> converges_to a (Some b).
Proof.
  intros. exists n. intros.
  assert (B_le (iter n a) (iter m a)). apply iter_monot. auto.
  elim H1; intro; congruence.
Qed.

Lemma converges_to_exists:
  forall a, exists b, converges_to a b.
Proof.
  intros. elim (iter_either a).
  intros [n [b EQ]]. exists (Some b). apply converges_to_Some with n. assumption.
  intro. exists (@None B). exists O. intros. auto.
Qed.

Lemma converges_to_unique:
  forall a b, converges_to a b -> forall b', converges_to a b' -> b = b'.
Proof.
  intros a b [n C] b' [n' C'].
  rewrite <- (C (max n n')). rewrite <- (C' (max n n')). auto. lia. lia.
Qed.

Lemma converges_to_exists_uniquely:
  forall a, exists! b, converges_to a b .
Proof.
  intro. destruct (converges_to_exists a) as [b CT].
  exists b. split. assumption. exact (converges_to_unique _ _ CT).
Qed.

Definition iterate (a: A) : option B :=
  proj1_sig (CDD _ (converges_to a) (converges_to_exists_uniquely a)).

Lemma converges_to_iterate:
  forall a b, converges_to a b -> iterate a = b.
Proof.
  intros. unfold iterate.
  destruct (CDD _ (converges_to a) (converges_to_exists_uniquely a)) as [b' P].
  simpl. apply converges_to_unique with a; auto.
Qed.

Lemma iterate_converges_to:
  forall a, converges_to a (iterate a).
Proof.
  intros. unfold iterate.
  destruct (CDD _ (converges_to a) (converges_to_exists_uniquely a)) as [b' P].
  simpl; auto.
Qed.

(** Invariance property. *)

Variable P: A -> Prop.
Variable Q: B -> Prop.

Hypothesis step_prop:
  forall a : A, P a ->
  match step a with inl b => Q b | inr a' => P a' end.

Lemma iter_prop:
  forall n a b, P a -> iter n a = Some b -> Q b.
Proof.
  induction n; intros until b; intro H; simpl.
  congruence.
  unfold F_iter. generalize (step_prop a H).
  case (step a); intros. congruence.
  apply IHn with a0; auto.
Qed.

Lemma iterate_prop:
  forall a b, iterate a = Some b -> P a -> Q b.
Proof.
  intros. destruct (iterate_converges_to a) as [n IT].
  rewrite H in IT. apply iter_prop with n a. auto. apply IT. auto.
Qed.

End ITERATION.

End GenIter.

(** * Counted loops *)

Module CountedLoop.

(** Counted loops are presented as folds over integer ranges.

[CountedLoop.up f lo hi a] is [ a |> f lo |> f (lo+1) |> ... |> f (hi-1) ] .

[CountedLoop.down f hi lo a] is [ a |> f (hi-1) |> ... |> f (lo+1) |> f lo ].

*)

Section COUNTED_LOOP.

Context {A: Type} (f: Z -> A -> A).

Remark up_aux: forall {lo hi}, lo < hi -> Zwf_up hi (Z.succ lo) lo.
Proof. intros; red; lia. Qed.

Fixpoint up_rec (lo hi: Z) (a: A) (acc: Acc (Zwf_up hi) lo) : A :=
  match zlt lo hi with
  | left LT => up_rec (Z.succ lo) hi (f lo a) (Acc_inv acc (up_aux LT))
  | right GE => a
  end.

Definition up (lo hi: Z) (a: A) :=
  up_rec lo hi a (Zwf_up_well_founded hi lo).

Lemma unroll_up: forall lo hi a,
  up lo hi a = if zlt lo hi then up (Z.succ lo) hi (f lo a) else a.
Proof.
  assert (EXT: forall hi lo a acc1 acc2,
            up_rec lo hi a acc1 = up_rec lo hi a acc2).
  { intros hi. induction lo using (well_founded_induction (Zwf_up_well_founded hi)).
    intros. destruct acc1, acc2; simpl. destruct (zlt lo hi); auto. apply H. red; lia. }
  intros. unfold up at 1. destruct (Zwf_up_well_founded hi lo). simpl.
  destruct (zlt lo hi); auto. apply EXT.
Qed.

Lemma up_split: forall lo mid hi a,
  lo <= mid <= hi -> up lo hi a = up mid hi (up lo mid a).
Proof.
  intros until a; intros [L H]. revert lo a L.
  induction lo using (well_founded_induction (Zwf_up_well_founded hi)).
  intros. rewrite (unroll_up lo mid). destruct (zlt lo mid).
- rewrite (unroll_up lo hi), zlt_true by lia. apply H0. red; lia. lia.
- replace mid with lo by lia. auto.
Qed.

Lemma unroll_up_rev: forall lo hi a,
  up lo hi a = if zlt lo hi then f (Z.pred hi) (up lo (Z.pred hi) a) else a.
Proof.
  intros. destruct (zlt lo hi).
- rewrite up_split with (mid := (Z.pred hi)) by lia.
  rewrite unroll_up, zlt_true by lia. rewrite unroll_up, zlt_false by lia. auto.
- rewrite unroll_up, zlt_false by lia. auto.
Qed.

Lemma up_induction: forall (P: Z -> A -> Prop) lo hi a,
  (forall i a, lo <= i < hi -> P i a -> P (i + 1) (f i a)) ->
  P (Z.min lo hi) a -> P hi (up lo hi a).
Proof.
  intros.
  assert (REC: forall x b acc, lo <= x <= hi -> P x b -> P hi (up_rec x hi b acc)).
  { induction x using (well_founded_induction (Zwf_up_well_founded hi)); intros.
    destruct acc; simpl. destruct (zlt x hi).
  - apply H1. red; lia. lia. apply H; auto. lia.
  - assert (x = hi) by lia. congruence. }
  intros. destruct (zle lo hi).
- apply REC. lia. replace lo with (Z.min lo hi) by lia. auto.
- rewrite unroll_up, zlt_false by lia. assert (Z.min lo hi = hi) by lia. congruence.  
Qed.

Remark down_aux: forall {lo hi}, lo < hi -> Zwf lo (Z.pred hi) hi.
Proof. intros; red; lia. Qed.

Fixpoint down_rec (hi lo: Z) (a: A) (acc: Acc (Zwf lo) hi) : A :=
  match zlt lo hi with
  | left LT => down_rec (Z.pred hi) lo (f (Z.pred hi) a) (Acc_inv acc (down_aux LT))
  | right GE => a
  end.

Definition down (hi lo: Z) (a: A) :=
  down_rec hi lo a (Zwf_well_founded lo hi).

Lemma unroll_down: forall hi lo a,
  down hi lo a = if zlt lo hi then down (Z.pred hi) lo (f (Z.pred hi) a) else a.
Proof.
  assert (EXT: forall lo hi a acc1 acc2,
            down_rec hi lo a acc1 = down_rec hi lo a acc2).
  { intros lo. induction hi using (well_founded_induction (Zwf_well_founded lo)).
    intros. destruct acc1, acc2; simpl. destruct (zlt lo hi); auto. apply H. red; lia. }
  intros. unfold down at 1. destruct (Zwf_well_founded lo hi). simpl.
  destruct (zlt lo hi); auto. apply EXT.
Qed.

Lemma down_split: forall lo mid hi a,
  lo <= mid <= hi -> down hi lo a = down mid lo (down hi mid a).
Proof.
  intros until a; intros [L H]. revert hi a H.
  induction hi using (well_founded_induction (Zwf_well_founded lo)).
  intros. rewrite (unroll_down hi mid). destruct (zlt mid hi).
- rewrite (unroll_down hi lo), zlt_true by lia. apply H. red; lia. lia.
- replace mid with hi by lia. auto.
Qed.

Lemma unroll_down_rev: forall hi lo a,
  down hi lo a = if zlt lo hi then f lo (down hi (Z.succ lo) a) else a.
Proof.
  intros. destruct (zlt lo hi).
- rewrite down_split with (mid := (Z.succ lo)) by lia.
  rewrite unroll_down, zlt_true by lia. rewrite unroll_down, zlt_false by lia.
  f_equal. lia.
- rewrite unroll_down, zlt_false by lia. auto.
Qed.

Lemma down_induction: forall (P: Z -> A -> Prop) lo hi a,
  (forall i a, lo <= i < hi -> P (i + 1) a -> P i (f i a)) ->
  P (Z.max lo hi) a -> P lo (down hi lo a).
Proof.
  intros.
  assert (REC: forall x b acc, lo <= x <= hi -> P x b -> P lo (down_rec x lo b acc)).
  { induction x using (well_founded_induction (Zwf_well_founded lo)); intros.
    destruct acc; simpl. destruct (zlt lo x).
  - apply H1. red; lia. lia. apply H; auto. lia. replace (Z.pred x + 1) with x by lia. auto.
  - assert (x = lo) by lia. congruence. }
  intros. destruct (zle lo hi).
- apply REC; auto. lia. replace hi with (Z.max lo hi) by lia. auto.
- rewrite unroll_down, zlt_false by lia. assert (Z.max lo hi = lo) by lia. congruence.  
Qed.

End COUNTED_LOOP.

End CountedLoop.


(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Bounded and unbounded iterators *)

Require Import Axioms.
Require Import Coqlib.
Require Import Classical.
Require Import Max.

Module Type ITER.
Variable iterate
     : forall A B : Type, (A -> B + A) -> A -> option B.
Hypothesis iterate_prop
     : forall (A B : Type) (step : A -> B + A) (P : A -> Prop) (Q : B -> Prop),
       (forall a : A, P a ->
           match step a with inl b => Q b | inr a' => P a' end) ->
       forall (a : A) (b : B), iterate A B step a = Some b -> P a -> Q b.
End ITER.

Axiom
  dependent_description' :
    forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
      (forall x:A,
          exists y : B x, R x y /\ (forall y':B x, R x y' -> y = y')) ->
       sigT (fun f : forall x:A, B x => (forall x:A, R x (f x))).

(* A constructive implementation using bounded iteration. *)

Module PrimIter: ITER.

Section ITERATION.

Variables A B: Type.
Variable step: A -> B + A.

(** The [step] parameter represents one step of the iteration.  From a 
  current iteration state [a: A], it either returns a value of type [B],
  meaning that iteration is over and that this [B] value is the final
  result of the iteration, or a value [a' : A] which is the next state
  of the iteration.

  The naive way to define the iteration is:
<<
Fixpoint iterate (a: A) : B :=
  match step a with
  | inl b => b
  | inr a' => iterate a'
  end.
>>
  However, this is a general recursion, not guaranteed to terminate,
  and therefore not expressible in Coq.  The standard way to work around
  this difficulty is to use Noetherian recursion (Coq module [Wf]).
  This requires that we equip the type [A] with a well-founded ordering [<]
  (no infinite ascending chains) and we demand that [step] satisfies
  [step a = inr a' -> a < a'].  For the types [A] that are of interest to us
  in this development, it is however very painful to define adequate
  well-founded orderings, even though we know our iterations always
  terminate.

  Instead, we choose to bound the number of iterations by an arbitrary
  constant.  [iterate] then becomes a function that can fail,
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

Definition iter_step (x: positive)
                     (next: forall y, Plt y x -> A -> option B)
                     (s: A) : option B :=
  match peq x xH with
  | left EQ => None
  | right NOTEQ =>
      match step s with
      | inl res => Some res
      | inr s'  => next (Ppred x) (Ppred_Plt x NOTEQ) s'
      end
  end.

Definition iter: positive -> A -> option B :=
  Fix Plt_wf (fun _ => A -> option B) iter_step.

(** We then prove the expected unrolling equations for [iter]. *)

Remark unroll_iter:
  forall x, iter x = iter_step x (fun y _ => iter y).
Proof.
  unfold iter; apply (Fix_eq Plt_wf (fun _ => A -> option B) iter_step).
  intros. unfold iter_step. apply extensionality. intro s. 
  case (peq x xH); intro. auto. 
  rewrite H. auto. 
Qed.

(** The [iterate] function is defined as [iter] up to
    [num_iterations] through the loop. *)

Definition iterate := iter num_iterations.

(** We now prove the invariance property [iterate_prop]. *)

Variable P: A -> Prop.
Variable Q: B -> Prop.

Hypothesis step_prop:
  forall a : A, P a ->
  match step a with inl b => Q b | inr a' => P a' end.

Lemma iter_prop:
  forall n a b, P a -> iter n a = Some b -> Q b.
Proof.
  apply (well_founded_ind Plt_wf 
         (fun p => forall a b, P a -> iter p a = Some b -> Q b)).
  intros until b. intro. rewrite unroll_iter.
  unfold iter_step. case (peq x 1); intro. congruence.
  generalize (step_prop a H0).
  case (step a); intros. congruence. 
  apply H with (Ppred x) a0. apply Ppred_Plt; auto. auto. auto.
Qed.

Lemma iterate_prop:
  forall a b, iterate a = Some b -> P a -> Q b.
Proof.
  intros. apply iter_prop with num_iterations a; assumption.
Qed.

End ITERATION.

End PrimIter.

(* An implementation using classical logic and unbounded iteration,
  in the style of Yves Bertot's paper, "Extending the Calculus
  of Constructions with Tarski's fix-point theorem". *)

Module GenIter: ITER.

Section ITERATION.

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
  destruct q. elimtype False; omega. 
  simpl. apply F_iter_monot. apply IHp. omega.
Qed.

Lemma iter_either:
  forall a,
  (exists n, exists b, iter n a = Some b) \/
  (forall n, iter n a = None).
Proof.
  intro a. elim (classic (forall n, iter n a = None)); intro.
  right; assumption.
  left. generalize (not_all_ex_not nat (fun n => iter n a = None) H).
  intros [n D]. exists n. generalize D. 
  case (iter n a); intros. exists b; auto. congruence.
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
  rewrite <- (C (max n n')). rewrite <- (C' (max n n')). auto.
  apply le_max_r. apply le_max_l.
Qed.

Lemma converges_to_exists_uniquely:
  forall a, exists b, converges_to a b /\ forall b', converges_to a b' -> b = b'.
Proof.
  intro. destruct (converges_to_exists a) as [b CT]. 
  exists b. split. assumption. exact (converges_to_unique _ _ CT).
Qed.

Definition exists_iterate :=
  dependent_description' A (fun _ => option B)
     converges_to converges_to_exists_uniquely.

Definition iterate : A -> option B :=
  match exists_iterate with existT f P => f end.

Lemma converges_to_iterate:
  forall a b, converges_to a b -> iterate a = b.
Proof.
  intros. unfold iterate. destruct exists_iterate as [f P]. 
  apply converges_to_unique with a. apply P. auto.
Qed.

Lemma iterate_converges_to:
  forall a, converges_to a (iterate a).
Proof.
  intros. unfold iterate. destruct exists_iterate as [f P]. apply P.
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

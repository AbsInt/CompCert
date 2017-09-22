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

(** A persistent union-find data structure. *)

Require Coq.Program.Wf.
Require Import Coqlib.

Open Scope nat_scope.
Set Implicit Arguments.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Type MAP.
  Parameter elt: Type.
  Parameter elt_eq: forall (x y: elt), {x=y} + {x<>y}.
  Parameter t: Type -> Type.
  Parameter empty: forall (A: Type), t A.
  Parameter get: forall (A: Type), elt -> t A -> option A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Axiom gempty: forall (A: Type) (x: elt), get x (empty A) = None.
  Axiom gsspec: forall (A: Type) (x y: elt) (v: A) (m: t A),
    get x (set y v m) = if elt_eq x y then Some v else get x m.
End MAP.

Unset Implicit Arguments.

Module Type UNIONFIND.
  Parameter elt: Type.
  Parameter elt_eq: forall (x y: elt), {x=y} + {x<>y}.
  Parameter t: Type.

  Parameter repr: t -> elt -> elt.
  Axiom repr_canonical: forall uf a, repr uf (repr uf a) = repr uf a.

  Definition sameclass (uf: t) (a b: elt) : Prop := repr uf a = repr uf b.
  Axiom sameclass_refl:
    forall uf a, sameclass uf a a.
  Axiom sameclass_sym:
    forall uf a b, sameclass uf a b -> sameclass uf b a.
  Axiom sameclass_trans:
    forall uf a b c,
    sameclass uf a b -> sameclass uf b c -> sameclass uf a c.
  Axiom sameclass_repr:
    forall uf a, sameclass uf a (repr uf a).

  Parameter empty: t.
  Axiom repr_empty:
    forall a, repr empty a = a.
  Axiom sameclass_empty:
    forall a b, sameclass empty a b -> a = b.

  Parameter find: t -> elt -> elt * t.
  Axiom find_repr:
    forall uf a, fst (find uf a) = repr uf a.
  Axiom find_unchanged:
    forall uf a x, repr (snd (find uf a)) x = repr uf x.
  Axiom sameclass_find_1:
    forall uf a x y, sameclass (snd (find uf a)) x y <-> sameclass uf x y.
  Axiom sameclass_find_2:
    forall uf a, sameclass uf a (fst (find uf a)).
  Axiom sameclass_find_3:
    forall uf a, sameclass (snd (find uf a)) a (fst (find uf a)).

  Parameter union: t -> elt -> elt -> t.
  Axiom repr_union_1:
    forall uf a b x, repr uf x <> repr uf a -> repr (union uf a b) x = repr uf x.
  Axiom repr_union_2:
    forall uf a b x, repr uf x = repr uf a -> repr (union uf a b) x = repr uf b.
  Axiom repr_union_3:
    forall uf a b, repr (union uf a b) b = repr uf b.
  Axiom sameclass_union_1:
    forall uf a b, sameclass (union uf a b) a b.
  Axiom sameclass_union_2:
    forall uf a b x y, sameclass uf x y -> sameclass (union uf a b) x y.
  Axiom sameclass_union_3:
    forall uf a b x y,
    sameclass (union uf a b) x y ->
       sameclass uf x y
    \/ sameclass uf x a /\ sameclass uf y b
    \/ sameclass uf x b /\ sameclass uf y a.

  Parameter merge: t -> elt -> elt -> t.
  Axiom repr_merge:
    forall uf a b x, repr (merge uf a b) x = repr (union uf a b) x.
  Axiom sameclass_merge:
    forall uf a b x y, sameclass (merge uf a b) x y <-> sameclass (union uf a b) x y.

  Parameter path_ord: t -> elt -> elt -> Prop.
  Axiom path_ord_wellfounded:
    forall uf, well_founded (path_ord uf).
  Axiom path_ord_canonical:
    forall uf x y, repr uf x = x -> ~path_ord uf y x.
  Axiom path_ord_merge_1:
    forall uf a b x y,
    path_ord uf x y -> path_ord (merge uf a b) x y.
  Axiom path_ord_merge_2:
    forall uf a b,
    repr uf a <> repr uf b -> path_ord (merge uf a b) b (repr uf a).

  Parameter pathlen: t -> elt -> nat.
  Axiom pathlen_zero:
    forall uf a, repr uf a = a <-> pathlen uf a = O.
  Axiom pathlen_merge:
    forall uf a b x,
    pathlen (merge uf a b) x =
      if elt_eq (repr uf a) (repr uf b) then
        pathlen uf x
      else if elt_eq (repr uf x) (repr uf a) then
        pathlen uf x + pathlen uf b + 1
      else
        pathlen uf x.
  Axiom pathlen_gt_merge:
    forall uf a b x y,
    repr uf x = repr uf y ->
    pathlen uf x > pathlen uf y ->
    pathlen (merge uf a b) x > pathlen (merge uf a b) y.

End UNIONFIND.

Module UF (M: MAP) : UNIONFIND with Definition elt := M.elt.

Definition elt := M.elt.
Definition elt_eq := M.elt_eq.

(* A set of equivalence classes over elt is represented by a map m.
   M.get a m = Some a' means that a is in the same class as a'.
   M.get a m = None means that a is the canonical representative
     for its equivalence class. *)

(* The ordering over elt induced by such a map.
   repr_order m a a' iff M.get a' m = Some a.
   This ordering must be well founded. *)

Definition order (m: M.t elt) (a a': elt) : Prop :=
  M.get a' m = Some a.

Record unionfind : Type := mk { m: M.t elt; mwf: well_founded (order m) }.

Definition t := unionfind.

Definition getlink (m: M.t elt) (a: elt) : {a' | M.get a m = Some a'} + {M.get a m = None}.
Proof.
  destruct (M.get a m). left. exists e; auto. right; auto.
Defined.

(* The canonical representative of an element *)

Section REPR.

Variable uf: t.

Definition F_repr (a: elt) (rec: forall b, order uf.(m) b a -> elt) : elt :=
  match getlink uf.(m) a with
  | inleft (exist a' P) => rec a' P
  | inright _ => a
  end.

Definition repr (a: elt) : elt := Fix uf.(mwf) (fun _ => elt) F_repr a.

Lemma repr_unroll:
  forall a, repr a = match M.get a uf.(m) with Some a' => repr a' | None => a end.
Proof.
  intros. unfold repr at 1. rewrite Fix_eq.
  unfold F_repr. destruct (getlink uf.(m) a) as [[a' P] | Q].
  rewrite P; auto.
  rewrite Q; auto.
  intros. unfold F_repr. destruct (getlink (m uf) x) as [[a' P] | Q]; auto.
Qed.

Lemma repr_none:
  forall a,
  M.get a uf.(m) = None ->
  repr a = a.
Proof.
  intros. rewrite repr_unroll. rewrite H; auto.
Qed.

Lemma repr_some:
  forall a a',
  M.get a uf.(m) = Some a' ->
  repr a = repr a'.
Proof.
  intros. rewrite repr_unroll. rewrite H; auto.
Qed.

Lemma repr_res_none:
  forall (a: elt), M.get (repr a) uf.(m) = None.
Proof.
  apply (well_founded_ind (mwf uf)). intros.
  rewrite repr_unroll. destruct (M.get x (m uf)) as [y|] eqn:X; auto.
Qed.

Lemma repr_canonical:
  forall (a: elt), repr (repr a) = repr a.
Proof.
  intros. apply repr_none. apply repr_res_none.
Qed.

Lemma repr_some_diff:
  forall a a', M.get a uf.(m) = Some a' -> a <> repr a'.
Proof.
  intros; red; intros.
  assert (repr a = a). rewrite (repr_some a a'); auto.
  assert (M.get a uf.(m) = None). rewrite <- H1. apply repr_res_none.
  congruence.
Qed.

End REPR.

Definition sameclass (uf: t) (a b: elt) : Prop :=
  repr uf a = repr uf b.

Lemma sameclass_refl:
  forall uf a, sameclass uf a a.
Proof.
  intros. red. auto.
Qed.

Lemma sameclass_sym:
  forall uf a b, sameclass uf a b -> sameclass uf b a.
Proof.
  intros. red. symmetry. exact H.
Qed.

Lemma sameclass_trans:
  forall uf a b c,
  sameclass uf a b -> sameclass uf b c -> sameclass uf a c.
Proof.
  intros. red. transitivity (repr uf b). exact H. exact H0.
Qed.

Lemma sameclass_repr:
  forall uf a, sameclass uf a (repr uf a).
Proof.
  intros. red. symmetry. rewrite repr_canonical. auto.
Qed.

(* The empty unionfind structure (each element in its own class) *)

Lemma wf_empty:
  well_founded (order (M.empty elt)).
Proof.
  red. intros. apply Acc_intro. intros b RO. red in RO.
  rewrite M.gempty in RO. discriminate.
Qed.

Definition empty : t := mk (M.empty elt) wf_empty.

Lemma repr_empty:
  forall a, repr empty a = a.
Proof.
  intros. apply repr_none. simpl. apply M.gempty.
Qed.

Lemma sameclass_empty:
  forall a b, sameclass empty a b -> a = b.
Proof.
  intros. red in H. repeat rewrite repr_empty in H. auto.
Qed.

(* Merging two equivalence classes *)

Section IDENTIFY.

Variable uf: t.
Variables a b: elt.
Hypothesis a_canon: M.get a uf.(m) = None.
Hypothesis not_same_class: repr uf b <> a.

Lemma identify_order:
  forall x y,
  order (M.set a b uf.(m)) y x <->
  order uf.(m) y x \/ (x = a /\ y = b).
Proof.
  intros until y. unfold order. rewrite M.gsspec.
  destruct (M.elt_eq x a). intuition congruence. intuition congruence.
Qed.

Remark identify_Acc_b:
  forall x,
  Acc (order uf.(m)) x -> repr uf x <> a -> Acc (order (M.set a b uf.(m))) x.
Proof.
  induction 1; intros. constructor; intros.
  rewrite identify_order in H2. destruct H2 as [A | [A B]].
  apply H0; auto. rewrite <- (repr_some uf _ _ A). auto.
  subst. elim H1. apply repr_none. auto.
Qed.

Remark identify_Acc:
  forall x,
  Acc (order uf.(m)) x -> Acc (order (M.set a b uf.(m))) x.
Proof.
  induction 1. constructor; intros.
  rewrite identify_order in H1. destruct H1 as [A | [A B]].
  auto.
  subst. apply identify_Acc_b; auto. apply uf.(mwf).
Qed.

Lemma identify_wf:
  well_founded (order (M.set a b uf.(m))).
Proof.
  red; intros. apply identify_Acc. apply uf.(mwf).
Qed.

Definition identify := mk (M.set a b uf.(m)) identify_wf.

Lemma repr_identify_1:
  forall x, repr uf x <> a -> repr identify x = repr uf x.
Proof.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  rewrite (repr_unroll uf) in *.
  destruct (M.get x (m uf)) as [a'|] eqn:X.
  rewrite <- H; auto.
  apply repr_some. simpl. rewrite M.gsspec. rewrite dec_eq_false; auto. congruence.
  apply repr_none. simpl. rewrite M.gsspec. rewrite dec_eq_false; auto.
Qed.

Lemma repr_identify_2:
  forall x, repr uf x = a -> repr identify x = repr uf b.
Proof.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  rewrite (repr_unroll uf) in H0. destruct (M.get x (m uf)) as [a'|] eqn:X.
  rewrite <- (H a'); auto.
  apply repr_some. simpl. rewrite M.gsspec. rewrite dec_eq_false; auto. congruence.
  subst x. rewrite (repr_unroll identify). simpl. rewrite M.gsspec.
  rewrite dec_eq_true. apply repr_identify_1. auto.
Qed.

End IDENTIFY.

(* Union *)

Remark union_not_same_class:
  forall uf a b, repr uf a <> repr uf b -> repr uf (repr uf b) <> repr uf a.
Proof.
  intros. rewrite repr_canonical. auto.
Qed.

Definition union (uf: t) (a b: elt) : t :=
  let a' := repr uf a in
  let b' := repr uf b in
  match M.elt_eq a' b' with
  | left EQ => uf
  | right NEQ => identify uf a' b' (repr_res_none uf a) (union_not_same_class uf a b NEQ)
  end.

Lemma repr_union_1:
  forall uf a b x, repr uf x <> repr uf a -> repr (union uf a b) x = repr uf x.
Proof.
  intros. unfold union. destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto.
  apply repr_identify_1. auto.
Qed.

Lemma repr_union_2:
  forall uf a b x, repr uf x = repr uf a -> repr (union uf a b) x = repr uf b.
Proof.
  intros. unfold union. destruct (M.elt_eq (repr uf a) (repr uf b)).
  congruence.
  rewrite <- (repr_canonical uf b). apply repr_identify_2. auto.
Qed.

Lemma repr_union_3:
  forall uf a b, repr (union uf a b) b = repr uf b.
Proof.
  intros. unfold union. destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto. apply repr_identify_1. auto.
Qed.

Lemma sameclass_union_1:
  forall uf a b, sameclass (union uf a b) a b.
Proof.
  intros; red. rewrite repr_union_2; auto. rewrite repr_union_3. auto.
Qed.

Lemma sameclass_union_2:
  forall uf a b x y, sameclass uf x y -> sameclass (union uf a b) x y.
Proof.
  unfold sameclass; intros.
  destruct (M.elt_eq (repr uf x) (repr uf a));
  destruct (M.elt_eq (repr uf y) (repr uf a)).
  repeat rewrite repr_union_2; auto.
  congruence. congruence.
  repeat rewrite repr_union_1; auto.
Qed.

Lemma sameclass_union_3:
  forall uf a b x y,
  sameclass (union uf a b) x y ->
     sameclass uf x y
  \/ sameclass uf x a /\ sameclass uf y b
  \/ sameclass uf x b /\ sameclass uf y a.
Proof.
  intros until y. unfold sameclass.
  destruct (M.elt_eq (repr uf x) (repr uf a));
  destruct (M.elt_eq (repr uf y) (repr uf a)).
  intro. left. congruence.
  rewrite repr_union_2; auto. rewrite repr_union_1; auto.
  rewrite repr_union_1; auto. rewrite repr_union_2; auto.
  repeat rewrite repr_union_1; auto.
Qed.

(* Merge *)

Definition merge (uf: t) (a b: elt) : t :=
  let a' := repr uf a in
  let b' := repr uf b in
  match M.elt_eq a' b' with
  | left EQ => uf
  | right NEQ => identify uf a' b (repr_res_none uf a) (not_eq_sym NEQ)
  end.

Lemma repr_merge:
  forall uf a b x, repr (merge uf a b) x = repr (union uf a b) x.
Proof.
  intros. unfold merge, union. destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto.
  destruct (M.elt_eq (repr uf x) (repr uf a)).
  repeat rewrite repr_identify_2; auto. rewrite repr_canonical; auto.
  repeat rewrite repr_identify_1; auto.
Qed.

Lemma sameclass_merge:
  forall uf a b x y, sameclass (merge uf a b) x y <-> sameclass (union uf a b) x y.
Proof.
  unfold sameclass; intros. repeat rewrite repr_merge. tauto.
Qed.

(* Path order and merge *)

Definition path_ord (uf: t) : elt -> elt -> Prop := order uf.(m).

Lemma path_ord_wellfounded:
  forall uf, well_founded (path_ord uf).
Proof.
  intros. apply mwf.
Qed.

Lemma path_ord_canonical:
  forall uf x y, repr uf x = x -> ~path_ord uf y x.
Proof.
  intros; red; intros. hnf in H0.
  assert (M.get x (m uf) = None). rewrite <- H. apply repr_res_none.
  congruence.
Qed.

Lemma path_ord_merge_1:
  forall uf a b x y,
  path_ord uf x y -> path_ord (merge uf a b) x y.
Proof.
  intros. unfold merge.
  destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto.
  red. simpl. red. rewrite M.gsspec. rewrite dec_eq_false. apply H.
  red; intros. hnf in H. generalize (repr_res_none uf a). congruence.
Qed.

Lemma path_ord_merge_2:
  forall uf a b,
  repr uf a <> repr uf b -> path_ord (merge uf a b) b (repr uf a).
Proof.
  intros. unfold merge.
  destruct (M.elt_eq (repr uf a) (repr uf b)).
  congruence.
  red. simpl. red. rewrite M.gsspec. rewrite dec_eq_true; auto.
Qed.

(* Path length and merge *)

Section PATHLEN.

Variable uf: t.

Definition F_pathlen (a: elt) (rec: forall b, order uf.(m) b a -> nat) : nat :=
  match getlink uf.(m) a with
  | inleft (exist a' P) => S (rec a' P)
  | inright _ => O
  end.

Definition pathlen (a: elt) : nat := Fix uf.(mwf) (fun _ => nat) F_pathlen a.

Lemma pathlen_unroll:
  forall a, pathlen a = match M.get a uf.(m) with Some a' => S(pathlen a') | None => O end.
Proof.
  intros. unfold pathlen at 1. rewrite Fix_eq.
  unfold F_pathlen. destruct (getlink uf.(m) a) as [[a' P] | Q].
  rewrite P; auto.
  rewrite Q; auto.
  intros. unfold F_pathlen. destruct (getlink (m uf) x) as [[a' P] | Q]; auto.
Qed.

Lemma pathlen_none:
  forall a,
  M.get a uf.(m) = None ->
  pathlen a = 0.
Proof.
  intros. rewrite pathlen_unroll. rewrite H; auto.
Qed.

Lemma pathlen_some:
  forall a a',
  M.get a uf.(m) = Some a' ->
  pathlen a = S (pathlen a').
Proof.
  intros. rewrite pathlen_unroll. rewrite H; auto.
Qed.

Lemma pathlen_zero:
  forall a, repr uf a = a <-> pathlen a = O.
Proof.
  intros; split; intros.
  apply pathlen_none. rewrite <- H. apply repr_res_none.
  apply repr_none. rewrite pathlen_unroll in H.
  destruct (M.get a (m uf)); congruence.
Qed.

End PATHLEN.

(* Path length and merge *)

Lemma pathlen_merge:
  forall uf a b x,
  pathlen (merge uf a b) x =
    if M.elt_eq (repr uf a) (repr uf b) then
      pathlen uf x
    else if M.elt_eq (repr uf x) (repr uf a) then
      pathlen uf x + pathlen uf b + 1
    else
      pathlen uf x.
Proof.
  intros. unfold merge.
  destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto.
  set (uf' := identify uf (repr uf a) b (repr_res_none uf a) (not_eq_sym n)).
  pattern x. apply (well_founded_ind (mwf uf')); intros.
  rewrite (pathlen_unroll uf'). destruct (M.get x0 (m uf')) as [x'|] eqn:G.
  rewrite H; auto. simpl in G. rewrite M.gsspec in G.
  destruct (M.elt_eq x0 (repr uf a)). rewrite e. rewrite repr_canonical. rewrite dec_eq_true.
  inversion G. subst x'. rewrite dec_eq_false; auto.
  replace (pathlen uf (repr uf a)) with 0. omega.
  symmetry. apply pathlen_none. apply repr_res_none.
  rewrite (repr_unroll uf x0), (pathlen_unroll uf x0); rewrite G.
  destruct (M.elt_eq (repr uf x') (repr uf a)); omega.
  simpl in G. rewrite M.gsspec in G. destruct (M.elt_eq x0 (repr uf a)); try discriminate.
  rewrite (repr_none uf x0) by auto. rewrite dec_eq_false; auto.
  symmetry. apply pathlen_zero; auto. apply repr_none; auto.
Qed.

Lemma pathlen_gt_merge:
  forall uf a b x y,
  repr uf x = repr uf y ->
  pathlen uf x > pathlen uf y ->
  pathlen (merge uf a b) x > pathlen (merge uf a b) y.
Proof.
  intros. repeat rewrite pathlen_merge.
  destruct (M.elt_eq (repr uf a) (repr uf b)). auto.
  rewrite H. destruct (M.elt_eq (repr uf y) (repr uf a)).
  omega. auto.
Qed.

(* Path compression *)

Section COMPRESS.

Variable uf: t.
Variable a b: elt.
Hypothesis a_diff_b: a <> b.
Hypothesis a_repr_b: repr uf a = b.

Lemma compress_order:
  forall x y,
  order (M.set a b uf.(m)) y x ->
  order uf.(m) y x \/ (x = a /\ y = b).
Proof.
  intros until y. unfold order. rewrite M.gsspec.
  destruct (M.elt_eq x a).
  intuition congruence.
  auto.
Qed.

Remark compress_Acc:
  forall x,
  Acc (order uf.(m)) x -> Acc (order (M.set a b uf.(m))) x.
Proof.
  induction 1. constructor; intros.
  destruct (compress_order _ _ H1) as [A | [A B]].
  auto.
  subst x y. constructor; intros.
  destruct (compress_order _ _ H2) as [A | [A B]].
  red in A. generalize (repr_res_none uf a). congruence.
  congruence.
Qed.

Lemma compress_wf:
  well_founded (order (M.set a b uf.(m))).
Proof.
  red; intros. apply compress_Acc. apply uf.(mwf).
Qed.

Definition compress := mk (M.set a b uf.(m)) compress_wf.

Lemma repr_compress:
  forall x, repr compress x = repr uf x.
Proof.
  apply (well_founded_ind (mwf compress)); intros.
  rewrite (repr_unroll compress).
  destruct (M.get x (m compress)) as [y|] eqn:G.
  rewrite H; auto.
  simpl in G. rewrite M.gsspec in G. destruct (M.elt_eq x a).
  inversion G. subst x y. rewrite <- a_repr_b. apply repr_canonical.
  symmetry; apply repr_some; auto.
  simpl in G. rewrite M.gsspec in G. destruct (M.elt_eq x a).
  congruence.
  symmetry; apply repr_none; auto.
Qed.

End COMPRESS.

(* Find with path compression *)

Section FIND.

Variable uf: t.

Program Fixpoint find_x (a: elt) {wf (order uf.(m)) a} :
    { r: elt * t | fst r = repr uf a /\ forall x, repr (snd r) x = repr uf x } :=
  match M.get a uf.(m) with
  | Some a' =>
      match find_x a' with
      | pair b uf' => (b, compress uf' a b _ _)
      end
  | None => (a, uf)
  end.
Next Obligation.
  red. auto.
Qed.
Next Obligation.
  (* a <> b*)
  destruct (find_x a')
  as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous.
  apply repr_some_diff. auto.
Qed.
Next Obligation.
  destruct (find_x a') as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous.
  rewrite B. apply repr_some. auto.
Qed.
Next Obligation.
  split.
  destruct (find_x a')
  as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous.
  symmetry. apply repr_some. auto.
  intros. rewrite repr_compress.
  destruct (find_x a')
  as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous. auto.
Qed.
Next Obligation.
  split; auto. symmetry. apply repr_none. auto.
Qed.
Next Obligation.
  apply mwf.
Defined.

Definition find (a: elt) : elt * t := proj1_sig (find_x a).

Lemma find_repr:
  forall a, fst (find a) = repr uf a.
Proof.
  unfold find; intros. destruct (find_x a) as [[b uf'] [A B]]. simpl. auto.
Qed.

Lemma find_unchanged:
  forall a x, repr (snd (find a)) x = repr uf x.
Proof.
  unfold find; intros. destruct (find_x a) as [[b uf'] [A B]]. simpl. auto.
Qed.

Lemma sameclass_find_1:
  forall a x y, sameclass (snd (find a)) x y <-> sameclass uf x y.
Proof.
  unfold sameclass; intros. repeat rewrite find_unchanged. tauto.
Qed.

Lemma sameclass_find_2:
  forall a, sameclass uf a (fst (find a)).
Proof.
  intros. rewrite find_repr. apply sameclass_repr.
Qed.

Lemma sameclass_find_3:
  forall a, sameclass (snd (find a)) a (fst (find a)).
Proof.
  intros. rewrite sameclass_find_1. apply sameclass_find_2.
Qed.

End FIND.

End UF.


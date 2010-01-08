Require Import List.
Require Import InterfGraphMapImp.

Section fold_assoc_interf_map.

Variable A : Type.

Inductive eq_set_option : option VertexSet.t -> option VertexSet.t -> Prop :=
|None_eq : eq_set_option None None
|Some_eq : forall s s', VertexSet.Equal s s' -> eq_set_option (Some s) (Some s').

Definition EqualSetMap m1 m2 := forall x, eq_set_option (VertexMap.find x m1) (VertexMap.find x m2).

Lemma EqualSetMap_refl : forall m, EqualSetMap m m.

Proof.
unfold EqualSetMap. intro m. intro x.
destruct (VertexMap.find x m).
constructor. intuition.
constructor.
Qed.

Lemma EqualSetMap_trans : forall m1 m2 m3,
EqualSetMap m1 m2 ->
EqualSetMap m2 m3 ->
EqualSetMap m1 m3.

Proof.
intros m1 m2 m3 H H0.
unfold EqualSetMap in *.
intro x.
generalize (H x). clear H. intro H.
generalize (H0 x). clear H0. intro H0.
destruct (VertexMap.find x m1).
inversion H. subst.
rewrite <-H2 in H0.
destruct (VertexMap.find x m3).
constructor. inversion H0. subst.
rewrite H3. assumption.
inversion H0.
destruct (VertexMap.find x m3).
inversion H0. inversion H. subst. rewrite <-H4 in H1. inversion H1.
constructor.
Qed.

Lemma fold_left_compat_map : forall (f : VertexMap.t VertexSet.t -> A -> VertexMap.t VertexSet.t) l e e',
EqualSetMap e e' ->
(forall e1 e2 a, EqualSetMap e1 e2 -> EqualSetMap (f e1 a) (f e2 a)) ->
EqualSetMap (fold_left f l e) (fold_left f l e').

Proof.
intro f;induction l;simpl.
auto.
intros e e' H H0 H1.
apply (IHl (f e a) (f e' a)).
apply H0;assumption.
assumption.
Qed.

Lemma fold_left_assoc_map : forall l (f : VertexMap.t VertexSet.t -> A -> VertexMap.t VertexSet.t) x h,
(forall (y z : A) s, EqualSetMap (f (f s y) z) (f (f s z) y)) ->
(forall e1 e2 a, EqualSetMap e1 e2 -> EqualSetMap (f e1 a) (f e2 a)) ->
EqualSetMap (fold_left f (h :: l) x) (f (fold_left f l x) h).

Proof.
induction l;simpl;intros f x h H H0.
apply EqualSetMap_refl.
apply EqualSetMap_trans with (m2 := fold_left f (h :: l) (f x a)).
simpl. apply fold_left_compat_map. apply H.
assumption.
apply IHl. assumption. assumption.
Qed.
(*
Add Morphism EqualSetMap : equalsetmap_m.

Proof.
unfold EqualSetMap, VertexMap.Equal. split; intros.
rewrite <-(H0 x1). rewrite <-(H x1). apply H1.
rewrite (H0 x1). rewrite (H x1). apply H1.
Qed.
*)
End fold_assoc_interf_map.
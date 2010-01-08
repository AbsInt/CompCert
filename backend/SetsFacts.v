Require Import FSets.
Set Implicit Arguments.

(* Useful properties over finite sets and ordered types *)

Module MyOTFacts (M : OrderedType).

Section compat.

Lemma compat_not_compat : forall f : M.t -> bool,
compat_bool M.eq f ->
compat_bool M.eq (fun x => negb (f x)).

Proof.
unfold compat_bool;intros f H.
intros; unfold negb.
rewrite (H x y H0);reflexivity.
Qed.

End compat.

End MyOTFacts.

Module MyFacts (M : S).

Import M.
Module Import Props := Properties M.
Module Import Facts := OrderedTypeFacts E.
Module Import OTFacts := MyOTFacts E.

Lemma set_induction2 : forall s,
Empty s \/ exists x, exists s', Add x s' s.

Proof.
intros. case_eq (choose s);intros.
right. exists e. exists (remove e s).
constructor;intro H0.
destruct (eq_dec e y).
left;assumption.
right;apply (remove_2 n H0).
destruct H0.
rewrite <-H0;apply (choose_1 H).
eapply remove_3;eassumption.
left;apply (choose_2 H).
Qed.

Lemma equal_equivlist : forall s s',
Equal s s' -> equivlistA E.eq (elements s) (elements s').

Proof.
unfold equivlistA.
generalize elements_1;generalize elements_2;intros H0 H1 s s' H x.
split;intro H2.
apply H1;rewrite <-H;apply H0;assumption.
apply H1;rewrite H;apply H0;assumption.
Qed.

Section Fold_Facts.

Variable A : Type.

Lemma fold_left_compat_set : forall (f : t -> A -> t) l e e',
Equal e e' ->
(forall e1 e2 a, Equal e1 e2 -> Equal (f e1 a) (f e2 a)) ->
Equal (fold_left f l e) (fold_left f l e').

Proof.
intros f l.
induction l;simpl.
auto.
intros e e' H H0 H1.
apply (IHl (f e a) (f e' a)).
apply H0;assumption.
assumption.
Qed.

Lemma fold_left_assoc : forall l f x h,
(forall (y z : A) s, Equal (f (f s y) z) (f (f s z) y)) ->
(forall e1 e2 a, Equal e1 e2 -> Equal (f e1 a) (f e2 a)) ->
Equal (fold_left f (h :: l) x) (f (fold_left f l x) h).

Proof.
induction l;simpl;intros f x h H H0.
intuition.
rewrite <-IHl;simpl;try assumption.
apply fold_left_compat_set;[apply H|];auto.
Qed.

Lemma NoDupA_elements : forall s,
NoDupA E.eq (elements s).

Proof.
intro s.
apply SortA_NoDupA with (ltA := E.lt).
apply E.eq_refl.
apply E.eq_sym.
apply E.lt_trans.
apply E.lt_not_eq.
apply Facts.lt_eq.
apply Facts.eq_lt.
apply elements_3.
Qed.

End Fold_Facts.
End MyFacts.
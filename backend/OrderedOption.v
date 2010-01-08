Require Import FSets.

(* Definition of options types as ordered types,
    in order to define weights *)

Module OrderedOpt (O : OrderedType) <: OrderedType.

Definition t := option O.t.

Inductive eq_ : t -> t -> Prop :=
|None_eq : eq_ None None
|Some_eq : forall x y, O.eq x y -> eq_ (Some x) (Some y).

Definition eq := eq_.

Inductive lt_ : t -> t -> Prop := 
|None_lt : forall o : O.t, lt_ None (Some o)
|Some_lt : forall o o', O.lt o o' -> lt_ (Some o) (Some o').

Definition lt := lt_.

Lemma eq_refl : forall x : t, eq x x.

Proof.
unfold eq;intro x;destruct x;constructor;apply O.eq_refl.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.

Proof.
unfold eq;intros x y H;destruct x;destruct y.
constructor;inversion H;apply O.eq_sym;assumption.
inversion H.
inversion H.
assumption.
Qed.

Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.

Proof.
unfold eq;intros x y z H H0.
inversion H;inversion H0.
constructor.
rewrite <-H2 in H4;inversion H4.
rewrite <-H3 in H4;inversion H4.
rewrite <-H3 in H5;inversion H5;subst.
constructor;apply (O.eq_trans H1 H4).
Qed.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

Proof.
unfold lt;intros x y z H H0.
inversion H;inversion H0;constructor.
rewrite <-H3 in H4;inversion H4.
rewrite <-H3 in H5;inversion H5.
subst.
apply (O.lt_trans H1 H4).
Qed.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.

Proof.
intros x y H.
unfold eq;intro Heq.
inversion H;inversion Heq.
rewrite <-H3 in H1;inversion H1.
rewrite <-H0 in H3;inversion H3.
rewrite <-H1 in H3;inversion H3.
subst;inversion H4;inversion H5;subst.
elim (O.lt_not_eq H0 H3).
Qed.

Lemma compare : forall x y : t, Compare lt eq x y.

Proof.
intros x y.
destruct x;destruct y.
destruct (O.compare t0 t1);
[apply LT;unfold lt|apply EQ;unfold eq|apply GT;unfold lt];constructor;assumption.
apply GT;unfold lt;constructor.
apply LT;unfold lt;constructor.
apply EQ;unfold eq;constructor.
Qed.

Lemma eq_dec : forall x y, {eq x y}+{~eq x y}.

Proof.
intros x y.
destruct (compare x y).
right. apply lt_not_eq. assumption.
left. assumption.
right. intro H. generalize (eq_sym _ _ H). intro H0. elim (lt_not_eq _ _ l H0).
Qed.

End OrderedOpt.
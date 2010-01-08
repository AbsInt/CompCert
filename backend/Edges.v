Require Import FSets.
Require Import OrderedOption.
Require Import ZArith.
Require Import MyRegisters.

(* Module of edges in a simple graph : there is never more
   than one edge between two vertices *)

Module Edge.

Module Import Vertex := Regs.

(* Definition of pair of vertices, to represent edges *)
Module VertexPair := PairOrderedType Vertex Vertex.

(* N_as_OT is the OrderedType with t := N,
   to describe weights of edges *)
Module OptionN_as_OT := OrderedOpt N_as_OT.

(* An edge is finally a pair of endpoints and a weight *)
Module E := PairOrderedType VertexPair OptionN_as_OT.

(* Useful modules imports *)
Module Import OTFacts := OrderedTypeFacts Vertex.
Module OTPairFacts := OrderedTypeFacts VertexPair.
Module OTEFacts := OrderedTypeFacts E.

(* t is simply E.t *)
Definition t := E.t.

(* accessors to the edges, their endpoints and their weight *)
Definition get_edge : t -> (Vertex.t*Vertex.t) := fun x => fst x.
Definition fst_ext : t -> Vertex.t := fun x => fst (get_edge x).
Definition snd_ext : t -> Vertex.t := fun x => snd (get_edge x).
Definition get_weight : t -> option N := fun x => snd x.

(* get_edge e is only the extremities of e *)
Lemma get_edge_ext : forall e,
get_edge e = (fst_ext e,snd_ext e).

Proof.
unfold fst_ext. unfold snd_ext. unfold get_edge.
simpl. intro e. destruct (fst e);auto.
Qed.

(* An edge is the pair of vertices and a weight *)
Lemma edge_edge_weight : forall e, 
e = (get_edge e, get_weight e).

Proof.
unfold get_edge. unfold get_weight.
simpl. intro e. destruct e;auto.
Qed.

(* Expansion of an edge *)
Lemma edge_eq : forall e,
e = (fst_ext e, snd_ext e, get_weight e).

Proof.
intro e. unfold get_weight.
destruct e. unfold fst_ext. unfold snd_ext. unfold get_edge. simpl.
destruct p. auto.
Qed.

(* Equality does not depend on the order of endpoints, e.g
   (x,y,w) is equal to (y,x,w) so we need to define ordered edges *)
Definition ordered_edge e := 
match (lt_dec (snd_ext e) (fst_ext e)) with
|left _ => (snd_ext e, fst_ext e, get_weight e)
|right _ => e
end.

(* Commutativity of ordered_edge*)
Lemma ordered_edge_comm : forall x y o,
E.eq (ordered_edge (x,y,o)) (ordered_edge (y,x,o)).

Proof.
unfold ordered_edge, snd_ext, fst_ext, get_edge. intros x y o. simpl.
destruct (lt_dec y x);destruct (lt_dec x y).
elim (lt_not_gt r r0).
apply E.eq_refl.
apply E.eq_refl.
destruct (Vertex.compare x y).
elim (n0 l).
unfold E.eq. simpl. repeat split; auto.
apply Vertex.eq_sym. auto.
apply OptionN_as_OT.eq_refl.
elim (n l).
Qed.

(* Definition of equality as equality of s *)
Definition eq x y := E.eq (ordered_edge x) (ordered_edge y).

(* The weak equality is the equality of their type (interference or preference)
   and of their extremities, but not necessarily of their weight *)
Definition weak_eq x y := 
(Vertex.eq (fst_ext x) (fst_ext y) /\ Vertex.eq (snd_ext x) (snd_ext y)) \/
(Vertex.eq (fst_ext x) (snd_ext y) /\ Vertex.eq (snd_ext x) (fst_ext y)).

(* Two edges having equal extremities (in the right order) and equal weights
   are equal *)
Lemma eq_ordered_eq : forall x y,
E.eq x y -> eq x y.

Proof.
unfold eq;unfold E.eq;intros x y H.
unfold ordered_edge;unfold fst_ext;unfold snd_ext;unfold get_edge;simpl.
destruct x as [x wx];destruct x as [x1 x2];
destruct y as [y wy];destruct y as [y1 y2];simpl in *.
destruct (lt_dec x2 x1); destruct (lt_dec y2 y1);simpl in *.
intuition.
destruct H as [H HH];destruct H as [H H0].
elim n. apply eq_lt with (y := x2).
 apply Vertex.eq_sym;assumption.
 apply lt_eq with (y := x1);assumption.
destruct H as [H HH];destruct H as [H H0].
elim n. apply eq_lt with (y := y2).
 assumption.
 apply lt_eq with (y := y1); auto. apply Regs.eq_sym. auto.
assumption.
Qed.

(* Definition of lt as the lexicographic order on endpoints
    of the edges, after ordering *)
Definition lt x y :=  VertexPair.lt (get_edge (ordered_edge x)) (get_edge (ordered_edge y)) \/
                             (VertexPair.eq (get_edge (ordered_edge x)) (get_edge (ordered_edge y)) /\
                              OptionN_as_OT.lt (get_weight x) (get_weight y)).

Lemma eq_refl : forall x, eq x x.

Proof.
unfold eq;unfold E.eq.
repeat split;[apply Vertex.eq_refl|apply Vertex.eq_refl|apply OptionN_as_OT.eq_refl].
Qed.

Lemma eq_sym : forall x y, eq x y -> eq y x.

Proof.
unfold eq;unfold E.eq;intros x y H. intuition.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
apply OptionN_as_OT.eq_sym;assumption.
Qed.

Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.

Proof.
unfold eq;intros x y z H H0.
apply (E.eq_trans _ _ _ H H0).
Qed.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

Proof.
unfold lt;unfold get_edge;unfold ordered_edge;intros x y z H H0.
destruct (lt_dec (snd_ext x) (fst_ext x));simpl in *.
destruct (lt_dec (snd_ext y) (fst_ext y));simpl in *.
destruct (lt_dec (snd_ext z) (fst_ext z));simpl in *.
destruct H;destruct H0.
left;apply (VertexPair.lt_trans _ _ _ H H0).
left;apply OTPairFacts.lt_eq with (y := (snd_ext y, fst_ext y));simpl.
unfold VertexPair.lt in H;simpl in H;assumption.
destruct H0 as [H0 HH0].
unfold VertexPair.eq in H0;assumption.
left;apply OTPairFacts.eq_lt with (y := (snd_ext y, fst_ext y));simpl.
destruct H as [H HH].
unfold VertexPair.eq in H;unfold VertexPair.lt in H0;
simpl in H0;assumption.
unfold VertexPair.lt in H0;simpl in H0;assumption.
right;destruct H as [H HH];destruct H0 as [H0 HH0];split.
apply (VertexPair.eq_trans _ _ _ H H0).
apply (OptionN_as_OT.lt_trans _ _ _ HH HH0).
destruct H;destruct H0.
left;apply (VertexPair.lt_trans _ _ _ H H0).
left;apply OTPairFacts.lt_eq with (y := (snd_ext y, fst_ext y));simpl.
unfold VertexPair.lt in H;simpl in H;assumption.
destruct H0 as [H0 HH0].
unfold VertexPair.eq in H0;assumption.
left;apply OTPairFacts.eq_lt with (y := (snd_ext y, fst_ext y));simpl.
destruct H as [H HH].
unfold VertexPair.eq in H;unfold VertexPair.lt in H0;
simpl in H0;assumption.
unfold VertexPair.lt in H0;simpl in H0;assumption.
right;destruct H as [H HH];destruct H0 as [H0 HH0];split.
apply (VertexPair.eq_trans _ _ _ H H0).
apply (OptionN_as_OT.lt_trans _ _ _ HH HH0).
destruct (lt_dec (snd_ext y) (fst_ext y));simpl in *.
elim (n r0).
destruct (lt_dec (snd_ext z) (fst_ext z));simpl in *.
destruct H;destruct H0.
left;apply (VertexPair.lt_trans _ _ _ H H0).
left;apply OTPairFacts.lt_eq with (y := (fst y));simpl.
unfold VertexPair.lt in H;simpl in H;assumption.
destruct H0 as [H0 HH0].
unfold VertexPair.eq in H0;assumption.
left;apply OTPairFacts.eq_lt with (y := (fst y));simpl.
destruct H as [H HH].
unfold VertexPair.eq in H;unfold VertexPair.lt in H0;
simpl in H0;assumption.
unfold VertexPair.lt in H0;simpl in H0;assumption.
right;destruct H as [H HH];destruct H0 as [H0 HH0];split.
apply (VertexPair.eq_trans _ _ _ H H0).
apply (OptionN_as_OT.lt_trans _ _ _ HH HH0).
destruct H;destruct H0.
left;apply (VertexPair.lt_trans _ _ _ H H0).
left;apply OTPairFacts.lt_eq with (y := (fst y));simpl.
unfold VertexPair.lt in H;simpl in H;assumption.
destruct H0 as [H0 HH0].
unfold VertexPair.eq in H0;assumption.
left;apply OTPairFacts.eq_lt with (y := (fst y));simpl.
destruct H as [H HH].
unfold VertexPair.eq in H;unfold VertexPair.lt in H0;
simpl in H0;assumption.
unfold VertexPair.lt in H0;simpl in H0;assumption.
right;destruct H as [H HH];destruct H0 as [H0 HH0];split.
apply (VertexPair.eq_trans _ _ _ H H0).
apply (OptionN_as_OT.lt_trans _ _ _ HH HH0).
destruct (lt_dec (snd_ext y) (fst_ext y));simpl in *.
destruct (lt_dec (snd_ext z) (fst_ext z));simpl in *.
destruct H;destruct H0.
left;apply (VertexPair.lt_trans _ _ _ H H0).
left;apply OTPairFacts.lt_eq with (y := (snd_ext y, fst_ext y));simpl.
unfold VertexPair.lt in H;simpl in H;assumption.
destruct H0 as [H0 HH0].
unfold VertexPair.eq in H0;assumption.
left;apply OTPairFacts.eq_lt with (y := (snd_ext y,fst_ext y));simpl.
destruct H as [H HH].
unfold VertexPair.eq in H;unfold VertexPair.lt in H0;
simpl in H0;assumption.
unfold VertexPair.lt in H0;simpl in H0;assumption.
right;destruct H as [H HH];destruct H0 as [H0 HH0];split.
apply (VertexPair.eq_trans _ _ _ H H0).
apply (OptionN_as_OT.lt_trans _ _ _ HH HH0).
destruct H;destruct H0.
left;apply (VertexPair.lt_trans _ _ _ H H0).
left;apply OTPairFacts.lt_eq with (y := (snd_ext y,fst_ext y));simpl.
unfold VertexPair.lt in H;simpl in H;assumption.
destruct H0 as [H0 HH0].
unfold VertexPair.eq in H0;assumption.
left;apply OTPairFacts.eq_lt with (y := (snd_ext y, fst_ext y));simpl.
destruct H as [H HH].
unfold VertexPair.eq in H;unfold VertexPair.lt in H0;
simpl in H0;assumption.
unfold VertexPair.lt in H0;simpl in H0;assumption.
right;destruct H as [H HH];destruct H0 as [H0 HH0];split.
apply (VertexPair.eq_trans _ _ _ H H0).
apply (OptionN_as_OT.lt_trans _ _ _ HH HH0).
destruct (lt_dec (snd_ext y) (fst_ext y));simpl in *.
elim (n0 r).
destruct (lt_dec (snd_ext z) (fst_ext z));simpl in *.
destruct H;destruct H0.
left;apply (VertexPair.lt_trans _ _ _ H H0).
left;apply OTPairFacts.lt_eq with (y := (fst y));simpl.
unfold VertexPair.lt in H;simpl in H;assumption.
destruct H0 as [H0 HH0].
unfold VertexPair.eq in H0;assumption.
left;apply OTPairFacts.eq_lt with (y := (fst y));simpl.
destruct H as [H HH].
unfold VertexPair.eq in H;unfold VertexPair.lt in H0;
simpl in H0;assumption.
unfold VertexPair.lt in H0;simpl in H0;assumption.
right;destruct H as [H HH];destruct H0 as [H0 HH0];split.
apply (VertexPair.eq_trans _ _ _ H H0).
apply (OptionN_as_OT.lt_trans _ _ _ HH HH0).
destruct H;destruct H0.
left;apply (VertexPair.lt_trans _ _ _ H H0).
left;apply OTPairFacts.lt_eq with (y := (fst y));simpl.
unfold VertexPair.lt in H;simpl in H;assumption.
destruct H0 as [H0 HH0].
unfold VertexPair.eq in H0;assumption.
left;apply OTPairFacts.eq_lt with (y := (fst y));simpl.
destruct H as [H HH].
unfold VertexPair.eq in H;unfold VertexPair.lt in H0;
simpl in H0;assumption.
unfold VertexPair.lt in H0;simpl in H0;assumption.
right;destruct H as [H HH];destruct H0 as [H0 HH0];split.
apply (VertexPair.eq_trans _ _ _ H H0).
apply (OptionN_as_OT.lt_trans _ _ _ HH HH0).
Qed.

Lemma weight_ordered_weight : forall x,
get_weight x = get_weight (ordered_edge x).

Proof.
intro x;unfold ordered_edge;unfold get_weight;simpl.
destruct (lt_dec (snd_ext x) (fst_ext x));simpl;reflexivity.
Qed.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.

Proof.
unfold lt;unfold eq;unfold E.eq;intros x y H.
destruct H.
generalize (VertexPair.lt_not_eq _ _ H);intro H0.
unfold VertexPair.eq in H0.
intro H1; elim H0.
destruct H1 as [H1 H2].
unfold get_edge;assumption.
destruct H as [H H0].
unfold VertexPair.eq in H.
unfold get_edge in H.
intro H1.
destruct H1 as [H1 HH1].
elim (OptionN_as_OT.lt_not_eq _ _ H0).
rewrite (weight_ordered_weight x).
rewrite (weight_ordered_weight y).
unfold get_weight;assumption.
Qed.

Lemma compare : forall x y, Compare lt eq x y.

Proof.
intros x y.
destruct (OTEFacts.lt_dec (ordered_edge x) (ordered_edge y)).
apply LT.
unfold lt;unfold get_edge;unfold VertexPair.lt;
unfold VertexPair.eq.
rewrite (weight_ordered_weight x).
rewrite (weight_ordered_weight y).
unfold get_weight.
destruct (ordered_edge x) as [ex wx];destruct ex as [ex1 ex2];
destruct (ordered_edge y) as [ey wy];destruct ey as [ey1 ey2];simpl in *.
assumption.
destruct (OTEFacts.eq_dec (ordered_edge x) (ordered_edge y)).
apply EQ.
unfold eq.
destruct (ordered_edge x) as [ex wx];destruct ex as [ex1 ex2];
destruct (ordered_edge y) as [ey wy];destruct ey as [ey1 ey2];simpl in *.
destruct a as [H H0];destruct H as [H H1].
unfold E.eq;auto.
apply GT.
generalize (OTEFacts.le_neq n n0);intro H.
unfold lt;unfold get_edge;unfold VertexPair.lt;
unfold VertexPair.eq.
rewrite (weight_ordered_weight x).
rewrite (weight_ordered_weight y).
unfold get_weight.
destruct (ordered_edge x) as [ex wx];destruct ex as [ex1 ex2];
destruct (ordered_edge y) as [ey wy];destruct ey as [ey1 ey2];simpl in *.
assumption.
Qed.

(* Edges commutativity *)
Lemma edge_comm : forall x y o, eq (x,y,o) (y,x,o).

Proof.
unfold eq;apply ordered_edge_comm.
Qed.

(* Definition of affinity edges *)
Definition aff_edge x := exists w, get_weight x = Some w.

(* Definition of interference edges *)
Definition interf_edge x := get_weight x = None.

(* An edge is incident to a vertex iff this vertex is an endpoint of the edge *)
Definition incident e x := Vertex.eq x (fst_ext e) \/ Vertex.eq x (snd_ext e).

(* An edge is incident to a vertex, or is not *)
Lemma incident_dec : forall e x,
incident e x \/ ~incident e x.

Proof.
intros e x.
destruct (eq_dec x (fst_ext e)).
left;unfold incident;left;assumption.
destruct (eq_dec x (snd_ext e)).
left;unfold incident;right;assumption.
right;unfold incident;intro Heq.
destruct Heq;[elim (n H)|elim (n0 H)].
Qed.

(* Definition redirect : redirect x y e replaces the extremity x of the edge e
    with y, if e is incident to x *)
Definition redirect x y e :=
match eq_dec (fst_ext e) x with
|left _ => (y, snd_ext e, get_weight e)
|right _ => match eq_dec (snd_ext e) x with
                 | left _ => (fst_ext e, y, get_weight e)
                 | right _ => e
                 end
end.

(* Decidable equality over edges *)
Lemma eq_dec : forall x y, {eq x y}+{~eq x y}.

Proof.
intros x y.
destruct (compare x y).
right. apply lt_not_eq. assumption.
left. assumption.
right. intro H. generalize (eq_sym _ _ H). intro H0. elim (lt_not_eq _ _ l H0).
Qed.

(* Equality of edges implies constraints of their endpoints *)
Lemma eq_charac : forall x y,
eq x y -> (Vertex.eq (fst_ext x) (fst_ext y) /\ Vertex.eq (snd_ext x) (snd_ext y)) \/
                (Vertex.eq (fst_ext x) (snd_ext y) /\ Vertex.eq (snd_ext x) (fst_ext y)).

Proof.
intros x y H;unfold eq in H;unfold ordered_edge in H;
unfold get_edge in H.
destruct (lt_dec (snd_ext x) (fst_ext x));
destruct (lt_dec (snd_ext y) (fst_ext y));
unfold E.eq in H;simpl in H;intuition.
Qed.

Definition same_type e e' := (aff_edge e /\ aff_edge e') \/
                                              (interf_edge e /\ interf_edge e').

End Edge.
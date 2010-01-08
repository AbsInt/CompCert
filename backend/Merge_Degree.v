Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Merge_Adjacency.
Require Import ZArith.
Require Import Edges.
Require Import MyRegisters.
Require Import Merge_Adjacency.
Require Import Interference_adjacency.
Require Import Remove_Vertex_Degree.

Module Register := Regs.

Import Edge Props RegFacts.

(* If x interferes with both (fst_ext e) and (snd_ext e), then
    its degree decreases of one when e is coalesced *)
Lemma merge_degree_dec_inter : forall x e g Hin Haff,
VertexSet.In x (interference_adj (fst_ext e) g) ->
VertexSet.In x (interference_adj (snd_ext e) g) ->
interf_degree g x = S (interf_degree (merge e g Hin Haff) x).

Proof.
intros. unfold interf_degree.
rewrite (cardinal_m (merge_interf_adj_in_both _ _ _ Hin Haff H0 H)).
rewrite remove_cardinal_1. reflexivity. apply interf_adj_comm. auto.
Qed.

(* If x does not interfere with both (fst_ext e) and (snd_ext e)
    then its degree is unchanged when e is coalesced *)
Lemma merge_dec_eq : forall x e g Hin Haff,
~VertexSet.In x (interference_adj (fst_ext e) g) \/
~VertexSet.In x (interference_adj (snd_ext e) g) ->
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
interf_degree g x = interf_degree (merge e g Hin Haff) x.

Proof.
intros. unfold interf_degree. destruct H.
destruct (In_dec x (interference_adj (snd_ext e) g)).
rewrite (cardinal_m (merge_interf_adj_in_snd _ _ _ Hin Haff H0 H1 i)).
rewrite add_cardinal_2. rewrite remove_cardinal_1. reflexivity.
apply interf_adj_comm. auto.
intro. elim H. apply interf_adj_comm. apply (VertexSet.remove_3 H2).
rewrite (cardinal_m (merge_interf_adj_not_in _ _ _ Hin Haff H0 H1 n)). reflexivity.
rewrite (cardinal_m (merge_interf_adj_not_in _ _ _ Hin Haff H0 H1 H)). reflexivity.
Qed.

(* The interference degree of any vertex which is not an endpoint
    of e decreases when e is coalesced *)
Lemma merge_degree_dec : forall x e g Hin Haff,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
interf_degree (merge e g Hin Haff) x <= interf_degree g x.

Proof.
intros. destruct (In_dec x (interference_adj (fst_ext e) g)).
destruct (In_dec x (interference_adj (snd_ext e) g)).
rewrite (merge_degree_dec_inter x e g Hin Haff i i0). auto.
rewrite (merge_dec_eq x e g Hin Haff (or_intror _ n)); auto.
rewrite (merge_dec_eq x e g Hin Haff (or_introl _ n)); auto.
Qed.

(* If x does not interfere with the first endpoint of e then
    x is of low-degree in (merge e g Hin Haff) iff it is in g *)
Lemma low_merge_low_fst : forall x e g K Hin Haff,
~VertexSet.In x (interference_adj (fst_ext e) g) ->
~Register.eq x (snd_ext e) ->
~Register.eq x (fst_ext e) ->
has_low_degree (merge e g Hin Haff) K x = has_low_degree g K x.

Proof.
intros x e g palette Hin Haff H H0 H1. unfold has_low_degree.
rewrite (merge_dec_eq x e g Hin Haff); auto.
Qed.

(* If x does not interfere with the second endpoint of e then
    x is of low-degree in (merge e g Hin Haff) iff it is in g *)
Lemma low_merge_low_snd : forall x e g K Hin Haff,
~VertexSet.In x (interference_adj (snd_ext e) g) ->
~Register.eq x (snd_ext e) ->
~Register.eq x (fst_ext e) ->
has_low_degree (merge e g Hin Haff) K x = has_low_degree g K x.

Proof.
intros x e g palette Hin Haff H H0 H1. unfold has_low_degree.
rewrite (merge_dec_eq x e g Hin Haff); auto.
Qed.

(* A high-degree vertex of (merge e g Hin Haff) is of high-degree in g *)
Lemma merge_low_1 : forall g e x K Haff Hin,
has_low_degree (merge e g Hin Haff) K x = false ->
~Register.eq x (snd_ext e) ->
~Register.eq x (fst_ext e) ->
has_low_degree g K x = false.

Proof.
intros g e x K Haff Hin Hpre H0 H1. unfold has_low_degree in *.
destruct (le_lt_dec K (interf_degree (merge e g Hin Haff) x));
destruct (le_lt_dec K (interf_degree g x )); inversion Hpre.
reflexivity.
generalize (merge_degree_dec x e g Hin Haff H1 H0). intro.
apply False_ind. intuition.
Qed.

(* A low-degree vertex of g is of low-degree in (merge e g Haff Hin) *)
Lemma low_dec : forall x e g Hin Haff K,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
has_low_degree g K x = true ->
has_low_degree (merge e g Hin Haff) K x = true.

Proof.
intros.
case_eq (has_low_degree (merge e g Hin Haff) K x);[auto|intros].
rewrite (merge_low_1 g e x K Haff Hin H2 H0 H) in H1. inversion H1.
Qed.

(* A vertex high-degree vertex of g (which is not an endpoint of e) 
    which is of low-degree in (merge e g p q) belongs to the interference
    neighborhood of the two endpoints of e in g *)
Lemma merge_dec_interf : forall x e k g p q,
has_low_degree g k x = false ->
has_low_degree (merge e g p q) k x = true ->
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
VertexSet.In x (interference_adj (fst_ext e) g) /\
VertexSet.In x (interference_adj (snd_ext e) g).

Proof.
intros.
destruct (In_dec x (interference_adj (fst_ext e) g)).
split. assumption.
destruct (In_dec x (interference_adj (snd_ext e) g)).
assumption.
rewrite (low_merge_low_snd _ _ _ _ p q n H2 H1) in H0. rewrite H0 in H. inversion H.
rewrite (low_merge_low_fst _ _ _ _ p q n H2 H1) in H0. rewrite H0 in H. inversion H.
Qed.

(* A vertex high-degree vertex of g (which is not an endpoint of e) 
    which is of low-degree in (merge e g p q) is of degree k in g *) 
Lemma merge_dec_K : forall x e k g p q,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
has_low_degree g k x = false ->
has_low_degree (merge e g p q) k x = true ->
interf_degree g x = k.

Proof.
intros x e k g p q H0 H1 H2 H3. generalize I. intro H. unfold interf_degree.
assert (VertexSet.In x (interference_adj (fst_ext e) g) /\
        VertexSet.In x (interference_adj (snd_ext e) g)).
apply (merge_dec_interf x e k g p q); auto.
destruct H4.
generalize (merge_degree_dec_inter x e g p q H4 H5). intro.
unfold has_low_degree, interf_degree in *.
destruct (le_lt_dec k (VertexSet.cardinal (interference_adj x (merge e g p q)))).
inversion H3.
destruct (le_lt_dec k (VertexSet.cardinal (interference_adj x g))).
rewrite H6 in l0. rewrite (lt_le_S_eq _ _ l l0). assumption.
inversion H2.
Qed.

(* Reciprocally, a vertex of degree k interfering with
    the two endpoints of g is of low-degree in (merge e g p q) *)
Lemma merge_dec_low : forall x e k g p q,
interf_degree g x = k ->
VertexSet.In x (interference_adj (fst_ext e) g) ->
VertexSet.In x (interference_adj (snd_ext e) g) ->
has_low_degree (merge e g p q) k x = true.

Proof.
unfold interf_degree. intros x e k g p q H0 H1 H2. generalize I. intro H.
assert (~Register.eq x (fst_ext e)).
intro. elim (not_in_interf_self (fst_ext e) g). rewrite H3 in H1. assumption.
assert (~Register.eq x (snd_ext e)).
intro. elim (not_in_interf_self (snd_ext e) g). rewrite H4 in H2. assumption.
generalize (merge_degree_dec_inter x e g p q H1 H2). intro.
unfold has_low_degree, interf_degree in *.
destruct (le_lt_dec k (VertexSet.cardinal (interference_adj x (merge e g p q)))).
rewrite H5 in H0. rewrite <-H0 in l. elim (le_S_irrefl _ l).
reflexivity.
Qed.

(* Again, unused but meaningful theorem, summarizing evolution of degree
   when an edge e is coalesced *)

Theorem merge_degree_evolution : forall x e k g p q,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
((has_low_degree g k x = false /\ has_low_degree (merge e g p q) k x = true)
                                               <->
(interf_degree g x = k /\
 VertexSet.In x (interference_adj (fst_ext e) g) /\ 
 VertexSet.In x (interference_adj (snd_ext e) g))).

Proof.
split; intros.
destruct H1. 
split. apply (merge_dec_K x e k g p q); auto.
apply (merge_dec_interf x e k g p q); auto.
destruct H1. destruct H2.
split. unfold has_low_degree. rewrite H1. 
destruct (le_lt_dec k k). reflexivity. elim (lt_irrefl _ l).
apply merge_dec_low; auto.
Qed.

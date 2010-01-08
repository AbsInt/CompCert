Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Remove_Vertex_Adjacency.
Require Import ZArith.
Require Import Edges.
Require Import MyRegisters.
Require Import Interference_adjacency.

Module Register := Regs.

Import RegFacts Props.

(* The degree of any vertex different from r decreases when
    r is removed from the a graph g. Hence, a low-degree vertex of g
    is a low-degree vertex of (remove_vertex r g) *)
Lemma low_remove_low : forall x r g K,
has_low_degree g K x = true ->
~Register.eq x r ->
has_low_degree (remove_vertex r g) K x = true.

Proof.
intros x r g K H H0. unfold has_low_degree, interf_degree in *.
generalize (sub_remove_interf _ _ g H0);intro H1.
generalize (subset_cardinal H1);intro H2.
destruct (le_lt_dec K (VertexSet.cardinal (interference_adj x g))).
inversion H.
destruct (le_lt_dec K (VertexSet.cardinal (interference_adj x (remove_vertex r g)))).
apply False_ind;intuition.
auto.
Qed.

(* For the same reason, a high-degree vertex of (remove_vertex r g)
    is a high-degree vertex of g *)
Lemma not_low_remove_not_low : forall x r g K,
has_low_degree (remove_vertex r g) K x = false ->
~Register.eq x r ->
has_low_degree g K x = false.

Proof.
intros x r g K H H0.
case_eq (has_low_degree g K x);[intros|auto].
rewrite (low_remove_low _ _ _ _ H1) in H. inversion H.
auto.
Qed.

(* The degree of any vertex x which is not an interference neighbor of
    (remove_vertex r g) is the same in g and in (remove_vertex r g) *)
Lemma low_deg : forall x r g K,
~VertexSet.In x (interference_adj r g) ->
~Register.eq x r ->
has_low_degree g K x = has_low_degree (remove_vertex r g) K x.

Proof.
intros x r g K H H0. unfold has_low_degree, interf_degree.
destruct (le_lt_dec K (VertexSet.cardinal (interference_adj x g)));
destruct (le_lt_dec K (VertexSet.cardinal (interference_adj x (remove_vertex r g)))).
reflexivity.
rewrite <-(cardinal_m(interf_adj_remove _ _ _ H H0)) in l0.
apply False_ind. intuition.
elim (lt_irrefl (VertexSet.cardinal (interference_adj x g))).
apply lt_le_trans with (m := K). auto.
rewrite (cardinal_m (interf_adj_remove x r g H H0)). auto.
reflexivity.
Qed.

Lemma lt_le_S_eq : forall n x,
x < n ->
n <= S x ->
n = S x.

Proof.
induction n; intros.
intuition.
induction x; intros.
apply eq_S. intuition.
apply eq_S. apply IHn. intuition. intuition.
Qed.

Lemma le_S_irrefl : forall x,
S x <= x -> False.

Proof.
induction x; intros.
inversion H.
apply IHx. apply le_S_n. assumption.
Qed.

(* If x is a low-degree degree of (remove_vertex r g) and x is
    a high-degree vertex of g then the interference degree
    of x in g is exactly k *)
Lemma degree_dec_remove_K : forall x k r g,
~Register.eq x r ->
has_low_degree g k x = false ->
has_low_degree (remove_vertex r g) k x = true ->
interf_degree g x = k.

Proof.
unfold has_low_degree, interf_degree. intros.
destruct (le_lt_dec k (VertexSet.cardinal (interference_adj x (remove_vertex r g)))) in H1.
inversion H1.
rewrite (cardinal_m (remove_interf_adj _ _ _ H)) in l.
unfold has_low_degree in H0.
destruct (le_lt_dec k (VertexSet.cardinal (interference_adj x g))).
destruct (In_dec r (interference_adj x g)).
generalize (remove_cardinal_1 i). intro HH. rewrite <-HH in l0.
set (card := VertexSet.cardinal (VertexSet.remove r (interference_adj x g))) in *.
rewrite <-HH. symmetry. apply lt_le_S_eq; auto.
generalize (remove_cardinal_2 n). intro HH. rewrite <-HH in l0.
elim (lt_irrefl k). intuition.
inversion H0.
Qed.

(* Any x which is of high-degree in g and of low-degree in (remove_vertex r g)
    interferes with r *)
Lemma low_degree_in_interf : forall x r g K,
has_low_degree (remove_vertex r g) K x = true ->
~Register.eq x r ->
has_low_degree g K x = false ->
VertexSet.In x (interference_adj r g).

Proof.
unfold has_low_degree, interf_degree. intros x r g K H HH H0.
destruct (le_lt_dec K (VertexSet.cardinal (interference_adj x g))).
destruct (le_lt_dec K (VertexSet.cardinal (interference_adj x (remove_vertex r g)))).
inversion H.
destruct (In_dec x (interference_adj r g)).
assumption.
generalize (interf_adj_remove _ _ _ n HH);intro H2.
rewrite (cardinal_m H2) in l.
apply False_ind. intuition.
inversion H0.
Qed.

(* Reciprocally, a high-degree vertex x of g which is
    exactly of degree k in g and interferes with r is
    of low-degree in (remove_vertex r g) *)

Lemma degree_K_remove_dec : forall x k r g,
~Register.eq x r ->
interf_degree g x = k ->
VertexSet.In x (interference_adj r g) ->
has_low_degree (remove_vertex r g) k x = true.

Proof.
unfold has_low_degree, interf_degree. intros.
destruct (le_lt_dec k (VertexSet.cardinal (interference_adj x g))).
destruct (le_lt_dec k (VertexSet.cardinal (interference_adj x (remove_vertex r g)))).
rewrite (cardinal_m (remove_interf_adj _ _ _ H)) in l0.
generalize (remove_cardinal_1 (interf_adj_comm _ _ _ H1)). 
intro HH. rewrite <-HH in l.
set (card := VertexSet.cardinal (VertexSet.remove r (interference_adj x g))) in *.
rewrite <-HH in H0. rewrite <-H0 in *. elim (le_S_irrefl _ l0).
reflexivity.
apply False_ind. intuition.
Qed.

(* Finally, an unused but meaningful theorem summarizing
    conditions leading to an evolution of the interference degrees
    when a vertex r is removed *)
Theorem remove_low_degree_evolution : forall x k r g,
~Register.eq x r ->
((has_low_degree g k x = false /\ has_low_degree (remove_vertex r g) k x = true)
                                                 <->
 (VertexSet.In x (interference_adj r g) /\ interf_degree g x = k)).

Proof.
intros. split; intros; destruct H0.
split. eapply low_degree_in_interf; eauto. eapply degree_dec_remove_K; eauto.
cut (has_low_degree g k x = false). intro.
split. assumption.
apply degree_K_remove_dec; auto.
unfold has_low_degree. rewrite H1. destruct (le_lt_dec k k). auto.  elim (lt_irrefl _ l).
Qed.

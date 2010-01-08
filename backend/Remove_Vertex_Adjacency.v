Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Interference_adjacency.
Require Import Edges.
Require Import MyRegisters.

Import RegFacts Props.

Module Register := Regs.

(* For any vertex x different from r, the neighborhood of x in
    (remove_vertex r g) is its one in g, minus r *)
Lemma remove_interf_adj : forall x r g,
~Register.eq x r ->
VertexSet.Equal (interference_adj x (remove_vertex r g)) 
                          (VertexSet.remove r (interference_adj x g)).

Proof.
intros.
split; intros.
apply VertexSet.remove_2. intro.
rewrite <-H1 in H0. rewrite in_interf in H0.
generalize (proj1 (In_graph_edge_in_ext _ _ H0)). change_rewrite. intro.
rewrite In_remove_vertex in H2. destruct H2. elim (H3 (Register.eq_refl _)).
rewrite in_interf in H0. rewrite In_remove_edge in H0. destruct H0.
rewrite in_interf. assumption.

rewrite in_interf. rewrite In_remove_edge.
split.
rewrite <-in_interf. apply (VertexSet.remove_3 H0).
intro. destruct H1; change_rewrite.
elim (VertexSet.remove_1 H1 H0).
elim H. auto.
Qed.

(* If x is different from r and does not belong to the interference neighborhood
   of r in g, then the interference neighborhood of x in (remove_vertex r g)
   is equal to the interference neighborhood of x in g *)
Lemma interf_adj_remove : forall x r g,
~VertexSet.In x (interference_adj r g) ->
~Register.eq x r ->
VertexSet.Equal (interference_adj x g) (interference_adj x (remove_vertex r g)).

Proof.
intros x r g H H0.
rewrite remove_interf_adj. rewrite remove_equal. apply VertexSet.eq_refl.
intro. elim H. apply interf_adj_comm. assumption.
auto.
Qed.

(* The interference neighborhood of x in (remove_vertex r g)
    is a subset of the interference neighborhood of x in g *)
Lemma sub_remove_interf : forall x r g,
~Register.eq x r ->
VertexSet.Subset (interference_adj x (remove_vertex r g))
                            (interference_adj x g).

Proof.
intros x r g H. rewrite remove_interf_adj.
unfold VertexSet.Subset. intros y H0.
apply (VertexSet.remove_3 H0).
assumption.
Qed.

(* If x is a neighbor of r in g, then x belongs to (remove_vertex r g) *)
Lemma in_interf_adj_in_remove : forall x r g,
VertexSet.In x (interference_adj r g) -> In_graph x (remove_vertex r g).

Proof.
intros x r g H. rewrite In_remove_vertex. split.
rewrite in_interf in H. apply (proj1 (In_graph_edge_in_ext _ _ H)).
intro H0. rewrite H0 in H. elim (not_in_interf_self _ _ H).
Qed.

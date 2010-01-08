Require Import InterfGraphMapImp.
Require Import Graph_Facts.
Require Import FSets.
Require Import SetsFacts.
Require Import Edges.

Import Edge RegFacts Props RegRegProps.

(* Some properties about the interference adjacency
   and the same about preference adjacency *)

(* x is not in its own interference neighborhood *)
Lemma not_in_interf_self : forall x g,
~VertexSet.In x (interference_adj x g).

Proof.
intros x g. rewrite in_interf. intro H.
elim (In_graph_edge_diff_ext _ _ H). auto.
Qed.

(* x is not in its own preference neighborhood *)
Lemma not_in_pref_self : forall x g,
~VertexSet.In x (preference_adj x g).

Proof.
intros x g. rewrite in_pref. intro H. destruct H.
elim (In_graph_edge_diff_ext _ _ H). auto.
Qed.

(* If x is an interference neighbor of y in g
   then y is an interference neighbor of x in g *)
Lemma interf_adj_comm : forall x y g,
VertexSet.In x (interference_adj y g) -> VertexSet.In y (interference_adj x g).

Proof.
intros x y g H. rewrite in_interf. rewrite edge_comm. rewrite <-in_interf. auto.
Qed.

(* If x is a preference neighbor of y in g
    then y is a preference neighbor of x in g *)
Lemma pref_adj_comm : forall x y g,
VertexSet.In x (preference_adj y g) -> VertexSet.In y (preference_adj x g).

Proof.
intros x y g H. 
rewrite in_pref in H. destruct H.  rewrite edge_comm in H. 
rewrite in_pref. exists x0. assumption.
Qed.

(* If x is an interference neighbor of any vertex of g then x is in g *)
Lemma in_interf_in : forall x r g,
VertexSet.In x (interference_adj r g) -> In_graph x g.

Proof.
intros x r g H. rewrite in_interf in H.
apply (proj1 (In_graph_edge_in_ext _ _ H)).
Qed.

(* If x is a preferenec neighbor of any vertex then x is in g *)
Lemma in_pref_in : forall x r g,
VertexSet.In x (preference_adj r g) -> In_graph x g.

Proof.
intros x r g H. rewrite in_pref in H. destruct H.
apply (proj1 (In_graph_edge_in_ext _ _ H)).
Qed.

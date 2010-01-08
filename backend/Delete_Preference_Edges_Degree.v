Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Delete_Preference_Edges_Adjacency.
Require Import Edges.

Import Edge Props RegFacts.

(* The interference degree is left unchanged when r is frozen. Hence,
   a vertex is of low-degree after freezing r iff it is before freezing r *)
Lemma delete_preference_edges_low : forall x r g K p,
has_low_degree g K x = has_low_degree (delete_preference_edges r g p) K x.

Proof.
intros x r g K p. unfold has_low_degree, interf_degree.
rewrite <-(Equal_cardinal (interf_adj_delete_preference x r g p)). reflexivity.
Qed.

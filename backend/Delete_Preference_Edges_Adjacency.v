Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Merge_Degree.
Require Import Interference_adjacency.
Require Import Edges.
Require Import MyRegisters.

Module Register := Regs.

Import Edge RegFacts Props.

(* The interference neighborhood of any vertex is left
    unchanged when x is frozen *)
Lemma interf_adj_delete_preference : forall x r g H,
VertexSet.Equal (interference_adj x g) 
                          (interference_adj x (delete_preference_edges r g H)).

Proof.
split;intros.
rewrite in_interf. rewrite In_delete_preference_edges_edge.
rewrite in_interf in H0. split. assumption.
intro. destruct H1.
unfold aff_edge in H1. destruct H1. simpl in H1. congruence.

rewrite in_interf in H0. rewrite In_delete_preference_edges_edge in H0. destruct H0.
rewrite in_interf. assumption.
Qed.

(* The preference neighborhood of any vertex different from r
    is obtained by removing r from its preference neighborhood in g *)
Lemma delete_preference_preference_adj : forall x r g H,
~Register.eq x r ->
VertexSet.Equal (preference_adj x (delete_preference_edges r g H))
                          (VertexSet.remove r (preference_adj x g)).

Proof.
intros.
split; intros.
apply VertexSet.remove_2.
intro. rewrite <-H2 in H1.
generalize (pref_adj_comm _ _ _ H1). intro.
rewrite in_pref in H3. destruct H3.
rewrite In_delete_preference_edges_edge in H3.
destruct H3. elim H4. split.
unfold aff_edge. exists x0. auto.
right. auto.
rewrite in_pref in H1.
destruct H1. rewrite In_delete_preference_edges_edge in H1.
destruct H1. rewrite in_pref. exists x0. assumption.

(* <= *)
assert (~Register.eq r a).
intro. elim (VertexSet.remove_1 H2 H1).
generalize (VertexSet.remove_3 H1). clear H1. intro.
rewrite in_pref in H1. destruct H1.
rewrite in_pref. exists x0.
rewrite In_delete_preference_edges_edge. split. assumption.
intro. destruct H3.
destruct H4; change_rewrite. elim (H2 H4). elim H0; auto.
Qed.

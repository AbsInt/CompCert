Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Merge_Move.
Require Import Edges.
Require Import MyRegisters.
Require Import Affinity_relation.
Require Import Interference_adjacency.
Require Import Delete_Preference_Edges_Adjacency.
Require Import Remove_Vertex_Move.

Import Edge Props RegFacts.

(* The frozen vertex is nonmove-related in the resulting graph *)
Lemma not_aff_related_delete_preference_edges : forall r g p,
move_related (delete_preference_edges r g p) r = false.

Proof.
intros. apply move_related_false_charac2.
intros.
rewrite In_delete_preference_edges_edge in H0. destruct H0.
intro. elim H1. split; assumption.
Qed.

(* A vertex which is move-related after a freeze is move-related before it *)
Lemma move_related_delete_move_related : forall x r g p,
move_related (delete_preference_edges r g p) x = true ->
move_related g x = true.

Proof.
intros x r g p H.
generalize (move_related_charac _ _ H);intro H0.
destruct H0 as [y H0].
destruct H0 as [H0 H1];destruct H1 as [H1 H2].
rewrite In_delete_preference_edges_edge in H1. destruct H1.
apply (move_related_charac2 _ _ _ H0 H1 H2).
Qed.

(* A vertex which is move-related in g and not in (delete_preference_edges r g H)
    is a preference neighbor of r in g *)
Lemma delete_preference_edges_move_1 : forall x r g H,
~Register.eq r x ->
move_related g x = true ->
move_related (delete_preference_edges r g H) x = false ->
VertexSet.In x (preference_adj r g).

Proof.
intros. generalize (not_move_related_empty_pref _ _ H2). intro.
rewrite delete_preference_preference_adj in H3.
destruct (In_dec r (preference_adj x g)).
apply pref_adj_comm. assumption.
assert (VertexSet.Equal (preference_adj x g) VertexSet.empty).
split; intros.
rewrite <-H3. apply VertexSet.remove_2.
intro. rewrite <-H5 in H4. elim n. auto.
assumption.
elim (VertexSet.empty_1 H4).
elim (move_related_not_empty_pref _ _ H1 H4).
auto.
Qed.

(* A vertex which is move-related in g and nonmove-related in 
   (delete_preference_edges r g H) has a preference degree of 1 *)
Lemma delete_preference_edges_move_2 : forall x r g H,
~Register.eq r x ->
move_related g x = true ->
move_related (delete_preference_edges r g H) x = false ->
VertexSet.cardinal (preference_adj x g) = 1.

Proof.
intros. generalize (not_move_related_empty_pref _ _ H2). intro.
rewrite delete_preference_preference_adj in H3.
destruct (In_dec r (preference_adj x g)).
cut (VertexSet.Equal (preference_adj x g) (VertexSet.singleton r)). intros.
rewrite H4. apply singleton_cardinal.
split; intros.
destruct (Register.eq_dec a r).
apply VertexSet.singleton_2. intuition.
assert (VertexSet.In a VertexSet.empty).
rewrite <-H3. apply VertexSet.remove_2; auto.
elim (VertexSet.empty_1 H5).
generalize (VertexSet.singleton_1 H4). intro.
rewrite <-H5. auto.
elim (move_related_not_empty_pref _ _ H1).
rewrite <-H3.

split; intros. 
rewrite Dec.F.remove_neq_iff.
assumption.
intro. rewrite <-H5 in H4. elim n. auto.
apply (VertexSet.remove_3 H4).
auto.
Qed.

(* Reciprocally, a vertex which is move-related in g,
    has a preference degree of 1 and is a preference neighbor of r
    is nonmove-related in (delete_preference_edges r g H) *)
Lemma delete_preference_edges_move_inv : forall x r g H,
~Register.eq r x ->
move_related g x = true ->
VertexSet.In x (preference_adj r g) ->
VertexSet.cardinal (preference_adj x g) = 1 ->
move_related (delete_preference_edges r g H) x = false.

Proof.
intros.
apply move_related_false_charac2. intros.
rewrite In_delete_preference_edges_edge in H5.
destruct H5.
intro. elim H6.
split. assumption.
cut (VertexSet.Equal (preference_adj x g) (VertexSet.singleton r)). intros.
destruct H7;[right|left].
rewrite (edge_eq e) in H5.
assert (eq (x, snd_ext e, get_weight e) (fst_ext e, snd_ext e, get_weight e)).
Eq_eq. rewrite <-H9 in H5.
destruct H4. rewrite H4 in H5.
apply VertexSet.singleton_1. rewrite <-H8. 
rewrite in_pref. exists x0. rewrite edge_comm. auto.
rewrite (edge_eq e) in H5.
assert (eq (fst_ext e, x, get_weight e) (fst_ext e, snd_ext e, get_weight e)).
Eq_eq. rewrite <-H9 in H5.
destruct H4. rewrite H4 in H5.
apply VertexSet.singleton_1. rewrite <-H8.
rewrite in_pref. exists x0. rewrite edge_comm. auto.
rewrite edge_comm. assumption.
apply cardinal_1_singleton. apply pref_adj_comm. assumption. assumption.
Qed.

Lemma delete_preference_edges_move_false_false : forall x r g H,
move_related g x = false ->
move_related (delete_preference_edges r g H) x = false.

Proof.
intros.
case_eq (move_related (delete_preference_edges r g H) x); intros.
rewrite (move_related_delete_move_related _ _ _ _ H1) in H0. inversion H0.
reflexivity.
Qed.

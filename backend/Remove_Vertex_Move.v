Require Import FSets.
Require Import InterfGraphMapImp.
Require Import WS.
Require Import Edges.
Require Import MyRegisters.
Require Import Affinity_relation.
Require Import Interference_adjacency.

Module Register := Regs.

Import RegFacts Props Edge.

(* A nonmove-related vertex of g is not move-related
   after the removal of a vertex *)
Lemma move_remove : forall x r g,
move_related g x = false ->
move_related (remove_vertex r g) x = false.

Proof.
intros.
apply move_related_false_charac2. intros.
apply move_related_false_charac with (g:=g); auto.
rewrite In_remove_edge in H1. intuition.
Qed.

(* Equivalently, a move-related vertex of (remove_vertex r g)
    is move-related in g *)
Lemma move_remove_2 : forall x r g,
move_related (remove_vertex r g) x = true ->
move_related g x = true.

Proof.
intros x r g H.
generalize (move_related_charac _ _ H);intro H0.
destruct H0 as [y H0]. destruct H0 as [H0 H1]. destruct H1 as [H1 H2].
apply move_related_charac2 with (e:= y).
assumption.
rewrite In_remove_edge in H1. destruct H1. assumption. assumption.
Qed.

(* If x (different from r) is move-related in g and nonmove-related
    in (remove_vertex r g) then x is a preference neighbor of r in g *)
Lemma move_related_not_remove_in_pref : forall x r g,
~Register.eq r x ->
move_related g x = true ->
move_related (remove_vertex r g) x = false ->
VertexSet.In x (preference_adj r g).

Proof.
intros.
generalize (move_related_charac _ _ H0). intro.
destruct H2. destruct H2. destruct H3.
destruct (incident_dec x0 r).
destruct H5. destruct H4.
elim H. rewrite H4. rewrite H5. auto.
unfold aff_edge in H2. destruct H2.
rewrite in_pref. exists x1.
assert (eq (x,r,Some x1) x0).
rewrite edge_comm. apply eq_ordered_eq.
unfold E.eq; split; simpl. split; auto.
unfold get_weight in H2. rewrite H2. apply OptionN_as_OT.eq_refl.
rewrite H6. assumption.
destruct H4.
destruct H2.
rewrite in_pref. exists x1.
assert (eq (x,r,Some x1) x0).
apply eq_ordered_eq.
unfold E.eq; split; simpl. split; auto.
unfold get_weight in H2. rewrite H2. apply OptionN_as_OT.eq_refl.
rewrite H6. assumption.
elim H. rewrite H4. rewrite H5. auto.
assert (In_graph_edge x0 (remove_vertex r g)).
rewrite In_remove_edge. split; assumption.
generalize (Aff_edge_aff _ _ H6 H2). intro.
destruct H7. destruct H4.
rewrite (compat_bool_move _ _ _ (Register.eq_sym _ _ H4)) in H7. rewrite H1 in H7. inversion H7.
rewrite (compat_bool_move _ _ _ (Register.eq_sym _ _ H4)) in H8. rewrite H1 in H8. inversion H8.
Qed.

(* The preference neighborhood of any vertex x different from r  in
    (remove_vertex r g) is obtained by removing r from the interference
    neighborhood of x in g *)
Lemma remove_pref_adj : forall x r g,
~Register.eq x r ->
VertexSet.Equal (preference_adj x (remove_vertex r g))
                          (VertexSet.remove r (preference_adj x g)).

Proof.
intros.
split; intros.
apply VertexSet.remove_2. intro.
rewrite <-H1 in H0. rewrite in_pref in H0. destruct H0.
generalize (proj1 (In_graph_edge_in_ext _ _ H0)). change_rewrite. intro.
rewrite In_remove_vertex in H2. destruct H2. elim (H3 (Register.eq_refl _)).
rewrite in_pref. rewrite in_pref in H0. destruct H0. exists x0.
rewrite In_remove_edge in H0. destruct H0. assumption.

generalize (VertexSet.remove_3 H0). intro.
rewrite in_pref in H1. destruct H1.
rewrite in_pref. exists x0. rewrite In_remove_edge. split. assumption.
intro. destruct H2; change_rewrite.
elim (VertexSet.remove_1 H2 H0).
elim H. intuition.
Qed.

(* The preference degree of any vertex which is move-related
    in g and nonmove-related in (remove_vertex r g) is equal to 1 *)
Lemma pref_degree_dec_remove_1 : forall x  r g,
~Register.eq x r ->
move_related g x = true ->
move_related (remove_vertex r g) x = false ->
pref_degree g x = 1.

Proof.
unfold pref_degree. intros.
generalize (not_move_related_empty_pref _ _ H1). intro.
generalize (remove_pref_adj x r g H). intro.
rewrite H2 in H3.
cut (~Register.eq r x). intro.
generalize (move_related_not_remove_in_pref _ _ _ H4 H0 H1). intro.
generalize (pref_adj_comm _ _ _ H5). intro.
generalize (remove_cardinal_1 H6). intro.
rewrite <-H7. apply eq_S. rewrite <-H3.
rewrite <-Props.cardinal_Empty. apply VertexSet.empty_1.
intuition.
Qed.

Lemma cardinal_1_singleton : forall x s,
VertexSet.In x s ->
VertexSet.cardinal s = 1 ->
VertexSet.Equal s (VertexSet.singleton x).

Proof.
intros.
apply VertexSet.eq_sym.
apply remove_singleton_empty. assumption.
assert (VertexSet.cardinal (VertexSet.remove x s) = 0).
rewrite <-remove_cardinal_1 with (x:=x) in H0. auto.
assumption.
rewrite <-Props.cardinal_Empty in H1.
rewrite (empty_is_empty_1 H1). apply VertexSet.eq_refl.
Qed.

(* Reciprocally, any vertex different from r which has a preference
    degree equal to 1 in g and is a preference neighbor of r in g is
    nonmove-related in (remove_vertex r g) *)
Lemma pref_degree_1_remove_dec : forall x r g,
~Register.eq x r ->
pref_degree g x = 1 ->
VertexSet.In x (preference_adj r g) ->
move_related (remove_vertex r g) x = false.

Proof.
intros.
case_eq (move_related (remove_vertex r g) x); intros.
generalize (remove_pref_adj x r g H). intro.
assert (VertexSet.Equal (preference_adj x g) (VertexSet.singleton r)).
apply cardinal_1_singleton. apply pref_adj_comm. assumption. assumption.
rewrite H4 in H3.
cut (VertexSet.Equal (preference_adj x (remove_vertex r g)) VertexSet.empty). intro.
generalize (move_related_charac _ _ H2). intro.
destruct H6. destruct H6. destruct H7.
destruct H8.
assert (VertexSet.In (snd_ext x0) (preference_adj x (remove_vertex r g))).
destruct H6. rewrite in_pref. exists x1.
assert (eq (snd_ext x0, x, Some x1) x0).
rewrite edge_comm. apply eq_ordered_eq.
unfold E.eq. split; intros. simpl. split; intuition. apply Regs.eq_refl.
auto. auto. simpl. unfold get_weight in H6. rewrite H6. apply OptionN_as_OT.eq_refl.
rewrite H9. assumption.
rewrite H5 in H9. elim (VertexSet.empty_1 H9).
assert (VertexSet.In (fst_ext x0) (preference_adj x (remove_vertex r g))).
destruct H6. rewrite in_pref. exists x1.
assert (eq (fst_ext x0, x, Some x1) x0).
apply eq_ordered_eq.
unfold E.eq. split; intros. simpl. split; intuition. apply Regs.eq_refl.
auto. auto. simpl. unfold get_weight in H6. rewrite H6. apply OptionN_as_OT.eq_refl.
rewrite H9. assumption.
rewrite H5 in H9. elim (VertexSet.empty_1 H9).
rewrite H3.
split; intros.
destruct (Register.eq_dec r a).
elim (VertexSet.remove_1 e H5).
generalize (VertexSet.remove_3 H5). intro.
generalize (VertexSet.singleton_1 H6). intro.
elim (n H7).
elim (VertexSet.empty_1 H5).
reflexivity.
Qed.

(* Meaningful theorem *)
Theorem Remove_vertex_move_evolution : forall x r g,
~Register.eq x r ->
((move_related g x = true /\ move_related (remove_vertex r g) x = false)
                                        <->
            (pref_degree g x = 1 /\ VertexSet.In x (preference_adj r g))).

Proof.
split; intros.
destruct H0.
split. apply pref_degree_dec_remove_1 with (r:=r); auto.
        apply move_related_not_remove_in_pref; auto.
destruct H0.
split. apply move_related_card. congruence.
        apply pref_degree_1_remove_dec; auto.
Qed.

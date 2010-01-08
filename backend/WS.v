Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Conservative_criteria.
Require Import Edges.
Require Import MyRegisters.
Require Import Affinity_relation.

Import Edge RegFacts Props OTFacts.

(* Intersections of vertices sets of the worklists are empty *)
Lemma WS_empty_inter_1 : forall g palette WL,
WS_properties g palette WL ->
VertexSet.Empty (VertexSet.inter (get_spillWL WL) (get_freezeWL WL)).

Proof.
intros g palette WL H.
unfold VertexSet.Empty.
intros a H0.
generalize (VertexSet.inter_1 H0);intro H1.
generalize (VertexSet.inter_2 H0);intro H2.
unfold WS_properties in H.
destruct H as [H H3];destruct H3 as [H3 H4];destruct H4 as [H4 H5].
generalize (proj1 (H a) H1);intro H6.
destruct H6 as [H6 _].
generalize (proj1 (H3 a) H2);intro H7.
destruct H7 as [H7 _].
rewrite H6 in H7; inversion H7.
Qed.

Lemma WS_empty_inter_2 : forall g palette WL,
WS_properties g palette WL ->
VertexSet.Empty (VertexSet.inter (get_spillWL WL) (get_simplifyWL WL)).

Proof.
intros g palette WL H.
unfold VertexSet.Empty.
intros a H0.
generalize (VertexSet.inter_1 H0);intro H1.
generalize (VertexSet.inter_2 H0);intro H2.
unfold WS_properties in H.
destruct H as [H H3];destruct H3 as [H3 H4];destruct H4 as [H4 H5].
generalize (proj1 (H a) H1);intro H6.
destruct H6 as [H6 _].
generalize (proj1 (H4 a) H2);intro H7.
destruct H7 as [H7 _].
rewrite H6 in H7; inversion H7.
Qed.

Lemma WS_empty_inter_3 : forall g palette WL,
WS_properties g palette WL ->
VertexSet.Empty (VertexSet.inter (get_freezeWL WL) (get_simplifyWL WL)).

Proof.
intros g palette WL H.
unfold VertexSet.Empty.
intros a H0.
generalize (VertexSet.inter_1 H0);intro H1.
generalize (VertexSet.inter_2 H0);intro H2.
unfold WS_properties in H.
destruct H as [H H3];destruct H3 as [H3 H4];destruct H4 as [H4 H5].
generalize (proj1 (H3 a) H1);intro H6.
destruct H6 as [_ H6].
destruct H6 as [H6 _].
generalize (proj1 (H4 a) H2);intro H7.
destruct H7 as [_ H7].
destruct H7 as [H7 _].
rewrite H6 in H7; inversion H7.
Qed.

(* A tactic for simplifying proofs of belonging of a vertex to a worklist *)
Ltac WS_apply H := generalize H;intro HWS_;
match goal with
| |- (VertexSet.In ?A _) => destruct HWS_ as [HWS_ HWS__];
                                   try (apply (proj2 (HWS_ A)));
                                   destruct HWS__ as [HWS__ HWS___];
                                   try (apply (proj2 (HWS__ A)));
				   destruct HWS___ as [HWS___ HWS____];
                                   try (apply (proj2 (HWS___ A)));
                                   clear HWS_ HWS__ HWS___ HWS____
| |- (EdgeSet.In ?A _) => do 3 destruct HWS_ as [_ HWS_];
                              apply (proj2 (HWS_ A));
                              clear HWS_
end.

(* Lemmas for generalizing properties of a vertex belonging to a given worklist *)
Lemma In_spill_props : forall x g WL s a b c palette,
VertexSet.In x s ->
WL = (s,a,b,c) ->
WS_properties g palette WL ->
has_low_degree g palette x = false /\ In_graph x g /\ ~VertexSet.In x (precolored g).

Proof.
intros x g WL s a b c palette H H0 H1.
unfold WS_properties in H1;rewrite H0 in H1.
destruct H1 as [H1 _].
unfold get_spillWL in H1;simpl in H1.
apply (proj1 (H1 x) H).
Qed.

Lemma In_freeze_props : forall x g WL s a b c palette,
VertexSet.In x s ->
WL = (a,s,b,c) ->
WS_properties g palette WL ->
has_low_degree g palette x = true /\ move_related g x = true /\ In_graph x g /\ ~VertexSet.In x (precolored g).

Proof.
intros x g WL s a b c palette H H0 H1.
unfold WS_properties in H1;rewrite H0 in H1.
destruct H1 as [_ H1].
destruct H1 as [H1 _].
unfold get_freezeWL in H1;simpl in H1.
generalize (proj1 (H1 x) H);intro.
intuition.
apply move_related_in_graph;intuition.
Qed.

Lemma In_simplify_props : forall x g WL s a b c palette,
VertexSet.In x s ->
WL = (a,b,s,c) ->
WS_properties g palette WL ->
has_low_degree g palette x = true /\ move_related g x = false /\ In_graph x g /\ ~VertexSet.In x (precolored g).

Proof.
intros x g WL s a b c palette H H0 H1.
unfold WS_properties in H1;rewrite H0 in H1.
do 2 destruct H1 as [_ H1].
destruct H1 as [H1 _].
unfold get_spillWL in H1;simpl in H1.
apply (proj1 (H1 x) H).
Qed.

Lemma In_move_props : forall e g WL s a b c palette,
EdgeSet.In e s ->
WL = (a,b,c,s) ->
WS_properties g palette WL ->
aff_edge e /\ In_graph_edge e g.

Proof.
intros e g WL s a b c palette H H0 H1.
unfold WS_properties in H1;rewrite H0 in H1.
do 3 destruct H1 as [_ H1].
unfold get_movesWL in H1;simpl in H1.
apply (proj1 (H1 e) H).
Qed.

Lemma WS_props_equal :
forall g palette ws ws',
VertexSet.Equal (get_simplifyWL ws) (get_simplifyWL ws') ->
VertexSet.Equal (get_freezeWL ws) (get_freezeWL ws') ->
VertexSet.Equal (get_spillWL ws) (get_spillWL ws') ->
EdgeSet.Equal (get_movesWL ws) (get_movesWL ws') ->
WS_properties g palette ws ->
WS_properties g palette ws'.

Proof.
unfold WS_properties;unfold get_spillWL;unfold get_freezeWL;
unfold get_simplifyWL;unfold get_movesWL;simpl;unfold VertexSet.Equal;
unfold EdgeSet.Equal;intros g palette ws ws' H H0 H1 H2 H3.
destruct ws as [ws d]; destruct ws as [ws c]; destruct ws as [a b].
destruct ws' as [ws' p]; destruct ws' as [ws' o]; destruct ws' as [m n]. simpl in *.
generalize (VertexSet.eq_sym H);generalize (VertexSet.eq_sym H0);
generalize (VertexSet.eq_sym H1);generalize (EdgeSet.eq_sym H2);
clear H;clear H0;clear H1;clear H2;intros H2 H1 H0 H.

destruct H3 as [Hsp H3];destruct H3 as [Hf H3];
destruct H3 as [Hsi Hm].
do 2 split.
intro H4;apply (proj1 (Hsp x) (proj1 (H1 x) H4)).
intro H4;apply (proj2 (H1 x) (proj2 (Hsp x) H4)).
split;intro H4.
apply (proj1 (Hf x) (proj1 (H0 x) H4)).
apply (proj2 (H0 x) (proj2 (Hf x) H4)).
split.
split;intro H4.
apply (proj1 (Hsi x) (proj1 (H x) H4)).
apply (proj2 (H x) (proj2 (Hsi x) H4)).
split;intro H4.
apply (proj1 (Hm e) (proj1 (H2 e) H4)).
apply (proj2 (H2 e) (proj2 (Hm e) H4)).
Qed.

(* Definition of the nonprecolored vertices of a graph *)
Definition not_precolored g := VertexSet.diff (V g) (precolored g).

(* The union of vertices worklists forms the nonprecolored vertices set of g *)
Lemma not_precolored_union_ws : forall g palette ws,
WS_properties g palette ws ->
VertexSet.Equal 
(VertexSet.union (VertexSet.union (get_spillWL ws) (get_freezeWL ws)) (get_simplifyWL ws))
(not_precolored g).

Proof.
intros g palette ws HWS. 
split. intro H.
unfold not_precolored. apply VertexSet.diff_3.
destruct (VertexSet.union_1 H).
destruct (VertexSet.union_1 H0).
apply (proj1(proj2 (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS))).
apply (proj2(proj2 (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS))).
apply (proj2(proj2 (In_simplify_props _ _ _ _ _ _ _ _ H0 (refl_equal _) HWS))).
destruct (VertexSet.union_1 H).
destruct (VertexSet.union_1 H0).
apply (proj2(proj2 (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS))).
apply (proj2(proj2 (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS))).
apply (proj2(proj2 (In_simplify_props _ _ _ _ _ _ _ _ H0 (refl_equal _) HWS))).
intro H. 
unfold not_precolored in H.
generalize (VertexSet.diff_1 H). intro H0.
generalize (VertexSet.diff_2 H). clear H. intro H.
case_eq (has_low_degree g palette a); intro Hlow.
case_eq (move_related g a); intro Haff.
apply VertexSet.union_2. apply VertexSet.union_3.
WS_apply HWS. intuition.
apply VertexSet.union_3.
WS_apply HWS. intuition.
apply VertexSet.union_2. apply VertexSet.union_2.
WS_apply HWS. intuition.
Qed.

(* The moves worklists is equal to the set of affinity edges *)
Lemma moves_AE : forall g palette ws,
WS_properties g palette ws ->
EdgeSet.Equal (AE g) (get_movesWL ws).

Proof.
split; intros.
destruct ws. destruct p. destruct p.
simpl. WS_apply H. apply (proj1 (In_graph_aff_edge_in_AE _ _) H0).
generalize (In_move_props _ _ _ _ _ _ _ _ H0 (refl_equal _) H). intro H1.
apply (proj2 (In_graph_aff_edge_in_AE _ _) H1).
Qed.

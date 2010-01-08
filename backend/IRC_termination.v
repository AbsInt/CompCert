Require Import FSets.
Require Import InterfGraphMapImp.
Require Import IRC_Graph_Functions.
Require Import ZArith.
Require Import IRC_Graph_Functions.
Require Import WS.
Require Import IRC_graph.
Require Import Simplify_WL.
Require Import Spill_WL.
Require Import Freeze_WL.
Require Import Merge_WL.
Require Import MyRegisters.
Require Import Remove_Vertex_WL.
Require Import Affinity_relation.
Require Import Edges.
Require Import Merge_Move.
Require Import Merge_Degree.
Require Import Conservative_criteria.
Require Import Delete_Preference_Edges_Degree.
Require Import Delete_Preference_Edges_Move.
Require Import Remove_Vertex_Move.
Require Import Remove_Vertex_Degree.

Import Edge RegFacts Props OTFacts.

Definition not_precolored_irc g := not_precolored (irc_g g).

Definition irc_measure g :=
let simplifyWL := get_simplifyWL (irc_wl g) in
let m := VertexSet.cardinal simplifyWL in
let np := not_precolored_irc g in
let n := VertexSet.cardinal np in
2*n - m.

Lemma empty_union_empty :
VertexSet.Equal 
(VertexSet.union VertexSet.empty VertexSet.empty)
(VertexSet.empty).

Proof.
split;intros.
destruct (VertexSet.union_1 H); elim (VertexSet.empty_1 H0).
elim (VertexSet.empty_1 H).
Qed.

Lemma cardinal_union_not_precolored : forall g,
VertexSet.cardinal (not_precolored_irc g) =
VertexSet.cardinal (get_simplifyWL (irc_wl g)) +
VertexSet.cardinal (get_freezeWL (irc_wl g)) +
VertexSet.cardinal (get_spillWL (irc_wl g)).

Proof.
intros. unfold not_precolored_irc. rewrite <-(not_precolored_union_ws _ _ (irc_wl g)).
do 2 rewrite union_cardinal_inter. rewrite union_inter_1.
generalize (WS_empty_inter_1 _ _ (irc_wl g) (HWS_irc g)). intro.
generalize (WS_empty_inter_2 _ _ (irc_wl g) (HWS_irc g)). intro.
generalize (WS_empty_inter_3 _ _ (irc_wl g) (HWS_irc g)). intro.
generalize (empty_is_empty_1 H). intro.
generalize (empty_is_empty_1 H0). intro.
generalize (empty_is_empty_1 H1). intro.
rewrite H2. rewrite H3. rewrite H4. rewrite empty_union_empty.
rewrite empty_cardinal. omega.
apply HWS_irc.
Qed.

Lemma irc_measure_equiv_aux : forall g,
irc_measure g = VertexSet.cardinal (get_simplifyWL (irc_wl g)) +
                VertexSet.cardinal (get_freezeWL (irc_wl g)) +
                VertexSet.cardinal (get_freezeWL (irc_wl g)) +
                VertexSet.cardinal (get_spillWL (irc_wl g)) +
                VertexSet.cardinal (get_spillWL (irc_wl g)).

Proof.
intros. unfold irc_measure. simpl.
rewrite cardinal_union_not_precolored. repeat rewrite <-plus_n_O. omega.
Qed.

Definition card_n g := VertexSet.cardinal (not_precolored_irc g).
Definition card_p g := 
VertexSet.cardinal (VertexSet.union (get_freezeWL (irc_wl g)) (get_spillWL  (irc_wl g))).

Lemma irc_measure_equiv : forall g,
irc_measure g = card_n g + card_p g.

Proof.
intros. unfold card_n, card_p. 
rewrite irc_measure_equiv_aux. rewrite cardinal_union_not_precolored.
repeat rewrite <-plus_assoc.
rewrite plus_comm. rewrite <-plus_assoc.
rewrite union_cardinal. omega.
intros. intro.  destruct H. elim (WS_empty_inter_1 _ _ _ (HWS_irc g) x).
apply VertexSet.inter_3; auto.
Qed.

Lemma remove_cardinal_weak_dec : forall x s,
VertexSet.cardinal s - 1 <= VertexSet.cardinal (VertexSet.remove x s).

Proof.
intros.
destruct (In_dec x s); intros.
rewrite <-(remove_cardinal_1 i). omega.
rewrite <-(remove_cardinal_2 n). omega.
Qed.

Lemma simplify_dec_aux_1 : forall g r H,
card_n (simplify_irc r g H) < card_n g.

Proof.
intros. unfold card_n, simplify_irc, not_precolored_irc, not_precolored; simpl.
generalize (In_simplify_props _ _ _ _ _ _ _ _ H (refl_equal _) (HWS_irc g)). intro.
destruct H0. destruct H1. destruct H2.
apply subset_cardinal_lt with (x:=r).
unfold VertexSet.Subset. intros.
generalize (VertexSet.diff_1 H4). intro.
generalize (VertexSet.diff_2 H4). clear H4. intro.
apply VertexSet.diff_3. apply (VertexSet.remove_3 H5).
rewrite precolored_remove_vertex in H4. intro. elim H4.
apply VertexSet.remove_2; auto.
intro. elim (VertexSet.remove_1 H7 H5).
apply VertexSet.diff_3; auto.
intro. generalize (VertexSet.diff_1 H4). intro.
       generalize (VertexSet.diff_2 H4). intro.
elim (VertexSet.remove_1 (MyRegisters.Regs.eq_refl _) H5).
Qed.

Lemma simplify_dec_aux_2 : forall g r H,
card_p (simplify_irc r g H) <= card_p g.

Proof.
intros. unfold card_p, simplify_irc, not_precolored_irc, not_precolored; simpl.
apply subset_cardinal. unfold simplify_wl.
case_eq (VertexSet.partition (move_related (irc_g g))
               (VertexSet.filter
                  (fun x : VertexSet.elt =>
                   eq_K (irc_k g)
                     (VertexSet.cardinal (interference_adj x (irc_g g))))
                  (VertexSet.diff (interference_adj r (irc_g g))
                     (precolored (irc_g g))))); intros.
unfold get_spillWL, get_freezeWL; simpl.
assert (VertexSet.Equal t0 (fst (VertexSet.partition (move_related (irc_g g))
       (VertexSet.filter
          (fun x : VertexSet.elt =>
           eq_K (irc_k g)
             (VertexSet.cardinal (interference_adj x (irc_g g))))
          (VertexSet.diff (interference_adj r (irc_g g))
             (precolored (irc_g g))))))) as Ht0.
rewrite H0. simpl. apply VertexSet.eq_refl.
rewrite VertexSet.partition_1 in Ht0.

unfold VertexSet.Subset; intros.
destruct (VertexSet.union_1 H1).
destruct (VertexSet.union_1 H2).
apply VertexSet.union_2. auto.
apply VertexSet.union_3. WS_apply (HWS_irc g). rewrite Ht0 in H3. clear H0 H1.
generalize (VertexSet.filter_1 (compat_bool_move _ ) H3). intro.
generalize (VertexSet.filter_2 (compat_bool_move _) H3). clear H3. intro.
generalize (VertexSet.filter_1 (eq_K_compat _ _) H0). intro.
generalize (VertexSet.filter_2 (eq_K_compat _ _) H0). clear H0. intro.
generalize (eq_K_2 _ _ H0). clear H0. intro.
generalize (VertexSet.diff_1 H3). intro.
generalize (VertexSet.diff_2 H3). clear H3. intro.
split.
unfold has_low_degree, interf_degree. rewrite <-H0.
destruct (le_lt_dec (irc_k g) (irc_k g)). reflexivity. elim (lt_irrefl _ l).
split.
apply move_related_in_graph; auto.
assumption.
apply VertexSet.union_3. apply (VertexSet.diff_1 H2).
apply compat_bool_move.
Qed.

Lemma simplify_dec : forall (g : irc_graph) (r : Register.t) (g' : irc_graph),
simplify g = Some (r, g') -> irc_measure g' < irc_measure g.

Proof.
intros. do 2 rewrite irc_measure_equiv.
generalize (simplify_inv _ _ H). intro.
generalize (simplify_inv2 _ _ H). intro. simpl in *. 
destruct H1 as [H1 H2]. clear H H0. rewrite H2 in *.
generalize (simplify_dec_aux_1 g r (VertexSet.choose_1 H1)). 
generalize (simplify_dec_aux_2 g r (VertexSet.choose_1 H1)). omega.
Qed.

Lemma coalesce_dec_aux_1 : forall g e p q,
~VertexSet.In (snd_ext e) (precolored (irc_g g)) ->
card_n (merge_irc e g p q) < card_n g.

Proof.
intros. unfold card_n, merge_irc, not_precolored_irc, not_precolored; simpl.
apply subset_cardinal_lt with (x:=(snd_ext e)).
unfold VertexSet.Subset. intros.
generalize (VertexSet.diff_1 H0). intro.
generalize (VertexSet.diff_2 H0). clear H0. intro.
apply VertexSet.diff_3.
apply (VertexSet.remove_3 H1).
rewrite precolored_merge in H0. intro. elim H0.
apply VertexSet.remove_2; auto.
intro. elim (VertexSet.remove_1 H3 H1).
apply VertexSet.diff_3. apply (proj2 (In_graph_edge_in_ext _ _ p)). auto.
intro. generalize (VertexSet.diff_1 H0). intro.
       generalize (VertexSet.diff_2 H0). intro.
elim (VertexSet.remove_1 (Regs.eq_refl _) H1).
Qed.

Lemma coalesce_dec_aux_2 : forall g e p q,
~VertexSet.In (snd_ext e) (precolored (irc_g g)) ->
card_p (merge_irc e g p q) <= card_p g.

Proof.
intros. unfold card_p, merge_irc, not_precolored_irc, not_precolored; simpl.
apply subset_cardinal. unfold VertexSet.Subset; intros.
destruct (VertexSet.union_1 H0).
generalize (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) (ws_merge3 _ _ _ _)). intro.
destruct H2. destruct H3. destruct H4.
case_eq (has_low_degree (irc_g g) (irc_k g) a); intros.
apply VertexSet.union_2. WS_apply (HWS_irc g).
split. assumption.
split. eapply move_related_merge_move_related; eauto.
intro. elim H5. rewrite precolored_merge. apply VertexSet.remove_2.
rewrite In_merge_vertex in H4. destruct H4. auto.
assumption.
apply VertexSet.union_3. WS_apply (HWS_irc g).
split. assumption.
split. rewrite In_merge_vertex in H4. destruct H4. auto.
intro. elim H5. rewrite precolored_merge. apply VertexSet.remove_2.
rewrite In_merge_vertex in H4. destruct H4. auto.
assumption.

generalize (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) (ws_merge3 _ _ _ _)). intro.
destruct H2. destruct H3.
rewrite In_merge_vertex in H3. destruct H3.
destruct (Register.eq_dec a (fst_ext e)).
rewrite e0. case_eq (has_low_degree (irc_g g) (irc_k g) (fst_ext e)); intros.
apply VertexSet.union_2. WS_apply (HWS_irc g).
split. assumption.
split. apply (proj1 (Aff_edge_aff _ _ p q)). rewrite e0 in H4.
intro. elim H4. rewrite precolored_merge. apply VertexSet.remove_2.
apply (In_graph_edge_diff_ext _ _ p).
assumption.
apply VertexSet.union_3. WS_apply (HWS_irc g).
split. assumption.
split. rewrite <-e0. assumption.
rewrite e0 in H4.
intro. elim H4. rewrite precolored_merge. apply VertexSet.remove_2.
apply (In_graph_edge_diff_ext _ _ p).
assumption.

apply VertexSet.union_3. WS_apply (HWS_irc g).
split. rewrite Hk in H2. eapply merge_low_1; eauto.
split. assumption.
intro. elim H4. rewrite precolored_merge. apply VertexSet.remove_2; auto.
Qed.

Lemma coalesce_dec : forall (g : irc_graph) (e : Edge.t) (g' : irc_graph),
coalesce g = Some (e, g') -> irc_measure g' < irc_measure g.

Proof.
intros. do 2 rewrite irc_measure_equiv.
generalize (coalesce_inv _ _ H). intro.
generalize (coalesce_inv_2 _ _ H). intro. simpl in *. 
destruct H1 as [H1 H2]. destruct H2 as [H2 H3]. clear H. rewrite H3 in *.
cut (forall e', EdgeSet.In e' (get_movesWL (irc_wl g)) -> In_graph_edge e' (irc_g g)). intro HH.
generalize (any_coalescible_edge_1 _ _ _ _ HH H0). intro. destruct H.
generalize (any_coalescible_edge_2  _ _ _ _ HH H0). intro.
generalize (coalesce_dec_aux_1 g e H1 H2 H5).
generalize (coalesce_dec_aux_2 g e H1 H2 H5). omega.
intros. apply (proj2(In_move_props _ _ _ _ _ _ _ _ H (refl_equal _) (HWS_irc g))).
Qed.

Lemma freeze_dec_aux_1 : forall g x H H0,
card_n (delete_preference_edges_irc2 x g H H0) <= card_n g.

Proof.
intros.  unfold card_n, delete_preference_edges_irc2, not_precolored_irc, not_precolored; simpl.
apply subset_cardinal. unfold VertexSet.Subset; intros.
generalize (VertexSet.diff_1 H1). intro.
generalize (VertexSet.diff_2 H1). clear H1. intro.
rewrite precolored_delete_preference_edges in H1.
apply VertexSet.diff_3; assumption.
Qed.

Lemma freeze_dec_aux_2 : forall g x H H0,
card_p (delete_preference_edges_irc2 x g H H0) < card_p g.

Proof.
intros.  unfold card_p, delete_preference_edges_irc2, not_precolored_irc, not_precolored; simpl.
generalize (In_freeze_props _ _ _ _ _ _ _ _ H0 (refl_equal _) (HWS_irc g)). intro.
destruct H1. destruct H2. destruct H3.
apply subset_cardinal_lt with (x:=x). unfold VertexSet.Subset; intros.
destruct (VertexSet.union_1 H5). 
apply VertexSet.union_2. WS_apply (HWS_irc g).
generalize (In_freeze_props _ _ _ _ _ _ _ _ H6 (refl_equal _) (WS_freeze _ _ H H0)). intro.
destruct H7. destruct H8. destruct H9.
split. 
rewrite <-delete_preference_edges_low in H7. auto.
split. eapply move_related_delete_move_related; eauto.
rewrite precolored_delete_preference_edges in H10. assumption.
apply VertexSet.union_3. WS_apply (HWS_irc g).
generalize (In_spill_props _ _ _ _ _ _ _ _ H6 (refl_equal _) (WS_freeze _ _ H H0)). intro.
destruct H7. destruct H8.
split. 
rewrite <-delete_preference_edges_low in H7. auto.
split. rewrite In_delete_preference_edges_vertex in H8. auto.
rewrite precolored_delete_preference_edges in H9. assumption.

apply VertexSet.union_2. assumption.

intro.
destruct (VertexSet.union_1 H5).
generalize (In_freeze_props _ _ _ _ _ _ _ _ H6 (refl_equal _) (WS_freeze _ _ H H0)). intro.
destruct H7. destruct H8.
rewrite (not_aff_related_delete_preference_edges _ _ H) in H8. congruence.
generalize (In_spill_props _ _ _ _ _ _ _ _ H6 (refl_equal _) (WS_freeze _ _ H H0)). intro.
destruct H7.
rewrite <-delete_preference_edges_low in H7. congruence.
Qed.

Lemma freeze_dec : forall (g : irc_graph) (r : Register.t) (g' : irc_graph),
freeze g = Some (r, g') -> irc_measure g' < irc_measure g.

Proof.
intros. do 2 rewrite irc_measure_equiv.
generalize (freeze_inv _ _ H). intro.
generalize (freeze_inv2 _ _ H). intro. simpl in *. 
destruct H1 as [H1 H2]. destruct H2 as [H2 H3]. clear H. rewrite H3 in *.
generalize (freeze_dec_aux_1 g r H2 H1).
generalize (freeze_dec_aux_2 g r H2 H1). omega.
Qed.

Lemma spill_dec_aux_1 : forall g r H,
card_n (spill_irc r g H) < card_n g.

Proof.
intros. unfold card_n, spill_irc, not_precolored_irc, not_precolored; simpl.
generalize (In_spill_props _ _ _ _ _ _ _ _ H (refl_equal _) (HWS_irc g)). intro.
destruct H0. destruct H1. generalize H2. intro H3.
apply subset_cardinal_lt with (x:=r).
unfold VertexSet.Subset. intros.
generalize (VertexSet.diff_1 H4). intro.
generalize (VertexSet.diff_2 H4). clear H4. intro.
apply VertexSet.diff_3.
apply (VertexSet.remove_3 H5).
rewrite precolored_remove_vertex in H4. intro. elim H4.
apply VertexSet.remove_2; auto.
intro. elim (VertexSet.remove_1 H7 H5).
apply VertexSet.diff_3; auto.
intro. generalize (VertexSet.diff_1 H4). intro.
       generalize (VertexSet.diff_2 H4). intro.
elim (VertexSet.remove_1 (Regs.eq_refl _) H5).
Qed.

Lemma spill_dec_aux_2 : forall g r H,
card_p (spill_irc r g H) <= card_p g.

Proof.
intros. unfold card_p, spill_irc, not_precolored_irc, not_precolored; simpl.
apply subset_cardinal. unfold VertexSet.Subset; intros.
destruct (VertexSet.union_1 H0).
case_eq (has_low_degree (irc_g g) (irc_k g) a); intros.
apply VertexSet.union_2. WS_apply (HWS_irc g).
generalize (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) (WS_spill _ _ H)). intro.
destruct H3. destruct H4. destruct H5.
split. assumption.
split. apply move_remove_2 with (r:=r). assumption.
intro. elim H6. rewrite precolored_remove_vertex.
apply VertexSet.remove_2. rewrite In_remove_vertex in H5. destruct H5. auto.
assumption.
apply VertexSet.union_3. WS_apply (HWS_irc g).
generalize (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) (WS_spill _ _ H)). intro.
destruct H3. destruct H4. destruct H5.
split. assumption.
split. rewrite In_remove_vertex in H5. destruct H5. auto.
intro. elim H6. rewrite precolored_remove_vertex.
apply VertexSet.remove_2. rewrite In_remove_vertex in H5. destruct H5. auto.
assumption.
apply VertexSet.union_3.
WS_apply (HWS_irc g).
generalize (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) (WS_spill _ _ H)). intro.
destruct H2. destruct H3.
rewrite In_remove_vertex in H3. destruct H3.
split. apply not_low_remove_not_low with (r:=r); assumption.
split. assumption.
intro. elim H4. rewrite precolored_remove_vertex.
apply VertexSet.remove_2. auto. assumption.
Qed.

Lemma spill_dec : forall (g : irc_graph) (r : Register.t) (g' : irc_graph),
spill g = Some (r, g') -> irc_measure g' < irc_measure g.

Proof.
intros. do 2 rewrite irc_measure_equiv.
generalize (spill_inv _ _ H). intro.
generalize (spill_inv2 _ _ H). intro. simpl in *. 
destruct H1 as [H1 H2]. clear H H0. rewrite H2 in *.
generalize (spill_dec_aux_1 g r (lowest_cost_in _ _ _ H1)). 
generalize (spill_dec_aux_2 g r (lowest_cost_in _ _ _  H1)). omega.
Qed.

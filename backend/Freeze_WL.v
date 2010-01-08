Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Merge_WL.
Require Import Edges.
Require Import Remove_Vertex_WL.
Require Import IRC_graph.
Require Import Delete_Preference_Edges_Degree.
Require Import WS.
Require Import Delete_Preference_Edges_Move.
Require Import Graph_Facts.
Require Import Interference_adjacency.
Require Import Affinity_relation.

Import RegFacts Props.

Definition delete_preferences_wl2 v ircg k :=
let wl := irc_wl ircg in
let g := irc_g ircg in
let simplify := get_simplifyWL wl in
let freeze := get_freezeWL wl in
let spill := get_spillWL wl in
let moves := get_movesWL wl in
let adj_fst := VertexSet.diff (preference_adj v g) (precolored g) in
let new_simp := VertexSet.filter (fun x => eq_K 1 (VertexSet.cardinal (preference_adj x g)) && has_low_degree g k x) adj_fst in
let simplifyWL' := VertexSet.add v (VertexSet.union simplify new_simp) in
let freezeWL' := VertexSet.remove v (VertexSet.diff freeze new_simp) in
let movesWL' := not_incident_edges v moves g in 
(spill, freezeWL', simplifyWL', movesWL').

Lemma WS_delete_preferences_wl2 : forall r ircg (Hin : In_graph r (irc_g ircg)),
VertexSet.In r (get_freezeWL (irc_wl ircg)) ->
WS_properties (delete_preference_edges r (irc_g ircg) Hin) 
              (VertexSet.cardinal (pal ircg))
              (delete_preferences_wl2 r ircg (VertexSet.cardinal (pal ircg))).


Proof.
intros r ircg Hin HH.
unfold WS_properties. unfold delete_preferences_wl2.
generalize (HWS_irc ircg). intro HWS.
set (wl := irc_wl ircg) in *.
set (g := irc_g ircg) in *.
set (simplify := get_simplifyWL wl) in *.
set (freeze := get_freezeWL wl) in *.
set (spill := get_spillWL wl) in *.
set (adj_fst := VertexSet.diff (preference_adj r g) (precolored g)) in *.
set (new_simp := VertexSet.filter (fun x => eq_K 1 (VertexSet.cardinal (preference_adj x g))) adj_fst) in *.
set (simplifyWL_ := VertexSet.union simplify new_simp) in *.
set (simplifyWL' := VertexSet.add r simplifyWL_) in *.
set (freezeWL' := VertexSet.diff freeze new_simp) in *.
set (movesWL' := not_incident_edges r (get_movesWL wl) g) in *.
rewrite <-(Hk ircg) in HWS. set (K := VertexSet.cardinal (pal ircg)) in *.

unfold get_spillWL, get_simplifyWL, get_freezeWL, get_movesWL. simpl.

split. intro x.
rewrite <-delete_preference_edges_low.
rewrite precolored_delete_preference_edges.
rewrite In_delete_preference_edges_vertex.
split; intros.
apply (In_spill_props _ _ _ _ _ _ _ _ H (refl_equal _) HWS).
WS_apply HWS. assumption.

(* freeze *)
split. intro x.
rewrite precolored_delete_preference_edges.
rewrite <-delete_preference_edges_low.

split; intros.
unfold freezeWL' in H.
assert (~Register.eq r x) as Hneq.
intro. elim (VertexSet.remove_1 H0 H).
generalize (VertexSet.remove_3 H). clear H. intro H.
generalize (VertexSet.diff_1 H). generalize (VertexSet.diff_2 H). clear H. intros.
generalize (In_freeze_props _ _ _ _ _ _ _ _ H0 (refl_equal _) HWS). intro.
destruct H1. destruct H2. destruct H3.
split.
assumption.
split.

destruct (Register.eq_dec r x). elim (Hneq e).
case_eq (move_related (delete_preference_edges r g Hin) x); intros.
reflexivity.
elim H. unfold new_simp.
apply VertexSet.filter_3.
apply compat_move_up.
apply VertexSet.diff_3.
apply delete_preference_edges_move_1 with (H := Hin); auto.
assumption.
rewrite andb_true_iff. split.
apply eq_K_1.
apply delete_preference_edges_move_2 with (H := Hin); auto. 
assumption.
assumption.

destruct H. destruct H0.
apply VertexSet.remove_2. intro.
rewrite (compat_bool_move _ _ _ (Register.eq_sym _ _ H2)) in H0.
rewrite (not_aff_related_delete_preference_edges r g Hin) in H0. inversion H0.
unfold freezeWL'. apply VertexSet.diff_3.
WS_apply HWS. split.
assumption.
split.
apply (move_related_delete_move_related _ _ _ _ H0).
assumption.
intro. assert (move_related (delete_preference_edges r g Hin) x = false).
apply delete_preference_edges_move_inv.
intro.
rewrite (compat_bool_move _ _ _ (Register.eq_sym _ _ H3)) in H0.
rewrite (not_aff_related_delete_preference_edges r g Hin) in H0. inversion H0.
apply (move_related_delete_move_related _ _ _ _ H0).
unfold new_simp in H2.
apply (VertexSet.diff_1 (VertexSet.filter_1 (compat_move_up _ _) H2)).
symmetry. apply eq_K_2. generalize (VertexSet.filter_2 (compat_move_up _ _) H2). intro.
rewrite andb_true_iff in H3. destruct H3. assumption.
rewrite H0 in H3. inversion H3.

(* simplify *)
split. intro x.
rewrite <-delete_preference_edges_low.
rewrite precolored_delete_preference_edges.
rewrite In_delete_preference_edges_vertex.
split; intros.
unfold simplifyWL' in H.
destruct (proj1 (Dec.F.add_iff _ _ _) H).
generalize (In_freeze_props _ _ _ _ _ _ _ _ HH (refl_equal _) HWS). intro.
destruct H1. destruct H2. destruct H3.
split. rewrite <-(compat_bool_low _ _ _ _ H0). assumption.
split. rewrite <-(compat_bool_move _ _ _ H0). apply not_aff_related_delete_preference_edges.
split. rewrite <-H0. assumption.
rewrite <-H0. assumption.

unfold simplifyWL_ in H0.
destruct (VertexSet.union_1 H0).
generalize (In_simplify_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS). intro.
destruct H2. destruct H3. destruct H4.
split.
assumption.
split.
apply delete_preference_edges_move_false_false. assumption.
split; assumption.
unfold new_simp in H1.
generalize (VertexSet.filter_1 (compat_move_up _ _) H1). intro.
generalize (VertexSet.filter_2 (compat_move_up _ _) H1). clear H1. intro.
rewrite andb_true_iff in H1. destruct H1.
split. assumption.
split. apply delete_preference_edges_move_inv.
intro. elim (not_in_pref_self r g).
rewrite <-H4 in H2. apply (VertexSet.diff_1 H2).
apply move_related_card.
unfold pref_degree. rewrite <-(eq_K_2 _ _ H1). auto.
apply (VertexSet.diff_1 H2).
symmetry. apply (eq_K_2 _ _ H1).
split.
apply (in_pref_in _ _ _ (VertexSet.diff_1 H2)).
apply (VertexSet.diff_2 H2).

destruct H. destruct H0. destruct H1.
destruct (Register.eq_dec r x).
apply VertexSet.add_1. auto.
apply VertexSet.add_2.
case_eq (In_dec x adj_fst); intros.
case_eq (eq_K 1 (VertexSet.cardinal (preference_adj x g))); intros.
apply VertexSet.union_3. apply VertexSet.filter_3.
apply compat_move_up.
assumption.
rewrite H4. rewrite H. auto.
apply VertexSet.union_2. WS_apply HWS.
split. assumption.
split.
case_eq (move_related g x); intros.
generalize (delete_preference_edges_move_2 _ _ _ Hin n H5 H0). intro.
rewrite (eq_K_1 _ _ H6) in H4. inversion H4.
reflexivity.
split; assumption.
apply VertexSet.union_2.
WS_apply HWS.
split. assumption.
split. case_eq (move_related g x); intros.
generalize (delete_preference_edges_move_1 _ _ _ Hin n H4 H0). intro.
elim n0. apply VertexSet.diff_3; assumption.
reflexivity.
split; assumption.

unfold movesWL'. intro. rewrite not_incident_edges_1.
rewrite In_delete_preference_edges_edge.
split; intros.
destruct H.
generalize (In_move_props _ _ _ _ _ _ _ _ H (refl_equal _) HWS). intro.
destruct H1.
split. assumption.
split. assumption.
intro. elim H0. destruct H3. assumption.
destruct H. destruct H0.
split. WS_apply HWS. split; assumption.
intro. elim H1. split; assumption.

intros. apply (In_move_props _ _ _ _ _ _ _ _ H (refl_equal _) HWS).
Qed.

Lemma WS_freeze : forall r ircg (Hin : In_graph r (irc_g ircg)),
VertexSet.In r (get_freezeWL (irc_wl ircg)) ->
WS_properties (delete_preference_edges r (irc_g ircg) Hin) 
                        (irc_k ircg)
                       (delete_preferences_wl2 r ircg (irc_k ircg)).


Proof.
intros. rewrite <-(Hk ircg). apply WS_delete_preferences_wl2. auto.
Qed.

Require Import FSets.
Require Import InterfGraphMapImp.
Require Import IRC_graph.
Require Import ZArith.
Require Import Edges.
Require Import Remove_Vertex_Degree.
Require Import WS.
Require Import Remove_Vertex_Move.
Require Import Affinity_relation.
Require Import Interference_adjacency.

Import RegFacts Props OTFacts.

Definition eq_K x K := match eq_nat_dec x K with
|left _ => true
|right _ => false
end.

Lemma eq_K_1 : forall x y,
y = x ->
eq_K x y = true.

Proof.
intros. unfold eq_K. rewrite <-H. destruct (eq_nat_dec y y); intuition.
Qed.

Lemma eq_K_2 : forall x y,
eq_K x y = true ->
x = y.

Proof.
intros. unfold eq_K in H. destruct (eq_nat_dec x y). auto. inversion H.
Qed.

Lemma eq_K_compat : forall K g,
compat_bool Register.eq (fun x => eq_K K (VertexSet.cardinal (interference_adj x g))).

Proof.
unfold compat_bool. intros. rewrite (compat_interference_adj _ _ _ H). reflexivity.
Qed.

Lemma eq_K_compat_pref : forall K g,
compat_bool Register.eq (fun x => eq_K K (VertexSet.cardinal (preference_adj x g))).

Proof.
unfold compat_bool. intros. rewrite (compat_preference_adj _ _ _ H). reflexivity.
Qed.

Lemma compat_move_up : forall g K,
compat_bool Register.eq 
(fun x => eq_K 1 (VertexSet.cardinal (preference_adj x g)) && has_low_degree g K x).

Proof.
unfold compat_bool; intros.
rewrite (compat_preference_adj _ _ _ H).
destruct (eq_K 1 (VertexSet.cardinal (preference_adj y g))). simpl.
apply compat_bool_low. assumption.
simpl. reflexivity.
Qed.

Definition remove_wl_2 r ircg K :=
  let g := irc_g ircg in
  let wl := irc_wl ircg in
  let simplify := get_simplifyWL wl in
  let freeze := get_freezeWL wl in
  let spillWL := get_spillWL wl in
  let movesWL := get_movesWL wl in
  let pre := precolored g in
  let int_adj := interference_adj r g in
  let not_pre_int_adj := VertexSet.diff int_adj pre in
  let pre_adj := preference_adj r g in
  let not_pre_pre_adj := VertexSet.diff pre_adj pre in  
  let newlow := VertexSet.filter (fun x => eq_K K (VertexSet.cardinal (interference_adj x g))) not_pre_int_adj in
  let (free, simp) := VertexSet.partition (move_related g) newlow in
  let newnmr := VertexSet.filter (fun x => eq_K 1 (VertexSet.cardinal (preference_adj x g)) && has_low_degree g K x) not_pre_pre_adj in
  let simplifyWL__ := VertexSet.union simplify simp in
  let simplifyWL_ := VertexSet.union simplifyWL__ newnmr in
  let simplifyWL' := VertexSet.remove r simplifyWL_ in
  let freezeWL__ := VertexSet.diff freeze newnmr in
  let freezeWL_ := VertexSet.union freezeWL__ free in
  let freezeWL' := VertexSet.remove r freezeWL_ in
  let spillWL_ := VertexSet.diff spillWL newlow in
  let spillWL' := VertexSet.remove r spillWL_ in
  let movesWL' := not_incident_edges r movesWL g in
  (spillWL', freezeWL', simplifyWL', movesWL').

Lemma WS_remove_wl_2 : forall r ircg,
WS_properties (remove_vertex r (irc_g ircg)) (VertexSet.cardinal (pal ircg))
                        (remove_wl_2 r ircg (VertexSet.cardinal (pal ircg))).

Proof.
unfold remove_wl_2. intros r ircg.
generalize (HWS_irc ircg). intro HWS. rewrite <-(Hk ircg) in *.
set (g' := remove_vertex r (irc_g ircg)) in *.
set (k := VertexSet.cardinal (pal ircg)) in *.
set (g := irc_g ircg) in *.
set (wl := irc_wl ircg) in *.
set ( simplify := get_simplifyWL wl ) in *.
set ( freeze := get_freezeWL wl ) in *.
set ( spillWL := get_spillWL wl ) in *.
set ( int_adj := interference_adj r g ) in *.
set ( not_pre_int_adj := VertexSet.diff int_adj (precolored g) ) in *.
set ( pre_adj := preference_adj r g ) in *.
set ( not_pre_pre_adj := VertexSet.diff pre_adj (precolored g) ) in *.
set ( low := VertexSet.filter (fun x => eq_K k (VertexSet.cardinal (interference_adj x g))) not_pre_int_adj ) in *.
set ( simpfree := VertexSet.partition (move_related g) low ) in *.
case_eq simpfree. intros free simp Hsf.
unfold simpfree in Hsf.
set ( nmr := VertexSet.filter (fun x => eq_K 1 (VertexSet.cardinal (preference_adj x g)) && has_low_degree g k x) not_pre_pre_adj) in *.
set ( simplifyWL__ := VertexSet.union simplify simp ) in *.
set ( simplifyWL_ := VertexSet.union simplifyWL__ nmr) in *.
set ( simplifyWL' := VertexSet.remove r simplifyWL_ ) in *.
set ( freezeWL__ := VertexSet.diff freeze nmr ) in *.
set ( freezeWL_ := VertexSet.union freezeWL__ free ) in *.
set ( freezeWL' := VertexSet.remove r freezeWL_ ) in *.
set ( spillWL_ := VertexSet.diff spillWL low ) in *.
set ( spillWL' := VertexSet.remove r spillWL_ ) in *.
set ( movesWL' := not_incident_edges r (get_movesWL wl) g) in *.

unfold WS_properties. split.
split; intro H.
unfold get_spillWL in H. simpl in H.
(* spillWL' => *)
unfold spillWL' in H.
generalize (VertexSet.remove_3 H). intro H0.
unfold spillWL_ in H0.
generalize (VertexSet.diff_1 H0). intro H1.
generalize (VertexSet.diff_2 H0). intro H2.
split.
case_eq (has_low_degree g' k x); intros.
elim H2. apply VertexSet.filter_3.
apply eq_K_compat.
unfold not_pre_int_adj. apply VertexSet.diff_3.
apply low_degree_in_interf with (K := k).
assumption.
intro. elim (VertexSet.remove_1 (Register.eq_sym _ _  H4) H).
apply (proj1 (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS)).
apply (proj2 (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS)).
apply eq_K_1.
apply degree_dec_remove_K with (r := r).
intro. elim (VertexSet.remove_1 (Register.eq_sym _ _ H4) H).
apply (proj1 (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS)).
assumption.
reflexivity.
split.
unfold g'. rewrite In_remove_vertex. split.
apply (proj2 (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS)).
intro. elim (VertexSet.remove_1 (Register.eq_sym _ _ H3) H).
unfold g'. rewrite precolored_remove_vertex.
intro. elim (proj2 (proj2 (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS))).
apply (VertexSet.remove_3 H3).

(* spillWL' <= *)
destruct H. destruct H0.
unfold get_spillWL. simpl.
unfold spillWL'.
assert (~Register.eq r x) as Hr.
intro. rewrite <-H2 in H0. unfold g' in H0. 
rewrite In_remove_vertex in H0. destruct H0. elim H3. auto.
apply VertexSet.remove_2. assumption.
unfold spillWL_. apply VertexSet.diff_3.
WS_apply HWS.
split.
apply not_low_remove_not_low with (r:=r).
assumption.
intuition.
split.
unfold g' in H0. rewrite In_remove_vertex in H0. intuition.
unfold g' in H1. rewrite precolored_remove_vertex in H1.
intro. elim H1. apply VertexSet.remove_2; auto.
intro. unfold low in H2.
generalize (VertexSet.filter_1 (eq_K_compat k g) H2). intro H3.
generalize (VertexSet.filter_2 (eq_K_compat k g) H2). clear H2. intro H2.
generalize (eq_K_2 _ _ H2). clear H2. intro H2.
assert (has_low_degree g' k x = true).
apply degree_K_remove_dec. intuition.
unfold has_low_degree, interf_degree. rewrite <-H2.
destruct (le_lt_dec k k). reflexivity. elim (lt_irrefl _ l).
auto.
unfold not_pre_int_adj in H3. generalize (VertexSet.diff_1 H3). intro.
unfold int_adj in H4. assumption.
rewrite H in H4. inversion H4.

(* freezeWL' => *)
split.
unfold get_freezeWL. simpl. split; intros.
unfold freezeWL' in H.
assert (~Register.eq r x) as Hr.
intro. elim (VertexSet.remove_1 H0 H).
generalize (VertexSet.remove_3 H). clear H. intro.
unfold freezeWL_ in H.
destruct (VertexSet.union_1 H).
unfold freezeWL__ in H0.
generalize (VertexSet.diff_1 H0). intro.
generalize (VertexSet.diff_2 H0). clear H0. intro.
split.
apply low_remove_low.
apply (proj1 (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS)).
intuition.
split.
unfold nmr in H0.
case_eq (move_related g' x); intros.
reflexivity.
elim H0. apply VertexSet.filter_3.
apply compat_move_up.
unfold not_pre_pre_adj. apply VertexSet.diff_3.
unfold pre_adj. apply move_related_not_remove_in_pref. intuition.
apply (proj1 (proj2 (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS))).
assumption.
apply (proj2 (proj2 (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS))).
assert (VertexSet.cardinal (preference_adj x g) = 1).
apply pref_degree_dec_remove_1 with (r:=r). intuition.
apply (proj1 (proj2 (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS))). assumption.
rewrite (eq_K_1 _ _ H3). simpl.
apply (proj1 (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS)).
unfold g'. rewrite precolored_remove_vertex.
intro. elim (proj2 (proj2 (proj2 (In_freeze_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS)))).
apply (VertexSet.remove_3 H2).
split.
assert (VertexSet.cardinal (interference_adj x g) = k).
assert (VertexSet.In x (fst (VertexSet.partition (move_related g) low))).
rewrite Hsf. simpl. assumption.
rewrite (VertexSet.partition_1) in H1.
generalize (VertexSet.filter_1 (compat_bool_move _) H1). intro.
unfold low in H2.
generalize (VertexSet.filter_1 (eq_K_compat k g) H2). intro H3.
generalize (VertexSet.filter_2 (eq_K_compat k g) H2). clear H2. intro H2.
generalize (eq_K_2 _ _ H2). auto. apply compat_bool_move.
apply degree_K_remove_dec.
intuition.
unfold has_low_degree, interf_degree. rewrite H1.
destruct (le_lt_dec k k). reflexivity. elim (lt_irrefl _ l). auto.
assert (VertexSet.In x (fst (VertexSet.partition (move_related g) low))).
rewrite Hsf. simpl. assumption.
rewrite (VertexSet.partition_1) in H2.
generalize (VertexSet.filter_1 (compat_bool_move _) H2). intro.
unfold low in H3.
generalize (VertexSet.filter_1 (eq_K_compat k g) H3). intro H4.
generalize (VertexSet.filter_2 (eq_K_compat k g) H3). clear H3. intro H3.
unfold not_pre_int_adj in H4. apply (VertexSet.diff_1 H4).
apply compat_bool_move.
split.
case_eq (move_related g' x); intros.
reflexivity.
assert (VertexSet.In x (fst (VertexSet.partition (move_related g) low))).
rewrite Hsf. simpl. assumption.
rewrite (VertexSet.partition_1) in H2.
generalize (VertexSet.filter_1 (compat_bool_move _) H2). intro.
generalize (VertexSet.filter_2 (compat_bool_move _) H2). clear H2. intro H2.
assert (VertexSet.In x (preference_adj r g)).
apply move_related_not_remove_in_pref; assumption.
assert (VertexSet.In x (interference_adj r g)).
unfold low in H3.
generalize (VertexSet.filter_1 (eq_K_compat k g) H3). intro H5.
apply (VertexSet.diff_1 H5).
elim (interf_pref_conflict x r g). split.
rewrite in_pref in H4. destruct H4.
unfold Prefere. exists x0. assumption.
rewrite in_interf in H5. unfold Interfere. assumption.
apply compat_bool_move.
unfold g'. rewrite precolored_remove_vertex.
intro.
assert (VertexSet.In x (fst (VertexSet.partition (move_related g) low))).
rewrite Hsf. simpl. assumption.
rewrite (VertexSet.partition_1) in H2.
generalize (VertexSet.filter_1 (compat_bool_move _) H2). intro.
unfold low in H3.
generalize (VertexSet.filter_1 (eq_K_compat k g) H3). intro.
elim (VertexSet.diff_2 H4). apply (VertexSet.remove_3 H1).
apply compat_bool_move.

(* freezeWL' <= *)
destruct H. destruct H0.
unfold freezeWL'.
assert (~Register.eq r x).
intro. generalize (move_related_in_graph _ _ H0). intro. rewrite <-H2 in H3.
unfold g' in H3. rewrite In_remove_vertex in H3. destruct H3. elim H4. auto.
apply VertexSet.remove_2. assumption.
unfold freezeWL_.
case_eq (has_low_degree g k x); intros.
apply VertexSet.union_2. unfold freezeWL__.
apply VertexSet.diff_3.
WS_apply HWS.
split.
assumption.
split.
apply move_remove_2 with (r:=r). assumption.
unfold g' in H1. rewrite precolored_remove_vertex in H1.
intro. elim H1. apply VertexSet.remove_2. assumption. assumption.
intro. unfold nmr in H4.
assert (move_related g' x = false).
apply pref_degree_1_remove_dec.
intuition.
generalize (VertexSet.filter_2 (compat_move_up g k) H4). intro.
case_eq (eq_K 1 (VertexSet.cardinal (preference_adj x g))); intros.
rewrite (eq_K_2 _ _ H6); auto.
rewrite H6 in H5. inversion H5.
generalize (VertexSet.filter_1 (compat_move_up g k) H4). intro.
apply (VertexSet.diff_1 H5).
rewrite H0 in H5. inversion H5.
apply VertexSet.union_3.
cut (VertexSet.In x (fst (VertexSet.partition (move_related g) low))). intro.
rewrite Hsf in H4. simpl in H4. assumption.
rewrite VertexSet.partition_1.
apply VertexSet.filter_3.
apply compat_bool_move.
unfold low. apply VertexSet.filter_3.
apply eq_K_compat.
apply VertexSet.diff_3.
unfold int_adj.
apply low_degree_in_interf with (K:=k).
assumption. intuition. assumption.
unfold g' in H1. rewrite precolored_remove_vertex in H1.
intro. elim H1. apply VertexSet.remove_2; auto.
apply eq_K_1.
apply degree_dec_remove_K with (r:=r).
intuition. assumption. assumption.
apply move_remove_2 with (r:=r). assumption.
apply compat_bool_move.

(* simplifyWL' => *)
split.
unfold get_simplifyWL. simpl.
split; intros.
unfold simplifyWL' in H.
assert (~Register.eq r x) as Hr.
intro. elim (VertexSet.remove_1 H0 H).
generalize (VertexSet.remove_3 H). clear H. intro H.
unfold simplifyWL_ in H.
destruct (VertexSet.union_1 H).
unfold simplifyWL__ in H0.
destruct (VertexSet.union_1 H0).
generalize (In_simplify_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS). clear H1. intro.
destruct H1. destruct H2. destruct H3.
split. apply low_remove_low. assumption. intuition.
split. unfold g'.
apply move_remove. assumption.
split. unfold g'. rewrite In_remove_vertex. split; auto.
unfold g'. rewrite precolored_remove_vertex. intro.
elim H4. apply (VertexSet.remove_3 H5).
assert (VertexSet.In x (snd (VertexSet.partition (move_related g) low))).
rewrite Hsf. simpl. assumption.
rewrite VertexSet.partition_2 in H2.
generalize (VertexSet.filter_1 (compat_not_compat (compat_bool_move g)) H2). intro.
generalize (VertexSet.filter_2 (compat_not_compat (compat_bool_move g)) H2). clear H2. intro.
unfold low in H3.
generalize (VertexSet.filter_1 (eq_K_compat k g) H3). intro.
generalize (VertexSet.filter_2 (eq_K_compat k g) H3). clear H3. intro.
generalize (eq_K_2 _ _ H3). clear H3. intro.
split.
apply degree_K_remove_dec. intuition.
unfold has_low_degree, interf_degree. rewrite <-H3.
destruct (le_lt_dec k k). auto. elim (lt_irrefl _ l). auto.
apply (VertexSet.diff_1 H4).
split.
apply move_remove.
destruct (move_related g x). inversion H2. reflexivity.
split.
unfold g'. rewrite In_remove_vertex. split.
apply in_interf_in with (r:=r).
apply (VertexSet.diff_1 H4). intuition.
unfold g'. rewrite precolored_remove_vertex. intro.
elim (VertexSet.diff_2 H4). apply (VertexSet.remove_3 H5).
apply compat_bool_move.
(* x in nmr *)
unfold nmr in H0.
generalize (VertexSet.filter_1 (compat_move_up g k) H0). intro.
generalize (VertexSet.filter_2 (compat_move_up g k) H0). clear H0. intro.
assert (VertexSet.cardinal (preference_adj x g) = 1).
symmetry. apply eq_K_2.
case_eq (eq_K 1 (VertexSet.cardinal (preference_adj x g))); intros.
reflexivity.
rewrite H2 in H0. inversion H0.
rewrite (eq_K_1 _ _ H2) in H0. simpl in H0.
split.
apply low_remove_low. assumption. intuition.
split.
case_eq (move_related g x); intros.
apply pref_degree_1_remove_dec. intuition. assumption.
apply (VertexSet.diff_1 H1).
apply move_remove. assumption.
split. unfold g'. rewrite In_remove_vertex. split. apply in_pref_in with (r:=r).
apply (VertexSet.diff_1 H1). intuition.
unfold g'. rewrite precolored_remove_vertex. intro.
elim (VertexSet.diff_2 H1). apply (VertexSet.remove_3 H3).

(* simplifyWL' <= *)
destruct H. destruct H0. destruct H1.
unfold simplifyWL'.
assert (~Register.eq r x) as Hr.
intro. rewrite <-H3 in H1. 
unfold g' in H1. rewrite In_remove_vertex in H1. destruct H1. elim H4. auto.
apply VertexSet.remove_2. assumption.
unfold simplifyWL_.
case_eq (has_low_degree g k x); intros.
case_eq (move_related g x); intros.
apply VertexSet.union_3.
unfold nmr. apply VertexSet.filter_3.
apply compat_move_up.
apply VertexSet.diff_3.
apply move_related_not_remove_in_pref. assumption. assumption. assumption.
unfold g' in H2. rewrite precolored_remove_vertex in H2.
intro. elim H2. apply VertexSet.remove_2. intuition. assumption.
assert (eq_K 1 (VertexSet.cardinal (preference_adj x g)) = true).
apply eq_K_1.
apply pref_degree_dec_remove_1 with (r:=r). intuition . assumption. assumption.
rewrite H5. simpl. assumption.
apply VertexSet.union_2.
unfold simplifyWL__.
apply VertexSet.union_2.
WS_apply HWS.
split.
assumption.
split.
assumption.
split.
unfold g' in H1. rewrite In_remove_vertex in H1. intuition.
unfold g' in H2. rewrite precolored_remove_vertex in H2.
intro. elim H2. apply VertexSet.remove_2. intuition. assumption.
apply VertexSet.union_2.
unfold simplifyWL__.
apply VertexSet.union_3.
assert (VertexSet.In x (snd (VertexSet.partition (move_related g) low))).
rewrite VertexSet.partition_2.
apply VertexSet.filter_3.
apply compat_not_compat. apply compat_bool_move.
unfold low.
apply VertexSet.filter_3.
apply eq_K_compat. apply VertexSet.diff_3.
apply low_degree_in_interf with (K:=k). assumption. intuition. assumption.
unfold g' in H2. rewrite precolored_remove_vertex in H2.
intro. elim H2. apply VertexSet.remove_2. intuition. assumption.
apply eq_K_1. apply degree_dec_remove_K with (r:=r). intuition. assumption. assumption.
case_eq (move_related g x); intros.
assert (VertexSet.In x (interference_adj r g)).
apply low_degree_in_interf with (K:=k). assumption. intuition. assumption.
assert (VertexSet.In x (preference_adj r g)).
apply move_related_not_remove_in_pref. assumption. assumption. assumption.
elim (interf_pref_conflict x r g).
split.
unfold Prefere. rewrite in_pref in H6. assumption.
unfold Interfere. rewrite <-in_interf. assumption.
auto.
apply compat_bool_move.
rewrite Hsf in H4. simpl in H4. assumption.

(* movesWL => *)
unfold movesWL', get_movesWL. simpl.
split; intros.
simpl in H.
rewrite not_incident_edges_1 in H. destruct H as [H HH].
generalize (In_move_props _ _ _ _ _ _ _ _ H (refl_equal _) HWS). clear H. intro H.
destruct H. destruct H0.
split. assumption.
unfold g'. rewrite In_remove_edge. split.
apply (proj2 (proj1 (In_graph_aff_edge_in_AE _ _) H0)).
assumption.
generalize (proj1 (In_graph_interf_edge_in_IE _ _) H0). intro.
destruct H1.
inversion H. rewrite H1 in H3. inversion H3.
intros. apply (In_move_props _ _ _ _ _ _ _ _ H0 (refl_equal _) HWS).
destruct H.
rewrite not_incident_edges_1.
split.
WS_apply HWS.
split.
assumption.
unfold g' in H0. rewrite In_remove_edge in H0. intuition.
intro H1.
elim (In_graph_edge_in_ext _ _ H0).
intros.
destruct H1.
rewrite <-H1 in H2.
unfold g' in H2. rewrite In_remove_vertex in H2. destruct H2. elim H4. auto.
rewrite <-H1 in H3.
unfold g' in H3. rewrite In_remove_vertex in H3. destruct H3. elim H4. auto.
intros. apply (In_move_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS).
Qed.

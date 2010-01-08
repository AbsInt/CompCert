Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Remove_Vertex_WL.
Require Import WS.
Require Import Affinity_relation.
Require Import Interference_adjacency.
Require Import Edges.
Require Import IRC_graph.

Import Edge RegFacts Props OTFacts.

Definition simplify_wl r ircg K :=
  let g := irc_g ircg in
  let wl := irc_wl ircg in
  let simplify := get_simplifyWL wl in
  let freeze := get_freezeWL wl in
  let spillWL := get_spillWL wl in
  let movesWL := get_movesWL wl in
  let pre := precolored g in
  let int_adj := interference_adj r g in
  let not_pre_int_adj := VertexSet.diff int_adj pre in
  let newlow := VertexSet.filter (fun x => eq_K K (VertexSet.cardinal (interference_adj x g))) not_pre_int_adj in
  let (free, simp) := VertexSet.partition (move_related g) newlow in
  let simplifyWL_ := VertexSet.union simplify simp in
  let simplifyWL' := VertexSet.remove r simplifyWL_ in
  let freezeWL' := VertexSet.union freeze free in
  let spillWL' := VertexSet.diff spillWL newlow in
  let movesWL' := movesWL in (spillWL', freezeWL', simplifyWL', movesWL').

Lemma WS_simplify_aux : forall r ircg,
VertexSet.In r (get_simplifyWL (irc_wl ircg)) ->
WS_properties (remove_vertex r (irc_g ircg)) (VertexSet.cardinal (pal ircg))
                        (simplify_wl r ircg (VertexSet.cardinal (pal ircg))).

Proof.
intros.
generalize (WS_props_equal (remove_vertex r (irc_g ircg)) (VertexSet.cardinal (pal ircg))
           (remove_wl_2 r ircg (VertexSet.cardinal (pal ircg)))
           (simplify_wl r ircg (VertexSet.cardinal (pal ircg)))).
generalize (WS_remove_wl_2 r ircg).
unfold remove_wl_2, simplify_wl, get_simplifyWL,
       get_freezeWL, get_spillWL, get_movesWL.
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
set ( movesWL' := not_incident_edges r (get_movesWL wl) g) in *. simpl.
generalize (In_simplify_props _ _ _ _ _ _ _ _ H (refl_equal _) (HWS_irc ircg)). intro Hr.

assert (VertexSet.Equal (preference_adj r g) VertexSet.empty) as Hempty_pre.
apply not_move_related_empty_pref. intuition.
assert (VertexSet.Equal nmr VertexSet.empty) as Hempty_nmr.
unfold nmr.
split; intros.
generalize (VertexSet.filter_1 (compat_move_up _ _) H0). intro.
unfold not_pre_pre_adj in H1. generalize (VertexSet.diff_1 H1). intro.
unfold pre_adj in H2. rewrite Hempty_pre in H2. elim (VertexSet.empty_1 H2).
elim (VertexSet.empty_1 H0).

intros HWS H0. apply H0.

(* simplify worklist is only decreasing from r and increasing from simp,
   since nmr is empty, because preference adj r g is empty *)
split; intros.
apply VertexSet.remove_2.
intro. elim (VertexSet.remove_1 H2 H1).
destruct (VertexSet.union_1 (VertexSet.remove_3 H1)).
assumption.
rewrite Hempty_nmr in H2. elim (VertexSet.empty_1 H2).

apply VertexSet.remove_2.
intro. elim (VertexSet.remove_1 H2 H1).
apply VertexSet.union_2. apply (VertexSet.remove_3 H1).

(* r is not deleted from freezewl, since it is not move-related and
   no vertex is removed from freeze, since free is empty, because
   preference adj r g is empty *)

set (s := VertexSet.union (VertexSet.diff (snd (fst (fst wl))) nmr) free).
split; intros.
unfold s in H1. destruct (VertexSet.union_1 (VertexSet.remove_3 H1)).
apply VertexSet.union_2. apply (VertexSet.diff_1 H2).
apply VertexSet.union_3. assumption.

apply VertexSet.remove_2. intro. rewrite <-H2 in H1. clear H2.
unfold s in H1.
destruct (VertexSet.union_1 H1).
generalize (In_freeze_props _ _ _ _ _ _ _ _ H2 (refl_equal _) (HWS_irc ircg)). intro.
destruct H3. destruct H4. destruct Hr. destruct H7.
rewrite H7 in H4. inversion H4.
assert (free = fst (VertexSet.partition (move_related g) low)).
rewrite Hsf. auto.
rewrite H3 in H2. rewrite VertexSet.partition_1 in H2.
generalize (VertexSet.filter_2 (compat_bool_move _ ) H2). intro.
destruct Hr. destruct H6. unfold g in H4. rewrite H6 in H4. inversion H4.
apply compat_bool_move.

unfold s. destruct (VertexSet.union_1 H1).
apply VertexSet.union_2. apply VertexSet.diff_3.
assumption.
intro. rewrite Hempty_nmr in H3. elim (VertexSet.empty_1 H3).
apply VertexSet.union_3. assumption.

(* identically, r is not removed from spillwl, since it is not of high-degree,
   but degrees remain the same even if r is not move related *)
set (s := VertexSet.diff (fst (fst (fst wl))) low).
split; intros.
apply (VertexSet.remove_3 H1).
apply VertexSet.remove_2. intro. rewrite <-H2 in H1. clear H2.
unfold s in H1.
generalize (VertexSet.diff_1 H1). intro.
generalize (In_spill_props _ _ _ _ _ _ _ _ H2 (refl_equal _) (HWS_irc ircg)). intro.
destruct H3. destruct Hr. rewrite H5 in H3. inversion H3.
assumption.

(* there is no preference edge incident to r *)
split; intros.
rewrite not_incident_edges_1 in H1. destruct H1. assumption.
intros. apply (In_move_props _ _ _ _ _ _ _ _ H2 (refl_equal _) (HWS_irc ircg)).
rewrite not_incident_edges_1. split.
assumption.
intro. destruct Hr. destruct H4.
cut (move_related g r = true). intro. unfold g in H6. rewrite H4 in H6. inversion H6.
generalize (In_move_props _ _ _ _ _ _ _ _ H1 (refl_equal _) (HWS_irc ircg)). intro.
destruct H6.
apply move_related_charac2 with (e:=a); assumption.
intros. apply (In_move_props _ _ _ _ _ _ _ _ H2 (refl_equal _) (HWS_irc ircg)).

(* WS_remove_wl respects the invariant *)
assumption.
Qed.

Lemma WS_simplify : forall r ircg,
VertexSet.In r (get_simplifyWL (irc_wl ircg)) ->
WS_properties (remove_vertex r (irc_g ircg)) (irc_k ircg)
              (simplify_wl r ircg (irc_k ircg)).

Proof.
intros. rewrite <-(Hk ircg). apply WS_simplify_aux. auto.
Qed.

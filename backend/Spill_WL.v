Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Freeze_WL.
Require Import Edges.
Require Import WS.
Require Import Interference_adjacency.
Require Import Affinity_relation.
Require Import Remove_Vertex_WL.
Require Import IRC_graph.

Import RegFacts Props OTFacts.

Definition spill_wl r ircg K :=
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
  let simplifyWL' := VertexSet.union simplifyWL__ newnmr in
  let freezeWL__ := VertexSet.diff freeze newnmr in
  let freezeWL' := VertexSet.union freezeWL__ free in
  let spillWL_ := VertexSet.diff spillWL newlow in
  let spillWL' := VertexSet.remove r spillWL_ in
  let movesWL' := not_incident_edges r movesWL g in
  (spillWL', freezeWL', simplifyWL', movesWL').


Lemma WS_spill_aux : forall r ircg,
VertexSet.In r (get_spillWL (irc_wl ircg)) ->
WS_properties (remove_vertex r (irc_g ircg)) (VertexSet.cardinal (pal ircg))
              (spill_wl r ircg (VertexSet.cardinal (pal ircg))).

Proof.
intros.
generalize (WS_props_equal (remove_vertex r (irc_g ircg)) (VertexSet.cardinal (pal ircg))
           (remove_wl_2 r ircg (VertexSet.cardinal (pal ircg)))
           (spill_wl r ircg (VertexSet.cardinal (pal ircg)))).
generalize (WS_remove_wl_2 r ircg).
unfold remove_wl_2, spill_wl, get_simplifyWL,
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
generalize (In_spill_props _ _ _ _ _ _ _ _ H (refl_equal _) (HWS_irc ircg)). intro Hr.

intros HWS H0. apply H0.

(* r is not removed from simplify *)
split; intros.
apply (VertexSet.remove_3 H1).

apply VertexSet.remove_2. intro. rewrite <-H2 in H1. clear H2.
destruct (VertexSet.union_1 H1).
destruct (VertexSet.union_1 H2).
generalize (In_simplify_props _ _ _ _ _ _ _ _ H3 (refl_equal _) (HWS_irc ircg)). intro.
destruct H4. destruct Hr. rewrite H4 in H6. inversion H6.

assert (simp = snd (VertexSet.partition (move_related g) low)) as Hsimp.
rewrite Hsf. auto. rewrite Hsimp in H3.
rewrite VertexSet.partition_2 in H3.
generalize (VertexSet.filter_1 (compat_not_compat (compat_bool_move _)) H3). intro.
unfold low in H4. generalize (VertexSet.filter_1 (eq_K_compat _ _) H4). intro.
elim (not_in_interf_self r g). apply (VertexSet.diff_1 H5).
apply compat_bool_move.

unfold nmr in H2. generalize (VertexSet.filter_1 (compat_move_up _ _) H2). intro.
elim (not_in_pref_self r g (VertexSet.diff_1 H3)).
assumption.

(* r is not deleted from freezewl, since it is not move-related and
   no vertex is removed from freeze, since free is empty, because
   preference adj r g is empty *)

set (s := VertexSet.union (VertexSet.diff (snd (fst (fst wl))) nmr) free).
split; intros.
apply (VertexSet.remove_3 H1).

apply VertexSet.remove_2. intro. rewrite <-H2 in H1. clear H2.
unfold s in H1.
destruct (VertexSet.union_1 H1).
generalize (In_freeze_props _ _ _ _ _ _ _ _ (VertexSet.diff_1 H2) (refl_equal _) (HWS_irc ircg)). intro.
destruct H3. destruct Hr. rewrite H5 in H3. inversion H3.

assert (free = fst (VertexSet.partition (move_related g) low)).
rewrite Hsf. auto.
rewrite H3 in H2. rewrite VertexSet.partition_1 in H2.
generalize (VertexSet.filter_1 (compat_bool_move _ ) H2). intro.
unfold low in H4. generalize (VertexSet.filter_1 (eq_K_compat _ _) H4). intro.
elim (not_in_interf_self r g). apply (VertexSet.diff_1 H5).
apply compat_bool_move. assumption.

(* spill worklist is unchanged *)
apply VertexSet.eq_refl.

(* moves worklst is unchanged *)
apply EdgeSet.eq_refl.

(* WS_remove_wl respects the invariant *)
assumption.
Qed.

Lemma WS_spill : forall r ircg,
VertexSet.In r (get_spillWL (irc_wl ircg)) ->
WS_properties (remove_vertex r (irc_g ircg)) (irc_k ircg)
              (spill_wl r ircg (irc_k ircg)).

Proof.
intros. rewrite <-(Hk ircg). apply WS_spill_aux. auto.
Qed.

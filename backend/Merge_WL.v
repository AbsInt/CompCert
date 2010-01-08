Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Simplify_WL.
Require Import IRC_graph.
Require Import WS.
Require Import Edges.
Require Import Affinity_relation.
Require Import Interference_adjacency.
Require Import Remove_Vertex_WL.
Require Import Merge_Degree.

Import Edge RegFacts Props OTFacts.

Definition classify x g' palette wl :=
if is_precolored x g' then wl else
let a := get_spillWL wl in
let b := get_freezeWL wl in
let c := get_simplifyWL wl in
let d := get_movesWL wl in
if has_low_degree g' palette x then 
   if move_related g' x then (a, VertexSet.add x b, c, d)
   else (a, VertexSet.remove x b, VertexSet.add x c, d)
else (VertexSet.add x a, VertexSet.remove x b, c, d).

Definition merge_wl3 e ircg g' (p : In_graph_edge e (irc_g ircg)) (q : aff_edge e) :=
let wl := (irc_wl ircg) in
let g := (irc_g ircg) in
let palette := (pal ircg) in
let k := (irc_k ircg) in
let simplifyWL := get_simplifyWL wl in
let freezeWL := get_freezeWL wl in
let spillWL := get_spillWL wl in
let movesWL := get_movesWL wl in
let pre := precolored g in
let iadj_fst_ := interference_adj (fst_ext e) g in
let iadj_fst := VertexSet.diff iadj_fst_ pre in
let iadj_snd_ := interference_adj (snd_ext e) g in
let iadj_snd := VertexSet.diff iadj_snd_ pre in
let padj_fst_ := preference_adj (fst_ext e) g in
let padj_fst := VertexSet.diff padj_fst_ pre in
let padj_snd_ := preference_adj (snd_ext e) g in
let padj_snd := VertexSet.diff padj_snd_ pre in
let iadj_interf := VertexSet.inter iadj_fst iadj_snd in
let iadj_padj_interf := VertexSet.union
                           (VertexSet.inter padj_fst iadj_snd)
                           (VertexSet.inter padj_snd iadj_fst) in
let N := VertexSet.filter 
         (fun x => eq_K k (VertexSet.cardinal (interference_adj x g)))
         iadj_interf in
let (mr, nmr) := VertexSet.partition (move_related g) N in
let M := VertexSet.filter 
         (fun x => eq_K 1 (VertexSet.cardinal (preference_adj x g)) && has_low_degree g k x)
         iadj_padj_interf in
let simplifyWL_ := VertexSet.union simplifyWL nmr in
let simplifyWL' := VertexSet.union simplifyWL_ M in
let freezeWL__ := VertexSet.diff freezeWL M in
let freezeWL_ := VertexSet.union freezeWL__ mr in
let freezeWL' := VertexSet.remove (fst_ext e) (VertexSet.remove (snd_ext e) freezeWL_) in
let spillWL_ := VertexSet.diff spillWL N in
let spillWL' := VertexSet.remove (fst_ext e) (VertexSet.remove (snd_ext e) spillWL_) in
let movesWL' := AE_merge_up (preference_adj (fst_ext e) g')
                             padj_fst_ padj_snd_ e movesWL in
classify (fst_ext e) g' k (spillWL', freezeWL', simplifyWL', movesWL').


Lemma ws_merge3 : forall e ircg H H0,
WS_properties (merge e (irc_g ircg) H H0) 
              (VertexSet.cardinal (pal ircg))
              (merge_wl3 e ircg (merge e (irc_g ircg) H H0) H H0).

Proof.
intros e ircg HH HH0.
unfold merge_wl3. unfold WS_properties. rewrite <-(Hk ircg) in *. 
set (wl := irc_wl ircg) in *.
set (g := irc_g ircg) in *.
set (g' := merge e g HH HH0) in *.
set (palette := (pal ircg)) in *.
set (simplify := get_simplifyWL wl) in *.
set (freeze := get_freezeWL wl) in *.
set (spill := get_spillWL wl) in *.
set (moves := get_movesWL wl) in *.
set (k := VertexSet.cardinal palette) in *.
set (pre := precolored g) in *.
set (iadj_fst_ := interference_adj (fst_ext e) g) in *.
set (iadj_snd_ := interference_adj (snd_ext e) g) in *.
set (padj_fst_ := preference_adj (fst_ext e) g) in *.
set (padj_snd_ := preference_adj (snd_ext e) g) in *.
set (iadj_fst := VertexSet.diff iadj_fst_ pre) in *.
set (iadj_snd := VertexSet.diff iadj_snd_ pre) in *.
set (padj_fst := VertexSet.diff padj_fst_ pre) in *.
set (padj_snd := VertexSet.diff padj_snd_ pre) in *.
set (inter_interf := VertexSet.inter iadj_fst iadj_snd) in *.
set (iadj_padj_interf := VertexSet.union
                         (VertexSet.inter padj_fst iadj_snd)
                         (VertexSet.inter padj_snd iadj_fst)) in *.
set (N := VertexSet.filter
          (fun x => eq_K k (VertexSet.cardinal (interference_adj x g)))
          inter_interf) in *.
set (M := VertexSet.filter
          (fun x => eq_K 1 (VertexSet.cardinal (preference_adj x g))
           && has_low_degree g k x)
           iadj_padj_interf) in *.
set (mrnmr := VertexSet.partition (move_related g) N) in *.
case_eq mrnmr. intros mr nmr Hmr. unfold mrnmr in Hmr.
set (simplifyWL_ := VertexSet.union simplify nmr) in *.
set (simplifyWL' := VertexSet.union simplifyWL_ M) in *.
set (freezeWL__ := VertexSet.diff freeze M) in *.
set (freezeWL_ := VertexSet.union freezeWL__ mr) in *.
set (freezeWL' := VertexSet.remove (fst_ext e) (VertexSet.remove (snd_ext e) freezeWL_)) in *.
set (spillWL_ := VertexSet.diff spill N) in *.
set (spillWL' := VertexSet.remove (fst_ext e) (VertexSet.remove (snd_ext e) spillWL_)) in *.
set (movesWL' := AE_merge_up (preference_adj (fst_ext e) g') padj_fst_ padj_snd_ e moves) in *.

unfold get_spillWL. unfold get_freezeWL. unfold get_simplifyWL. unfold get_movesWL. simpl.
generalize (HWS_irc ircg). intro HWS. rewrite <-(Hk ircg) in HWS.
generalize HH0. intro Haffa. destruct Haffa as [x2 Haffa].

cut (VertexSet.Equal mr (VertexSet.filter (move_related g) N)).
intro HMR.
cut (VertexSet.Equal nmr (VertexSet.filter (fun x => negb (move_related g x)) N)).
intro HNMR.

split.
intro x.
(* spillWL for x = fst_ext e *)
destruct (Register.eq_dec x (fst_ext e)); split; intros.
(* spillWL => for x = fst_ext e *)
unfold classify in H.
unfold get_simplifyWL, get_freezeWL, get_spillWL, get_movesWL in H. simpl in H.
(* fst_ext e is precolored => False *)
case_eq (is_precolored (fst_ext e) g'); intros; rewrite H0 in H.
simpl in H.
unfold spillWL' in H. generalize (VertexSet.remove_3 (VertexSet.remove_3 H)). intro.
unfold spillWL_ in H1. generalize (VertexSet.diff_1 H1). intro.
generalize (In_spill_props _ _ _ _ _ _ _ _ H2 (refl_equal _) HWS). intro.
elim (proj2 (proj2 H3)).
apply VertexSet.remove_3 with (x:=snd_ext e).
rewrite <-(precolored_merge e (irc_g ircg) HH HH0). rewrite precolored_equiv. split.
rewrite is_precolored_ext with (y := fst_ext e); eassumption.
rewrite In_merge_vertex. split. intuition.
intro. elim (In_graph_edge_diff_ext e g). assumption.
rewrite <-e0. rewrite <-H4. auto.
(* fst_ext e is not precolored *)
case_eq (has_low_degree g' k (fst_ext e)); intros; rewrite H1 in H.
(* fst_ext e is of low-degree in g' *)
case_eq (move_related g' (fst_ext e)); intros; rewrite H2 in H;
simpl in H; unfold spillWL' in H; elim (VertexSet.remove_1 (Register.eq_sym _ _ e0) H).
(* fst_ext e is of high-degree in g' *)
simpl in H. split.
rewrite (compat_bool_low _ _ _ _ e0). assumption.
split. unfold g'. rewrite In_merge_vertex. split.
rewrite e0. apply (proj1 (In_graph_edge_in_ext _ _ HH)).
intro. elim (In_graph_edge_diff_ext e g). assumption.
rewrite <-e0. rewrite <-H2. auto.
rewrite precolored_equiv. intro. destruct H2.
rewrite (is_precolored_ext _ _ g' e0) in H2. rewrite H0 in H2. inversion H2.
(* spillWL <= for x = fst_ext e *)
destruct H. destruct H0.
unfold classify, get_spillWL, get_simplifyWL, get_freezeWL, get_movesWL. simpl.
case_eq (is_precolored (fst_ext e) g'); intros; simpl.
(* fst_ext e is precolored => False *)
elim H1. rewrite precolored_equiv. split.
rewrite (is_precolored_ext _ _ g' e0). assumption. assumption.
(* fst_ext e is not precolored *)
case_eq (has_low_degree g' k (fst_ext e)); intros; simpl.
(* fst_ext e is of low-degree in g' *)
rewrite (compat_bool_low _ _ _ _ e0) in H. rewrite H in H3. inversion H3.
(* fst_ext e is of high-degree in g' *)
apply VertexSet.add_1. intuition.

(* spillWL : x is different from fst_ext e *)
assert (VertexSet.In x spillWL').
unfold classify, get_simplifyWL, get_movesWL, get_freezeWL, get_spillWL in H. simpl in H.
case_eq (is_precolored (fst_ext e) g'); simpl in H; intro; rewrite H0 in H.
assumption.
case_eq (has_low_degree g' k (fst_ext e)); intros; rewrite H1 in H; simpl in H.
case_eq (move_related g' (fst_ext e)); intros; rewrite H2 in H; simpl in H; assumption.
apply VertexSet.add_3 with (x:=fst_ext e). auto. assumption.
generalize H0. clear H H0. intro H.
unfold spillWL' in H. generalize (VertexSet.remove_3 H). clear H. intro H.
assert (~Register.eq x (snd_ext e)).
intro. elim (VertexSet.remove_1 (Register.eq_sym _ _ H0) H).
generalize (VertexSet.remove_3 H). clear H. intro H.
unfold spillWL_ in H.
generalize (VertexSet.diff_1 H). intro.
generalize (VertexSet.diff_2 H). clear H. intro H.
generalize (In_spill_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS). intro.
destruct H2. destruct H3. fold palette in H2. fold k in H2.
split.
case_eq (has_low_degree g' k x); intros.
generalize (merge_dec_interf _ _ _ _ HH HH0 H2 H5 n H0). intro.
generalize (merge_dec_K _ _ _ _ HH HH0 n H0 H2 H5). intro.
destruct H6. elim H. unfold N.
apply VertexSet.filter_3.
apply eq_K_compat.
unfold inter_interf. apply VertexSet.inter_3.
apply VertexSet.diff_3; assumption.
apply VertexSet.diff_3; assumption.
apply eq_K_1. assumption.
reflexivity.
split. unfold g'. rewrite In_merge_vertex. split; assumption.
unfold g'. rewrite precolored_merge.
intro. elim H4. apply (VertexSet.remove_3 H5).
(* spillWL <= for x different from fst_ext e *)
destruct H. destruct H0.
assert (VertexSet.In x spillWL').
unfold spillWL'. apply VertexSet.remove_2. auto.
apply VertexSet.remove_2. intro.
unfold g' in H0. rewrite In_merge_vertex in H0. destruct H0. elim H3. auto.
unfold spillWL_. apply VertexSet.diff_3.
WS_apply HWS.
split.
apply (merge_low_1 g e x k HH0 HH). assumption.
intro. rewrite H2 in H0.
unfold g' in H0. rewrite In_merge_vertex in H0. destruct H0. elim H3. auto.
assumption.
split. unfold g' in H0. rewrite In_merge_vertex in H0. intuition.
unfold g' in H1. rewrite precolored_merge in H1.
intro. elim H1. apply VertexSet.remove_2. intro.
rewrite <-H3 in H0.
unfold g' in H0. rewrite In_merge_vertex in H0. destruct H0. elim H4. auto.
assumption.
intro. unfold N in H2.
generalize (VertexSet.filter_1 (eq_K_compat k g) H2). intro.
generalize (VertexSet.filter_2 (eq_K_compat k g) H2). clear H2. intro.
generalize (eq_K_2 _ _ H2). clear H2. intro H2.
assert (has_low_degree g' k x = true).
apply merge_dec_low. auto.
generalize (VertexSet.inter_1 H3). intro. apply (VertexSet.diff_1 H4).
generalize (VertexSet.inter_2 H3). intro. apply (VertexSet.diff_1 H4).
rewrite H in H4. inversion H4.
unfold classify, get_simplifyWL, get_freezeWL, get_movesWL, get_spillWL. simpl.
case_eq (is_precolored (fst_ext e) g'); intros.
assumption.
case_eq (has_low_degree g' k (fst_ext e)); intros.
case_eq (move_related g' (fst_ext e)); intros.
assumption.
assumption.
simpl. apply VertexSet.add_2. assumption.

(* freezeWL *)
split.
intro x. destruct (Register.eq_dec x (fst_ext e)).
(* x = fst_ext e *)
split; intro.
(* => *)
unfold classify, get_spillWL, get_simplifyWL, get_movesWL, get_freezeWL in H. simpl in H.
case_eq (is_precolored (fst_ext e) g'); intros; rewrite H0 in H; simpl in H.
unfold freezeWL' in H. elim (VertexSet.remove_1 (Register.eq_sym _ _ e0) H).
case_eq (has_low_degree g' k (fst_ext e)); intros; rewrite H1 in H; simpl in H.
split.
rewrite (compat_bool_low _ _ _ _ e0). assumption.
case_eq (move_related g' (fst_ext e)); intros; rewrite H2 in H; simpl in H.
split.
rewrite (compat_bool_move _ _ _ e0). assumption.
rewrite precolored_equiv. intro. destruct H3.
rewrite (is_precolored_ext _ _ g' e0) in H3. rewrite H0 in H3. inversion H3.
elim (VertexSet.remove_1 (Register.eq_sym _ _ e0) H).
elim (VertexSet.remove_1 (Register.eq_sym _ _ e0) H).
(* <= *)
destruct H. destruct H0.
unfold classify, get_simplifyWL, get_spillWL, get_freezeWL, get_movesWL. simpl.
case_eq (is_precolored (fst_ext e) g'); intros; simpl.
elim H1. rewrite precolored_equiv. split.
rewrite (is_precolored_ext _ _ g' e0). assumption.
apply move_related_in_graph. assumption.
case_eq (has_low_degree g' k (fst_ext e)); intros; simpl.
case_eq (move_related g' (fst_ext e)); intros; simpl.
apply VertexSet.add_1. intuition.
rewrite (compat_bool_move _ _ _ e0) in H0. rewrite H0 in H4. inversion H4.
rewrite (compat_bool_low _ _ _ _ e0) in H. rewrite H3 in H. inversion H.

(* x <> fst_ext e => *)
split; intro.
assert (VertexSet.In x freezeWL').
unfold classify, get_spillWL, get_simplifyWL, get_freezeWL, get_movesWL in H. simpl in H.
case_eq (is_precolored (fst_ext e) g'); intros; rewrite H0 in H.
assumption.
case_eq (has_low_degree g' k (fst_ext e)); intros; rewrite H1 in H.
case_eq (move_related g' (fst_ext e)); intros; rewrite H2 in H.
simpl in H. apply VertexSet.add_3 with (x:= fst_ext e). auto. assumption.
simpl in H. apply (VertexSet.remove_3 H).
simpl in H. apply (VertexSet.remove_3 H).
generalize H0. clear H H0. intro H.
unfold freezeWL' in H.
generalize (VertexSet.remove_3 H). clear H. intro.
assert (~Register.eq x (snd_ext e)).
intro. elim (VertexSet.remove_1 (Register.eq_sym _ _ H0) H).
generalize (VertexSet.remove_3 H). clear H. intro.
unfold freezeWL_ in H.
destruct (VertexSet.union_1 H).
unfold freezeWL__ in H1.
generalize (VertexSet.diff_1 H1). intro.
generalize (VertexSet.diff_2 H1). clear H1. intro.
unfold freeze in H2.
generalize (In_freeze_props _ _ _ _ _ _ _ _ H2 (refl_equal _) HWS). intro.
destruct H3. destruct H4. destruct H5.
fold palette in H3. fold k in H3.
split.
apply low_dec; assumption.
split.
case_eq (move_related g' x); intros.
reflexivity.
elim H1. unfold M.
apply VertexSet.filter_3.
apply compat_move_up.
Require Import Merge_Move.
Require Import Graph_Facts.
generalize (move_merge_not_move x e g HH HH0 n H0 H7 H4). intro.
destruct H8.
apply VertexSet.union_3.
apply VertexSet.inter_3.
apply VertexSet.diff_3. apply (VertexSet.inter_2 H8). assumption.
apply VertexSet.diff_3. apply (VertexSet.inter_1 H8). assumption.
apply VertexSet.union_2.
apply VertexSet.inter_3.
apply VertexSet.diff_3. apply (VertexSet.inter_2 H8). assumption.
apply VertexSet.diff_3. apply (VertexSet.inter_1 H8). assumption.
generalize (move_related_dec_1 x e g HH HH0 n H0 H4 H7). intro.
unfold pref_degree in H8. rewrite (eq_K_1 _ _ H8). simpl. assumption.
unfold g'. rewrite precolored_merge. intro. elim H6.
apply (VertexSet.remove_3 H7).

(* x in mr *)
rewrite HMR in H1.
generalize (VertexSet.filter_1 (compat_bool_move _) H1). intro.
generalize (VertexSet.filter_2 (compat_bool_move _) H1). clear H1. intro H1.
unfold N in H2.
generalize (VertexSet.filter_1 (eq_K_compat _ _) H2). intro.
generalize (VertexSet.filter_2 (eq_K_compat _ _) H2). clear H2. intro.
generalize (eq_K_2 _ _ H2). clear H2. intro.
split.
apply merge_dec_low. auto.
apply (VertexSet.diff_1 (VertexSet.inter_1 H3)).
apply (VertexSet.diff_1 (VertexSet.inter_2 H3)).
split.
apply move_related_merge_true; auto.
intro.
generalize (VertexSet.inter_1 H4). intro.
generalize (VertexSet.inter_2 H4). clear H4. intro.
generalize (VertexSet.inter_1 H3). intro.
generalize (VertexSet.inter_2 H3). clear H3. intro.
generalize (VertexSet.diff_1 H3). clear H3. intro.
generalize (VertexSet.diff_1 H6). intro.
generalize (VertexSet.diff_2 H6). clear H6. intro.
elim (interf_pref_conflict x (snd_ext e) g).
split.
rewrite in_pref in H4. destruct H4.
unfold Prefere. exists x0. assumption.
unfold Interfere. rewrite <-in_interf. assumption.
intro.
generalize (VertexSet.inter_1 H4). intro.
generalize (VertexSet.inter_2 H4). clear H4. intro.
generalize (VertexSet.inter_1 H3). intro.
generalize (VertexSet.inter_2 H3). clear H3. intro.
generalize (VertexSet.diff_1 H3). clear H3. intro.
generalize (VertexSet.diff_1 H6). intro.
generalize (VertexSet.diff_2 H6). clear H6. intro.
elim (interf_pref_conflict x (fst_ext e) g).
split.
rewrite in_pref in H4. destruct H4.
unfold Prefere. exists x0. assumption.
unfold Interfere. unfold iadj_fst_ in H7. rewrite in_interf in H7. auto.
unfold g'. rewrite precolored_merge.
intro. elim (VertexSet.diff_2 (VertexSet.inter_1 H3)).
apply (VertexSet.remove_3 H4).

(* <= *)
assert (VertexSet.In x freezeWL').
destruct H. destruct H0.
unfold freezeWL'.
apply VertexSet.remove_2. auto.
apply VertexSet.remove_2.
intro. elim (not_in_merge_snd e g HH HH0).
apply move_related_in_graph. rewrite (compat_bool_move _ _ _ H2). assumption.
unfold freezeWL_.
case_eq (has_low_degree g k x); intros.
apply VertexSet.union_2.
unfold freezeWL__.
apply VertexSet.diff_3.
WS_apply HWS.
split. assumption.
split.
apply (move_related_merge_move_related g e x HH HH0). assumption.
unfold g' in H1. rewrite precolored_merge in H1. intro. elim H1.
apply VertexSet.remove_2. intro. elim (not_in_merge_snd _ _ HH HH0).
apply move_related_in_graph. rewrite (compat_bool_move _ _ _ H4). assumption. assumption.
intro. unfold M in H3.
generalize (VertexSet.filter_2 (compat_move_up _ _) H3). intro.
assert (move_related g' x = false).
apply move_related_change_charac.
generalize (VertexSet.filter_1 (compat_move_up _ _) H3). intro.
unfold iadj_padj_interf in H5.
destruct (VertexSet.union_1 H5).
apply VertexSet.union_3.
apply VertexSet.inter_3.
apply (VertexSet.diff_1 (VertexSet.inter_2 H6)).
apply (VertexSet.diff_1 (VertexSet.inter_1 H6)).
apply VertexSet.union_2.
apply VertexSet.inter_3.
apply (VertexSet.diff_1 (VertexSet.inter_2 H6)).
apply (VertexSet.diff_1 (VertexSet.inter_1 H6)).
case_eq (eq_K 1 (VertexSet.cardinal (preference_adj x g))); intros.
symmetry. apply (eq_K_2 _ _ H5). rewrite H5 in H4. inversion H4.
rewrite H0 in H5. inversion H5.
apply VertexSet.union_3.
rewrite HMR. apply VertexSet.filter_3.
apply compat_bool_move.
unfold N. apply VertexSet.filter_3.
apply eq_K_compat.
generalize (merge_dec_interf x e k g HH HH0 H2 H n). intro.
destruct H3.
intro. elim (not_in_merge_snd e g HH HH0). apply move_related_in_graph.
rewrite (compat_bool_move _ _ _ (Register.eq_sym _ _ H3)). assumption.
apply VertexSet.inter_3. 
apply VertexSet.diff_3. assumption. unfold pre. 
unfold g' in H1. rewrite precolored_merge in H1. intro. elim H1.
apply VertexSet.remove_2. intro.
elim (not_in_merge_snd _ _ HH HH0). rewrite H6. apply move_related_in_graph. assumption.
assumption.
apply VertexSet.diff_3. assumption. unfold pre. 
unfold g' in H1. rewrite precolored_merge in H1. intro. elim H1.
apply VertexSet.remove_2. intro.
elim (not_in_merge_snd _ _ HH HH0). rewrite H6. apply move_related_in_graph. assumption.
assumption.
apply eq_K_1. apply (merge_dec_K x e k g HH HH0); auto.
intro. elim (not_in_merge_snd e g HH HH0).
apply move_related_in_graph. rewrite (compat_bool_move _ _ _ H3) in H0. assumption.
apply (move_related_merge_move_related g e x HH HH0). assumption.

unfold classify, get_spillWL, get_freezeWL, get_simplifyWL, get_movesWL; simpl.
case_eq (is_precolored (fst_ext e) g'); intro; simpl.
assumption.
case_eq (has_low_degree g' k (fst_ext e)); intro; simpl.
case_eq (move_related g' (fst_ext e)); intro; simpl.
apply VertexSet.add_2. assumption.
apply VertexSet.remove_2. auto. assumption.
apply VertexSet.remove_2. auto. assumption.

(* simplifyWL *)
split. intro x.
(* x = fst_ext e *)
destruct (Register.eq_dec x (fst_ext e)).
(* => *)
split; intros.
unfold classify, get_spillWL, get_simplifyWL, get_movesWL, get_freezeWL in H. simpl in H.
case_eq (is_precolored (fst_ext e) g'); intros; rewrite H0 in H.
simpl in H. unfold simplifyWL' in H.
destruct (VertexSet.union_1 H).
unfold simplifyWL_ in H1.
destruct (VertexSet.union_1 H1).
generalize (In_simplify_props _ _ _ _ _ _ _ _ H2 (refl_equal _) HWS). intro.
destruct H3. destruct H4. destruct H5.
elim H6. apply VertexSet.remove_3 with (x:=snd_ext e). 
rewrite <-(precolored_merge e (irc_g ircg) HH HH0). rewrite precolored_equiv.
rewrite (is_precolored_ext _ _ (merge e (irc_g ircg) HH HH0) e0). split. eassumption.
rewrite In_merge_vertex. split. assumption. 
intro. elim (In_graph_edge_diff_ext e g). assumption.
rewrite <-H7. assumption.
rewrite HNMR in H2.
generalize (VertexSet.filter_1 (compat_not_compat (compat_bool_move _)) H2). intro.
unfold N in H3.
generalize (VertexSet.filter_1 (eq_K_compat _ _) H3). intro.
generalize (VertexSet.inter_1 H4). intro.
generalize (VertexSet.inter_2 H4). clear H4. intro.
elim (VertexSet.diff_2 H5). unfold pre.
apply VertexSet.remove_3 with (x:=snd_ext e). 
rewrite <-(precolored_merge e g HH HH0). rewrite precolored_equiv.
split. rewrite (is_precolored_ext _ _ (merge e g HH HH0) e0). eassumption.
rewrite In_merge_vertex. split. 
rewrite e0. apply (proj1 (In_graph_edge_in_ext _ _ HH)).
intro. elim (not_in_interf_self (snd_ext e) g). rewrite H6 in H4.
apply (VertexSet.diff_1 H4).
unfold M in H1.
generalize (VertexSet.filter_1 (compat_move_up _ _) H1). intro.
unfold iadj_padj_interf in H2.
destruct (VertexSet.union_1 H2).
generalize (VertexSet.inter_1 H3). intro. generalize (VertexSet.diff_2 H4). intro.
elim H5. unfold pre. 
apply VertexSet.remove_3 with (x:=snd_ext e). rewrite <-(precolored_merge e g HH HH0).
rewrite precolored_equiv. split.
rewrite (is_precolored_ext _ _ (merge e g HH HH0) e0). eassumption.
rewrite e0. rewrite In_merge_vertex. split.
apply (proj1 (In_graph_edge_in_ext _ _ HH)). 
intro. elim (In_graph_edge_diff_ext e g HH). auto.
generalize (VertexSet.inter_1 H3). intro. generalize (VertexSet.diff_2 H4). intro.
elim H5. unfold pre. 
apply VertexSet.remove_3 with (x:=snd_ext e). rewrite <-(precolored_merge e g HH HH0).
rewrite precolored_equiv. split.
rewrite (is_precolored_ext _ _ (merge e g HH HH0) e0). eassumption.
rewrite e0. rewrite In_merge_vertex. split.
apply (proj1 (In_graph_edge_in_ext _ _ HH)).
intro. elim (In_graph_edge_diff_ext e g HH). auto.

(* fst_ext e is not precolored *)
case_eq (has_low_degree g' k (fst_ext e)); intros; rewrite H1 in H.
case_eq (move_related g' (fst_ext e)); intros; rewrite H2 in H.
simpl in H. unfold simplifyWL' in H.
destruct (VertexSet.union_1 H).
unfold simplifyWL_ in H3.
destruct (VertexSet.union_1 H3).
assert (move_related g x = false).
apply (proj1 (proj2 (In_simplify_props _ _ _ _ _ _ _ _ H4 (refl_equal _) HWS))).
assert (move_related g x = true).
rewrite (compat_bool_move _ _ _ e0).
apply (proj1 (Aff_edge_aff _ _ HH HH0)).
rewrite H5 in H6. inversion H6.
rewrite HNMR in H4.
generalize (VertexSet.filter_1 (compat_not_compat (compat_bool_move _)) H4). intro.
generalize (VertexSet.filter_2 (compat_not_compat (compat_bool_move _)) H4). clear H4. intro H4.
unfold N in H5.
generalize (VertexSet.filter_1 (eq_K_compat _ _) H5). intro.
generalize (VertexSet.filter_2 (eq_K_compat _ _) H5). clear H5. intro.
generalize (eq_K_2 _ _ H5). clear H5. intro.
assert (move_related g x = true).
rewrite (compat_bool_move _ _ _ e0).
apply (proj1 (Aff_edge_aff _ _ HH HH0)).
rewrite H7 in H4. inversion H4.
unfold M in H3.
generalize (VertexSet.filter_1 (compat_move_up _ _) H3). intro.
unfold iadj_padj_interf in H4.
destruct (VertexSet.union_1 H4).
elim (not_in_pref_self (fst_ext e) g). rewrite e0 in H5.
apply (VertexSet.diff_1 (VertexSet.inter_1 H5)).
elim (not_in_interf_self (fst_ext e) g). rewrite e0 in H5.
apply (VertexSet.diff_1 (VertexSet.inter_2 H5)).
simpl in H.
split. rewrite (compat_bool_low _ _ _ _ e0). assumption.
split. rewrite (compat_bool_move _ _ _ e0). assumption.
split. unfold g'. rewrite In_merge_vertex. split. 
rewrite e0. apply (proj1 (In_graph_edge_in_ext e g HH)).
intro. elim (In_graph_edge_diff_ext e g HH). rewrite <-H3. assumption.

rewrite precolored_equiv. intro. destruct H3.
rewrite (is_precolored_ext _ _ g' e0) in H3. rewrite H0 in H3. inversion H3.
simpl in H.
unfold simplifyWL' in H.
destruct (VertexSet.union_1 H).
unfold simplifyWL_ in H2.
destruct (VertexSet.union_1 H2).
generalize (In_simplify_props _ _ _ _ _ _ _ _ H3 (refl_equal _) HWS). intro.
destruct H4. destruct H5. destruct H6.
generalize (proj1 (Aff_edge_aff _ _ HH HH0)). intro.
rewrite (compat_bool_move _ _ _ e0) in H5. fold g in H5. rewrite H5 in H8. inversion H8.
rewrite HNMR in H3.
generalize (VertexSet.filter_2 (compat_not_compat (compat_bool_move _)) H3). intro.
generalize (proj1 (Aff_edge_aff _ _ HH HH0)). intro.
rewrite (compat_bool_move _ _ _ e0) in H4. rewrite H5 in H4. inversion H4.
unfold M in H2.
generalize (VertexSet.filter_1 (compat_move_up _ _) H2). intro.
unfold iadj_padj_interf in H3.
destruct (VertexSet.union_1 H3).
elim (not_in_pref_self (fst_ext e) g). rewrite e0 in H4.
apply (VertexSet.diff_1 (VertexSet.inter_1 H4)).
elim (not_in_interf_self (fst_ext e) g). rewrite e0 in H4.
apply (VertexSet.diff_1 (VertexSet.inter_2 H4)).

(* <= *)
destruct H. destruct H0. destruct H1.
unfold classify, get_spillWL, get_simplifyWL, get_freezeWL, get_movesWL. simpl.
case_eq (is_precolored (fst_ext e) g'); intros; simpl.
rewrite precolored_equiv in H2. elim H2. 
split. rewrite (is_precolored_ext _ _ g' e0). assumption. assumption.
case_eq (has_low_degree g' k (fst_ext e)); intros; simpl.
case_eq (move_related g' (fst_ext e)); intros; simpl.
rewrite (compat_bool_move _ _ _ e0) in H0. rewrite H0 in H5. inversion H5.
apply VertexSet.add_1. intuition.
rewrite (compat_bool_low _ _ _ _ e0) in H. rewrite H in H4. inversion H4.

(* x <> fst_ext e *)
(* simplifyWL => *)
split; intros.
assert (VertexSet.In x simplifyWL').
unfold classify, get_spillWL, get_simplifyWL, get_movesWL, get_freezeWL in H. simpl in H.
case_eq (is_precolored (fst_ext e) g'); intros; rewrite H0 in H.
assumption.
case_eq (has_low_degree g' k (fst_ext e)); intros; rewrite H1 in H.
case_eq (move_related g' (fst_ext e)); intros; rewrite H2 in H.
assumption.
simpl in H. apply VertexSet.add_3 with (x:=fst_ext e). auto. assumption.
assumption.
generalize H0. clear H H0. intro H.
unfold simplifyWL' in H.
destruct (VertexSet.union_1 H).
unfold simplifyWL_ in H0.
destruct (VertexSet.union_1 H0).
generalize (In_simplify_props _ _ _ _ _ _ _ _ H1 (refl_equal _) HWS). intro.
destruct H2. destruct H3. destruct H4.
split.
apply low_dec; auto.
intro. generalize (proj2 (Aff_edge_aff e g HH HH0)). intro.
rewrite (compat_bool_move _ _ _ H6) in H3. fold g in H3.
rewrite H3 in H7. inversion H7.
split.
apply move_merge_false; auto.
split. unfold g'. rewrite In_merge_vertex. split. assumption.
intro. generalize (proj2 (Aff_edge_aff e g HH HH0)). intro.
rewrite (compat_bool_move _ _ _ H6) in H3. fold g in H3.
rewrite H3 in H7. inversion H7.
unfold g'. rewrite precolored_merge. intro. elim H5.
apply (VertexSet.remove_3 H6).
rewrite HNMR in H1.
generalize (VertexSet.filter_1 (compat_not_compat (compat_bool_move _)) H1). intro.
generalize (VertexSet.filter_2 (compat_not_compat (compat_bool_move _)) H1). clear H1. intro.
unfold N in H2.
generalize (VertexSet.filter_1 (eq_K_compat _ _) H2). intro.
generalize (VertexSet.filter_2 (eq_K_compat _ _) H2). clear H2. intro.
generalize (eq_K_2 _ _ H2). clear H2. intro.
split.
apply merge_dec_low. auto.
apply (VertexSet.diff_1 (VertexSet.inter_1 H3)).
apply (VertexSet.diff_1 (VertexSet.inter_2 H3)).
split.
apply move_merge_false; auto. case_eq (move_related g x); intros.
rewrite H4 in H1. inversion H1. reflexivity.
split. unfold g'. rewrite In_merge_vertex. split.
apply (in_interf_in x (fst_ext e) g).
apply (VertexSet.diff_1 (VertexSet.inter_1 H3)).
intro. generalize (proj2 (Aff_edge_aff e g HH HH0)). intro.
rewrite (compat_bool_move _ _ _ (Register.eq_sym _ _ H4)) in H5.
rewrite H5 in H1. inversion H1.
unfold g'. rewrite precolored_merge. intro.
elim (VertexSet.diff_2 (VertexSet.inter_1 H3)). apply (VertexSet.remove_3 H4).
unfold M in H0.
generalize (VertexSet.filter_1 (compat_move_up _ _) H0). intro.
generalize (VertexSet.filter_2 (compat_move_up _ _) H0). clear H0. intro.
assert (VertexSet.cardinal (preference_adj x g) = 1).
case_eq (eq_K 1 (VertexSet.cardinal (preference_adj x g))); intros.
generalize (eq_K_2 _ _ H2). clear H2. intro. auto.
rewrite H2 in H0. inversion H0.
generalize (eq_K_1 _ _ H2). intro. rewrite H3 in H0. simpl in H0.
split.
apply low_dec; auto.
intro.
destruct (VertexSet.union_1 H1).
elim (not_in_interf_self (snd_ext e) g).
rewrite H4 in H5. apply (VertexSet.diff_1 (VertexSet.inter_2 H5)).
elim (not_in_pref_self (snd_ext e) g).
rewrite H4 in H5. apply (VertexSet.diff_1 (VertexSet.inter_1 H5)).
split.
apply move_related_change_charac.
destruct (VertexSet.union_1 H1).
apply VertexSet.union_3.
apply VertexSet.inter_3.
apply (VertexSet.diff_1 (VertexSet.inter_2 H4)).
apply (VertexSet.diff_1 (VertexSet.inter_1 H4)).
apply VertexSet.union_2.
apply VertexSet.inter_3.
apply (VertexSet.diff_1 (VertexSet.inter_2 H4)).
apply (VertexSet.diff_1 (VertexSet.inter_1 H4)).
assumption.
split.
unfold g'. rewrite In_merge_vertex. split.
destruct (VertexSet.union_1 H1).
apply (in_interf_in x (snd_ext e) g). apply (VertexSet.diff_1 (VertexSet.inter_2 H4)).
apply (in_interf_in x (fst_ext e) g). apply (VertexSet.diff_1 (VertexSet.inter_2 H4)).
intro. destruct (VertexSet.union_1 H1).
elim (not_in_interf_self (snd_ext e) g).
rewrite H4 in H5. apply (VertexSet.diff_1 (VertexSet.inter_2 H5)).
elim (not_in_pref_self (snd_ext e) g).
rewrite H4 in H5. apply (VertexSet.diff_1 (VertexSet.inter_1 H5)).
unfold g'. rewrite precolored_merge.
intro.
destruct (VertexSet.union_1 H1).
elim (VertexSet.diff_2 (VertexSet.inter_1 H5)). apply (VertexSet.remove_3 H4).
elim (VertexSet.diff_2 (VertexSet.inter_1 H5)). apply (VertexSet.remove_3 H4).

(* <= *)
destruct H. destruct H0. destruct H1.
assert (VertexSet.In x simplifyWL').
unfold simplifyWL'.
case_eq (move_related g x); intros.
apply VertexSet.union_3.
unfold M.
apply VertexSet.filter_3.
apply compat_move_up.
assert (~Register.eq x (snd_ext e)) as Hsnd.
intro. elim (not_in_merge_snd e g HH HH0). rewrite H4 in H1. assumption. 
generalize (move_merge_not_move _ _ _ _ HH0 n Hsnd H0 H3). intro.
destruct H4.
generalize (VertexSet.inter_1 H4). generalize (VertexSet.inter_2 H4). intros.
apply VertexSet.union_3.
apply VertexSet.inter_3.
apply VertexSet.diff_3. assumption.
unfold g' in H2. rewrite precolored_merge in H2. intro. elim H2.
apply VertexSet.remove_2. intro. elim (not_in_merge_snd _ _ HH HH0).
rewrite H8. assumption.
assumption.
apply VertexSet.diff_3. assumption.
unfold g' in H2. rewrite precolored_merge in H2. intro. elim H2.
apply VertexSet.remove_2. intro. elim (not_in_merge_snd _ _ HH HH0).
rewrite H8. assumption.
assumption.
generalize (VertexSet.inter_1 H4). generalize (VertexSet.inter_2 H4). intros.
apply VertexSet.union_2.
apply VertexSet.inter_3.
apply VertexSet.diff_3. assumption.
unfold g' in H2.
rewrite precolored_merge in H2. intro. elim H2.
apply VertexSet.remove_2. intro. elim (not_in_merge_snd _ _ HH HH0).
rewrite H8. assumption.
assumption.
apply VertexSet.diff_3. assumption.
unfold g' in H2.
rewrite precolored_merge in H2. intro. elim H2.
apply VertexSet.remove_2. intro. elim (not_in_merge_snd _ _ HH HH0).
rewrite H8. assumption.
assumption.

assert (~Register.eq x (snd_ext e)) as Hsnd.
intro. rewrite H4 in H1. elim (not_in_merge_snd e g HH HH0 H1).
generalize (move_related_dec_1 _ _ _ HH HH0 n Hsnd H3 H0). intro.
unfold pref_degree in H4. rewrite (eq_K_1 _ _ H4). simpl.
case_eq (has_low_degree g k x); intros.
reflexivity.
generalize (move_merge_not_move _ _ _ _ HH0 n Hsnd H0 H3). intro.
assert (~Register.eq x (snd_ext e)).
intro. rewrite H7 in H1. elim (not_in_merge_snd e g HH HH0 H1).
generalize (merge_dec_interf _ _ _ _ HH HH0 H5 H n H7). intro.
destruct H8. destruct H6.
generalize (VertexSet.inter_2 H6). intro.
elim (interf_pref_conflict x (snd_ext e) g).
rewrite in_pref in H10.
split.
unfold Prefere. assumption.
unfold Interfere. rewrite <-in_interf. assumption.
elim (interf_pref_conflict x (fst_ext e) g).
generalize (VertexSet.inter_2 H6). intro.
rewrite in_pref in H10.
split.
unfold Prefere. assumption.
unfold Interfere. rewrite <-in_interf. auto.
apply VertexSet.union_2.
unfold simplifyWL_.
case_eq (has_low_degree g k x); intros.
apply VertexSet.union_2.

WS_apply HWS.
split. assumption.
split. assumption.
split. unfold g' in H1. rewrite In_merge_vertex in H1. intuition.
unfold g' in H2. rewrite precolored_merge in H2.
intro. elim H2. apply VertexSet.remove_2.
intro. apply (not_in_merge_snd _ _ HH HH0). rewrite H6. assumption.
assumption.

apply VertexSet.union_3.
rewrite HNMR.
apply VertexSet.filter_3.
apply compat_not_compat. apply compat_bool_move.
unfold N. apply VertexSet.filter_3.
apply eq_K_compat.
assert (~Register.eq x (snd_ext e)).
intro. rewrite H5 in H1. elim (not_in_merge_snd e g HH HH0 H1).
generalize (merge_dec_interf _ _ _ _ HH HH0 H4 H n H5).
intro. destruct H6. apply VertexSet.inter_3.
apply VertexSet.diff_3. assumption.
unfold g' in H2. rewrite precolored_merge in H2.
intro. elim H2. apply VertexSet.remove_2. auto.
assumption.
apply VertexSet.diff_3. assumption.
unfold g' in H2. rewrite precolored_merge in H2.
intro. elim H2. apply VertexSet.remove_2. auto.
assumption.
apply eq_K_1.
apply (merge_dec_K x e k g HH HH0 n).
intro. rewrite H5 in H1. elim (not_in_merge_snd e g HH HH0 H1).
assumption.
assumption.
rewrite H3. auto.

unfold classify, get_spillWL, get_simplifyWL, get_movesWL, get_freezeWL; simpl.
case_eq (is_precolored (fst_ext e) g'); intros.
assumption.
case_eq (has_low_degree g' k (fst_ext e)); intros.
case_eq (move_related g' (fst_ext e)); intros.
assumption.
simpl. apply VertexSet.add_2; auto.
assumption.

(* moves !!!!! *)
split; intros.
assert (EdgeSet.In e0 movesWL').
unfold classify,get_spillWL, get_simplifyWL, get_movesWL, get_freezeWL in H; simpl in H;
destruct (is_precolored (fst_ext e) g');
destruct (has_low_degree g' k (fst_ext e));
destruct (move_related g' (fst_ext e)); simpl; assumption.
unfold movesWL' in H0.
unfold g'. rewrite <-AE_merge_wl. eassumption.
intros. rewrite <-In_graph_aff_edge_in_AE.
rewrite moves_AE. unfold moves. reflexivity. eassumption.

destruct H. simpl.
assert (EdgeSet.In e0 movesWL').
unfold movesWL'. unfold g', padj_fst_, padj_snd_. rewrite AE_merge_wl.
split; assumption.

intros. rewrite <-In_graph_aff_edge_in_AE.
rewrite moves_AE. unfold moves. reflexivity. eassumption.
unfold classify,get_spillWL, get_simplifyWL, get_movesWL, get_freezeWL; simpl;
destruct (is_precolored (fst_ext e) g');
destruct (has_low_degree g' k (fst_ext e));
destruct (move_related g' (fst_ext e)); simpl; assumption.

rewrite <-VertexSet.partition_2. rewrite Hmr. intuition.
apply compat_bool_move.
rewrite <-VertexSet.partition_1. rewrite Hmr. intuition.
apply compat_bool_move.
Qed.

Lemma WS_coalesce : forall e ircg H H0,
WS_properties (merge e (irc_g ircg) H H0) 
                        (irc_k ircg)
                        (merge_wl3 e ircg (merge e (irc_g ircg) H H0) H H0).

Proof.
intros. rewrite <-(Hk ircg). apply ws_merge3.
Qed.
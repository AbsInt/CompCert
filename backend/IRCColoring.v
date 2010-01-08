Require Import Recdef.
Require Import IRC.
Require Import FSetInterface.
Require Import Edges.
Require Import Interference_adjacency.
Require Import IRC_graph.
Require Import Conservative_criteria.
Require Import InterfGraphMapImp.
Require Import Graph_Facts.
Require Import IRC_Graph_Functions.
Require Import WS.

Import Edge RegFacts Props OTFacts.

Module MapFacts := FMapFacts.Facts ColorMap.

Definition proper_coloring_1 (col : Coloring) g := forall e x y,
interf_edge e ->
In_graph_edge e g ->
OptionReg.eq (col (fst_ext e)) (Some x) ->
OptionReg.eq (col (snd_ext e)) (Some y) ->
~Register.eq x y.

Definition proper_coloring_2 (col : Coloring) g := forall x y,
OptionReg.eq (col x) (Some y) -> In_graph x g.

Definition proper_coloring_3 (col : Coloring) palette := forall x y,
OptionReg.eq (col x) (Some y) -> VertexSet.In y palette.

Definition proper_coloring col g palette := 
proper_coloring_1 col g /\ proper_coloring_2 col g /\ proper_coloring_3 col palette.

Lemma diff_empty_sub : forall s1 s2,
VertexSet.Empty (VertexSet.diff s1 s2) ->
VertexSet.Subset s1 s2.

Proof.
intros s1 s2 H.
intros a H0.
destruct (In_dec a s2).
assumption.
elim (H a).
apply (VertexSet.diff_3 H0 n).
Qed.

Lemma interf_in_forbidden : forall x y col g c,
Interfere x y g ->
OptionReg.eq (map_to_coloring col y) (Some c) ->
VertexSet.In c (forbidden_colors x col g).

Proof.
intros x y col g c H H0.
unfold forbidden_colors.
unfold Interfere in H. rewrite <-in_interf in H.
generalize (interf_adj_comm _ _ _ H). intro H1.
generalize (VertexSet.elements_1 H1);clear H1;intro H1.
rewrite VertexSet.fold_1.
induction (VertexSet.elements (interference_adj x g)).
inversion H1.
rewrite monad_fold.
inversion H1;subst.
unfold map_to_coloring in H0.
inversion H0;subst.
rewrite (MapFacts.find_o col H3) in H2.
rewrite <-H2.
simpl;apply VertexSet.add_1.
assumption.
destruct (ColorMap.find a col);[apply VertexSet.add_2|];apply IHl;assumption.
Qed.

Lemma available_coloring_1 : forall col x g,
proper_coloring (map_to_coloring col) (irc_g g) (pal g) ->
In_graph x (irc_g g) ->
proper_coloring (map_to_coloring (available_coloring g x col)) (irc_g g) (pal g).

Proof.
intros col x ircg H HH. unfold available_coloring.
set (palette := pal ircg) in *. set (g := irc_g ircg) in *.
case_eq (VertexSet.choose (VertexSet.diff palette (forbidden_colors x col g))).
intros c H1.
generalize H1;intro H0.
unfold proper_coloring.
split.
unfold proper_coloring_1.
intros e x' y' H2 H3 H4 H5.
destruct (Register.eq_dec x (fst_ext e)).
unfold map_to_coloring in H4;unfold map_to_coloring in H5.
rewrite MapFacts.add_eq_o in H4.
rewrite MapFacts.add_neq_o in H5.
generalize (VertexSet.choose_1 H1);clear H1;intro H1.
generalize (VertexSet.diff_1 H1);intro H6.
generalize (VertexSet.diff_2 H1);intro H7;clear H1.
assert (Interfere x (snd_ext e) g) as Hinterf.
unfold Interfere.
assert (eq (fst_ext e, snd_ext e,None) (x, snd_ext e, None)).
Eq_eq.
rewrite (edge_eq e) in H3.
rewrite H2 in H3.
rewrite H1 in H3;assumption.
generalize (interf_in_forbidden x (snd_ext e) col g y' Hinterf H5);intro H1.
intro H8.
inversion H4;subst.
generalize (Register.eq_trans H11 H8);clear H11 H8;intro H8.
rewrite H8 in H7.
elim (H7 H1).
intro Heq.
elim (In_graph_edge_diff_ext _ _ H3).
apply (Register.eq_trans (Register.eq_sym Heq) e0).
assumption.
destruct (Register.eq_dec x (snd_ext e)).
unfold map_to_coloring in H4;unfold map_to_coloring in H5.
rewrite MapFacts.add_eq_o in H5.
rewrite MapFacts.add_neq_o in H4.
generalize (VertexSet.choose_1 H1);clear H1;intro H1.
generalize (VertexSet.diff_1 H1);intro H6.
generalize (VertexSet.diff_2 H1);intro H7;clear H1.
assert (Interfere x (fst_ext e) g) as Hinterf.
unfold Interfere.
rewrite (edge_eq e) in H3. rewrite H2 in H3.
assert (eq (fst_ext e, snd_ext e,None) (x, fst_ext e, None)) by Eq_comm_eq.
rewrite H1 in H3;assumption.
generalize (interf_in_forbidden x (fst_ext e) col g x' Hinterf H4);intro H1.
intro H8.
inversion H5;subst.
generalize (Register.eq_trans H11 (Register.eq_sym H8));clear H11 H8;intro H8.
rewrite H8 in H7.
elim (H7 H1).
intro Heq.
elim (In_graph_edge_diff_ext _ _ H3).
apply (Register.eq_trans (Register.eq_sym e0) Heq).
assumption.
unfold map_to_coloring in H4;unfold map_to_coloring in H5.
rewrite MapFacts.add_neq_o in H5.
rewrite MapFacts.add_neq_o in H4.
unfold proper_coloring in H;destruct H as [H _].
unfold proper_coloring_1 in H.
apply (H e);assumption.
assumption.
assumption.
split.
unfold proper_coloring in *.
destruct H as [_ H];destruct H as [H _].
unfold proper_coloring_2 in *.
intros x' y' H2.
destruct (Register.eq_dec x x').
unfold map_to_coloring in H2.
rewrite e in HH;assumption.
apply (H x' y').
unfold map_to_coloring in H2.
rewrite MapFacts.add_neq_o in H2.
assumption.
assumption.
unfold proper_coloring in *.
do 2 destruct H as [_ H].
unfold proper_coloring_3 in *.
intros x' y' H2.
destruct (Register.eq_dec x x').
unfold map_to_coloring in H2.
generalize (VertexSet.choose_1 H1);clear H1;intro H1.
generalize (VertexSet.diff_1 H1);intro H3.
rewrite MapFacts.add_eq_o  in H2.
inversion H2;subst.
rewrite H6 in H3;assumption.
assumption.
apply (H x' y').
unfold map_to_coloring in H2.
rewrite MapFacts.add_neq_o in H2.
assumption.
assumption.
auto.
Qed.

Lemma complete_coloring_1 : forall col e g,
In_graph_edge e g ->
ColorMap.find (snd_ext e) col = None ->
OptionReg.eq 
(map_to_coloring (complete_coloring e col) (snd_ext e))
(map_to_coloring (complete_coloring e col) (fst_ext e)).

Proof.
intros col e g HH Hin;unfold complete_coloring.
case_eq (ColorMap.find (fst_ext e) col).
intros r H.
unfold map_to_coloring.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite H;apply OptionReg.eq_refl.
apply (In_graph_edge_diff_ext _ _ HH).
apply Register.eq_refl.
intro H0.
unfold map_to_coloring.
rewrite Hin;rewrite H0;apply OptionReg.eq_refl.
Qed.

Lemma complete_coloring_2 : forall col e x,
~Register.eq (snd_ext e) x ->
OptionReg.eq 
(map_to_coloring (complete_coloring e col) x)
(map_to_coloring col x).

Proof.
intros col e x H.
unfold complete_coloring.
destruct (ColorMap.find (fst_ext e) col).
unfold map_to_coloring.
rewrite MapFacts.add_neq_o.
apply OptionReg.eq_refl.
assumption.
apply OptionReg.eq_refl.
Qed.

Definition compat_col col := forall x y,
Register.eq x y -> OptionReg.eq (col x) (col y).

Lemma compat_IRC : forall g palette, compat_col (IRC g palette).

Proof.
unfold IRC.
unfold compat_col.
intros g palette x y H.
unfold map_to_coloring.
rewrite MapFacts.find_o with (y := y).
apply OptionReg.eq_refl.
assumption.
Qed.

Lemma compat_complete : forall col e,
compat_col (map_to_coloring col) ->
compat_col (map_to_coloring (complete_coloring e col)).

Proof.
unfold compat_col;intros col e H.
intros x y Heq;generalize (H x y Heq);clear H;intro H.
unfold complete_coloring.
destruct (ColorMap.find (fst_ext e) col).
unfold map_to_coloring.
destruct (Register.eq_dec x (snd_ext e)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
apply OptionReg.eq_refl.
apply (Register.eq_trans (Register.eq_sym e0) Heq). intuition.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
assumption.
intro Helim;elim n.
apply (Register.eq_trans Heq (Register.eq_sym Helim)).
intro H0;elim n;auto.
assumption.
Qed.

Lemma colored_complete_diff_colored : forall e col,
~Register.eq (snd_ext e) (fst_ext e) ->
OptionReg.eq (map_to_coloring (complete_coloring e col) (fst_ext e)) (map_to_coloring col (fst_ext e)).

Proof.
intros e col H.
unfold complete_coloring.
case_eq (ColorMap.find (fst_ext e) col).
intros r H0.
unfold map_to_coloring.
rewrite MapFacts.add_neq_o.
apply OptionReg.eq_refl.
assumption.
intro H0.
apply OptionReg.eq_refl.
Qed.

Lemma complete_coloring_coloring : forall col e g Hin Haff,
~VertexSet.In (snd_ext e) (precolored (irc_g g)) ->
proper_coloring (map_to_coloring col) (merge e (irc_g g) Hin Haff) (pal g) ->
conservative_coalescing_criteria e (irc_g g) (irc_k g) = true ->
compat_col (map_to_coloring col) ->
proper_coloring (map_to_coloring (complete_coloring e col)) (irc_g g) (pal g).

Proof.
unfold proper_coloring;unfold proper_coloring_1;
unfold proper_coloring_2;unfold proper_coloring_3.
intros col e ircg H1 Haff Hpre H H0 Hcompat.
set (g := irc_g ircg) in *. set (palette := pal ircg) in *.
rewrite <-(Hk ircg) in *.
destruct H as [H HH];destruct HH as [HH HHH].
split.
intros e' x' y' H2 H3 H4 H5.
apply (H (redirect (snd_ext e) (fst_ext e) e')).
unfold interf_edge;rewrite redirect_weight_eq;assumption.
apply In_merge_interf_edge.
assumption.
assumption.
(*intro Heq.
generalize (get_weight_m _ _ Heq);intro H6.
rewrite H2 in H6.
unfold aff_edge in Haff.
destruct Haff as [w Haff].
rewrite Haff in H6.
inversion H6.
assumption.*)
destruct e' as [e' we'];destruct e' as [e'1 e'2].
unfold redirect.
unfold interf_edge in H2;simpl in H2;subst.
change_rewrite.
destruct (OTFacts.eq_dec e'1 (snd_ext e));change_rewrite.
generalize (compat_complete col e);intro Hcompat2.
generalize (Hcompat2 Hcompat _ _ r);intro H7.
generalize (OptionReg.eq_trans _ _ _ (OptionReg.eq_sym _ _ H4) H7);
clear H7;intro H7.
assert (ColorMap.find (snd_ext e) col = None) as Hn.
case_eq (ColorMap.find (snd_ext e) col).
clear H3 H4 H5 r Hcompat2 H7.
intros r H8.
generalize (HH (snd_ext e) r);intro Helim.
unfold map_to_coloring in Helim.
rewrite H8 in Helim.
generalize (Helim (OptionReg.eq_refl _));clear Helim;intro Helim.
rewrite In_merge_vertex in Helim.  destruct Helim. elim H3. auto.
auto.
generalize (complete_coloring_1 col e g H1 Hn);intro H8.
generalize (OptionReg.eq_trans _ _ _ H7 H8);intro H9.
generalize (complete_coloring_2 col e (fst_ext e) (In_graph_edge_diff_ext _ _ H1)).
intro H10.
generalize (OptionReg.eq_trans _ _ _ H9 H10);intro H11.
apply OptionReg.eq_sym;assumption.
destruct (OTFacts.eq_dec e'2 (snd_ext e));change_rewrite;
apply OptionReg.eq_trans with (y := (map_to_coloring (complete_coloring e col) e'1));
[apply OptionReg.eq_sym;apply complete_coloring_2;intuition|assumption|
apply OptionReg.eq_sym;apply complete_coloring_2;intuition|assumption].
destruct e' as [e' we'];destruct e' as [e'1 e'2].
unfold redirect;change_rewrite.
unfold interf_edge in H2;simpl in H2;subst.
destruct (OTFacts.eq_dec e'1 (snd_ext e));change_rewrite.
destruct (Register.eq_dec (snd_ext e) e'2).
elim (In_graph_edge_diff_ext _ _ H3).
apply (Register.eq_trans (Register.eq_sym e0) (Register.eq_sym r)).
generalize (complete_coloring_2 col e e'2 n);intro H6.
apply OptionReg.eq_trans with (y := map_to_coloring (complete_coloring e col) e'2).
apply OptionReg.eq_sym;assumption.
assumption.
destruct (OTFacts.eq_dec e'2 (snd_ext e));change_rewrite.
generalize (compat_complete col e);intro Hcompat2.
generalize (Hcompat2 Hcompat _ _ r);intro H7.
generalize (OptionReg.eq_trans _ _ _ (OptionReg.eq_sym _ _ H5) H7);
clear H7;intro H7.
assert (ColorMap.find (snd_ext e) col = None) as Hn.
case_eq (ColorMap.find (snd_ext e) col).
clear H3 H4 H5 r Hcompat2 H7.
intros r H8.
generalize (HH (snd_ext e) r);intro Helim.
unfold map_to_coloring in Helim.
rewrite H8 in Helim.
generalize (Helim (OptionReg.eq_refl _));clear Helim;intro Helim.
rewrite In_merge_vertex in Helim. destruct Helim. elim H3. auto.
auto.
generalize (complete_coloring_1 col e g H1 Hn);intro H8.
generalize (OptionReg.eq_trans _ _ _ H7 H8);intro H9.
generalize (complete_coloring_2 col e (fst_ext e) (In_graph_edge_diff_ext _ _ H1)).
intro H10.
generalize (OptionReg.eq_trans _ _ _ H9 H10);intro H11.
apply OptionReg.eq_sym;assumption.
change (snd_ext (e'1,e'2,None)) with e'2.
assert (~Register.eq (snd_ext e) e'2) by intuition.
generalize (complete_coloring_2 col e e'2 H2);intro H6.
apply OptionReg.eq_trans with (y := map_to_coloring (complete_coloring e col) e'2).
apply OptionReg.eq_sym;assumption.
assumption.
(* second step *)
split.
intros x y H2.
destruct (Register.eq_dec x (snd_ext e)).
rewrite e0.
apply (In_graph_edge_in_ext _ _ H1).
assert (In_graph x (merge e g H1 Haff)).
apply HH with (y := y).
apply OptionReg.eq_trans with (y := map_to_coloring (complete_coloring e col) x).
apply OptionReg.eq_sym.
apply complete_coloring_2.
intuition.
assumption.
rewrite In_merge_vertex in H3. intuition.
(* third step *)
intros x y H2.
destruct (Register.eq_dec x (snd_ext e)).
assert (ColorMap.find (snd_ext e) col = None) as Hn.
case_eq (ColorMap.find (snd_ext e) col).
intros r H8.
generalize (HH (snd_ext e) r);intro Helim.
unfold map_to_coloring in Helim.
rewrite H8 in Helim.
generalize (Helim (OptionReg.eq_refl _));clear Helim;intro Helim.
rewrite In_merge_vertex in Helim. destruct Helim. elim H4. auto.
auto.
generalize (complete_coloring_1 col e g H1 Hn);intro H3.
generalize (complete_coloring_2 col e (fst_ext e) (In_graph_edge_diff_ext _ _ H1)).
intro H4.
generalize (OptionReg.eq_trans _ _ _ (OptionReg.eq_sym _ _ H4) (OptionReg.eq_sym _ _ H3)).
clear H3 H4;intro H3.
generalize (compat_complete col e Hcompat);intro Hcompat2.
generalize (Hcompat2 _ _ e0).
intro H4.
generalize (OptionReg.eq_trans _ _ _ H3 (OptionReg.eq_sym _ _ H4)).
clear H3 H4;intro H3.
apply HHH with (x:= fst_ext e).
apply (OptionReg.eq_trans _ _ _ H3 H2).
assert (~Register.eq (snd_ext e) x) by intuition.
generalize (complete_coloring_2 col e x H3).
intro H4.
apply HHH with (x:= x).
apply (OptionReg.eq_trans _ _ _ (OptionReg.eq_sym _ _ H4) H2).
Qed.

Lemma interf_edge_in_delete_preference : forall x e g H,
interf_edge e ->
In_graph_edge e g ->
In_graph_edge e (delete_preference_edges x g H).

Proof.
intros x e g HH H H0.
generalize (proj2 (In_graph_interf_edge_in_IE _ _) (conj H H0));intro H1.
rewrite In_delete_preference_edges_edge.
split. assumption.
intro. destruct H2. destruct H2. congruence.
Qed.

Lemma coloring_delete_preference : forall col x g H palette,
proper_coloring col (delete_preference_edges x g H) palette ->
proper_coloring col g palette.

Proof.
unfold proper_coloring;unfold proper_coloring_1;
unfold proper_coloring_2;unfold proper_coloring_3.
intros col x g Hdp palette H.
destruct H as [H HH];destruct HH as [HH HHH].
split.
intros e x' y' H0 H1 H2 H3.
apply H with (e:=e).
assumption.
apply interf_edge_in_delete_preference;assumption.
assumption.
assumption.
split.
intros x' y' H0. rewrite <-(In_delete_preference_edges_vertex x' x g Hdp).
apply (HH x' y');auto.
assumption. 
Qed.

Lemma proper_remove_proper : forall col g x palette,
proper_coloring col (remove_vertex x g) palette ->
compat_col col ->
proper_coloring col g palette.

Proof.
intros col g x palette H Hcompat.
unfold proper_coloring in *;unfold proper_coloring_1 in *;
unfold proper_coloring_2 in *;unfold proper_coloring_3 in *.
destruct H as [H HH];destruct HH as [HH HHH].
split.
intros e x' y' H0 H1 H2 H3.
destruct (incident_dec e x).
destruct H4.
generalize (Hcompat _ _ H4);intro H5.
generalize (OptionReg.eq_trans _ _ _ H5 H2);clear H5;intro H5.
generalize (HH _ _ H5). intro.
rewrite In_remove_vertex in H6. destruct H6. elim H7. auto.
generalize (Hcompat _ _ H4);intro H5.
generalize (OptionReg.eq_trans _ _ _ H5 H3);clear H5;intro H5.
generalize (HH _ _ H5). intro.
rewrite In_remove_vertex in H6. destruct H6. elim H7. auto.
apply H with (e:=e); auto.
rewrite In_remove_edge; auto.
split.
intros x' y' H0.
generalize (HH x' y' H0);intro H1.
rewrite In_remove_vertex in H1. intuition.
assumption.
Qed.

Section Fold_Facts.

Variable A : Type.

Lemma fold_left_compat_map : forall (f : ColorMap.t Register.t -> A -> ColorMap.t Register.t) l e e',
ColorMap.Equal e e' ->
(forall e1 e2 a, ColorMap.Equal e1 e2 -> ColorMap.Equal (f e1 a) (f e2 a)) ->
ColorMap.Equal (fold_left f l e) (fold_left f l e').

Proof.
intros f l.
induction l;simpl.
auto.
intros e e' H H0 H1.
apply (IHl (f e a) (f e' a)).
apply H0;assumption.
assumption.
Qed.

End Fold_Facts.

Lemma empty_coloring_simpl : forall l a,
NoDupA Register.eq (a :: l) ->
ColorMap.Equal (fold_left (fun (a0 : ColorMap.t VertexSet.elt) (e : VertexSet.elt) =>
                         ColorMap.add e e a0) (a :: l) (ColorMap.empty Register.t))
                         (ColorMap.add a a (
                         fold_left (fun (a0 : ColorMap.t VertexSet.elt) (e : VertexSet.elt) =>
                         ColorMap.add e e a0) l (ColorMap.empty Register.t))).

Proof.
intro l;generalize (ColorMap.empty Register.t).
induction l;simpl;intros.
unfold ColorMap.Equal;auto.
assert (ColorMap.Equal (ColorMap.add a a (ColorMap.add a0 a0 t0))
                                     (ColorMap.add a0 a0 (ColorMap.add a a t0))).
unfold ColorMap.Equal.
intro y.
destruct (Register.eq_dec a0 a).
inversion H;subst.
elim H2.
left;auto.
destruct (Register.eq_dec y a).
destruct (Register.eq_dec y a0).
elim (n (Register.eq_trans (Register.eq_sym e0) e)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
reflexivity.
intuition.
intro Hneq;elim n0;auto.
intuition.
rewrite MapFacts.add_neq_o.
destruct (Register.eq_dec a0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
reflexivity.
assumption.
assumption.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
reflexivity.
intro Hneq;elim n0;auto.
assumption.
assumption.
intro Hneq;elim n0;auto.
rewrite (fold_left_compat_map _
   (fun (a1 : ColorMap.t VertexSet.elt) (e : VertexSet.elt) => ColorMap.add e e a1) l _ _ H0).
simpl in IHl;apply IHl.
constructor.
inversion H;subst.
intro H5;elim H3.
right;auto.
inversion H;subst.
inversion H4;subst;assumption.
intros e1 e2 a1 H1.
unfold ColorMap.Equal;intro y.
destruct (Register.eq_dec a1 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
reflexivity.
assumption.
assumption.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply H1.
assumption.
assumption.
Qed.

Lemma map_to_coloring_ext : forall c1 c2 g palette,
ColorMap.Equal c2 c1 ->
proper_coloring (map_to_coloring c1) g palette ->
proper_coloring (map_to_coloring c2) g palette.

Proof.
unfold proper_coloring;unfold proper_coloring_1;
unfold proper_coloring_2;unfold proper_coloring_3.
intros c1 c2 g palette H H0.
destruct H0 as [H0 H1];destruct H1 as [H1 H2].
split.
intros e x y H3 H4 H5 H6.
apply (H0 e);try assumption.
unfold ColorMap.Equal in H.
apply OptionReg.eq_trans with (y := (map_to_coloring c2 (fst_ext e))).
unfold map_to_coloring.
rewrite H.
apply OptionReg.eq_refl.
assumption.
apply OptionReg.eq_trans with (y := (map_to_coloring c2 (snd_ext e))).
unfold map_to_coloring.
rewrite H.
apply OptionReg.eq_refl.
assumption.
split.
intros x y H3.
apply (H1 x y).
apply OptionReg.eq_trans with (y := (map_to_coloring c2 x)).
unfold map_to_coloring.
rewrite H.
apply OptionReg.eq_refl.
assumption.
intros x y H3.
apply (H2 x y).
apply OptionReg.eq_trans with (y := (map_to_coloring c2 x)).
unfold map_to_coloring.
rewrite H.
apply OptionReg.eq_refl.
assumption.
Qed.

Lemma compat_map_to_coloring : forall c1 c2 x,
ColorMap.Equal c1 c2 ->
OptionReg.eq (map_to_coloring c1 x) (map_to_coloring c2 x).

Proof.
intros c1 c2 x H;unfold map_to_coloring;
unfold ColorMap.Equal in H.
rewrite H;apply OptionReg.eq_refl.
Qed.

Lemma proper_coloring_empty_aux : forall g x,
OptionReg.eq (precoloring g x) (Some x) \/
OptionReg.eq (precoloring g x) None.

Proof.
intros g x.
unfold precoloring, precoloring_map.
rewrite VertexSet.fold_1.

assert (NoDupA Register.eq (VertexSet.elements (precolored g))) as HNoDup by
       (apply RegFacts.NoDupA_elements).
induction (VertexSet.elements (precolored g)).
simpl.
right;unfold map_to_coloring;rewrite MapFacts.empty_o.
apply OptionReg.eq_refl.
(* induction case *)
generalize (empty_coloring_simpl l a HNoDup);intro H0.
inversion HNoDup;subst.
generalize (IHl H3);clear IHl H2 H3;intro IHl.
destruct IHl.
left.
generalize (compat_map_to_coloring _ _ x H0);clear H0;intro H0.
apply (OptionReg.eq_trans _ _ _ H0).
destruct (Register.eq_dec a x).
unfold map_to_coloring.
rewrite MapFacts.add_eq_o.
constructor;assumption.
assumption.
unfold map_to_coloring.
rewrite MapFacts.add_neq_o.
apply H.
assumption.
destruct (Register.eq_dec a x).
left.
generalize (compat_map_to_coloring _ _ x H0);clear H0;intro H0.
apply (OptionReg.eq_trans _ _ _ H0).
unfold map_to_coloring.
rewrite MapFacts.add_eq_o.
constructor;assumption.
assumption.
right.
generalize (compat_map_to_coloring _ _ x H0);clear H0;intro H0.
apply (OptionReg.eq_trans _ _ _ H0).
unfold map_to_coloring.
rewrite MapFacts.add_neq_o.
apply H.
assumption.
Qed.

Lemma in_empty_coloring_in_precolored : forall x g y,
OptionReg.eq (precoloring g x)(Some y) ->
VertexSet.In x (precolored g).

Proof.
intros x g y H. unfold precoloring, precoloring_map in H.
rewrite VertexSet.fold_1 in H.
generalize (VertexSet.elements_2);intro H0.
generalize (H0 (precolored g));clear H0;intro H0.
assert (NoDupA Register.eq (VertexSet.elements (precolored g))) as HNoDup by
       (apply RegFacts.NoDupA_elements).
induction (VertexSet.elements (precolored g)).
simpl in H.
unfold map_to_coloring in H;rewrite MapFacts.empty_o in H.
inversion H.
destruct (Register.eq_dec a x).
apply H0.
left; intuition.
apply IHl.
generalize (empty_coloring_simpl l a HNoDup);intro H1.
generalize (compat_map_to_coloring _ _ x H1);clear H1;intro H1.
unfold map_to_coloring in H1.
rewrite MapFacts.add_neq_o in H1.
apply (OptionReg.eq_trans _ _ _ (OptionReg.eq_sym _ _ H1)).
clear H1 IHl.
assumption.
assumption.
intros;apply H0;right;auto.
inversion HNoDup;auto.
Qed.

Lemma proper_coloring_pre_inv : forall g  x,
VertexSet.In x (precolored g) ->
OptionReg.eq (precoloring g x) (Some x).

Proof.
intros g x H. unfold precoloring, precoloring_map.
rewrite VertexSet.fold_1.
generalize (VertexSet.elements_1);intro H0.
generalize (H0 (precolored g) x);clear H0;intro H0.
assert (NoDupA Register.eq (VertexSet.elements (precolored g))) as HNoDup by
       (apply RegFacts.NoDupA_elements).
induction (VertexSet.elements (precolored g)).
generalize (H0 H). intro. inversion H1.
generalize (empty_coloring_simpl l a HNoDup);intro H1. simpl in *.
generalize (compat_map_to_coloring _ _ x H1). intro.
unfold map_to_coloring in H2.
destruct (Register.eq_dec x a).
 rewrite MapFacts.add_eq_o in H2.
apply (OptionReg.eq_trans _ _ _ H2).
constructor. apply Register.eq_sym. auto.
apply Register.eq_sym. auto.
rewrite (MapFacts.add_neq_o) in H2. apply (OptionReg.eq_trans _ _ _ H2).
apply IHl. clear H1 H2.
intros. generalize (H0  H1). intro.
inversion H2; subst. elim n. auto.
auto.
inversion HNoDup;auto.
auto.
Qed.

Lemma proper_coloring_empty : forall g palette,
VertexSet.Subset (precolored g) palette ->
proper_coloring (precoloring g) g palette.

Proof.
intros g palette H.
unfold proper_coloring;unfold proper_coloring_1;
unfold proper_coloring_2;unfold proper_coloring_3.
split;[|split].
intros e x y H0 H1 H2 H3 H4.
destruct (proper_coloring_empty_aux g (fst_ext e));
generalize (OptionReg.eq_trans _ _ _ (OptionReg.eq_sym _ _ H2) H5);
clear H2 H5;intro H2.
destruct (proper_coloring_empty_aux g (snd_ext e));
generalize (OptionReg.eq_trans _ _ _ (OptionReg.eq_sym _ _ H3) H5);
clear H3 H5;intro H3.
elim (In_graph_edge_diff_ext _ _ H1).
inversion H2;inversion H3;subst.
apply (Register.eq_trans (Register.eq_sym H10) (Register.eq_trans (Register.eq_sym H4) H7)).
inversion H3.
inversion H2.
intros x y H0.
assert (VertexSet.In x (precolored g)).
apply in_empty_coloring_in_precolored with (y := y). assumption.
rewrite precolored_equiv in H1. intuition.
intros x y H0.
apply H.
destruct (proper_coloring_empty_aux g x);
generalize (OptionReg.eq_trans _ _ _ (OptionReg.eq_sym _ _ H1) H0);
intro H2;inversion H2;subst.
rewrite <-H5.
apply in_empty_coloring_in_precolored with (y := x).
assumption.
Qed.

Lemma proper_coloring_IRC_map : forall gp, 
VertexSet.Subset (precolored (irc_g gp)) (pal gp) ->
proper_coloring (map_to_coloring (IRC_map gp)) (irc_g gp) (pal gp).

Proof.
intros gp Hpre.
functional induction IRC_map gp;simpl in *.

(* simplify *)
generalize (simplify_inv _ _ e). intro.
generalize (simplify_inv2 _ _ e). intro. destruct H0. simpl in H0.
apply available_coloring_1.
apply proper_remove_proper with (x:=r).
rewrite H0 in *. unfold simplify_irc in *. simpl in *.
apply IHt0. rewrite precolored_remove_vertex.
unfold VertexSet.Subset. intros. apply Hpre. apply (VertexSet.remove_3 H1).

unfold compat_col.
intros. unfold map_to_coloring.
rewrite (MapFacts.find_o _ H1). apply OptionReg.eq_refl.

apply (In_simplify_props _ _ _ _ _ _ _ _ (VertexSet.choose_1 H) (refl_equal _) (HWS_irc g)).

(*coalesce*)
generalize (coalesce_inv _ _ e0). intro.
generalize (coalesce_inv_2 _ _ e0). intro.
destruct H0. destruct H0. simpl in *.

assert (forall e', EdgeSet.In e' (get_movesWL (irc_wl g)) -> In_graph_edge e' (irc_g g)).
intros. generalize (In_move_props _ _ _ _ _ _ _ _ H1 (refl_equal _) (HWS_irc g)). intuition.

apply (complete_coloring_coloring _ _ _ x x0).
apply (any_coalescible_edge_2 e1 _ _ (get_movesWL (irc_wl g)) H1 H).
rewrite H0 in *. unfold merge_irc in *. simpl in *. apply IHt0.
rewrite precolored_merge.
unfold VertexSet.Subset. intros. apply Hpre. apply (VertexSet.remove_3 H2).
apply (proj1 (any_coalescible_edge_1 _ _ _ _ H1 H)).

unfold compat_col.
intros. unfold map_to_coloring.
rewrite (MapFacts.find_o _ H2). apply OptionReg.eq_refl.

(* freeze *)
generalize (freeze_inv _ _ e1). intro.
generalize (freeze_inv2 _ _ e1). intro. destruct H0. destruct H0. simpl in *.
apply (coloring_delete_preference _ r (irc_g g) x0 _).
rewrite H0 in *. unfold delete_preference_edges_irc2 in *. simpl in *. apply IHt0.
unfold VertexSet.Subset. intros. apply Hpre.
rewrite precolored_delete_preference_edges in H1. assumption.

(* spill *)
generalize (spill_inv _ _ e2). intro.
generalize (spill_inv2 _ _ e2). intro. destruct H0. simpl in *.
apply available_coloring_1.
apply proper_remove_proper with (x:=r).
rewrite H0 in *. unfold spill_irc in *. simpl in *. apply IHt0.
unfold VertexSet.Subset. intros. apply Hpre.
rewrite precolored_remove_vertex in H1. apply (VertexSet.remove_3 H1).

unfold compat_col.
intros. unfold map_to_coloring.
rewrite (MapFacts.find_o _ H1). apply OptionReg.eq_refl.

apply (In_spill_props _ _ _ _ _ _ _ _ (lowest_cost_in _ _ _ H) (refl_equal _) (HWS_irc g)).

(* terminal case *)
apply proper_coloring_empty. assumption.
Qed.

Lemma proper_coloring_IRC_aux : forall g palette,
VertexSet.Subset (precolored g) palette ->
proper_coloring (IRC g palette) g palette.

Proof.
intros. apply proper_coloring_IRC_map. auto.
Qed.

Lemma proper_coloring_IRC : forall g palette,
proper_coloring (precoloring g) g palette ->
proper_coloring (IRC g palette) g palette.

Proof.
intros. apply proper_coloring_IRC_map.
intro. intro. unfold proper_coloring, proper_coloring_3 in H.
do 2 destruct H as [_ H]. unfold graph_to_IRC_graph in *. simpl in *.
apply H with (x:= a). apply proper_coloring_pre_inv. assumption.
Qed.
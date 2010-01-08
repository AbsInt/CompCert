Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Delete_Preference_Edges_Degree.
Require Import Edges.
Require Import MyRegisters.

Module Register := Regs.

Import Edge RegFacts Props.

Lemma compat_bool_move : forall g, 
compat_bool Register.eq (move_related g).

Proof.
unfold move_related, compat_bool. intros.
rewrite (compat_preference_adj _ _ _ H). reflexivity.
Qed.

(* Characterization of the move-relationship *)

(* If a vertex x is move-related in g then there exists an affinity edge e
    of g which is incident to x *)
Lemma move_related_charac : forall x g,
move_related g x = true ->
exists e, aff_edge e /\ In_graph_edge e g /\ incident e x.

Proof.
intros. unfold move_related in H.
destruct (set_induction2 (preference_adj x g)).
rewrite Dec.F.is_empty_iff in H0. rewrite H0 in H. inversion H.
destruct H0. destruct H0.
rewrite Add_Equal in H0.
assert (VertexSet.In x0 (preference_adj x g)).
rewrite H0. apply VertexSet.add_1. intuition.
rewrite in_pref in H1. destruct H1.
exists (x0, x, Some x2). 
split. unfold aff_edge. exists x2. auto.
split. assumption.
right. auto.
Qed.

(* The inversion characterization of move related *)
Lemma move_related_charac2 : forall x g e,
aff_edge e ->
In_graph_edge e g ->
incident e x ->
move_related g x = true.

Proof.
intros. unfold move_related.
case_eq (VertexSet.is_empty (preference_adj x g)); auto.
intros. rewrite <-Dec.F.is_empty_iff in H2.
generalize (empty_is_empty_1 H2). clear H2. intro.
destruct H. destruct H1.
assert (VertexSet.In (snd_ext e) (preference_adj x g)).
rewrite in_pref. exists x0. rewrite edge_comm. rewrite <-H.
assert (eq (x, snd_ext e, get_weight e) (fst_ext e, snd_ext e, get_weight e)) by Eq_eq.
rewrite H3. rewrite <-(edge_eq e). assumption.
rewrite H2 in H3. elim (VertexSet.empty_1 H3).
assert (VertexSet.In (fst_ext e) (preference_adj x g)).
rewrite in_pref. exists x0. rewrite <-H.
assert (eq (fst_ext e, x, get_weight e) (fst_ext e, snd_ext e, get_weight e)) by Eq_eq.
rewrite H3. rewrite <-(edge_eq e). assumption.
rewrite H2 in H3. elim (VertexSet.empty_1 H3).
Qed.

(* Characterization of nonmove relation *)
Lemma move_related_false_charac : forall e x g,
aff_edge e ->
In_graph_edge e g ->
move_related g x = false ->
~incident e x.

Proof.
intros e x g H H0 H1 H2.
generalize (move_related_charac2 _ _ _ H H0 H2).
intro H3;rewrite H1 in H3;inversion H3.
Qed.

Lemma move_related_false_charac2 : forall x g,
(forall e, aff_edge e -> In_graph_edge e g -> ~incident e x) ->
move_related g x = false.

Proof.
intros x g H.
case_eq (move_related g x);intro H0.
generalize (move_related_charac _ _ H0);intro H1.
destruct H1 as [e H1];destruct H1 as [H1 H2];destruct H2 as [H2 H3].
elim ((H e H1 H2) H3).
reflexivity.
Qed.

(* A move-related vertex of the graph belongs to the graph *)
Lemma move_related_in_graph : forall x g,
move_related g x = true -> In_graph x g.

Proof.
intros x g H.
generalize (move_related_charac x g H);intro H0.
destruct H0 as [e H0];destruct H0 as [H0 H1];destruct H1 as [H1 H2].
destruct H2;rewrite H2.
apply (proj1 (In_graph_edge_in_ext _ _ H1)).
apply (proj2 (In_graph_edge_in_ext _ _ H1)).
Qed.

(* The endpoints of any affinity edge of g are move-related in g *)
Lemma Aff_edge_aff : forall e g,
In_graph_edge e g ->
aff_edge e ->
move_related g (fst_ext e) = true /\ move_related g (snd_ext e) = true.

Proof.
intros. split.
apply move_related_charac2 with (e:=e); [idtac|idtac|left]; auto.
apply move_related_charac2 with (e:=e); [idtac|idtac|right]; auto.
Qed.

(* Any move-related vertex has a nonempty preference neighborhood *)
Lemma move_related_not_empty_pref : forall x g,
move_related g x = true ->
~VertexSet.Equal (preference_adj x g) VertexSet.empty.

Proof.
unfold move_related. intros. intro.
generalize (empty_is_empty_2 H0). intro.
rewrite Dec.F.is_empty_iff in H1. rewrite H1 in H. inversion H.
Qed.

(* Any nonmove-related vertex has an empty preference neighborhood *)
Lemma not_move_related_empty_pref : forall x g,
move_related g x = false ->
VertexSet.Equal (preference_adj x g) VertexSet.empty.

Proof.
unfold move_related. intros.
apply empty_is_empty_1. rewrite Dec.F.is_empty_iff.
case_eq (VertexSet.is_empty (preference_adj x g)); intros; auto.
rewrite H0 in H. inversion H.
Qed.

(* Any vertex having a preference degree different than 0 is move-related *)
Lemma move_related_card : forall x g,
pref_degree g x  <> 0 ->
move_related g x = true.

Proof.
unfold pref_degree. intros.
case_eq (move_related g x); intros.
reflexivity.
generalize (not_move_related_empty_pref _ _ H0). intro.
rewrite H1 in H. rewrite empty_cardinal in H. elim H. auto.
Qed.

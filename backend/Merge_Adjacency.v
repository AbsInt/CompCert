Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Remove_Vertex_Degree.
Require Import Edges.
Require Import MyRegisters.
Require Import Interference_adjacency.
Require Import Graph_Facts.

Module Register := Regs.

Import Edge RegFacts Props.

(* The following lemmas define the interference adjacency
   of the first endpoint of e after the merge of e *)

Lemma merge_interf_adj_fst_1 : forall e g H0 Haff,
VertexSet.Subset (interference_adj (fst_ext e) (merge e g H0 Haff))
                 (VertexSet.union (interference_adj (fst_ext e) g)
                                  (interference_adj (snd_ext e) g)).

Proof.
unfold VertexSet.Subset. intros e g H Haff a H1.
rewrite in_interf in H1. generalize (In_merge_edge_inv _ _ _ H Haff H1); intro.
destruct H0 as [x H0]. destruct H0 as [H3 H4].
destruct x as [ex wx]. destruct ex as [x1 x2].
assert (interf_edge (x1,x2,wx)) as Hinterf.
destruct H4. unfold same_type in H2. destruct H2; destruct H2.
unfold aff_edge in H4. destruct H4. simpl in H4. congruence.
assumption.
destruct H4 as [H4 HH4].
assert (eq (a, fst_ext e, None) (redirect (snd_ext e) (fst_ext e) (x1,x2,wx))).
apply weak_eq_interf_eq. assumption. unfold interf_edge. auto.
unfold interf_edge. rewrite redirect_weight_eq. auto. clear H4.
generalize (redirect_charac (x1,x2,wx) (snd_ext e) (fst_ext e)); intros.
destruct H2. destruct H2. destruct H4. rewrite <-H2 in H0.
apply VertexSet.union_2. rewrite in_interf. rewrite H0. assumption.
destruct H2. destruct H2. rewrite <-H2 in H0. change_rewrite.
apply VertexSet.union_3. rewrite in_interf.
destruct (eq_charac _ _ H0); destruct H5; change_rewrite.
assert (eq (a, snd_ext e, None) (x1, x2, wx)).
Eq_comm_eq. apply (Register.eq_trans _ _ _ H5 H6).
generalize (get_weight_m _ _ H0). simpl. intro. rewrite H7. apply OptionN_as_OT.eq_refl.
rewrite H7. assumption.
assert (eq (a,snd_ext e, None) (x1,x2,wx)).
Eq_comm_eq.
generalize (get_weight_m _ _ H0). simpl. intro. rewrite H7. apply OptionN_as_OT.eq_refl.
rewrite H7. assumption.
destruct H2; change_rewrite. rewrite <-H2 in H0.
destruct (eq_charac _ _ H0); destruct H5; change_rewrite.
apply VertexSet.union_3. rewrite in_interf.
assert (eq (a, snd_ext e, None) (x1,x2,wx)).
Eq_eq.
generalize (get_weight_m _ _ H0). simpl. intro. rewrite H7. apply OptionN_as_OT.eq_refl.
rewrite H7. assumption.
apply VertexSet.union_3. rewrite in_interf.
assert (eq (a, snd_ext e, None) (x1,x2,wx)).
Eq_eq.
apply (Register.eq_trans _ _ _ H5 H6).
generalize (get_weight_m _ _ H0). simpl. intro. rewrite H7. apply OptionN_as_OT.eq_refl.
rewrite H7. assumption.
Qed.

Lemma merge_interf_adj_fst_2 : forall e g H0 Haff,
VertexSet.Subset (interference_adj (fst_ext e) g)
                 (interference_adj (fst_ext e) (merge e g H0 Haff)).

Proof.
unfold VertexSet.Subset. intros.
rewrite in_interf in H. rewrite in_interf.
destruct (redirect_charac (a, fst_ext e, None) (snd_ext e) (fst_ext e)); intros.
change_rewrite. destruct H1. destruct H2.
rewrite H1. apply In_merge_interf_edge. assumption.
unfold interf_edge. auto.
change_rewrite. destruct H1. destruct H1.
elim (interf_pref_conflict (snd_ext e) (fst_ext e) g).
split. unfold Prefere. destruct Haff. exists x.
rewrite edge_comm. rewrite <-H3. rewrite (edge_eq e) in H0. assumption.
unfold Interfere.
assert (eq (snd_ext e, fst_ext e, None) (a, fst_ext e, None)) by Eq_eq.
rewrite H3. assumption.
destruct H1. rewrite H1. apply In_merge_interf_edge. assumption.
unfold interf_edge. auto.
Qed.

Lemma merge_interf_adj_fst_3 : forall e g H0 Haff,
VertexSet.Subset (interference_adj (snd_ext e) g)
                            (interference_adj (fst_ext e) (merge e g H0 Haff)).

Proof.
unfold VertexSet.Subset. intros.
rewrite in_interf in H. rewrite in_interf.
destruct (redirect_charac (a, snd_ext e, None) (snd_ext e) (fst_ext e)); intros.
change_rewrite. destruct H1. destruct H2. elim H3. auto.
change_rewrite. destruct H1. destruct H1.
elim (In_graph_edge_diff_ext _ _ H). change_rewrite. auto.
destruct H1. rewrite H1. apply In_merge_interf_edge. assumption.
unfold interf_edge. auto.
Qed.

Lemma merge_interf_adj_fst : forall e g H0 Haff,
VertexSet.Equal (interference_adj (fst_ext e) (merge e g H0 Haff))
                          (VertexSet.union (interference_adj (fst_ext e) g)
                                                     (interference_adj (snd_ext e) g)).

Proof.
intros. split; intros.
apply (merge_interf_adj_fst_1 _ _ H0 Haff _ H).
destruct (VertexSet.union_1 H).
 apply (merge_interf_adj_fst_2 _ _ H0 Haff _ H1).
 apply (merge_interf_adj_fst_3 _ _ H0 Haff _ H1).
Qed.

(* The following lemmas define the equality of the interference adjacency
   of any vertex which is not an endpoint of e after the merge of e *)

Lemma merge_interf_adj_1 : forall x e g Hin Haff,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
VertexSet.Subset (VertexSet.remove (snd_ext e) (interference_adj x g))
                            (interference_adj x (merge e g Hin Haff)).

Proof.
unfold VertexSet.Subset. intros.
rewrite in_interf. rewrite Dec.F.remove_iff in H1. destruct H1.
destruct (redirect_charac (a,x,None) (snd_ext e) (fst_ext e)); change_rewrite.
destruct H3. destruct H4. rewrite H3.
apply In_merge_interf_edge. rewrite <-in_interf. assumption.
unfold interf_edge. auto.
destruct H3. destruct H3. elim H2. auto.
destruct H3. elim H0. auto.
Qed.

Lemma merge_interf_adj_2 : forall x e g Hin Haff,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
VertexSet.Subset (interference_adj x (merge e g Hin Haff))
                 (VertexSet.add (fst_ext e) (interference_adj x g)).

Proof.
unfold VertexSet.Subset. intros.
destruct (Register.eq_dec a (fst_ext e)); [apply VertexSet.add_1|apply VertexSet.add_2]; intuition.
rewrite in_interf in H1. generalize (In_merge_edge_inv _ _ _ Hin Haff H1). intro.
destruct H2. destruct H2. destruct H3.
assert (eq (a,x,None) (redirect (snd_ext e) (fst_ext e) x0)).
apply weak_eq_interf_eq. assumption. unfold interf_edge. auto.
unfold interf_edge. rewrite redirect_weight_eq.
unfold same_type in H4. destruct H4; destruct H4.
unfold aff_edge in H5. destruct H5. simpl in H5. congruence.
auto. intuition.
rewrite in_interf. rewrite H5.
destruct (redirect_charac x0 (snd_ext e) (fst_ext e)).
destruct H6. destruct H7. rewrite <-H6. assumption.
destruct H6. destruct H6. rewrite <-H6 in H5.
destruct (eq_charac _ _ H5); destruct H8; change_rewrite.
elim n. auto. elim H. auto.
destruct H6. rewrite <-H6 in H5.
destruct (eq_charac _ _ H5); destruct H8; change_rewrite.
elim H. auto. elim n. auto.
Qed.

Lemma merge_interf_adj_not_in : forall x e g Hin Haff,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
~VertexSet.In x (interference_adj (snd_ext e) g) ->
VertexSet.Equal (interference_adj x (merge e g Hin Haff))
                          (interference_adj x g).

Proof.
intros. split; intros.
generalize (merge_interf_adj_2 x e g Hin Haff H H0 a H2). intro.
rewrite Dec.F.add_iff in H3. destruct H3.
rewrite <-H3 in H2. generalize (interf_adj_comm _ _ _ H2). intro.
rewrite merge_interf_adj_fst in H4. destruct (VertexSet.union_1 H4).
rewrite <-H3. apply interf_adj_comm. assumption.
elim H1. auto.
assumption.
apply merge_interf_adj_1; auto.
apply VertexSet.remove_2; auto.
intro. elim H1. apply interf_adj_comm. rewrite H3. assumption.
Qed.

Lemma merge_interf_adj_in_snd : forall x e g Hin Haff,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
VertexSet.In x (interference_adj (snd_ext e) g) ->
VertexSet.Equal (interference_adj x (merge e g Hin Haff))
                          (VertexSet.add (fst_ext e) (VertexSet.remove (snd_ext e)
                          (interference_adj x g))).

Proof.
intros. split; intros.
generalize (merge_interf_adj_2 _ _ _ Hin Haff H H0 _ H2). intro.
rewrite Dec.F.add_iff in H3. destruct H3.
apply VertexSet.add_1. assumption.
apply VertexSet.add_2. apply VertexSet.remove_2.
intro. rewrite <-H4 in H2. rewrite in_interf in H2.
generalize (proj1 (In_graph_edge_in_ext _ _ H2)). change_rewrite. intro.
rewrite In_merge_vertex in H5. destruct H5. elim H6. auto. assumption.

rewrite Dec.F.add_iff in H2. destruct H2.
rewrite <-H2. apply interf_adj_comm. rewrite merge_interf_adj_fst.
apply VertexSet.union_3. auto.
apply merge_interf_adj_1; auto.
Qed.

Lemma merge_interf_adj_in_both : forall x e g Hin Haff,
VertexSet.In x (interference_adj (snd_ext e) g) ->
VertexSet.In x (interference_adj (fst_ext e) g) ->
VertexSet.Equal (interference_adj x (merge e g Hin Haff))
                (VertexSet.remove (snd_ext e) (interference_adj x g)).

Proof.
intros.
assert (~Register.eq x (fst_ext e)).
intro. rewrite H1 in H0. elim (not_in_interf_self _ _ H0).
assert (~Register.eq x (snd_ext e)).
intro. rewrite H2 in H. elim (not_in_interf_self _ _ H).
rewrite merge_interf_adj_in_snd; auto.
split; intros.
rewrite Dec.F.add_iff in H3. destruct H3.
apply VertexSet.remove_2. intro.
elim (In_graph_edge_diff_ext _ _ Hin). rewrite H3. auto.
rewrite <-H3. apply interf_adj_comm. assumption.
assumption.
apply VertexSet.add_2. auto.
Qed.

Lemma preference_adj_merge : forall x e g p q,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
VertexSet.Subset (preference_adj x (merge e g p q))
                            (VertexSet.add (fst_ext e) 
                            (VertexSet.remove (snd_ext e) (preference_adj x g))).

Proof.
intros x e g p q H0 H1. generalize I. intro H.
unfold VertexSet.Subset; intros.
rewrite in_pref in H2. destruct H2.
generalize (In_merge_edge_inv e _ g p q H2). intro.
destruct H3. destruct H3. destruct H4 as [H4 HH4].
unfold weak_eq in H4. change_rewrite. destruct H4.
unfold redirect in H4; change_rewrite.
destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)); change_rewrite.
destruct H4. apply VertexSet.add_1. intuition.
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)); change_rewrite.
destruct H4. elim H0. intuition.
destruct H4. apply VertexSet.add_2. apply VertexSet.remove_2.
intro. elim n. rewrite H6. intuition.
rewrite in_pref. unfold same_type in HH4.
destruct HH4. destruct H6.
destruct H6. exists x2.
assert (eq (a,x,Some x2) x1).
apply eq_ordered_eq. split; try split; simpl; auto.
unfold get_weight in H6. rewrite H6. apply OptionN_as_OT.eq_refl.
rewrite H8. assumption.
destruct H6. unfold interf_edge in H7. simpl in H7. congruence.
unfold redirect in H4; change_rewrite.
destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)); change_rewrite.
destruct H4. elim H0. auto.
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)); change_rewrite.
destruct H4. apply VertexSet.add_1. intuition.
destruct H4. apply VertexSet.add_2. apply VertexSet.remove_2.
intro. elim n0. rewrite H6. intuition.
rewrite in_pref. unfold same_type in HH4.
destruct HH4. destruct H6.
destruct H6. exists x2.
assert (eq (a,x,Some x2) x1).
rewrite edge_comm. apply eq_ordered_eq. split; try split; simpl; auto.
unfold get_weight in H6. rewrite H6. apply OptionN_as_OT.eq_refl.
rewrite H8. assumption.
destruct H6. unfold interf_edge in H7. simpl in H7. congruence.
Qed.

Lemma preference_adj_merge_2 : forall x e g p q,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
VertexSet.Subset (VertexSet.remove (fst_ext e) (VertexSet.remove (snd_ext e) (preference_adj x g)))
                            (preference_adj x (merge e g p q)).

Proof.
unfold VertexSet.Subset; intros x e g p q H0 H1 a H2. generalize I. intro H.
assert (~Register.eq a (fst_ext e)). intro.
rewrite H3 in H2. elim (VertexSet.remove_1 (Register.eq_refl _) H2).
generalize (VertexSet.remove_3 H2). clear H2. intro H2.
assert (~Register.eq a (snd_ext e)). intro.
rewrite H4 in H2. elim (VertexSet.remove_1 (Register.eq_refl _) H2).
generalize (VertexSet.remove_3 H2). clear H2. intro.
rewrite in_pref in H2. destruct H2.
assert (exists w, In_graph_edge (a,x,Some w) (merge e g p q)).
cut (Prefere (fst_ext (redirect (snd_ext e) (fst_ext e) (a,x,Some x0)))
             (snd_ext (redirect (snd_ext e) (fst_ext e) (a,x,Some x0)))
             (merge e g p q)). intro.
unfold redirect in H5; change_rewrite.
destruct (OTFacts.eq_dec a (snd_ext e)); change_rewrite.
elim (H4 r).
destruct (OTFacts.eq_dec x (snd_ext e)); change_rewrite.
elim (H1 r).
unfold Prefere in H5. assumption.
apply In_merge_pref_edge. assumption.
intro. destruct (eq_charac _ _ H5); change_rewrite; destruct H6.
elim H1. auto.
elim H0. auto.
unfold aff_edge. exists x0. auto.
intro. unfold redirect in H5;change_rewrite.
destruct (OTFacts.eq_dec a (snd_ext e)); change_rewrite.
elim (H4 r).
destruct (OTFacts.eq_dec x (snd_ext e)); change_rewrite.
elim (H1 r).
unfold Interfere in H5. generalize (In_merge_edge_inv e _ g p q H5). intro H8.
generalize I. intro H7.
destruct H8. destruct H6. destruct H8.
unfold weak_eq in H8. change_rewrite. destruct H8.
unfold redirect in H8; change_rewrite.
destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)); change_rewrite; destruct H8.
elim (H3 H8).
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)); change_rewrite.
elim (H0 H10).
elim (interf_pref_conflict a x g).
split.
unfold Prefere. exists x0. assumption.
unfold Interfere.
assert (eq (a,x,None) x1).
apply weak_eq_interf_eq. unfold weak_eq. change_rewrite.
left. split; auto. unfold interf_edge. auto.
unfold same_type in H9. destruct H9. destruct H9.
unfold aff_edge in H11. destruct H11. simpl in H11. congruence.
destruct H9. assumption.
rewrite H11. assumption.

unfold redirect in H8; change_rewrite.
destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)); change_rewrite.
destruct H8. elim (H0 H10).
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)); change_rewrite.
destruct H8. elim (H3 H8).
elim (interf_pref_conflict a x g).
split.
unfold Prefere. exists x0. assumption.
unfold Interfere. destruct H8.
assert (eq (a,x,None) x1).
apply weak_eq_interf_eq. unfold weak_eq. change_rewrite.
right. split; auto. unfold interf_edge. auto.
unfold same_type in H9. destruct H9. destruct H9.
unfold aff_edge in H11. destruct H11. simpl in H11. congruence.
destruct H9. assumption.
rewrite H11. assumption.
rewrite in_pref. assumption.
Qed.

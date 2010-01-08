Require Import FSetInterface.
Require Import InterfGraphMapImp.
Require Import Remove_Vertex_Move.
Require Import ZArith.
Require Import Edges.
Require Import MyRegisters.
Require Import Affinity_relation.
Require Import Interference_adjacency.
Require Import Graph_Facts.
Require Import Merge_Adjacency.

Import Edge Props RegFacts.

(* A nonmove-related vertex of g different from the first endpoint of e
    is nonmove-related in (merge e g p q) *)
Lemma move_merge_false : forall x e g p q,
~Register.eq x (fst_ext e) ->
move_related g x = false ->
move_related (merge e g p q) x = false.

Proof.
intros x e g p q Hfst H0. generalize I. intro H.
case_eq (move_related (merge e g p q) x); intros.
generalize (move_related_charac _ _ H1). intro.
destruct H2. destruct H2. destruct H3.
generalize (In_merge_edge_inv _ _ _ p q H3). intro.
destruct H5. destruct H5.
assert (move_related g x = true).
apply move_related_charac2 with (e := x1).
unfold weak_eq in H6. destruct H6.
unfold same_type in H7. destruct H7. destruct H7. assumption.
destruct H7. destruct H2. unfold interf_edge in H2. congruence. assumption.
destruct H6.
unfold redirect in H6.
destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)); destruct H6; change_rewrite; destruct H6.
destruct H4.
elim Hfst. rewrite H4. auto.
right. rewrite H4. auto.
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)); change_rewrite.
destruct H4.
right. rewrite H4. auto.
elim Hfst. rewrite H4. auto.
destruct H4.
right. rewrite H4. auto.
elim Hfst. rewrite H4. auto.
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)); change_rewrite.
destruct H4.
left. rewrite H4. auto.
elim Hfst. rewrite H4. auto.
destruct H4.
left. rewrite H4. auto.
right. rewrite H4. auto.
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)); change_rewrite.
destruct H4.
elim Hfst. rewrite H4. auto.
left. rewrite H4. auto.
destruct H4.
right. rewrite H4. auto.
left. rewrite H4. auto.
rewrite H0 in H7. inversion H7.
auto.
Qed.

(* Equivalently, a move-related vertex of (merge e g p q) is
    move-related in g *)
Lemma move_related_merge_move_related : forall g e x H H0,
move_related (merge e g H H0) x = true ->
move_related g x = true.

Proof.
intros. case_eq (move_related g x); auto.
intro. assert (~Register.eq x (fst_ext e)).
intro. rewrite (compat_bool_move _ _ _ H3) in H2.
rewrite (proj1 (Aff_edge_aff _ _ H H0)) in H2. inversion H2.
rewrite (move_merge_false _ _ _ H H0 H3 H2) in H1. inversion H1.
Qed.

(* If x is neither a neighbor of (fst_ext e) nor (snd_ext e) and
    if x is move-related in g, then x is move-related in (merge e g H Haff) *)
Lemma move_related_move_related_merge : forall g e x Haff H,
~VertexSet.In x (preference_adj (fst_ext e) g) ->
~VertexSet.In x (preference_adj (snd_ext e) g) ->
move_related g x = true ->
move_related (merge e g H Haff) x = true.

Proof.
intros.
generalize (move_related_charac _ _ H2). intro.
destruct H3. destruct H3. destruct H4.
assert (~Register.eq x (fst_ext e)).
intro. elim H1. rewrite H6.
rewrite in_pref. destruct Haff. exists x1. rewrite <-H7.
rewrite (edge_eq e) in H. assumption.
assert (~Register.eq x (snd_ext e)).
intro. elim H0. rewrite H7.
rewrite in_pref. destruct Haff. exists x1. rewrite <-H8.
rewrite (edge_eq e) in H. rewrite edge_comm. assumption.

assert (Prefere (fst_ext (redirect (snd_ext e) (fst_ext e) x0))
                         (snd_ext (redirect (snd_ext e) (fst_ext e) x0))
                         (merge e g H Haff)).
apply In_merge_pref_edge. assumption.
intro. destruct (eq_charac _ _ H8); destruct H9.
destruct H5. elim H6. rewrite H5. auto.
elim H7. rewrite H5. auto.
destruct H5. elim H7. rewrite H5. auto.
elim H6. rewrite H5. auto.
assumption.

intro. unfold Interfere in H8. unfold redirect in H8.
destruct (OTFacts.eq_dec (fst_ext x0) (snd_ext e)); change_rewrite.
destruct H5. elim H7. rewrite H5. auto.
elim H1. rewrite in_pref. destruct H3. exists x1.
assert (eq (x, snd_ext e, Some x1) (snd_ext x0, fst_ext x0, Some x1)) by Eq_eq.
rewrite H9. rewrite <-H3. rewrite edge_comm. change Regs.registers with Regs.t. rewrite <-(edge_eq x0). auto.
destruct (OTFacts.eq_dec (snd_ext x0) (snd_ext e)); change_rewrite.
destruct H5.
elim H1. rewrite in_pref. destruct H3. exists x1.
assert (eq (x, snd_ext e, Some x1) (fst_ext x0, snd_ext x0, Some x1)) by Eq_eq.
rewrite H9. rewrite <-H3. rewrite <-(edge_eq x0). auto.
elim H7. rewrite H5. auto.
generalize (In_merge_edge_inv _ _ _ H Haff H8). intro. 
destruct H9. destruct H9. destruct H10.
unfold redirect in H10. destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)).
unfold weak_eq in H10; destruct H10; destruct H10; change_rewrite.
destruct H5. elim H6. rewrite H5. auto.
elim H0. rewrite in_pref. destruct H3. exists x2.
assert (eq (x, fst_ext e, Some x2) (snd_ext x0, fst_ext x0, Some x2)) by Eq_eq.
rewrite H13. rewrite edge_comm. rewrite <-H3. change Regs.registers with Regs.t. rewrite <-(edge_eq x0). auto.
destruct H5.
elim H0. rewrite in_pref. destruct H3. exists x2.
assert (eq (x, fst_ext e, Some x2) (fst_ext x0, snd_ext x0, Some x2)) by Eq_eq.
rewrite H13. rewrite <-H3. rewrite <-(edge_eq x0). auto.
elim H6. rewrite H5. auto.
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)).
unfold weak_eq in H10; destruct H10; destruct H10; change_rewrite.
destruct H5.
elim H0. rewrite in_pref. destruct H3. exists x2.
assert (eq (x, fst_ext e, Some x2) (fst_ext x0, snd_ext x0, Some x2)) by Eq_eq.
rewrite H13. rewrite <-H3. rewrite <-(edge_eq x0). auto.
elim H6. rewrite H5. auto.
destruct H5. elim H6. rewrite H5. auto.
elim H0. rewrite in_pref. destruct H3. exists x2.
assert (eq (x, fst_ext e, Some x2) (snd_ext x0, fst_ext x0, Some x2)) by Eq_eq.
rewrite H13. rewrite <-H3. rewrite edge_comm. change Regs.registers with Regs.t. rewrite <-(edge_eq x0). auto.
elim (interf_pref_conflict (fst_ext x0) (snd_ext x0) g).
unfold Prefere, Interfere. split.
destruct H3. exists x2. rewrite <-H3. change Regs.registers with Regs.t. rewrite <-(edge_eq x0). auto.
assert (eq (fst_ext x0, snd_ext x0, None) (fst_ext x1, snd_ext x1, None)).
unfold weak_eq in H10; destruct H10; destruct H10; change_rewrite. 
Eq_eq. Eq_comm_eq. rewrite H12.
unfold same_type in H11. destruct H11; destruct H11.
destruct H13. simpl in H13. congruence.
rewrite <-H11. rewrite <-(edge_eq x1). auto.

unfold redirect in H8. destruct (OTFacts.eq_dec (fst_ext x0) (snd_ext e)); change_rewrite.
destruct H5. elim H7. rewrite H5. auto.
elim H1. rewrite in_pref. destruct H3. exists x1.
assert (eq (x, snd_ext e, Some x1) (fst_ext x0, snd_ext x0, Some x1)) by Eq_comm_eq.
rewrite H9. rewrite <-H3. rewrite <-(edge_eq x0). auto.
destruct (OTFacts.eq_dec (snd_ext x0) (snd_ext e)); change_rewrite.
destruct H5.
elim H1. rewrite in_pref. destruct H3. exists x1.
assert (eq (x, snd_ext e, Some x1) (fst_ext x0, snd_ext x0, Some x1)) by Eq_eq.
rewrite H9. rewrite <-H3. rewrite <-(edge_eq x0). auto.
elim H7. rewrite H5. auto.
unfold Prefere in H8. destruct H8.
apply (move_related_charac2 _ _ (fst_ext x0, snd_ext x0, Some x1)).
unfold aff_edge. exists x1. auto.
assumption.
destruct H5;[left|right]; auto.
Qed.

Lemma interfere_dec : forall x y g,
Interfere x y g \/ ~Interfere x y g.

Proof.
intros. unfold Interfere.
destruct (RegRegProps.In_dec (x,y,None) (IE g)).
left. right. assumption.
right. intro. elim n.
rewrite In_graph_interf_edge_in_IE. split.
unfold interf_edge. auto.
assumption.
Qed.

(* A vertex x different from r which is move-related in g and nonmove-related
    in (merge e g p q) is either
    1) interfering with the first endpoint of e and prefering with the second one
    2) interfering with the second endpoint of e and prefering with the first one *)
Lemma move_merge_not_move : forall x e g p q,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
move_related (merge e g p q) x = false ->
move_related g x = true ->
(VertexSet.In x (VertexSet.inter (interference_adj (fst_ext e) g) (preference_adj (snd_ext e) g))) \/
(VertexSet.In x (VertexSet.inter (interference_adj (snd_ext e) g) (preference_adj (fst_ext e) g))).

Proof.
intros x e g p q H0 H1 H2 H3. generalize I. intro H.
generalize (move_related_charac _ _ H3). intro.
destruct H4. destruct H4. destruct H5.
cut (Interfere (fst_ext (redirect (snd_ext e) (fst_ext e) x0))
               (snd_ext (redirect (snd_ext e) (fst_ext e) x0))
               (merge e g p q)). intro.
unfold Interfere in H7. unfold redirect in H7.
destruct (OTFacts.eq_dec (fst_ext x0) (snd_ext e)); change_rewrite.
destruct H6.
elim H1. rewrite H6. auto.
generalize (In_merge_edge_inv e _ g p q H7). intro.
destruct H8. destruct H8. destruct H9 as [H9 HH9].
assert (eq (fst_ext e, snd_ext x0, None) (redirect (snd_ext e) (fst_ext e) x1)).
unfold weak_eq; destruct H9; destruct H9; change_rewrite.
apply eq_ordered_eq. split; intuition. change_rewrite. rewrite redirect_weight_eq.
unfold same_type in HH9. destruct HH9. destruct H11.
destruct H12. simpl in H12. congruence.
destruct H11. rewrite <-H11. apply OptionN_as_OT.eq_refl.
Eq_comm_eq. simpl. rewrite redirect_weight_eq.
unfold same_type in HH9. destruct HH9. destruct H11.
destruct H12. simpl in H12. congruence.
destruct H11. rewrite <-H11. apply OptionN_as_OT.eq_refl.
generalize H10. clear H9 HH9 H10. intro H9.
unfold redirect in H9.
destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)).
destruct (eq_charac _ _ H9); change_rewrite; destruct H10.
elim (interf_pref_conflict x (snd_ext e) g).
split.
destruct H4.
unfold Prefere. exists x2.
cut (eq (x, snd_ext e, Some x2) x0). intro.
rewrite H12. auto.
rewrite (edge_eq x0).
rewrite edge_comm. apply eq_ordered_eq. constructor; simpl.
split; intuition.
rewrite H4. apply OptionN_as_OT.eq_refl.
unfold Interfere.
cut (eq (x, snd_ext e, None) x1). intro.
rewrite H12. auto.
rewrite (edge_eq x1).
rewrite edge_comm. apply eq_ordered_eq. constructor;simpl.
split; intuition. rewrite H6. auto.
generalize (get_weight_m _ _ (eq_sym H9)). simpl. intro.
rewrite H12. apply OptionN_as_OT.eq_refl.

elim H0. rewrite H6. auto.
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)).
destruct (eq_charac _ _ H9); change_rewrite. destruct H10.
elim H0. rewrite H6. auto.
destruct H10.

elim (interf_pref_conflict x (snd_ext e) g).
split.
destruct H4.
unfold Prefere. exists x2.
cut (eq (x, snd_ext e, Some x2) x0). intro.
rewrite H12. auto.
rewrite (edge_eq x0).
rewrite edge_comm. apply eq_ordered_eq. constructor; simpl.
split; intuition.
rewrite H4. apply OptionN_as_OT.eq_refl.
unfold Interfere.
cut (eq (x, snd_ext e, None) x1). intro.
rewrite H12. auto.
rewrite (edge_eq x1).
apply eq_ordered_eq. constructor;simpl.
split; try rewrite H6; intuition.
generalize (get_weight_m _ _ (eq_sym H9)). simpl. intro.
rewrite H12. apply OptionN_as_OT.eq_refl.
left. apply VertexSet.inter_3.
rewrite in_interf.
cut (eq (x, fst_ext e, None) (fst_ext e, snd_ext x0, None)). intro.
rewrite H10. rewrite H9. auto.
rewrite edge_comm. apply eq_ordered_eq.
constructor; simpl. split; intuition.
apply OptionN_as_OT.eq_refl.
destruct H4.
rewrite in_pref. exists x2.
cut (eq (x,snd_ext e, Some x2) x0). intro.
rewrite H10. auto.
rewrite edge_comm. apply eq_ordered_eq. rewrite (edge_eq x0).
constructor; simpl. split; intuition.
auto. auto. rewrite H4. apply OptionN_as_OT.eq_refl.

destruct (OTFacts.eq_dec (snd_ext x0) (snd_ext e)); change_rewrite.
destruct H6.
generalize (In_merge_edge_inv e _ g p q H7). intro.
destruct H8. destruct H8. destruct H9 as [H9 HH9].
assert (eq (fst_ext x0, fst_ext e, None) (redirect (snd_ext e) (fst_ext e) x1)).
unfold weak_eq; destruct H9; destruct H9; change_rewrite.
Eq_eq. simpl. rewrite redirect_weight_eq.
unfold same_type in HH9. destruct HH9. destruct H11.
destruct H12. simpl in H12. congruence.
destruct H11. rewrite <-H11. apply OptionN_as_OT.eq_refl.
Eq_comm_eq. simpl. rewrite redirect_weight_eq.
unfold same_type in HH9. destruct HH9. destruct H11.
destruct H12. simpl in H12. congruence.
destruct H11. rewrite <-H11. apply OptionN_as_OT.eq_refl.
generalize H10. clear H9 HH9 H10. intro H9.
unfold redirect in H9.
destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)).
destruct (eq_charac _ _ H9); change_rewrite; destruct H10.
elim H0. rewrite H6. auto.
elim (interf_pref_conflict x (snd_ext e) g).
split.
destruct H4.
unfold Prefere. exists x2.
cut (eq (x, snd_ext e, Some x2) x0). intro.
rewrite H12. auto.
rewrite (edge_eq x0).
apply eq_ordered_eq. constructor; simpl.
split; intuition.
auto.
auto.
rewrite H4. apply OptionN_as_OT.eq_refl.
unfold Interfere.
cut (eq (x, snd_ext e, None) x1). intro.
rewrite H12. auto.
rewrite (edge_eq x1).
rewrite edge_comm. apply eq_ordered_eq. constructor;simpl.
split; try rewrite H6; intuition.
generalize (get_weight_m _ _ (eq_sym H9)). simpl. intro.
rewrite H12. apply OptionN_as_OT.eq_refl.

destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)).
destruct (eq_charac _ _ H9); change_rewrite. destruct H10.
elim (interf_pref_conflict x (snd_ext e) g).
split.
destruct H4.
unfold Prefere. exists x2.
cut (eq (x, snd_ext e, Some x2) x0). intro.
rewrite H12. auto.
rewrite (edge_eq x0).
apply eq_ordered_eq. constructor; simpl.
split; intuition.
rewrite H4. apply OptionN_as_OT.eq_refl.
unfold Interfere.
cut (eq (x, snd_ext e, None) x1). intro.
rewrite H12. auto.
rewrite (edge_eq x1).
apply eq_ordered_eq. constructor;simpl.
split; try rewrite H6; intuition.
generalize (get_weight_m _ _ (eq_sym H9)). simpl. intro.
rewrite H12. apply OptionN_as_OT.eq_refl.

destruct H10. elim H0. rewrite H6. auto.

left. apply VertexSet.inter_3.
rewrite in_interf.
cut (eq (x, fst_ext e, None) (fst_ext x0, fst_ext e, None)). intro.
rewrite H10. rewrite H9. auto.
apply eq_ordered_eq.
constructor; simpl. split; intuition.
apply OptionN_as_OT.eq_refl.
destruct H4.
rewrite in_pref. exists x2.
cut (eq (x,snd_ext e, Some x2) x0). intro.
rewrite H10. auto.
apply eq_ordered_eq. rewrite (edge_eq x0).
constructor; simpl. split; intuition.
rewrite H4. apply OptionN_as_OT.eq_refl.

elim H1. rewrite H6. auto.
generalize (In_merge_edge_inv e _ g p q H7). intro.
destruct H8. destruct H8. destruct H9 as [H9 HH9].
assert (eq (fst_ext x0, snd_ext x0, None) (redirect (snd_ext e) (fst_ext e) x1)).
unfold weak_eq; destruct H9; destruct H9; change_rewrite.
Eq_eq. simpl. rewrite redirect_weight_eq.
unfold same_type in HH9. destruct HH9. destruct H11.
destruct H12. simpl in H12. congruence.
destruct H11. rewrite <-H11. apply OptionN_as_OT.eq_refl.
Eq_comm_eq. simpl. rewrite redirect_weight_eq.
unfold same_type in HH9. destruct HH9. destruct H11.
destruct H12. simpl in H12. congruence.
destruct H11. rewrite <-H11. apply OptionN_as_OT.eq_refl.
generalize H10. clear H9 HH9 H10. intro H9.
unfold redirect in H9.
destruct (OTFacts.eq_dec (fst_ext x1) (snd_ext e)).
destruct (eq_charac _ _ H9); change_rewrite; destruct H10.
destruct H6. elim H0. rewrite H6. auto.
right. apply VertexSet.inter_3.
rewrite in_interf.
cut (eq (x, snd_ext e, None) x1). intro.
rewrite H12. auto.
rewrite edge_comm. apply eq_ordered_eq.
constructor; simpl. split; intuition.
auto. rewrite H6. auto.
generalize (get_weight_m _ _ H9). simpl. intro.
rewrite H12. unfold get_weight. apply OptionN_as_OT.eq_refl.
destruct H4.
rewrite in_pref. exists x2.
cut (eq (x, fst_ext e, Some x2) x0). intro.
rewrite H12. auto.
rewrite edge_comm. apply eq_ordered_eq. rewrite (edge_eq x0).
constructor; simpl. split; intuition.
auto. auto. rewrite H4. apply OptionN_as_OT.eq_refl.

destruct H6.
right. apply VertexSet.inter_3.
rewrite in_interf.
cut (eq (x, snd_ext e, None) x1). intro.
rewrite H12. auto.
rewrite edge_comm. apply eq_ordered_eq.
constructor; simpl. split; intuition.
auto. rewrite H6. auto.
generalize (get_weight_m _ _ H9). simpl. intro.
rewrite H12. unfold get_weight. apply OptionN_as_OT.eq_refl.
destruct H4.
rewrite in_pref. exists x2.
cut (eq (x, fst_ext e, Some x2) x0). intro.
rewrite H12. auto.
apply eq_ordered_eq. rewrite (edge_eq x0).
constructor; simpl. split; intuition.
auto. auto. rewrite H4. apply OptionN_as_OT.eq_refl.

elim H0. rewrite H6. auto.
destruct (OTFacts.eq_dec (snd_ext x1) (snd_ext e)).
destruct (eq_charac _ _ H9); change_rewrite; destruct H10.
destruct H6.
right. apply VertexSet.inter_3.
rewrite in_interf.
cut (eq (x, snd_ext e, None) x1). intro.
rewrite H12. auto.
apply eq_ordered_eq.
constructor; simpl. split; intuition.
rewrite H6. auto. auto.
generalize (get_weight_m _ _ H9). simpl. intro.
rewrite H12. unfold get_weight. apply OptionN_as_OT.eq_refl.
destruct H4.
rewrite in_pref. exists x2.
cut (eq (x, fst_ext e, Some x2) x0). intro.
rewrite H12. auto.
apply eq_ordered_eq. rewrite (edge_eq x0).
constructor; simpl. split; intuition.
auto. auto. rewrite H4. apply OptionN_as_OT.eq_refl.

elim H0. rewrite H6. auto.

destruct H6.
elim H0. rewrite H6. auto.
right. apply VertexSet.inter_3.
rewrite in_interf.
cut (eq (x, snd_ext e, None) x1). intro.
rewrite H12. auto.
apply eq_ordered_eq.
constructor; simpl. split; intuition.
rewrite H6. auto. auto.
generalize (get_weight_m _ _ H9). simpl. intro.
rewrite H12. unfold get_weight. apply OptionN_as_OT.eq_refl.
destruct H4.
rewrite in_pref. exists x2.
cut (eq (x, fst_ext e, Some x2) x0). intro.
rewrite H12. auto.
rewrite edge_comm. apply eq_ordered_eq. rewrite (edge_eq x0).
constructor; simpl. split; intuition.
auto. auto. rewrite H4. apply OptionN_as_OT.eq_refl.

elim (interf_pref_conflict (fst_ext x0) (snd_ext x0) g).
split.
unfold Prefere. destruct H4. exists x2. 
rewrite <-H4. change Regs.registers with Regs.t. rewrite <-(edge_eq x0). assumption.
unfold Interfere. rewrite H9. assumption.

(* cut *)
destruct (interfere_dec (fst_ext (redirect (snd_ext e) (fst_ext e) x0))
                        (snd_ext (redirect (snd_ext e) (fst_ext e) x0))
                        (merge e g p q)). auto.
cut (~eq e x0). intro.
generalize (In_merge_pref_edge e x0 g p q H5 H8 H4 H7). intro. clear H7.
unfold Prefere in H9. destruct H9. unfold redirect in H7.
destruct (OTFacts.eq_dec (fst_ext x0) (snd_ext e)); change_rewrite.
destruct H6.
elim H1. rewrite H6. auto.
assert (move_related (merge e g p q) x = true).
apply move_related_charac2 with (e:= (fst_ext e, snd_ext x0, Some x1)).
exists x1. auto.
auto.
right. change_rewrite. auto.
rewrite H2 in H9. inversion H9.

destruct (OTFacts.eq_dec (snd_ext x0) (snd_ext e)); change_rewrite.
destruct H6.
assert (move_related (merge e g p q) x = true).
apply move_related_charac2 with (e:= (fst_ext x0, fst_ext e, Some x1)).
exists x1. auto.
auto.
left. change_rewrite. auto.
rewrite H2 in H9. inversion H9.

elim H1. rewrite H6. auto.

assert (move_related (merge e g p q) x = true).
apply move_related_charac2 with (e:= (fst_ext x0, snd_ext x0, Some x1)).
exists x1. auto.
auto.
destruct H6;[left|right]; auto.
rewrite H2 in H9. inversion H9.

intro. destruct (eq_charac _ _ H8); destruct H9.
destruct H6.
elim H0. rewrite H6. auto.
elim H1. rewrite H6. auto.
destruct H6.
elim H1. rewrite H6. auto.
elim H0. rewrite H6. auto.
Qed.

(* A move-related vertex of g which does not interfere with an endpoint
    of e and prefere with the other one is move-related in (merge e g p q) *)
Lemma move_related_merge_true : forall x e g p q,
move_related g x = true ->
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
~VertexSet.In x (VertexSet.inter (interference_adj (fst_ext e ) g)
                                                    (preference_adj (snd_ext e) g)) ->
~VertexSet.In x (VertexSet.inter (interference_adj (snd_ext e) g)
                                                    (preference_adj (fst_ext e) g)) ->
move_related (merge e g p q) x = true.

Proof.
intros x e g p q H0 H1 H2 H3 H4. generalize I. intro H.
case_eq (move_related (merge e g p q) x); intros.
reflexivity.
generalize (move_merge_not_move _ _ _ p q H1 H2 H5 H0). intro.
destruct H6;[elim (H3 H6)|elim (H4 H6)].
Qed.

(*  A vertex which interferes with an endpoint of e, preferes with
     the other one and has a preference degree of one is
     nonmove-related in (merge e g p q) *)
Lemma move_related_change_charac : forall x e g p q,
VertexSet.In x (VertexSet.union (VertexSet.inter (interference_adj (fst_ext e) g)
                                                                             (preference_adj (snd_ext e) g))
                                                  (VertexSet.inter (interference_adj (snd_ext e) g)
                                                                            (preference_adj (fst_ext e) g))) ->
pref_degree g x = 1 ->
move_related (merge e g p q) x = false.

Proof.
unfold pref_degree. intros x e g p q H1 H2. generalize I. intro H.
assert (move_related g x = true).
case_eq (move_related g x); auto. intro. 
rewrite move_related_card in H0. inversion H0.
unfold pref_degree. congruence.
assert (~Register.eq x (fst_ext e)) as Hfst.
intro. rewrite H3 in H1.
destruct (VertexSet.union_1 H1).
elim (not_in_interf_self (fst_ext e) g).
apply (VertexSet.inter_1 H4).
elim (not_in_pref_self (fst_ext e) g).
apply (VertexSet.inter_2 H4).
assert (~Register.eq x (snd_ext e)) as Hsnd.
intro. rewrite H3 in H1.
destruct (VertexSet.union_1 H1).
elim (not_in_pref_self (snd_ext e) g).
apply (VertexSet.inter_2 H4).
elim (not_in_interf_self (snd_ext e) g).
apply (VertexSet.inter_1 H4).
destruct (VertexSet.union_1 H1).
assert (VertexSet.Equal (preference_adj x g) (VertexSet.singleton (snd_ext e))).
apply cardinal_1_singleton.
apply pref_adj_comm. apply (VertexSet.inter_2 H3).
assumption.

assert (VertexSet.Equal (preference_adj x (merge e g p q)) VertexSet.empty).
split; intros.
assert (VertexSet.Subset (preference_adj x (merge e g p q))
                         (VertexSet.add (fst_ext e)
                            (VertexSet.remove (snd_ext e) (preference_adj x g)))).
apply preference_adj_merge; assumption.
destruct (Register.eq_dec a (fst_ext e)).
elim (interf_pref_conflict (fst_ext e) x (merge e g p q)).
split.
rewrite in_pref in H5. destruct H5.
unfold Prefere. exists x0.
assert (eq (fst_ext e, x, Some x0) (a, x, Some x0)) by Eq_eq.
rewrite H7. assumption.
unfold Interfere.
assert (eq (fst_ext e, x,None) (redirect (snd_ext e) (fst_ext e) (fst_ext e, x,None))).
apply eq_ordered_eq.
split; simpl; try split; try apply Regs.eq_refl.
unfold redirect; change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e) (snd_ext e)). apply Regs.eq_refl.
destruct (OTFacts.eq_dec x (snd_ext e)). apply Regs.eq_refl. apply Regs.eq_refl.
unfold redirect; change_rewrite; simpl.
destruct (OTFacts.eq_dec (fst_ext e) (snd_ext e)). apply Regs.eq_refl.
destruct (OTFacts.eq_dec x (snd_ext e)). simpl.
elim (not_in_pref_self (snd_ext e) g).
rewrite r in H3. apply (VertexSet.inter_2 H3). apply Regs.eq_refl.
auto. rewrite redirect_weight_eq. simpl. apply OptionN_as_OT.eq_refl.
rewrite H7. apply In_merge_interf_edge.
rewrite <-in_interf. apply interf_adj_comm. apply (VertexSet.inter_1 H3).
unfold interf_edge. auto.

assert (VertexSet.In a (VertexSet.add (fst_ext e) (VertexSet.remove (snd_ext e) (preference_adj x g)))).
apply H6. assumption.
assert (VertexSet.In a (VertexSet.remove (snd_ext e) (preference_adj x g))).
apply VertexSet.add_3 with (x:=fst_ext e); auto.
rewrite H4 in H8.
assert (~Register.eq a (snd_ext e)).
intro. elim (VertexSet.remove_1 (Register.eq_sym _ _ H9) H8).
generalize (VertexSet.remove_3 H8). intro.
generalize (VertexSet.singleton_1 H10). intro. elim H9. auto.
elim (VertexSet.empty_1 H5).
case_eq (move_related (merge e g p q) x); intros.
elim (move_related_not_empty_pref _ _ H6). assumption.
reflexivity.

(* symetric part *)
assert (VertexSet.Equal (preference_adj x g) (VertexSet.singleton (fst_ext e))).
apply cardinal_1_singleton.
apply pref_adj_comm. apply (VertexSet.inter_2 H3).
assumption.

assert (VertexSet.Equal (preference_adj x (merge e g p q)) VertexSet.empty).
split; intros.
assert (VertexSet.Subset (preference_adj x (merge e g p q))
                         (VertexSet.add (fst_ext e)
                            (VertexSet.remove (snd_ext e) (preference_adj x g)))).
apply preference_adj_merge; assumption.
destruct (Register.eq_dec a (fst_ext e)).
elim (interf_pref_conflict (fst_ext e) x (merge e g p q)).
split.
rewrite in_pref in H5. destruct H5.
unfold Prefere. exists x0.
assert (eq (fst_ext e, x, Some x0) (a, x, Some x0)) by Eq_eq.
rewrite H7. assumption.
unfold Interfere.
assert (eq (fst_ext e, x,None) (redirect (snd_ext e) (fst_ext e) (snd_ext e, x,None))).
apply eq_ordered_eq.
split; simpl; try split; auto.
unfold redirect; change_rewrite.
destruct (OTFacts.eq_dec (snd_ext e) (snd_ext e)). apply Regs.eq_refl.
elim n. apply Regs.eq_refl.
unfold redirect; change_rewrite.
destruct (OTFacts.eq_dec (snd_ext e) (snd_ext e)). apply Regs.eq_refl.
elim n. apply Regs.eq_refl.
rewrite redirect_weight_eq. simpl. apply OptionN_as_OT.eq_refl.
rewrite H7. apply In_merge_interf_edge.
rewrite <-in_interf. apply interf_adj_comm. apply (VertexSet.inter_1 H3).
unfold interf_edge. auto.

assert (VertexSet.In a (VertexSet.add (fst_ext e) (VertexSet.remove (snd_ext e) (preference_adj x g)))).
apply H6. assumption.
assert (VertexSet.In a (VertexSet.remove (snd_ext e) (preference_adj x g))).
apply VertexSet.add_3 with (x:=fst_ext e); auto.
rewrite H4 in H8.
generalize (VertexSet.remove_3 H8). intro.
generalize (VertexSet.singleton_1 H9). intro. elim n. auto.
elim (VertexSet.empty_1 H5).
case_eq (move_related (merge e g p q) x); intros.
elim (move_related_not_empty_pref _ _ H6). assumption.
reflexivity.
Qed.

(* A move-related vertex of g which is not move-related in
   (merge e g p q) has a preference degree of 1 *)
Lemma move_related_dec_1 : forall x e g p q,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
move_related g x = true ->
move_related (merge e g p q) x = false ->
pref_degree g x = 1.

Proof.
unfold pref_degree. intros x e g p q H0 H1 H2 H3. generalize I. intro H.
generalize (preference_adj_merge_2 x e g p q H0 H1). intro.
cut (VertexSet.cardinal (preference_adj x g) <= 1). intro.
cut (VertexSet.cardinal (preference_adj x g) > 0). intro.
intuition.
generalize (move_related_not_empty_pref x g H2). intro.
case_eq (VertexSet.cardinal (preference_adj x g)); intros.
elim H6. apply empty_is_empty_1. apply (cardinal_inv_1 H7).
intuition.
generalize (not_move_related_empty_pref x (merge e g p q) H3). intro.
generalize (move_merge_not_move _ _ _ p q H0 H1 H3 H2). intro.
destruct H6.
assert (VertexSet.cardinal (VertexSet.remove (fst_ext e) (VertexSet.remove (snd_ext e) (preference_adj x g))) <= 
       (VertexSet.cardinal (preference_adj x (merge e g p q)))).
apply subset_cardinal. assumption.
rewrite H5 in H7. rewrite empty_cardinal in H7.
rewrite remove_cardinal_2 in H7.
rewrite <-remove_cardinal_1 with (x:=snd_ext e).
apply le_n_S. assumption.
apply pref_adj_comm. apply (VertexSet.inter_2 H6).
intro. generalize (VertexSet.remove_3 H8). intro.
elim (interf_pref_conflict (fst_ext e) x g).
split.
rewrite in_pref in H9. destruct H9.
unfold Prefere. exists x0. assumption.
unfold Interfere.
rewrite edge_comm. generalize (VertexSet.inter_1 H6). intro.
rewrite in_interf in H10. assumption.
assert (VertexSet.cardinal (VertexSet.remove (fst_ext e) (VertexSet.remove (snd_ext e) (preference_adj x g))) <= 
       (VertexSet.cardinal (preference_adj x (merge e g p q)))).
apply subset_cardinal. assumption.
rewrite H5 in H7. rewrite empty_cardinal in H7.
rewrite <-remove_cardinal_2 with (x:=snd_ext e).
rewrite <-remove_cardinal_1 with (x:=fst_ext e).
apply le_n_S. assumption.
apply VertexSet.remove_2.
apply (In_graph_edge_diff_ext e g p).
apply pref_adj_comm. apply (VertexSet.inter_2 H6).
intro. elim (interf_pref_conflict (snd_ext e) x g).
split.
rewrite in_pref in H8. destruct H8.
unfold Prefere. exists x0. assumption.
generalize (VertexSet.inter_1 H6). intro.
unfold Interfere. rewrite edge_comm. rewrite <-in_interf. assumption.
Qed.

(* Again, meaningful theorem *)
Theorem Merge_move_evolution : forall x e g p q,
~Register.eq x (fst_ext e) ->
~Register.eq x (snd_ext e) ->
((move_related g x = true /\ move_related (merge e g p q) x = false)
                                        <->
 (pref_degree g x = 1 /\
 (VertexSet.In x (VertexSet.inter (interference_adj (fst_ext e) g) (preference_adj (snd_ext e) g)) \/
  VertexSet.In x (VertexSet.inter (interference_adj (snd_ext e) g) (preference_adj (fst_ext e) g))))).

Proof.
split; intros.
destruct H1.
split. apply (move_related_dec_1 x e g p q); auto.
        apply (move_merge_not_move x e g p q); auto.
destruct H1.
split. case_eq (move_related g x); auto. intro. rewrite move_related_card in H3; congruence.
        apply move_related_change_charac; auto.
        destruct H2;[apply VertexSet.union_2|apply VertexSet.union_3]; auto.
Qed.

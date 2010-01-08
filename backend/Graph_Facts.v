Require Import FSets.
Require Import InterfGraphMapImp.
Require Import ZArith.
Require Import Edges.
Require Import MyRegisters.

Import  Edge OTFacts.
Module Import RegFacts := Facts VertexSet.
Module Import RegRegFacts := Facts EdgeSet.

(* Definition of useful morphisms *)

Add Morphism In_graph : In_graph_m.

Proof.
unfold In_graph;intros x y H g.
split;intro H0;[rewrite <-H|rewrite H];assumption.
Qed.

Add Morphism In_graph_edge : In_graph_edge_m.

Proof.
unfold In_graph_edge; intros x y H g. fold (eq x y) in H.
split;intro H0;[rewrite <-H|rewrite H];assumption.
Qed.

Add Morphism move_related : move_related_m.

Proof.
unfold move_related. intros. rewrite (compat_preference_adj _ _ _ H). reflexivity.
Qed.

Add Morphism get_weight : get_weight_m.

Proof.
intros x y H.
rewrite (weight_ordered_weight x);rewrite (weight_ordered_weight y).
unfold get_weight;unfold E.eq in H.
destruct H as [_ H];inversion H;[|rewrite H2];reflexivity.
Qed.

(* Useful rewriting lemmas *)

Lemma rewrite_fst : forall x y z,
fst_ext (x,y,z) = x.

Proof.
auto.
Qed.

Lemma rewrite_snd : forall x y z,
snd_ext (x,y,z) = y.

Proof.
auto.
Qed.

Lemma rewrite_weight : forall x y z,
get_weight (x,y,z) = z.

Proof.
auto.
Qed.

(* A rewriting tactic *)

Ltac change_rewrite := 
repeat (try rewrite rewrite_fst in *;
             try rewrite rewrite_snd in *;
             try rewrite rewrite_weight in *).

(* Two tactics for proving equality of edges *)
Ltac Eq_eq :=
apply eq_ordered_eq;unfold E.eq;
split;[simpl;split;auto; intuition |try apply OptionN_as_OT.eq_refl; intuition].

Ltac Eq_comm_eq := rewrite edge_comm; Eq_eq.

(* Extensionnality of redirect *)
Lemma redirect_ext : forall e e' x y,
eq e e' ->
eq (redirect x y e) (redirect x y e').

Proof.
intros e e' x y H.
destruct e as [xe we];destruct xe as [ex1 ex2];
destruct e' as [xe' we'];destruct xe' as [e'x1 e'x2];simpl in *.
generalize (get_weight_m _ _ H);simpl;intro Heq;subst.
destruct (eq_charac _  _ H);destruct H0 as [H0 H1];unfold redirect;change_rewrite.
destruct (OTFacts.eq_dec ex1 x).
destruct (OTFacts.eq_dec e'x1 x).
Eq_eq. intuition.
elim (n (Regs.eq_trans (Regs.eq_sym H0) r)).
destruct (OTFacts.eq_dec e'x1 x).
elim (n (Regs.eq_trans H0 r)).
destruct (OTFacts.eq_dec ex2 x).
destruct (OTFacts.eq_dec e'x2 x).
Eq_eq. intuition.
elim (n1 (Regs.eq_trans (Regs.eq_sym H1) r)).
destruct (OTFacts.eq_dec e'x2 x).
elim (n1 (Regs.eq_trans H1 r)).
Eq_eq.
destruct (OTFacts.eq_dec ex1 x).
destruct (OTFacts.eq_dec e'x1 x).
Eq_eq. intuition.
apply (Regs.eq_trans H1 (Regs.eq_trans r0 (Regs.eq_trans (Regs.eq_sym r) H0))).
destruct (OTFacts.eq_dec e'x2 x).
Eq_comm_eq. intuition.
elim (n0 (Regs.eq_trans (Regs.eq_sym H0) r)).
destruct (OTFacts.eq_dec e'x2 x).
elim (n (Regs.eq_trans H0 r)).
destruct (OTFacts.eq_dec ex2 x). 
destruct (OTFacts.eq_dec e'x1 x).
Eq_comm_eq.
elim (n1 (Regs.eq_trans (Regs.eq_sym H1) r)).
destruct (OTFacts.eq_dec e'x1 x).
elim (n1 (Regs.eq_trans H1 r)).
Eq_comm_eq.
Qed.

(* The weight is left unchanged while applying redirect *)
Lemma redirect_weight_eq : forall e x y,
Edge.get_weight (redirect x y e) = Edge.get_weight e.

Proof.
unfold redirect;intros e x y;destruct e as [e w];destruct e as [ex1 ex2];change_rewrite.
destruct (OTFacts.eq_dec ex1 x);destruct (OTFacts.eq_dec ex2 x);reflexivity.
Qed.

(* Specification of redirect *)
Lemma redirect_charac : forall e x y,
(eq e (redirect x y e) /\ (~Regs.eq x (fst_ext e) /\ ~Regs.eq x (snd_ext e))) \/
(eq (y, snd_ext e, get_weight e) (redirect x y e) /\ Regs.eq x (fst_ext e)) \/
(eq (fst_ext e, y, get_weight e) (redirect x y e) /\ Regs.eq x (snd_ext e)).

Proof.
intros e x y.
unfold redirect. change_rewrite.
destruct (OTFacts.eq_dec (fst_ext e) x).
right. left. split. apply eq_refl. auto.
destruct (OTFacts.eq_dec (snd_ext e) x).
right. right. split. apply eq_refl. auto.
left. split. apply eq_refl. split; intuition.
Qed.

(* Weak equality implies equality for interference edges *)
Lemma weak_eq_interf_eq : forall x y,
weak_eq x y ->
interf_edge x ->
interf_edge y ->
eq x y.

Proof.
unfold weak_eq, interf_edge, get_weight. intros. destruct H; destruct H. 
Eq_eq. rewrite H0. rewrite H1. apply OptionN_as_OT.eq_refl.
rewrite (edge_eq x). rewrite (edge_eq y).
Eq_comm_eq. simpl. unfold get_weight.
rewrite H0. rewrite H1. apply OptionN_as_OT.eq_refl.
Qed.

(* The second endpoint of e does not belongs to (merge e g H H0) *)
Lemma not_in_merge_snd : forall e g H H0,
~In_graph (snd_ext e) (merge e g H H0).

Proof.
intros. intro.
rewrite In_merge_vertex in H1. destruct H1.
elim (H2 (Regs.eq_refl _)).
Qed.

(* Extensionnality of the low-degree function *)
Lemma compat_bool_low : forall g K,
compat_bool Regs.eq (has_low_degree g K).

Proof.
unfold compat_bool, has_low_degree, interf_degree. intros.
rewrite (compat_interference_adj _ _ _ H). reflexivity.
Qed.

(* There cannot exist both an interference and 
    a preference between two vertices *)
Lemma interf_pref_conflict : forall x y g,
Prefere x y g /\ Interfere x y g -> False.

Proof.
unfold Prefere, Interfere. intros. destruct H. destruct H.
assert (eq (x,y,Some x0) (x,y,None)).
apply is_simple_graph with (g:=g); auto.
unfold weak_eq. left. change_rewrite. split; auto.
generalize (get_weight_m _ _ H1). simpl. congruence.
Qed.

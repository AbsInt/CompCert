Require Import FSets.
Require Import InterfGraphMapImp.
Require Import Affinity_relation.
Require Import ZArith.
Require Import Edges.
Require Import MyRegisters.

Import Edge RegFacts Props.

(* Definition of the Briggs criterion *)

Definition nb_of_significant_degree g K s :=
VertexSet.fold (fun x n => if (le_lt_dec K (interf_degree g x)) then S n else n)
               s 0.

(* Definition of the conservative criteria : an affinity edge e is coalescible if
    1) one of its endpoints is not precolored
    2) the endpoints have less than K interference neighbors of high-degree *)
Definition conservative_coalescing_criteria e g K :=
if (is_precolored (fst_ext e) g && is_precolored (snd_ext e) g) then false else
if le_lt_dec
K
(nb_of_significant_degree g K
                   (VertexSet.union (interference_adj (fst_ext e) g)
                   (interference_adj (snd_ext e) g)))
then false else true.

(* Specification of the coalescing criterion *)
Lemma conservative_coalescing_criteria_1 : forall e g K,
~VertexSet.In (fst_ext e) (precolored g) \/ 
~VertexSet.In (snd_ext e) (precolored g) ->
In_graph_edge e g ->
nb_of_significant_degree g K
      (VertexSet.union (interference_adj (fst_ext e) g) (interference_adj (snd_ext e) g))
      < K ->
conservative_coalescing_criteria e g K = true.

Proof.
intros e g K H HHHH H0.
assert (In_graph (fst_ext e) g /\ In_graph (snd_ext e) g).
apply In_graph_edge_in_ext. assumption. destruct H1 as [HH HHH].
unfold conservative_coalescing_criteria.
case_eq (is_precolored (fst_ext e) g && is_precolored (snd_ext e) g); intros.
destruct H.
case_eq (is_precolored (fst_ext e) g); intros.
elim H. apply (precolored_equiv _ _). split; assumption.
rewrite H2 in H1. inversion H1.
case_eq (is_precolored (snd_ext e) g); intros.
destruct H. apply (precolored_equiv _ _). split; assumption.
rewrite H2 in H1. destruct (is_precolored (fst_ext e)); auto.
destruct (le_lt_dec K (nb_of_significant_degree g K
         (VertexSet.union (interference_adj (fst_ext e) g)
            (interference_adj (snd_ext e) g)))).
intuition.
reflexivity.
Qed.

Lemma conservative_coalescing_criteria_2 : forall e g palette,
conservative_coalescing_criteria e g palette = true ->
~VertexSet.In (fst_ext e) (precolored g) \/ 
~VertexSet.In (snd_ext e) (precolored g).

Proof.
intros.
unfold conservative_coalescing_criteria in H.
case_eq (is_precolored (fst_ext e) g && is_precolored (snd_ext e) g); intros.
rewrite H0 in H.
inversion H.
rewrite H0 in H.
case_eq (is_precolored (fst_ext e) g);intros.
right.
case_eq (is_precolored (snd_ext e) g); intros.
rewrite H1 in H0. rewrite H2 in H0. inversion H0.
intro H3. generalize (proj1 (precolored_equiv _ _) H3). intro.
rewrite H2 in H4. destruct H4. inversion H4.
left.
intro H4. generalize (proj1 (precolored_equiv _ _) H4). intro.
rewrite H1 in H2. destruct H2. inversion H2.
Qed.

Lemma conservative_coalescing_criteria_3 : forall e g K,
conservative_coalescing_criteria e g K = true ->
nb_of_significant_degree g K
      (VertexSet.union (interference_adj (fst_ext e) g) (interference_adj (snd_ext e) g))
      < K.

Proof.
intros.
unfold conservative_coalescing_criteria in H.
case_eq (is_precolored (fst_ext e) g && is_precolored (snd_ext e) g); intros.
rewrite H0 in H. inversion H.
rewrite H0 in H.
destruct (le_lt_dec
          K
          (nb_of_significant_degree g K
             (VertexSet.union (interference_adj (fst_ext e) g)
                (interference_adj (snd_ext e) g)))).
inversion H.
assumption.
Qed.

Definition is_none (o : option Edge.t) :=
match o with
|None => true
|Some _ => false
end.

(* Function picking an edge satisfying a function f in a set s*)
Definition get_element_such_f (f : Edge.t -> bool) s :=
EdgeSet.fold (fun e o => if (is_none o) then if (f e) then Some e else None else o) s None.

(* Specification of the get_element_such function *)
Lemma element_some : forall l (f : Edge.t -> bool) a,
fold_left
      (fun (a : option Edge.t) (e : EdgeSet.elt) =>
       if is_none a then if f e then Some e else None else a) l (Some a) = Some a.

Proof.
induction l; simpl; intros.
reflexivity.
apply IHl.
Qed.

Lemma get_element_correct : forall f s (x : Edge.t),
get_element_such_f f s = Some x -> f x = true.

Proof.
unfold get_element_such_f. intros f s x H.
unfold get_element_such_f in H.
rewrite EdgeSet.fold_1 in H.
induction (EdgeSet.elements s); simpl in H.
simpl in H. inversion H.
case_eq (f a); intro H0; rewrite H0 in H.
rewrite element_some in H. inversion H. subst. assumption.
apply IHl. assumption.
Qed.

Lemma get_element_in : forall f s x,
get_element_such_f f s = Some x -> EdgeSet.In x s.

Proof.
intros f s x H.
unfold get_element_such_f in H.
rewrite EdgeSet.fold_1 in H.
generalize (EdgeSet.elements_2);intro H0.
generalize (H0 s);clear H0;intro H0.
induction (EdgeSet.elements s);simpl in *.
inversion H.
case_eq (f a); intro H1; rewrite H1 in H.
rewrite element_some in H. inversion H. subst.
apply H0. intuition.
apply IHl; intuition.
Qed.

Lemma compat_is_precolored : forall x y g,
Register.eq x y ->
is_precolored x g = is_precolored y g.

Proof.
exact is_precolored_ext.
Qed.

(* Definition of the any_coalescible_edge function which picks an affinity
    edge satisfying the coalescing criterion for K in g in the set moves *)
Definition any_coalescible_edge moves g K :=
match (get_element_such_f (fun e => conservative_coalescing_criteria e g K) moves) with
|None => None
|Some e => if (is_precolored (fst_ext e) g) then Some e else Some (snd_ext e, fst_ext e, get_weight e)
end.

Lemma adj_of_significant_degree_compat_set : forall g s s' K,
VertexSet.Equal s s' ->
nb_of_significant_degree g K s =
nb_of_significant_degree g K s'.

Proof.
intros g s s' K H.
unfold nb_of_significant_degree.
cut (eqlistA Register.eq (VertexSet.elements s) (VertexSet.elements s')). intro H0.
do 2 rewrite VertexSet.fold_1.
generalize H0. generalize (VertexSet.elements s').
clear H0. generalize 0. 
induction (VertexSet.elements s). simpl.
intros n l H0. 
destruct l.
simpl. reflexivity.
inversion H0.
simpl. intro n.
destruct l0. simpl. intro H0. inversion H0.
intro H0. simpl.
inversion H0. subst.
case_eq (le_lt_dec K (interf_degree g a)); intros H1 _;
case_eq (le_lt_dec K (interf_degree g e)); intros H2 _.
apply IHl. assumption.
unfold interf_degree in H1. rewrite (compat_interference_adj _ _ _ H4) in H1. 
apply False_ind. intuition.
unfold interf_degree in H2. apply False_ind. intuition.
unfold interf_degree in H1. rewrite (compat_interference_adj _ _ _ H4) in H1. 
unfold interf_degree in H2. apply False_ind. intuition.
apply IHl. assumption.
apply SortA_equivlistA_eqlistA with (ltA := Register.lt).
apply Register.eq_refl.
apply Register.eq_sym.
apply Register.eq_trans.
apply Register.lt_trans.
apply Register.lt_not_eq.
apply OTFacts.lt_eq.
apply OTFacts.eq_lt.
apply VertexSet.elements_3.
apply VertexSet.elements_3.
apply equal_equivlist. assumption.
Qed.

Lemma compat_criteria_aux : forall e e' g K,
eq e e' ->
In_graph_edge e g ->
conservative_coalescing_criteria e g K = true ->
conservative_coalescing_criteria e' g K = true.

Proof.
intros e e' g K H HH H0.
apply conservative_coalescing_criteria_1.
generalize (conservative_coalescing_criteria_2 _ _ _ H0). intro H1.
destruct H1.
destruct (eq_charac _ _ H); change_rewrite; destruct H2.
left. rewrite <-H2. assumption.
right. rewrite <-H2. assumption.
destruct (eq_charac _ _ H); change_rewrite; destruct H2.
right. rewrite <-H3. assumption.
left. rewrite <-H3. assumption.

rewrite <-H. assumption.

generalize (conservative_coalescing_criteria_3 _ _ _ H0). intro H1.
destruct (eq_charac _ _ H); change_rewrite; destruct H2 as [H2 H3];
rewrite <-(compat_interference_adj _ _ _ H2) in *;
rewrite <-(compat_interference_adj _ _ _ H3) in *.
assumption.
rewrite adj_of_significant_degree_compat_set with 
(s':= VertexSet.union (interference_adj (fst_ext e) g) (interference_adj (snd_ext e) g)).
assumption.
apply union_sym.
Qed.

Lemma compat_criteria : forall e e' g K,
eq e e' ->
In_graph_edge e g ->
conservative_coalescing_criteria e g K =
conservative_coalescing_criteria e' g K.

Proof.
intros e e' g palette HH H.
case_eq (conservative_coalescing_criteria e g palette); intros.
symmetry. apply compat_criteria_aux with (e:=e). assumption. assumption. assumption.
case_eq (conservative_coalescing_criteria e' g palette); intros.
assert (conservative_coalescing_criteria e g palette = true).
apply compat_criteria_aux with (e:=e'). apply eq_sym. assumption.
rewrite <-HH. assumption. assumption.
rewrite H0 in H2. inversion H2.
reflexivity.
Qed.

(* Specification of any_coalescible_edge *)
Lemma any_coalescible_edge_1 : forall e g K s,
(forall e', EdgeSet.In e' s -> In_graph_edge e' g) ->
any_coalescible_edge s g K = Some e ->
conservative_coalescing_criteria e g K = true /\ EdgeSet.In e s.

Proof.
intros e g K s HH H.
unfold any_coalescible_edge in H.
case_eq (get_element_such_f (fun e : t => conservative_coalescing_criteria e g K) s).
intros t0 H0.
rewrite H0 in H.
destruct (is_precolored (fst_ext t0) g);inversion H;subst.
split.
apply (get_element_correct _ _ _ H0).
apply (get_element_in _ _ _ H0).
assert (eq t0 (snd_ext t0, fst_ext t0, get_weight t0)) by (Eq_comm_eq; apply Regs.eq_refl).
split.
rewrite (compat_criteria _ _ _ _ (eq_sym H1)).
apply (get_element_correct _ _ _ H0).
apply HH. rewrite <-H1. apply (get_element_in _ _ _ H0).
rewrite <-H1. apply (get_element_in _ _ _ H0).
intro H0. rewrite H0 in H. inversion H.
Qed.

Lemma any_coalescible_edge_11 : forall e g palette s,
any_coalescible_edge s g palette = Some e ->
EdgeSet.In e s.

Proof.
intros.
unfold any_coalescible_edge in H.
case_eq (get_element_such_f
        (fun e : t => conservative_coalescing_criteria e g palette) s); intros.
rewrite H0 in H.
case_eq (is_precolored (fst_ext t0) g); intros.
rewrite H1 in H.
inversion H. subst.
apply (get_element_in _ _ _ H0).
rewrite H1 in H.
inversion H. subst.
rewrite edge_comm. change Regs.registers with Regs.t. rewrite <-(edge_eq t0).
 apply (get_element_in _ _ _ H0).
rewrite H0 in H.
inversion H.
Qed.

Lemma any_coalescible_edge_2 : forall e g palette s,
(forall e', EdgeSet.In e' s -> In_graph_edge e' g) ->
any_coalescible_edge s g palette = Some e ->
~VertexSet.In (snd_ext e) (precolored g).

Proof.
intros e g palette s H H0.
intro H1.
generalize (any_coalescible_edge_1 _ _ _ _ H H0). intro HH.
unfold any_coalescible_edge in H0.
case_eq (get_element_such_f (fun e : t =>conservative_coalescing_criteria e g palette) s).
intros t0 H2.
rewrite H2 in H0.
case_eq (is_precolored (fst_ext t0) g);intro H3.
rewrite H3 in H0.
generalize (proj1 (precolored_equiv _ _ ) H1);clear H1;intro H1.
inversion H0;subst. destruct HH as [HH H5].
generalize (conservative_coalescing_criteria_2 _ _ _ HH). intro H4.
destruct H4; elim H4; apply (proj2 (precolored_equiv _ _)).
split. assumption. apply (proj1 (In_graph_edge_in_ext _ _ (H e (get_element_in _ _ _ H2)))).
destruct H1. split; assumption.
rewrite H3 in H0.
inversion H0;subst.
clear H0.
change (snd_ext (snd_ext t0,fst_ext t0,get_weight t0)) with (fst_ext t0) in H1.
generalize (proj1 (precolored_equiv _ _) H1);clear H1;intro H1.
rewrite H3 in H1;inversion H1. inversion H0.
intro H2;rewrite H2 in H0.
inversion H0.
Qed.

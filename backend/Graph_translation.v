Require Import InterfGraph.
Require Import InterfGraphMapImp.
Require Import MyRegisters.
Require Import RTLtyping.
Require Import NArith.
Require Import List.
Require Import InterfGraph_Construction.
Require Import Edges.
Require Import EqualSetMap.

Import Edge.

Definition new_graph := tt.

Section Translation.

Variable g : graph.
Variable interfgraph_vertices : VertexSet.t.

Definition IE_reg_reg :=
SetRegReg.fold (fun e s => EdgeSet.add (Regs.reg_to_Reg (fst e), Regs.reg_to_Reg (snd e), None) s)
               (interf_reg_reg g) EdgeSet.empty.

Definition IE_reg_mreg :=
SetRegMreg.fold (fun e s => EdgeSet.add (Regs.reg_to_Reg (fst e), Regs.mreg_to_Reg (snd e), None) s)
               (interf_reg_mreg g) EdgeSet.empty.

Definition AE_reg_reg :=
SetRegReg.fold (fun e s => EdgeSet.add (Regs.reg_to_Reg (fst e), Regs.reg_to_Reg (snd e), Some N0) s)
               (pref_reg_reg g) EdgeSet.empty.

Definition AE_reg_mreg :=
SetRegMreg.fold (fun e s => EdgeSet.add (Regs.reg_to_Reg (fst e), Regs.mreg_to_Reg (snd e), Some N0) s)
                (pref_reg_mreg g) EdgeSet.empty.

Definition interfgraph_interference_edges := EdgeSet.union IE_reg_reg IE_reg_mreg.

Definition resolve_conflicts s1 s2 := 
EdgeSet.fold (fun e s => if EdgeSet.mem (fst_ext e, snd_ext e,None) s2
                      then s else EdgeSet.add e s) s1 EdgeSet.empty.

Definition interfgraph_affinity_edges := 
resolve_conflicts 
(EdgeSet.union AE_reg_reg AE_reg_mreg)
interfgraph_interference_edges.

Hypothesis extremities_interf_graph :
forall e, EdgeSet.In e interfgraph_affinity_edges \/
             EdgeSet.In e interfgraph_interference_edges ->
             VertexSet.In (fst_ext e) interfgraph_vertices /\
             VertexSet.In (snd_ext e) interfgraph_vertices.

Definition new_adj_set x y m :=
match (VertexMap.find x m) with
   | None => VertexSet.singleton y
   | Some s => VertexSet.add y s
end.

Definition empty_map := 
VertexSet.fold 
               (fun x m => VertexMap.add x VertexSet.empty m)
               interfgraph_vertices
               (VertexMap.empty VertexSet.t).

Definition set2map s map := 
EdgeSet.fold (fun e m => VertexMap.add (fst_ext e) (new_adj_set (fst_ext e) (snd_ext e) m)
                        (VertexMap.add (snd_ext e) (new_adj_set (snd_ext e) (fst_ext e) m) m))
                        s map.

Definition interf_map := set2map interfgraph_interference_edges empty_map.
Definition pref_map := set2map interfgraph_affinity_edges empty_map.

Lemma add_simpl : forall l a s s2,
EdgeSet.Equal
  (fold_left
     (fun (a0 : EdgeSet.t) (e0 : EdgeSet.elt) =>
      if EdgeSet.mem (fst_ext e0, snd_ext e0, None) s2
      then a0
      else EdgeSet.add e0 a0) l (EdgeSet.add a s))
(EdgeSet.add a  
(fold_left
     (fun (a0 : EdgeSet.t) (e0 : EdgeSet.elt) =>
      if EdgeSet.mem (fst_ext e0, snd_ext e0, None) s2
      then a0
      else EdgeSet.add e0 a0) l s)).

Proof.
induction l;simpl;intros.
intuition.
case_eq (EdgeSet.mem (fst_ext a,snd_ext a,None) s2);intro H.
apply IHl.
do 3 rewrite IHl.
apply RegRegProps.add_add.
Qed.


Lemma resolve_conflicts_2 : forall e s1 s2,
EdgeSet.In e (resolve_conflicts s1 s2) ->
EdgeSet.In e s1 /\ ~EdgeSet.In (fst_ext e,snd_ext e, None) s2.

Proof.
intros e s1 s2 H.
unfold resolve_conflicts in H.
rewrite EdgeSet.fold_1 in H.
split.
generalize (EdgeSet.elements_2);intro H0;generalize (H0 s1);clear H0;intro H0.
induction (EdgeSet.elements s1);simpl in *.
elim (EdgeSet.empty_1 H).
destruct (eq_dec a e).
apply H0.
fold (eq a e) in e0.
generalize (Edge.eq_sym e0);clear e0;intro e0.
intuition.
case_eq (EdgeSet.mem (fst_ext a, snd_ext a,None) s2);intro H1;rewrite H1 in H.
apply IHl.
apply H.
intuition.
apply IHl.

rewrite add_simpl in H.
apply (EdgeSet.add_3 n H).
intuition.
induction (EdgeSet.elements s1);simpl in *.
elim (EdgeSet.empty_1 H).
case_eq (EdgeSet.mem (fst_ext a,snd_ext a,None) s2);intro H0;rewrite H0 in H.
apply IHl;assumption.
destruct (eq_dec a e).
intro H1.
destruct (eq_charac _ _ e0).
destruct H2 as [H2 HH2].
assert (eq (fst_ext a,snd_ext a,None) (fst_ext e,snd_ext e,None)) by Eq_eq.
rewrite (RegRegProps.Dec.F.mem_b s2 H3) in H0.
generalize (EdgeSet.mem_1 H1);clear H1;intro H1.
rewrite H0 in H1;inversion H1.
destruct H2 as [H2 HH2].
assert (eq (fst_ext a,snd_ext a,None) (fst_ext e,snd_ext e,None)) by Eq_comm_eq.
rewrite (RegRegProps.Dec.F.mem_b s2 H3) in H0.
generalize (EdgeSet.mem_1 H1);clear H1;intro H1.
rewrite H0 in H1;inversion H1.
apply IHl.
rewrite add_simpl in H.
apply (EdgeSet.add_3 n H).
Qed.

(*
intros g e H.
unfold interfgraph_vertices.
destruct H.
unfold interfgraph_affinity_edges in H.
generalize (proj1 (resolve_conflicts_2 _ _ _ H)). clear H. intro H.
destruct (EdgeSet.union_1 H).
cut (VertexSet.In (fst_ext e) (V_pref_reg_reg g) /\
       VertexSet.In (snd_ext e) (V_pref_reg_reg g)).
intro H1. destruct H1 as [H1 H2]. split;
(do 2 apply VertexSet.union_3; 
apply VertexSet.union_2; assumption).
unfold V_pref_reg_reg.
unfold AE_reg_reg in H0.
rewrite SetRegReg.fold_1 in *.
induction (SetRegReg.elements (pref_reg_reg g)).
simpl in H0. elim (EdgeSet.empty_1 H0).
rewrite MEdgeFacts.fold_left_assoc in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (Regs.reg_to_Reg (fst a), Regs.reg_to_Reg (snd a), Some N0) e) in H1.
rewrite RegFacts.fold_left_assoc.
destruct (eq_charac _ _ H1); destruct H2 as [H2 H3].
change_rewrite. split.
apply VertexSet.add_1. assumption.
apply VertexSet.add_2. apply VertexSet.add_1. assumption.
change_rewrite. split.
apply VertexSet.add_2. apply VertexSet.add_1. assumption.
apply VertexSet.add_1. assumption.
intros y z s.
rewrite (Props.add_add  (VertexSet.add (Regs.reg_to_Reg (snd y)) s)
                                         (Regs.reg_to_Reg (snd z))
                                         (Regs.reg_to_Reg (fst y))).
rewrite (Props.add_add   s
                                       (Regs.reg_to_Reg (snd z))
                                       (Regs.reg_to_Reg (snd y))).
set (s' := VertexSet.add (Regs.reg_to_Reg (snd z) ) s).
rewrite (Props.add_add   s'
                                       (Regs.reg_to_Reg (snd y))
                                       (Regs.reg_to_Reg (fst z))).
apply Props.add_add.
intros. apply Props.Dec.F.add_m.
apply Regs.eq_refl.
apply Props.Dec.F.add_m;[apply Regs.eq_refl|assumption].
rewrite RegFacts.fold_left_assoc.
split; do 2 apply VertexSet.add_2.
apply (proj1 (IHl H1)).
apply (proj2 (IHl H1)).
intros y z s.
rewrite (Props.add_add  (VertexSet.add (Regs.reg_to_Reg (snd y)) s)
                                         (Regs.reg_to_Reg (snd z))
                                         (Regs.reg_to_Reg (fst y))).
rewrite (Props.add_add   s
                                       (Regs.reg_to_Reg (snd z))
                                       (Regs.reg_to_Reg (snd y))).
set (s' := VertexSet.add (Regs.reg_to_Reg (snd z) ) s).
rewrite (Props.add_add   s'
                                       (Regs.reg_to_Reg (snd y))
                                       (Regs.reg_to_Reg (fst z))).
apply Props.add_add.
intros. apply Props.Dec.F.add_m.
apply Regs.eq_refl.
apply Props.Dec.F.add_m;[apply Regs.eq_refl|assumption].
intros;apply RegRegProps.add_add.
intros;apply RegRegProps.Dec.F.add_m;[apply eq_refl|assumption].

cut (VertexSet.In (fst_ext e) (V_pref_reg_mreg g) /\
       VertexSet.In (snd_ext e) (V_pref_reg_mreg g)).
intro H1. destruct H1 as [H1 H2]. split;
(do 3 apply VertexSet.union_3; assumption).
unfold V_pref_reg_mreg.
unfold AE_reg_mreg in H0.
rewrite SetRegMreg.fold_1 in *.
induction (SetRegMreg.elements (pref_reg_mreg g)).
simpl in H0. elim (EdgeSet.empty_1 H0).
rewrite MEdgeFacts.fold_left_assoc in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (Regs.reg_to_Reg (fst a), Regs.mreg_to_Reg (snd a), Some N0) e) in H1.
rewrite RegFacts.fold_left_assoc.
destruct (eq_charac _ _ H1); destruct H2 as [H2 H3].
change_rewrite. split.
apply VertexSet.add_1. assumption.
apply VertexSet.add_2. apply VertexSet.add_1. assumption.
change_rewrite. split.
apply VertexSet.add_2. apply VertexSet.add_1. assumption.
apply VertexSet.add_1. assumption.
intros y z s.
rewrite (Props.add_add  (VertexSet.add (Regs.mreg_to_Reg (snd y)) s)
                                         (Regs.mreg_to_Reg (snd z))
                                         (Regs.reg_to_Reg (fst y))).
rewrite (Props.add_add   s
                                       (Regs.mreg_to_Reg (snd z))
                                       (Regs.mreg_to_Reg (snd y))).
set (s' := VertexSet.add (Regs.mreg_to_Reg (snd z) ) s).
rewrite (Props.add_add   s'
                                       (Regs.mreg_to_Reg (snd y))
                                       (Regs.reg_to_Reg (fst z))).
apply Props.add_add.
intros. apply Props.Dec.F.add_m.
apply Regs.eq_refl.
apply Props.Dec.F.add_m;[apply Regs.eq_refl|assumption].
rewrite RegFacts.fold_left_assoc.
split; do 2 apply VertexSet.add_2.
apply (proj1 (IHl H1)).
apply (proj2 (IHl H1)).
intros y z s.
rewrite (Props.add_add  (VertexSet.add (Regs.mreg_to_Reg (snd y)) s)
                                         (Regs.mreg_to_Reg (snd z))
                                         (Regs.reg_to_Reg (fst y))).
rewrite (Props.add_add   s
                                       (Regs.mreg_to_Reg (snd z))
                                       (Regs.mreg_to_Reg (snd y))).
set (s' := VertexSet.add (Regs.mreg_to_Reg (snd z) ) s).
rewrite (Props.add_add   s'
                                       (Regs.mreg_to_Reg (snd y))
                                       (Regs.reg_to_Reg (fst z))).
apply Props.add_add.
intros. apply Props.Dec.F.add_m.
apply Regs.eq_refl.
apply Props.Dec.F.add_m;[apply Regs.eq_refl|assumption].
intros;apply RegRegProps.add_add.
intros;apply RegRegProps.Dec.F.add_m;[apply eq_refl|assumption].

unfold interfgraph_interference_edges in H.
destruct (EdgeSet.union_1 H).
cut (VertexSet.In (fst_ext e) (V_interf_reg_reg g) /\
       VertexSet.In (snd_ext e) (V_interf_reg_reg g)).
intro H1. destruct H1 as [H1 H2]. split;
(apply VertexSet.union_2; assumption).
unfold V_interf_reg_reg.
unfold IE_reg_reg in H0.
rewrite SetRegReg.fold_1 in *.
induction (SetRegReg.elements (interf_reg_reg g)).
simpl in H0. elim (EdgeSet.empty_1 H0).
rewrite MEdgeFacts.fold_left_assoc in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (Regs.reg_to_Reg (fst a), Regs.reg_to_Reg (snd a), Some N0) e) in H1.
rewrite RegFacts.fold_left_assoc.
destruct (eq_charac _ _ H1); destruct H2 as [H2 H3].
change_rewrite. split.
apply VertexSet.add_1. assumption.
apply VertexSet.add_2. apply VertexSet.add_1. assumption.
change_rewrite. split.
apply VertexSet.add_2. apply VertexSet.add_1. assumption.
apply VertexSet.add_1. assumption.
intros y z s.
rewrite (Props.add_add  (VertexSet.add (Regs.reg_to_Reg (snd y)) s)
                                         (Regs.reg_to_Reg (snd z))
                                         (Regs.reg_to_Reg (fst y))).
rewrite (Props.add_add   s
                                       (Regs.reg_to_Reg (snd z))
                                       (Regs.reg_to_Reg (snd y))).
set (s' := VertexSet.add (Regs.reg_to_Reg (snd z) ) s).
rewrite (Props.add_add   s'
                                       (Regs.reg_to_Reg (snd y))
                                       (Regs.reg_to_Reg (fst z))).
apply Props.add_add.
intros. apply Props.Dec.F.add_m.
apply Regs.eq_refl.
apply Props.Dec.F.add_m;[apply Regs.eq_refl|assumption].
rewrite RegFacts.fold_left_assoc.
split; do 2 apply VertexSet.add_2.
apply (proj1 (IHl H1)).
apply (proj2 (IHl H1)).
intros y z s.
rewrite (Props.add_add  (VertexSet.add (Regs.reg_to_Reg (snd y)) s)
                                         (Regs.reg_to_Reg (snd z))
                                         (Regs.reg_to_Reg (fst y))).
rewrite (Props.add_add   s
                                       (Regs.reg_to_Reg (snd z))
                                       (Regs.reg_to_Reg (snd y))).
set (s' := VertexSet.add (Regs.reg_to_Reg (snd z) ) s).
rewrite (Props.add_add   s'
                                       (Regs.reg_to_Reg (snd y))
                                       (Regs.reg_to_Reg (fst z))).
apply Props.add_add.
intros. apply Props.Dec.F.add_m.
apply Regs.eq_refl.
apply Props.Dec.F.add_m;[apply Regs.eq_refl|assumption].
intros;apply RegRegProps.add_add.
intros;apply RegRegProps.Dec.F.add_m;[apply eq_refl|assumption].

cut (VertexSet.In (fst_ext e) (V_interf_reg_mreg g) /\
       VertexSet.In (snd_ext e) (V_interf_reg_mreg g)).
intro H1. destruct H1 as [H1 H2]. split;
(apply VertexSet.union_3; apply VertexSet.union_2; assumption).
unfold V_interf_reg_mreg.
unfold IE_reg_mreg in H0.
rewrite SetRegMreg.fold_1 in *.
induction (SetRegMreg.elements (interf_reg_mreg g)).
simpl in H0. elim (EdgeSet.empty_1 H0).
rewrite MEdgeFacts.fold_left_assoc in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (Regs.reg_to_Reg (fst a), Regs.mreg_to_Reg (snd a), Some N0) e) in H1.
rewrite RegFacts.fold_left_assoc.
destruct (eq_charac _ _ H1); destruct H2 as [H2 H3].
change_rewrite. split.
apply VertexSet.add_1. assumption.
apply VertexSet.add_2. apply VertexSet.add_1. assumption.
change_rewrite. split.
apply VertexSet.add_2. apply VertexSet.add_1. assumption.
apply VertexSet.add_1. assumption.
intros y z s.
rewrite (Props.add_add  (VertexSet.add (Regs.mreg_to_Reg (snd y)) s)
                                         (Regs.mreg_to_Reg (snd z))
                                         (Regs.reg_to_Reg (fst y))).
rewrite (Props.add_add   s
                                       (Regs.mreg_to_Reg (snd z))
                                       (Regs.mreg_to_Reg (snd y))).
set (s' := VertexSet.add (Regs.mreg_to_Reg (snd z) ) s).
rewrite (Props.add_add   s'
                                       (Regs.mreg_to_Reg (snd y))
                                       (Regs.reg_to_Reg (fst z))).
apply Props.add_add.
intros. apply Props.Dec.F.add_m.
apply Regs.eq_refl.
apply Props.Dec.F.add_m;[apply Regs.eq_refl|assumption].
rewrite RegFacts.fold_left_assoc.
split; do 2 apply VertexSet.add_2.
apply (proj1 (IHl H1)).
apply (proj2 (IHl H1)).
intros y z s.
rewrite (Props.add_add  (VertexSet.add (Regs.mreg_to_Reg (snd y)) s)
                                         (Regs.mreg_to_Reg (snd z))
                                         (Regs.reg_to_Reg (fst y))).
rewrite (Props.add_add   s
                                       (Regs.mreg_to_Reg (snd z))
                                       (Regs.mreg_to_Reg (snd y))).
set (s' := VertexSet.add (Regs.mreg_to_Reg (snd z) ) s).
rewrite (Props.add_add   s'
                                       (Regs.mreg_to_Reg (snd y))
                                       (Regs.reg_to_Reg (fst z))).
apply Props.add_add.
intros. apply Props.Dec.F.add_m.
apply Regs.eq_refl.
apply Props.Dec.F.add_m;[apply Regs.eq_refl|assumption].
intros;apply RegRegProps.add_add.
intros;apply RegRegProps.Dec.F.add_m;[apply eq_refl|assumption].
Qed.
*)

Lemma vertices_empty_map : forall x,
VertexMap.In x empty_map <->
VertexSet.In x interfgraph_vertices.

Proof.
unfold empty_map. split; intros.
set (f :=  (fun (x : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
          VertexMap.add x VertexSet.empty m)) in *.
rewrite VertexSet.fold_1 in *.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_2. intro HH.
generalize (HH interfgraph_vertices). clear HH. intro HH.
induction (VertexSet.elements interfgraph_vertices). simpl in H.
rewrite MapFacts.empty_in_iff in H. inversion H.
cut (EqualSetMap (fold_left f' (a :: l) (VertexMap.empty VertexSet.t)) 
                 (f' (fold_left f' l (VertexMap.empty VertexSet.t)) a)). intro.
generalize (H0 x). clear H0. intro H0. inversion H0. subst.
simpl in H. rewrite MapFacts.in_find_iff in H. rewrite <-H2 in H.
elim H. auto.
set (tmp := fold_left f' l (VertexMap.empty VertexSet.t)) in *.
unfold f', f in H2.
destruct (Vertex.eq_dec x a).
rewrite e. apply HH. left. apply Regs.eq_refl.
apply IHl.
rewrite MapFacts.add_neq_o in H2.
rewrite MapFacts.in_find_iff. rewrite <-H2. congruence.
auto.

intros. apply HH. right. auto.

apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f', f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
auto.
auto.

set (f :=  (fun (x : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
          VertexMap.add x VertexSet.empty m)) in *.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a) in *.
generalize VertexSet.elements_1. intro HH.
generalize (HH _ _ H). clear HH. intro HH.
induction (VertexSet.elements interfgraph_vertices).
inversion HH.
cut (EqualSetMap (fold_left f' (a :: l) (VertexMap.empty VertexSet.t)) 
                 (f' (fold_left f' l (VertexMap.empty VertexSet.t)) a)). intro.
generalize (H0 x). clear H0. intro H0. inversion H0. subst.
set (tmp := fold_left f' l (VertexMap.empty VertexSet.t)) in *.
unfold f', f in H3.
destruct (Vertex.eq_dec x a).
simpl. rewrite MapFacts.in_find_iff.
rewrite MapFacts.add_eq_o in H3. congruence.
apply Regs.eq_sym. auto.
inversion HH; subst.
elim (n H4).
rewrite MapFacts.add_neq_o in H3. 
rewrite MapFacts.in_find_iff in IHl. rewrite <-H3 in IHl.
elim (IHl H4 (refl_equal _)).
auto.
simpl. rewrite MapFacts.in_find_iff. rewrite <-H1. congruence.

apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f', f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
auto.
auto.
Qed.


Lemma extremities_imap : forall x,
VertexMap.In x interf_map <-> 
VertexSet.In x interfgraph_vertices.

Proof.
split; intros.
unfold interf_map in H.
unfold set2map in H.
set (f := (fun (e : EdgeSet.elt) (m : VertexMap.t VertexSet.t) =>
          VertexMap.add (fst_ext e) (new_adj_set (fst_ext e) (snd_ext e) m)
            (VertexMap.add (snd_ext e)
               (new_adj_set (snd_ext e) (fst_ext e) m) m))) in *.
rewrite EdgeSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
cut (forall e, EdgeSet.In e interfgraph_interference_edges ->
               VertexSet.In (fst_ext e) interfgraph_vertices
               /\ VertexSet.In (snd_ext e) interfgraph_vertices). intro.

generalize EdgeSet.elements_2. intro HH.
generalize (HH interfgraph_interference_edges). clear HH. intro HH.

induction (EdgeSet.elements interfgraph_interference_edges). simpl in H.
apply (proj1 (vertices_empty_map x)). auto.

cut (EqualSetMap (fold_left f' (a :: l) empty_map) 
                 (f' (fold_left f' l empty_map ) a)). intro.
generalize (H1 x). clear H1. intro H1. inversion H1. subst.
simpl in H. rewrite MapFacts.in_find_iff in H. rewrite <-H3 in H.
elim H. auto.

set (tmp := fold_left f' l empty_map) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite e. apply (H0 a).
apply HH. left. apply E.eq_refl.
destruct (Regs.eq_dec x (snd_ext a)).
rewrite e. apply (H0 a).
apply HH. left. apply E.eq_refl.
apply IHl.
do 2 rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.in_find_iff. rewrite <-H3. congruence.
auto.
auto.
auto.

intros. apply HH. right. auto.

apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
intro. elim n. rewrite e. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite e. auto.
intro. elim n. rewrite e. auto.
apply (Regs.eq_sym e).
intro. elim n0. auto.
intro. elim n. auto.
apply (Regs.eq_sym e).
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Regs.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H1. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H1. auto.
intro. elim n0. rewrite H1. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H1. auto.
intro. elim n. rewrite H1. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
constructor.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H1. auto.
intro. elim n. rewrite H1. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold f'. unfold f. unfold EqualSetMap. intros.
destruct (Regs.eq_dec x0 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H1 (fst_ext a0)). intro.
inversion H2.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H1 (snd_ext a0)). intro.
inversion H2.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H2. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
intro. elim n0. rewrite H2. auto.
intro. elim n. rewrite H2. auto.
auto.
auto.

intros. apply extremities_interf_graph. right. auto.

rewrite <-vertices_empty_map in H.
unfold interf_map. unfold set2map.
set (f :=  (fun (e : EdgeSet.elt) (m : VertexMap.t VertexSet.t) =>
      VertexMap.add (fst_ext e) (new_adj_set (fst_ext e) (snd_ext e) m)
        (VertexMap.add (snd_ext e) (new_adj_set (snd_ext e) (fst_ext e) m) m))) in *.
rewrite EdgeSet.fold_1.
set (f' := fun e a => f a e) in *.
induction (EdgeSet.elements interfgraph_interference_edges). simpl. auto.
cut (EqualSetMap (fold_left f' (a :: l) empty_map) 
                 (f' (fold_left f' l empty_map) a)). intro.
generalize (H0 x). clear H0. intro H0. inversion H0. subst.
set (tmp := fold_left f' l empty_map) in *.
unfold f' in H3.  unfold f in H3.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite MapFacts.add_eq_o in H3. congruence.
apply (Regs.eq_sym e).
destruct (Vertex.eq_dec x (snd_ext a)).
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_eq_o in H3.
congruence.
apply (Regs.eq_sym e).
auto.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.in_find_iff in IHl. rewrite <-H3 in IHl.
congruence.
auto.
auto.

simpl. rewrite MapFacts.in_find_iff. rewrite <-H1. congruence.
apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
intro. elim n. rewrite e. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite e. auto.
intro. elim n. rewrite e. auto.
apply (Regs.eq_sym e).
intro. elim n0. auto.
intro. elim n. auto.
apply (Regs.eq_sym e).
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Regs.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H0. auto.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
constructor.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold f'. unfold f. unfold EqualSetMap. intros.
destruct (Regs.eq_dec x0 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (fst_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (snd_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H1. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
intro. elim n0. rewrite H1. auto.
intro. elim n. rewrite H1. auto.
auto.
auto.
Qed.

Lemma extremities_pmap : forall x,
VertexMap.In x pref_map <-> 
VertexSet.In x interfgraph_vertices.

Proof.
split; intros.
unfold pref_map in H.
unfold set2map in H.
set (f := (fun (e : EdgeSet.elt) (m : VertexMap.t VertexSet.t) =>
          VertexMap.add (fst_ext e) (new_adj_set (fst_ext e) (snd_ext e) m)
            (VertexMap.add (snd_ext e)
               (new_adj_set (snd_ext e) (fst_ext e) m) m))) in *.
rewrite EdgeSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
cut (forall e, EdgeSet.In e interfgraph_affinity_edges ->
               VertexSet.In (fst_ext e) interfgraph_vertices
               /\ VertexSet.In (snd_ext e) interfgraph_vertices). intro.

generalize EdgeSet.elements_2. intro HH.
generalize (HH interfgraph_affinity_edges). clear HH. intro HH.

induction (EdgeSet.elements interfgraph_affinity_edges). simpl in H.
apply (proj1 (vertices_empty_map x)). auto.

cut (EqualSetMap (fold_left f' (a :: l) empty_map) 
                 (f' (fold_left f' l empty_map) a)). intro.
generalize (H1 x). clear H1. intro H1. inversion H1. subst.
simpl in H. rewrite MapFacts.in_find_iff in H. rewrite <-H3 in H.
elim H. auto.

set (tmp := fold_left f' l empty_map) in *.
unfold f' in H3. unfold f in H3.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite e. apply (H0 a).
apply HH. left. apply E.eq_refl.
destruct (Regs.eq_dec x (snd_ext a)).
rewrite e. apply (H0 a).
apply HH. left. apply E.eq_refl.
apply IHl.
do 2 rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.in_find_iff. rewrite <-H3. congruence.
auto.
auto.
auto.

intros. apply HH. right. auto.

apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
intro. elim n. rewrite e. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite e. auto.
intro. elim n. rewrite e. auto.
apply (Regs.eq_sym e).
intro. elim n0. auto.
intro. elim n. auto.
apply (Regs.eq_sym e).
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Regs.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H1. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H1. auto.
intro. elim n0. rewrite H1. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H1. auto.
intro. elim n. rewrite H1. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
constructor.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H1. auto.
intro. elim n. rewrite H1. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold f'. unfold f. unfold EqualSetMap. intros.
destruct (Regs.eq_dec x0 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H1 (fst_ext a0)). intro.
inversion H2.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H1 (snd_ext a0)). intro.
inversion H2.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H2. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
intro. elim n0. rewrite H2. auto.
intro. elim n. rewrite H2. auto.
auto.
auto.

intros. apply extremities_interf_graph. left. auto.

rewrite <-vertices_empty_map in H.
unfold pref_map. unfold set2map.
set (f :=  (fun (e : EdgeSet.elt) (m : VertexMap.t VertexSet.t) =>
      VertexMap.add (fst_ext e) (new_adj_set (fst_ext e) (snd_ext e) m)
        (VertexMap.add (snd_ext e) (new_adj_set (snd_ext e) (fst_ext e) m) m))) in *.
rewrite EdgeSet.fold_1.
set (f' := fun e a => f a e) in *.
induction (EdgeSet.elements interfgraph_affinity_edges). simpl. auto.
cut (EqualSetMap (fold_left f' (a :: l) empty_map) 
                 (f' (fold_left f' l empty_map) a)). intro.
generalize (H0 x). clear H0. intro H0. inversion H0. subst.
set (tmp := fold_left f' l empty_map) in *.
unfold f' in H3.  unfold f in H3.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite MapFacts.add_eq_o in H3. congruence.
apply (Regs.eq_sym e).
destruct (Vertex.eq_dec x (snd_ext a)).
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_eq_o in H3.
congruence.
apply (Regs.eq_sym e).
auto.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.in_find_iff in IHl. rewrite <-H3 in IHl.
congruence.
auto.
auto.

simpl. rewrite MapFacts.in_find_iff. rewrite <-H1. congruence.
apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
intro. elim n. rewrite e. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite e. auto.
intro. elim n. rewrite e. auto.
apply (Regs.eq_sym e).
intro. elim n0. auto.
intro. elim n. auto.
apply (Regs.eq_sym e).
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Regs.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H0. auto.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (fst_ext y)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
constructor.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold f'. unfold f. unfold EqualSetMap. intros.
destruct (Regs.eq_dec x0 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (fst_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (snd_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H1. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
intro. elim n0. rewrite H1. auto.
intro. elim n. rewrite H1. auto.
auto.
auto.
Qed.

Lemma set2map_charac : forall x y s m,
VertexSet.In x (adj_set y (set2map s m)) ->
(exists w, EdgeSet.In (x,y,w) s) \/ VertexSet.In x (adj_set y m).

Proof.
intros.
unfold set2map in H.
set (f :=  (fun (e : EdgeSet.elt) (m : VertexMap.t VertexSet.t) =>
             VertexMap.add (fst_ext e)
               (new_adj_set (fst_ext e) (snd_ext e) m)
               (VertexMap.add (snd_ext e)
                  (new_adj_set (snd_ext e) (fst_ext e) m) m))) in *.
rewrite EdgeSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize EdgeSet.elements_2. intro HH.
generalize (HH s). clear HH. intro HH.
induction (EdgeSet.elements s). simpl in H. right. auto.
cut (EqualSetMap (fold_left f' (a :: l) m) 
                 (f' (fold_left f' l m) a)). intro.
generalize (H0 y). clear H0. intro H0. inversion H0. subst.
set (tmp := fold_left f' l m) in *.
unfold f', f in H3.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H3.
congruence.
apply Regs.eq_sym. auto.
destruct (Vertex.eq_dec y (snd_ext a)).
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_eq_o in H3.
congruence.
apply Regs.eq_sym. auto.
auto.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_neq_o in H3.
simpl in H. unfold adj_set in H. rewrite <-H2 in H.
elim (VertexSet.empty_1 H).
auto.
auto.
simpl in H. unfold adj_set in H. rewrite <-H1 in H.
rewrite H3 in H.
set (tmp := fold_left f' l m) in *.
unfold f', f in H2.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H2. inversion H2.
rewrite H5 in H.
unfold new_adj_set in H.
case_eq (VertexMap.find (fst_ext a) tmp); intros.
rewrite H4 in H.
destruct (Regs.eq_dec (snd_ext a) x).
left. exists (get_weight a).
apply HH. left.
fold (eq (x,y,get_weight a) a).
rewrite edge_comm. Eq_eq.
generalize (VertexSet.add_3 n H). intro.
apply IHl.
unfold adj_set. rewrite (MapFacts.find_o _ e).
rewrite H4. auto.
intros. apply HH. right. auto.
rewrite H4 in H.
left. exists (get_weight a).
apply HH. left.
fold (eq (x,y,get_weight a) a).
rewrite edge_comm. Eq_eq.
apply Regs.eq_sym. apply VertexSet.singleton_1. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H2.
destruct (Vertex.eq_dec y (snd_ext a)).
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
unfold new_adj_set in H.
case_eq (VertexMap.find (snd_ext a) tmp); intros.
rewrite H2 in H.
destruct (Vertex.eq_dec (fst_ext a) x).
left. exists (get_weight a).
apply HH. left.
fold (eq (x,y,get_weight a) a). Eq_eq.
apply IHl.
generalize (VertexSet.add_3 n0 H). intro.
unfold new_adj_set in H3. rewrite H2 in H3.
unfold adj_set. rewrite (MapFacts.find_o _ e). rewrite H2.
auto.
intros. apply HH. right. auto.
rewrite H2 in H.
left. exists (get_weight a).
apply HH. left.
fold (eq (x,y,get_weight a) a). Eq_eq.
apply Regs.eq_sym. apply VertexSet.singleton_1. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H2.
apply IHl.
unfold adj_set. rewrite <-H2. auto.
intros. apply HH. right. auto.
auto.
auto.

apply fold_left_assoc_map.
unfold f', f, EqualSetMap. intros.
destruct (Vertex.eq_dec x0 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x0 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x0 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x0 s0). apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x0 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H0. auto.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold EqualSetMap, f', f. intros.
destruct (Vertex.eq_dec x0 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (fst_ext a0)). intro.
inversion H1. apply VertexSet.eq_refl.
apply Props.Dec.F.add_m.
apply Regs.eq_refl.
auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (snd_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m.
apply Regs.eq_refl.
auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
auto.
auto.
auto.
auto.
Qed.

Lemma adj_set_empty : forall x,
VertexSet.Equal (adj_set x empty_map) VertexSet.empty.

Proof.
intros.
unfold empty_map.
set (f := (fun (x0 : VertexSet.elt) (m : VertexMap.t VertexSet.t) =>
      VertexMap.add x0 VertexSet.empty m)) in *.
rewrite VertexSet.fold_1.
set (f' := fun a e => f e a) in *.
induction (VertexSet.elements interfgraph_vertices).
simpl. unfold adj_set. simpl. reflexivity.
cut (EqualSetMap (fold_left f' (a :: l) (VertexMap.empty VertexSet.t)) 
                 (f' (fold_left f' l (VertexMap.empty VertexSet.t)) a)). intro.
generalize (H x). clear H. intro H. inversion H. subst.
set (tmp := fold_left f' l (VertexMap.empty VertexSet.t)) in *.
unfold f', f in H2.
destruct (Regs.eq_dec x a). rewrite MapFacts.add_eq_o in H2. congruence.
apply Regs.eq_sym. auto.
simpl. unfold adj_set. rewrite <-H1. apply VertexSet.eq_refl.
set (tmp := fold_left f' l (VertexMap.empty VertexSet.t)) in *.
unfold f', f in H1.
destruct (Regs.eq_dec x a). rewrite MapFacts.add_eq_o in H1.
unfold adj_set. simpl. rewrite <-H0. inversion H1.
rewrite H4 in H2. auto.
apply Regs.eq_sym. auto.
simpl. unfold adj_set. rewrite <-H0.
rewrite MapFacts.add_neq_o in H1.
unfold adj_set in IHl. rewrite <-H1 in IHl.
rewrite H2. auto.
auto.

apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 z).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 y).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.

unfold EqualSetMap. intros.
unfold f', f.
destruct (Vertex.eq_dec x0 a0).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor. apply VertexSet.eq_refl.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
auto.
auto.
Qed.

Lemma affinity_weights_interf_graph : 
forall e, EdgeSet.In e interfgraph_affinity_edges ->
get_weight e = Some N0.

Proof.
intros e H.
unfold interfgraph_affinity_edges in H.
generalize (proj1 (resolve_conflicts_2 _ _ _ H)). clear H. intro H.
destruct (EdgeSet.union_1 H).
unfold AE_reg_reg in H0.
rewrite SetRegReg.fold_1 in H0.
induction (SetRegReg.elements (pref_reg_reg g)).
simpl in H0. elim (EdgeSet.empty_1 H0).
rewrite MEdgeFacts.fold_left_assoc in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (Regs.reg_to_Reg (fst a), Regs.reg_to_Reg (snd a), Some N0) e) in H1.
rewrite <-(get_weight_m _ _ H1). auto.
apply IHl. assumption.
intros;apply RegRegProps.add_add.
intros;apply RegRegProps.Dec.F.add_m;[apply eq_refl|assumption].
unfold AE_reg_mreg in H0.
rewrite SetRegMreg.fold_1 in H0.
induction (SetRegMreg.elements (pref_reg_mreg g)).
simpl in H0. elim (EdgeSet.empty_1 H0).
rewrite MEdgeFacts.fold_left_assoc in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (Regs.reg_to_Reg (fst a), Regs.mreg_to_Reg (snd a), Some N0) e) in H1.
rewrite <-(get_weight_m _ _ H1). auto.
apply IHl. assumption.
intros;apply RegRegProps.add_add.
intros;apply RegRegProps.Dec.F.add_m;[apply eq_refl|assumption].
Qed.

Lemma interference_weights_interf_graph : 
forall e, EdgeSet.In e interfgraph_interference_edges ->
get_weight e = None.

Proof.
intros e H.
unfold interfgraph_affinity_edges in H.
destruct (EdgeSet.union_1 H).
unfold IE_reg_reg in H0.
rewrite SetRegReg.fold_1 in H0.
induction (SetRegReg.elements (interf_reg_reg g)).
simpl in H0. elim (EdgeSet.empty_1 H0).
rewrite MEdgeFacts.fold_left_assoc in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (Regs.reg_to_Reg (fst a), Regs.reg_to_Reg (snd a), Some N0) e) in H1.
rewrite <-(get_weight_m _ _ H1). auto.
apply IHl. assumption.
intros;apply RegRegProps.add_add.
intros;apply RegRegProps.Dec.F.add_m;[apply eq_refl|assumption].
unfold IE_reg_mreg in H0.
rewrite SetRegMreg.fold_1 in H0.
induction (SetRegMreg.elements (interf_reg_mreg g)).
simpl in H0. elim (EdgeSet.empty_1 H0).
rewrite MEdgeFacts.fold_left_assoc in H0.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H0).
fold (eq (Regs.reg_to_Reg (fst a), Regs.mreg_to_Reg (snd a), Some N0) e) in H1.
rewrite <-(get_weight_m _ _ H1). auto.
apply IHl. assumption.
intros;apply RegRegProps.add_add.
intros;apply RegRegProps.Dec.F.add_m;[apply eq_refl|assumption].
Qed.

Lemma simple_graph : forall  x y,
       VertexSet.In x (adj_set y interf_map ) /\
       VertexSet.In x (adj_set y pref_map ) -> False.

Proof.
intros. destruct H.
unfold interf_map in H.
generalize (set2map_charac x y interfgraph_interference_edges empty_map H).
clear H. intro H. destruct H. destruct H.
unfold pref_map in H0.
generalize (set2map_charac x y interfgraph_affinity_edges empty_map H0).
clear H0. intro H0. destruct H0. destruct H0.
generalize (resolve_conflicts_2 (x,y,x1) _ _ H0). intro.
destruct H1. elim H2.
change_rewrite.
generalize (interference_weights_interf_graph (x,y,x0) H). simpl. intro.
rewrite H3 in H. assumption.
rewrite adj_set_empty in H0. elim (VertexSet.empty_1 H0).
rewrite adj_set_empty in H. elim (VertexSet.empty_1 H).
Qed.

Lemma sym_imap : forall x y,
      VertexSet.In x (adj_set y interf_map ) ->
      VertexSet.In y (adj_set x interf_map).

Proof.
intros.
unfold interf_map, set2map in *.
set (f := (fun (e : EdgeSet.elt) (m : VertexMap.t VertexSet.t) =>
         VertexMap.add (fst_ext e) (new_adj_set (fst_ext e) (snd_ext e) m)
           (VertexMap.add (snd_ext e) (new_adj_set (snd_ext e) (fst_ext e) m)
              m))) in *.
rewrite EdgeSet.fold_1. rewrite EdgeSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
induction (EdgeSet.elements interfgraph_interference_edges).
simpl in H.
rewrite adj_set_empty in H. elim (VertexSet.empty_1 H).
cut (EqualSetMap (fold_left f' (a :: l) empty_map)
                 (f' (fold_left f' l empty_map) a)). intro.
generalize (H0 y). intro. inversion H1. simpl in *.
unfold adj_set in H. rewrite <-H3 in H.
elim (VertexSet.empty_1 H).
set (tmp := fold_left f' l empty_map) in *.
unfold f', f in H3.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H3.
unfold adj_set in H. simpl in H. rewrite <-H2 in H.
inversion H3. subst. clear H3.
rewrite H4 in H.
unfold new_adj_set in H.
generalize (H0 x). intro. inversion H3. subst.
unfold f', f in H7.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite MapFacts.add_eq_o in H7. congruence.
apply Regs.eq_sym. auto.
destruct (Vertex.eq_dec (snd_ext a) x).
rewrite MapFacts.add_neq_o in H7. rewrite MapFacts.add_eq_o in H7.
congruence.
apply Regs.eq_sym. auto.
auto.
rewrite MapFacts.add_neq_o in H7.
rewrite MapFacts.add_neq_o in H7.
case_eq (VertexMap.find (fst_ext a) tmp); intros; rewrite H5 in H.
generalize (VertexSet.add_3 n0 H). clear H. intro H.
assert (VertexSet.In y (adj_set x tmp)).
apply IHl. unfold adj_set. rewrite (MapFacts.find_o _ e).
rewrite H5. auto.
unfold adj_set in H8. rewrite <-H7 in H8. elim (VertexSet.empty_1 H8).
elim (n0 (VertexSet.singleton_1 H)).
auto.
auto.

simpl. unfold adj_set. rewrite <-H5.
rewrite H7.
unfold f', f in H6.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite MapFacts.add_eq_o in H6.
inversion H6. subst. clear H6.
unfold new_adj_set. case_eq (VertexMap.find (fst_ext a) tmp); intros.
rewrite H6 in H.
destruct (Vertex.eq_dec y (snd_ext a)).
apply VertexSet.add_1. apply Regs.eq_sym. auto.
apply VertexSet.add_2.
assert (VertexSet.In y (adj_set x tmp)).
apply IHl. unfold adj_set.
rewrite (MapFacts.find_o _ e).
rewrite H6. 
destruct (Vertex.eq_dec (snd_ext a) x).
elim n. rewrite e. rewrite <-e0. apply Regs.eq_sym. auto.
apply (VertexSet.add_3 n0 H).
unfold adj_set in H8.
rewrite (MapFacts.find_o _ e0) in H8. rewrite H6 in H8. auto.
rewrite H6 in H.
rewrite e. rewrite <-e0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H6.
destruct (Vertex.eq_dec (snd_ext a) x).
rewrite MapFacts.add_eq_o in H6.
inversion H6. subst. clear H6.
unfold new_adj_set.
destruct (VertexMap.find (snd_ext a) tmp).
apply VertexSet.add_1.
apply Regs.eq_sym. auto.
apply VertexSet.singleton_2. apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H6.
clear H0 H1.
assert (VertexSet.In y (adj_set x tmp)).
apply IHl.
unfold adj_set. rewrite (MapFacts.find_o _ e).
case_eq (VertexMap.find (fst_ext a) tmp); intros.
rewrite H0 in H.
apply (VertexSet.add_3 n0 H).
rewrite H0 in H. elim (n0 (VertexSet.singleton_1 H)).
unfold adj_set in H0. rewrite <-H6 in H0. auto.
auto.
auto.
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o in H3.
destruct (Vertex.eq_dec y (snd_ext a)).
rewrite MapFacts.add_eq_o in H3.
unfold adj_set in H. simpl in H. rewrite <-H2 in H.
rewrite H4 in H.
inversion H3. subst. clear H3.
unfold new_adj_set in H.
case_eq (VertexMap.find (snd_ext a) tmp); intros.
rewrite H3 in H.
destruct (Vertex.eq_dec (fst_ext a) x).
unfold adj_set. simpl.
generalize (H0 x). clear H0. intro. inversion H0.
unfold f',f in H7.
rewrite MapFacts.add_eq_o in H7.
congruence.
apply Regs.eq_sym. auto.
unfold f', f in H6.
rewrite MapFacts.add_eq_o in H6. inversion H6. subst. clear H6.
rewrite H7.
unfold new_adj_set in H4. rewrite H3 in H4.
unfold new_adj_set.
destruct (VertexMap.find (fst_ext a) tmp).
apply VertexSet.add_1. apply Regs.eq_sym. auto.
apply VertexSet.singleton_2. apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
unfold adj_set. simpl.
generalize (H0 x). clear H0. intro. inversion H0.
unfold f',f in H7.
rewrite MapFacts.add_neq_o in H7.
destruct (Vertex.eq_dec (snd_ext a) x).
rewrite MapFacts.add_eq_o in H7. congruence. auto.
rewrite MapFacts.add_neq_o in H7.
unfold adj_set in IHl. rewrite <-H7 in IHl. apply IHl.
rewrite (MapFacts.find_o _ e). rewrite H3.
apply (VertexSet.add_3 n0 H).
auto.
auto.
unfold f', f in H6.
rewrite MapFacts.add_neq_o in H6.
destruct (Vertex.eq_dec x (snd_ext a)).
rewrite MapFacts.add_eq_o in H6. inversion H6. subst. clear H6.
rewrite H7.
unfold new_adj_set. rewrite H3.
apply VertexSet.add_2.
unfold adj_set in IHl. rewrite <-(MapFacts.find_o _ e0) in H3.
rewrite H3 in IHl. apply IHl.
rewrite (MapFacts.find_o _ e). rewrite <-(MapFacts.find_o _ e0).
rewrite H3.
apply (VertexSet.add_3 n0 H).
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H6.
rewrite H7.
unfold adj_set in IHl. rewrite <-H6 in IHl.
apply IHl. rewrite (MapFacts.find_o _ e).
rewrite H3. 
apply (VertexSet.add_3 n0 H).
auto.
auto.
rewrite H3 in H.
generalize (H0 x). intro. inversion H5. subst.
unfold f',f in H8.
rewrite MapFacts.add_eq_o in H8.
congruence.
apply VertexSet.singleton_1. auto.
unfold f', f in H7.
rewrite MapFacts.add_eq_o in H7.
inversion H7. subst. clear H7.
simpl. unfold adj_set. rewrite <-H6.
rewrite H8. unfold new_adj_set.
destruct (VertexMap.find (fst_ext a) tmp).
apply VertexSet.add_1. apply Regs.eq_sym. auto.
apply VertexSet.singleton_2. apply Regs.eq_sym. auto.
apply (VertexSet.singleton_1 H).
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o in H3.
generalize (H0 x). intro. inversion H5. subst.
unfold f', f in H8.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite MapFacts.add_eq_o in H8.
congruence.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H8.
destruct (Vertex.eq_dec x (snd_ext a)).
rewrite MapFacts.add_eq_o in H8.
congruence.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H8.
simpl in H. unfold adj_set in H. rewrite <-H2 in H.
unfold adj_set in IHl.
assert (VertexSet.In y VertexSet.empty).
rewrite <-H8 in IHl. apply IHl.
rewrite <-H3. rewrite <-H4. auto.
elim (VertexSet.empty_1 H6).
auto.
auto.
unfold f',f in H7.
destruct (Vertex.eq_dec (fst_ext a) x).
rewrite MapFacts.add_eq_o in H7.
inversion H7. subst. clear H7.
unfold adj_set. simpl. rewrite <-H6.
rewrite H8.
unfold new_adj_set.
simpl in H. unfold adj_set in H. rewrite <-H2 in H.
case_eq (VertexMap.find (fst_ext a) tmp); intros.
unfold adj_set in IHl.
rewrite <-(MapFacts.find_o _ e) in IHl.
rewrite H7 in IHl.
apply VertexSet.add_2. apply IHl.
rewrite <-H3. rewrite <-H4. auto.
assert (VertexSet.In y VertexSet.empty).
unfold adj_set in IHl. rewrite (MapFacts.find_o _ e) in H7.
rewrite H7 in IHl. apply IHl.
rewrite <-H3. rewrite <-H4. auto.
elim (VertexSet.empty_1 H9).
auto.
rewrite MapFacts.add_neq_o in H7.
destruct (Vertex.eq_dec (snd_ext a) x).
rewrite MapFacts.add_eq_o in H7.
inversion H7. subst. clear H7.
simpl. unfold adj_set. rewrite <-H6.
rewrite H8. unfold new_adj_set.
simpl in H. unfold adj_set in H. rewrite <-H2 in H.
rewrite (MapFacts.find_o _ e).
unfold adj_set in IHl.
case_eq (VertexMap.find x tmp); intros.
rewrite H7 in IHl.
apply VertexSet.add_2.
apply IHl.
rewrite <-H3. rewrite <-H4. auto.
assert (VertexSet.In y VertexSet.empty).
unfold adj_set in IHl. rewrite H7 in IHl.
apply IHl. rewrite <-H3. rewrite <-H4. auto.
elim (VertexSet.empty_1 H9).
auto.
rewrite MapFacts.add_neq_o in H7.
simpl. unfold adj_set. rewrite <-H6.
rewrite H8.
unfold adj_set in IHl. rewrite <-H7 in IHl. rewrite <-H3 in IHl.
apply IHl. rewrite <-H4. simpl in H. unfold adj_set in H. rewrite <-H2 in H. auto.
auto.
auto.
auto.
auto.

apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
intro. elim n. rewrite e. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite e. auto.
intro. elim n. rewrite e. auto.
apply (Regs.eq_sym e).
intro. elim n0. auto.
intro. elim n. auto.
apply (Regs.eq_sym e).
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Regs.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H0. auto.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
constructor.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold f'. unfold f. unfold EqualSetMap. intros.
destruct (Regs.eq_dec x0 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (fst_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (snd_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H1. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
intro. elim n0. rewrite H1. auto.
intro. elim n. rewrite H1. auto.
auto.
auto.
Qed.

Lemma sym_pmap : forall x y,
      VertexSet.In x (adj_set y pref_map) ->
      VertexSet.In y (adj_set x pref_map).

Proof.
intros.
unfold pref_map, set2map in *.
set (f := (fun (e : EdgeSet.elt) (m : VertexMap.t VertexSet.t) =>
         VertexMap.add (fst_ext e) (new_adj_set (fst_ext e) (snd_ext e) m)
           (VertexMap.add (snd_ext e) (new_adj_set (snd_ext e) (fst_ext e) m)
              m))) in *.
rewrite EdgeSet.fold_1. rewrite EdgeSet.fold_1 in H.
set (f' := fun a e => f e a) in *.
induction (EdgeSet.elements interfgraph_affinity_edges).
simpl in H.
rewrite adj_set_empty in H. elim (VertexSet.empty_1 H).
cut (EqualSetMap (fold_left f' (a :: l) empty_map)
                 (f' (fold_left f' l empty_map) a)). intro.
generalize (H0 y). intro. inversion H1. simpl in *.
unfold adj_set in H. rewrite <-H3 in H.
elim (VertexSet.empty_1 H).
set (tmp := fold_left f' l empty_map) in *.
unfold f', f in H3.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H3.
unfold adj_set in H. simpl in H. rewrite <-H2 in H.
inversion H3. subst. clear H3.
rewrite H4 in H.
unfold new_adj_set in H.
generalize (H0 x). intro. inversion H3. subst.
unfold f', f in H7.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite MapFacts.add_eq_o in H7. congruence.
apply Regs.eq_sym. auto.
destruct (Vertex.eq_dec (snd_ext a) x).
rewrite MapFacts.add_neq_o in H7. rewrite MapFacts.add_eq_o in H7.
congruence.
apply Regs.eq_sym. auto.
auto.
rewrite MapFacts.add_neq_o in H7.
rewrite MapFacts.add_neq_o in H7.
case_eq (VertexMap.find (fst_ext a) tmp); intros; rewrite H5 in H.
generalize (VertexSet.add_3 n0 H). clear H. intro H.
assert (VertexSet.In y (adj_set x tmp)).
apply IHl. unfold adj_set. rewrite (MapFacts.find_o _ e).
rewrite H5. auto.
unfold adj_set in H8. rewrite <-H7 in H8. elim (VertexSet.empty_1 H8).
elim (n0 (VertexSet.singleton_1 H)).
auto.
auto.

simpl. unfold adj_set. rewrite <-H5.
rewrite H7.
unfold f', f in H6.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite MapFacts.add_eq_o in H6.
inversion H6. subst. clear H6.
unfold new_adj_set. case_eq (VertexMap.find (fst_ext a) tmp); intros.
rewrite H6 in H.
destruct (Vertex.eq_dec y (snd_ext a)).
apply VertexSet.add_1. apply Regs.eq_sym. auto.
apply VertexSet.add_2.
assert (VertexSet.In y (adj_set x tmp)).
apply IHl. unfold adj_set.
rewrite (MapFacts.find_o _ e).
rewrite H6. 
destruct (Vertex.eq_dec (snd_ext a) x).
elim n. rewrite e. rewrite <-e0. apply Regs.eq_sym. auto.
apply (VertexSet.add_3 n0 H).
unfold adj_set in H8.
rewrite (MapFacts.find_o _ e0) in H8. rewrite H6 in H8. auto.
rewrite H6 in H.
rewrite e. rewrite <-e0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H6.
destruct (Vertex.eq_dec (snd_ext a) x).
rewrite MapFacts.add_eq_o in H6.
inversion H6. subst. clear H6.
unfold new_adj_set.
destruct (VertexMap.find (snd_ext a) tmp).
apply VertexSet.add_1.
apply Regs.eq_sym. auto.
apply VertexSet.singleton_2. apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H6.
clear H0 H1.
assert (VertexSet.In y (adj_set x tmp)).
apply IHl.
unfold adj_set. rewrite (MapFacts.find_o _ e).
case_eq (VertexMap.find (fst_ext a) tmp); intros.
rewrite H0 in H.
apply (VertexSet.add_3 n0 H).
rewrite H0 in H. elim (n0 (VertexSet.singleton_1 H)).
unfold adj_set in H0. rewrite <-H6 in H0. auto.
auto.
auto.
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o in H3.
destruct (Vertex.eq_dec y (snd_ext a)).
rewrite MapFacts.add_eq_o in H3.
unfold adj_set in H. simpl in H. rewrite <-H2 in H.
rewrite H4 in H.
inversion H3. subst. clear H3.
unfold new_adj_set in H.
case_eq (VertexMap.find (snd_ext a) tmp); intros.
rewrite H3 in H.
destruct (Vertex.eq_dec (fst_ext a) x).
unfold adj_set. simpl.
generalize (H0 x). clear H0. intro. inversion H0.
unfold f',f in H7.
rewrite MapFacts.add_eq_o in H7.
congruence.
apply Regs.eq_sym. auto.
unfold f', f in H6.
rewrite MapFacts.add_eq_o in H6. inversion H6. subst. clear H6.
rewrite H7.
unfold new_adj_set in H4. rewrite H3 in H4.
unfold new_adj_set.
destruct (VertexMap.find (fst_ext a) tmp).
apply VertexSet.add_1. apply Regs.eq_sym. auto.
apply VertexSet.singleton_2. apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
unfold adj_set. simpl.
generalize (H0 x). clear H0. intro. inversion H0.
unfold f',f in H7.
rewrite MapFacts.add_neq_o in H7.
destruct (Vertex.eq_dec (snd_ext a) x).
rewrite MapFacts.add_eq_o in H7. congruence. auto.
rewrite MapFacts.add_neq_o in H7.
unfold adj_set in IHl. rewrite <-H7 in IHl. apply IHl.
rewrite (MapFacts.find_o _ e). rewrite H3.
apply (VertexSet.add_3 n0 H).
auto.
auto.
unfold f', f in H6.
rewrite MapFacts.add_neq_o in H6.
destruct (Vertex.eq_dec x (snd_ext a)).
rewrite MapFacts.add_eq_o in H6. inversion H6. subst. clear H6.
rewrite H7.
unfold new_adj_set. rewrite H3.
apply VertexSet.add_2.
unfold adj_set in IHl. rewrite <-(MapFacts.find_o _ e0) in H3.
rewrite H3 in IHl. apply IHl.
rewrite (MapFacts.find_o _ e). rewrite <-(MapFacts.find_o _ e0).
rewrite H3.
apply (VertexSet.add_3 n0 H).
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H6.
rewrite H7.
unfold adj_set in IHl. rewrite <-H6 in IHl.
apply IHl. rewrite (MapFacts.find_o _ e).
rewrite H3. 
apply (VertexSet.add_3 n0 H).
auto.
auto.
rewrite H3 in H.
generalize (H0 x). intro. inversion H5. subst.
unfold f',f in H8.
rewrite MapFacts.add_eq_o in H8.
congruence.
apply VertexSet.singleton_1. auto.
unfold f', f in H7.
rewrite MapFacts.add_eq_o in H7.
inversion H7. subst. clear H7.
simpl. unfold adj_set. rewrite <-H6.
rewrite H8. unfold new_adj_set.
destruct (VertexMap.find (fst_ext a) tmp).
apply VertexSet.add_1. apply Regs.eq_sym. auto.
apply VertexSet.singleton_2. apply Regs.eq_sym. auto.
apply (VertexSet.singleton_1 H).
apply Regs.eq_sym. auto.

rewrite MapFacts.add_neq_o in H3.
generalize (H0 x). intro. inversion H5. subst.
unfold f', f in H8.
destruct (Vertex.eq_dec x (fst_ext a)).
rewrite MapFacts.add_eq_o in H8.
congruence.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H8.
destruct (Vertex.eq_dec x (snd_ext a)).
rewrite MapFacts.add_eq_o in H8.
congruence.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H8.
simpl in H. unfold adj_set in H. rewrite <-H2 in H.
unfold adj_set in IHl.
assert (VertexSet.In y VertexSet.empty).
rewrite <-H8 in IHl. apply IHl.
rewrite <-H3. rewrite <-H4. auto.
elim (VertexSet.empty_1 H6).
auto.
auto.
unfold f',f in H7.
destruct (Vertex.eq_dec (fst_ext a) x).
rewrite MapFacts.add_eq_o in H7.
inversion H7. subst. clear H7.
unfold adj_set. simpl. rewrite <-H6.
rewrite H8.
unfold new_adj_set.
simpl in H. unfold adj_set in H. rewrite <-H2 in H.
case_eq (VertexMap.find (fst_ext a) tmp); intros.
unfold adj_set in IHl.
rewrite <-(MapFacts.find_o _ e) in IHl.
rewrite H7 in IHl.
apply VertexSet.add_2. apply IHl.
rewrite <-H3. rewrite <-H4. auto.
assert (VertexSet.In y VertexSet.empty).
unfold adj_set in IHl. rewrite (MapFacts.find_o _ e) in H7.
rewrite H7 in IHl. apply IHl.
rewrite <-H3. rewrite <-H4. auto.
elim (VertexSet.empty_1 H9).
auto.
rewrite MapFacts.add_neq_o in H7.
destruct (Vertex.eq_dec (snd_ext a) x).
rewrite MapFacts.add_eq_o in H7.
inversion H7. subst. clear H7.
simpl. unfold adj_set. rewrite <-H6.
rewrite H8. unfold new_adj_set.
simpl in H. unfold adj_set in H. rewrite <-H2 in H.
rewrite (MapFacts.find_o _ e).
unfold adj_set in IHl.
case_eq (VertexMap.find x tmp); intros.
rewrite H7 in IHl.
apply VertexSet.add_2.
apply IHl.
rewrite <-H3. rewrite <-H4. auto.
assert (VertexSet.In y VertexSet.empty).
unfold adj_set in IHl. rewrite H7 in IHl.
apply IHl. rewrite <-H3. rewrite <-H4. auto.
elim (VertexSet.empty_1 H9).
auto.
rewrite MapFacts.add_neq_o in H7.
simpl. unfold adj_set. rewrite <-H6.
rewrite H8.
unfold adj_set in IHl. rewrite <-H7 in IHl. rewrite <-H3 in IHl.
apply IHl. rewrite <-H4. simpl in H. unfold adj_set in H. rewrite <-H2 in H. auto.
auto.
auto.
auto.
auto.

apply fold_left_assoc_map.
intros.
unfold f'. unfold f.
unfold EqualSetMap. intro.
destruct (Vertex.eq_dec x0 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
intro. elim n. rewrite e. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite e. auto.
intro. elim n. rewrite e. auto.
apply (Regs.eq_sym e).
intro. elim n0. auto.
intro. elim n. auto.
apply (Regs.eq_sym e).
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Regs.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite (MapFacts.find_o _ (Regs.eq_sym e)).
rewrite (MapFacts.find_o _ (Regs.eq_sym e0)).
destruct (VertexMap.find x0 s).
apply Props.add_add.
do 2 rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. auto.
rewrite <-e0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H0. auto.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
constructor.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s).
constructor. apply VertexSet.eq_refl.
constructor.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold f'. unfold f. unfold EqualSetMap. intros.
destruct (Regs.eq_dec x0 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (fst_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Regs.eq_dec x0 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (snd_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m. apply Regs.eq_refl. auto.
apply Regs.eq_sym. auto.
intro. elim n. rewrite H1. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
intro. elim n0. rewrite H1. auto.
intro. elim n. rewrite H1. auto.
auto.
auto.
Qed.

Lemma set_reg_reg_diff_ext : forall x g,
SetRegReg.In x (interf_reg_reg g) \/
SetRegReg.In x (pref_reg_reg g) -> fst x <> snd x.

Proof.
Admitted.

Lemma IE_reg_reg_diff : forall x y w,
EdgeSet.In (x,y,w) IE_reg_reg -> ~Vertex.eq x y.

Proof.
intros.
unfold IE_reg_reg in H.
set (f :=  (fun (e : SetRegReg.elt) (s : EdgeSet.t) =>
          EdgeSet.add
            (Regs.reg_to_Reg (fst e), Regs.reg_to_Reg (snd e), None) s)) in *.
rewrite SetRegReg.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize SetRegReg.elements_2. intro HH.
generalize (HH (interf_reg_reg g)). clear HH. intro HH.
induction (SetRegReg.elements (interf_reg_reg g)). simpl in H.
elim (EdgeSet.empty_1 H).
rewrite MEdgeFacts.fold_left_assoc in H.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f', f in H.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H).
fold (eq (Regs.reg_to_Reg (fst a), Regs.reg_to_Reg (snd a), None) (x,y,w)) in H0.
destruct (eq_charac _ _ H0); change_rewrite; destruct H1.
assert (fst a <> snd a).
apply set_reg_reg_diff_ext with (g:=g).
left. apply HH.
left. auto.
intro. rewrite <-H1 in H4. rewrite <-H2 in H4.
inversion H4. subst. elim (H3 H7).
assert (fst a <> snd a).
apply set_reg_reg_diff_ext with (g:=g).
left. apply HH.
left. auto.
intro. rewrite <-H1 in H4. rewrite <-H2 in H4.
inversion H4. subst. elim H3. auto.
apply IHl. auto.

intros. apply HH. right. auto.

unfold f', f. intros.
apply RegRegProps.add_add.

unfold f', f. intros.
apply RegRegProps.Dec.F.add_m. apply E.eq_refl. auto.
Qed.

Lemma IE_reg_mreg_diff : forall x y w,
EdgeSet.In (x,y,w) IE_reg_mreg -> ~Vertex.eq x y.

Proof.
intros.
unfold IE_reg_mreg in H.
set (f :=  (fun (e : SetRegMreg.elt) (s : EdgeSet.t) =>
          EdgeSet.add
            (Regs.reg_to_Reg (fst e), Regs.mreg_to_Reg (snd e), None) s)) in *.
rewrite SetRegMreg.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize SetRegMreg.elements_2. intro HH.
generalize (HH (interf_reg_mreg g)). clear HH. intro HH.
induction (SetRegMreg.elements (interf_reg_mreg g)). simpl in H.
elim (EdgeSet.empty_1 H).
rewrite MEdgeFacts.fold_left_assoc in H.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f', f in H.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H).
fold (eq (Regs.reg_to_Reg (fst a), Regs.mreg_to_Reg (snd a), None) (x,y,w)) in H0.
destruct (eq_charac _ _ H0); change_rewrite; destruct H1.
intro. rewrite <-H1 in H3. rewrite <-H2 in H3. inversion H3.
intro. rewrite <-H1 in H3. rewrite <-H2 in H3. inversion H3.
apply IHl. auto.

intros. apply HH. right. auto.

unfold f', f. intros.
apply RegRegProps.add_add.

unfold f', f. intros.
apply RegRegProps.Dec.F.add_m. apply E.eq_refl. auto.
Qed.

Lemma AE_reg_reg_diff : forall x y w,
EdgeSet.In (x,y,w) AE_reg_reg -> ~Vertex.eq x y.

Proof.
intros.
unfold AE_reg_reg in H.
set (f :=  (fun (e : SetRegReg.elt) (s : EdgeSet.t) =>
          EdgeSet.add
            (Regs.reg_to_Reg (fst e), Regs.reg_to_Reg (snd e), Some N0) s)) in *.
rewrite SetRegReg.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize SetRegReg.elements_2. intro HH.
generalize (HH (pref_reg_reg g)). clear HH. intro HH.
induction (SetRegReg.elements (pref_reg_reg g)). simpl in H.
elim (EdgeSet.empty_1 H).
rewrite MEdgeFacts.fold_left_assoc in H.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f', f in H.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H).
fold (eq (Regs.reg_to_Reg (fst a), Regs.reg_to_Reg (snd a), None) (x,y,w)) in H0.
destruct (eq_charac _ _ H0); change_rewrite; destruct H1.
assert (fst a <> snd a).
apply set_reg_reg_diff_ext with (g:=g).
right. apply HH.
left. auto.
intro. rewrite <-H1 in H4. rewrite <-H2 in H4.
inversion H4. subst. elim (H3 H7).
assert (fst a <> snd a).
apply set_reg_reg_diff_ext with (g:=g).
right. apply HH.
left. auto.
intro. rewrite <-H1 in H4. rewrite <-H2 in H4.
inversion H4. subst. elim H3. auto.
apply IHl. auto.

intros. apply HH. right. auto.

unfold f', f. intros.
apply RegRegProps.add_add.

unfold f', f. intros.
apply RegRegProps.Dec.F.add_m. apply E.eq_refl. auto.
Qed.

Lemma AE_reg_mreg_diff : forall x y w,
EdgeSet.In (x,y,w) AE_reg_mreg -> ~Vertex.eq x y.

Proof.
intros.
unfold AE_reg_mreg in H.
set (f :=  (fun (e : SetRegMreg.elt) (s : EdgeSet.t) =>
          EdgeSet.add
            (Regs.reg_to_Reg (fst e), Regs.mreg_to_Reg (snd e), Some N0) s)) in *.
rewrite SetRegMreg.fold_1 in H.
set (f' := fun a e => f e a) in *.
generalize SetRegMreg.elements_2. intro HH.
generalize (HH (pref_reg_mreg g)). clear HH. intro HH.
induction (SetRegMreg.elements (pref_reg_mreg g)). simpl in H.
elim (EdgeSet.empty_1 H).
rewrite MEdgeFacts.fold_left_assoc in H.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f', f in H.
destruct (proj1 (RegRegProps.Dec.F.add_iff _ _ _) H).
fold (eq (Regs.reg_to_Reg (fst a), Regs.mreg_to_Reg (snd a), None) (x,y,w)) in H0.
destruct (eq_charac _ _ H0); change_rewrite; destruct H1.
intro. rewrite <-H1 in H3. rewrite <-H2 in H3. inversion H3.
intro. rewrite <-H1 in H3. rewrite <-H2 in H3. inversion H3.
apply IHl. auto.

intros. apply HH. right. auto.

unfold f', f. intros.
apply RegRegProps.add_add.

unfold f', f. intros.
apply RegRegProps.Dec.F.add_m. apply E.eq_refl. auto.
Qed.

Lemma not_eq_extremities : forall x y, 
VertexSet.In x (adj_set y interf_map) \/ VertexSet.In x (adj_set y pref_map) ->
~Vertex.eq x y.

Proof.
intros.
destruct H.
generalize (set2map_charac _ _ _ _ H). intro.
destruct H0. destruct H0.
unfold interfgraph_interference_edges in H0.
destruct (EdgeSet.union_1 H0).
apply (IE_reg_reg_diff x y x0 H1).
apply (IE_reg_mreg_diff x y x0 H1).
rewrite adj_set_empty in H0. elim (VertexSet.empty_1 H0).
generalize (set2map_charac _ _ _ _ H). intro.
destruct H0. destruct H0.
unfold interfgraph_affinity_edges in H0.
generalize (resolve_conflicts_2 _ _ _ H0). intro.
clear H0. destruct H1 as [H0 _].
destruct (EdgeSet.union_1 H0).
apply (AE_reg_reg_diff x y x0 H1).
apply (AE_reg_mreg_diff x y x0 H1).
rewrite adj_set_empty in H0. elim (VertexSet.empty_1 H0).
Qed.

Definition graph_translation : new_graph :=
let vert := interfgraph_vertices in
let iedges := interfgraph_interference_edges in
let aedges := resolve_conflicts (EdgeSet.union AE_reg_reg AE_reg_mreg) iedges in
let emp := VertexSet.fold 
               (fun x m => VertexMap.add x VertexSet.empty m)
               vert  
               (VertexMap.empty VertexSet.t) in
let im := set2map iedges emp in
let pm := set2map aedges emp in
Make_Graph
           vert im pm
           extremities_imap
           extremities_pmap
           simple_graph
           sym_imap
           sym_pmap
           not_eq_extremities.

Lemma set2map_charac_2 : forall x y s m,
(exists w, EdgeSet.In (x,y,w) s) \/ VertexSet.In x (adj_set y m) ->
VertexSet.In x (adj_set y (set2map s m)).

Proof.
intros.
unfold set2map.
set (f :=  (fun (e : EdgeSet.elt) (m : VertexMap.t VertexSet.t) =>
             VertexMap.add (fst_ext e)
               (new_adj_set (fst_ext e) (snd_ext e) m)
               (VertexMap.add (snd_ext e)
                  (new_adj_set (snd_ext e) (fst_ext e) m) m))) in *.
rewrite EdgeSet.fold_1.
set (f' := fun a e => f e a) in *.
destruct H. destruct H.
generalize EdgeSet.elements_1. intro HH.
generalize (HH s (x,y,x0) H). clear HH. intro HH.
induction (EdgeSet.elements s).
inversion HH.
cut (EqualSetMap (fold_left f' (a :: l) m) 
                 (f' (fold_left f' l m) a)). intro.
generalize (H0 y). clear H0. intro H0. inversion H0. subst.
set (tmp := fold_left f' l m) in *.
unfold f', f in H3.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H3.
congruence.
apply Regs.eq_sym. auto.
destruct (Vertex.eq_dec y (snd_ext a)).
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_eq_o in H3.
congruence.
apply Regs.eq_sym. auto.
auto.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_neq_o in H3.
inversion HH; subst.
destruct (eq_charac _ _ H4); change_rewrite; destruct H4; destruct H1.
elim (n0 H6).
elim (n H6).
unfold adj_set in IHl. rewrite <-H3 in IHl.
elim (VertexSet.empty_1 (IHl H4)).
auto.
auto.

set (tmp := fold_left f' l m) in *.
unfold adj_set. simpl. rewrite <-H1. rewrite H3.
unfold f',f in H2.
inversion HH; subst.
destruct (eq_charac _ _ H5); change_rewrite; destruct H4.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
unfold new_adj_set.
destruct (VertexMap.find (fst_ext a) tmp).
apply VertexSet.add_1. rewrite H4. rewrite <-H6. rewrite <-e. apply Regs.eq_refl.
apply VertexSet.singleton_2. rewrite H4. rewrite <-H6. rewrite <-e. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H2.
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
unfold new_adj_set. destruct (VertexMap.find (snd_ext a) tmp).
apply VertexSet.add_1. apply Regs.eq_sym. auto.
apply VertexSet.singleton_2. apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
auto.
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
unfold new_adj_set. destruct (VertexMap.find (fst_ext a) tmp).
apply VertexSet.add_1. apply Regs.eq_sym. auto.
apply VertexSet.singleton_2. apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
unfold new_adj_set.
rewrite <-(MapFacts.find_o _ e).
case_eq (VertexMap.find y tmp); intros.
apply VertexSet.add_2.
unfold adj_set in IHl. rewrite H2 in IHl.
apply IHl. auto.
assert (VertexSet.In x VertexSet.empty).
unfold adj_set in IHl. rewrite H2 in IHl. apply IHl. auto.
elim (VertexSet.empty_1 H4).
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H2.
destruct (Vertex.eq_dec y (snd_ext a)).
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
unfold new_adj_set.
rewrite <-(MapFacts.find_o _ e).
case_eq (VertexMap.find y tmp); intros.
apply VertexSet.add_2.
unfold adj_set in IHl. rewrite H2 in IHl. apply IHl. auto.
assert (VertexSet.In x VertexSet.empty).
unfold adj_set in IHl. rewrite H2 in IHl. apply IHl. auto.
elim (VertexSet.empty_1 H4).
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H2.
unfold adj_set in IHl. rewrite <-H2 in IHl. apply IHl. auto.
auto.
auto.

apply fold_left_assoc_map.
unfold f', f, EqualSetMap. intros.
destruct (Vertex.eq_dec x1 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x1 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x1 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x1 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x1 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x1 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x1 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x1 s0). apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x1 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x1 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H0. auto.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x1 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x1 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x1 s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold EqualSetMap, f', f. intros.
destruct (Vertex.eq_dec x1 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (fst_ext a0)). intro.
inversion H1. apply VertexSet.eq_refl.
apply Props.Dec.F.add_m.
apply Regs.eq_refl.
auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x1 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (snd_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m.
apply Regs.eq_refl.
auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
auto.
auto.
auto.
auto.

induction (EdgeSet.elements s). simpl. auto.
cut (EqualSetMap (fold_left f' (a :: l) m) 
                 (f' (fold_left f' l m) a)). intro.
generalize (H0 y). clear H0. intro H0. inversion H0. subst.
set (tmp := fold_left f' l m) in *.
unfold f', f in H3.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H3.
congruence.
apply Regs.eq_sym. auto.
destruct (Vertex.eq_dec y (snd_ext a)).
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_eq_o in H3.
congruence.
apply Regs.eq_sym. auto.
auto.
rewrite MapFacts.add_neq_o in H3.
rewrite MapFacts.add_neq_o in H3.
unfold adj_set in IHl. rewrite <-H3 in IHl. elim (VertexSet.empty_1 IHl).
auto.
auto.

unfold adj_set. simpl. rewrite <-H1.
rewrite H3.
set (tmp := fold_left f' l m) in *.
unfold f', f in H2.
destruct (Vertex.eq_dec y (fst_ext a)).
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
unfold new_adj_set.
rewrite <-(MapFacts.find_o _ e).
case_eq (VertexMap.find y tmp); intros.
apply VertexSet.add_2.
unfold adj_set in IHl. rewrite H2 in IHl. apply IHl.
unfold adj_set in IHl. rewrite H2 in IHl. inversion IHl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H2.
destruct (Vertex.eq_dec y (snd_ext a)).
rewrite MapFacts.add_eq_o in H2.
inversion H2. subst. clear H2.
unfold new_adj_set.
rewrite <-(MapFacts.find_o _ e).
case_eq (VertexMap.find y tmp); intros.
apply VertexSet.add_2.
unfold adj_set in IHl. rewrite H2 in IHl. apply IHl.
unfold adj_set in IHl. rewrite H2 in IHl. inversion IHl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o in H2.
unfold adj_set in IHl. rewrite <-H2 in IHl. apply IHl.
auto.
auto.

apply fold_left_assoc_map.
unfold f', f, EqualSetMap. intros.
destruct (Vertex.eq_dec x0 (fst_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x0 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x0 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext z)).
rewrite MapFacts.add_eq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x0 s0). apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
rewrite <-(MapFacts.find_o _ e).
rewrite <-(MapFacts.find_o _ e0).
destruct (VertexMap.find x0 s0).
apply Props.add_add.
rewrite Props.singleton_equal_add. apply Props.add_add.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n. rewrite H0. auto.
rewrite <-e. rewrite <-e0. apply Regs.eq_refl.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n1. rewrite H0. auto.
intro. elim n0. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (fst_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext y0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
apply VertexSet.eq_refl.
intro. elim n0. rewrite H0. auto.
intro. elim n. rewrite H0. auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
destruct (VertexMap.find x0 s0); constructor.
apply VertexSet.eq_refl.
auto.
auto.
auto.
auto.
auto.
auto.
auto.
auto.

intros.
unfold EqualSetMap, f', f. intros.
destruct (Vertex.eq_dec x0 (fst_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (fst_ext a0)). intro.
inversion H1. apply VertexSet.eq_refl.
apply Props.Dec.F.add_m.
apply Regs.eq_refl.
auto.
apply Regs.eq_sym. auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
destruct (Vertex.eq_dec x0 (snd_ext a0)).
rewrite MapFacts.add_eq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_eq_o.
constructor.
unfold new_adj_set.
generalize (H0 (snd_ext a0)). intro.
inversion H1.
apply VertexSet.eq_refl.
apply Props.Dec.F.add_m.
apply Regs.eq_refl.
auto.
apply Regs.eq_sym. auto.
auto.
apply Regs.eq_sym. auto.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
rewrite MapFacts.add_neq_o.
auto.
auto.
auto.
auto.
auto.
Qed.

Lemma regreg_IE : forall x y,
SetRegReg.In (x,y) (interf_reg_reg g) ->
EdgeSet.In (Regs.reg_to_Reg x,Regs.reg_to_Reg y,None) IE_reg_reg.

Proof.
intros.
unfold IE_reg_reg.
set (f := (fun (e : SetRegReg.elt) (s : EdgeSet.t) =>
      EdgeSet.add (Regs.reg_to_Reg (fst e), Regs.reg_to_Reg (snd e), None) s)) in *.
rewrite SetRegReg.fold_1.
set (f' := fun a e => f e a) in *.
generalize SetRegReg.elements_1. intro HH.
generalize (HH (interf_reg_reg g) (x,y) H). clear HH. intro HH.
induction (SetRegReg.elements (interf_reg_reg g)). simpl.
inversion HH.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f', f.
inversion HH; subst.
apply EdgeSet.add_1. destruct H1. simpl in *. subst. apply Edge.eq_refl.
apply EdgeSet.add_2. apply IHl. auto.
unfold f', f. intros.
apply RegRegProps.add_add.

unfold f', f. intros.
apply RegRegProps.Dec.F.add_m. apply E.eq_refl. auto.
Qed.

Lemma regmreg_IE : forall x y,
SetRegMreg.In (x,y) (interf_reg_mreg g) ->
EdgeSet.In (Regs.reg_to_Reg x,Regs.mreg_to_Reg y,None) IE_reg_mreg.

Proof.
intros.
unfold IE_reg_mreg.
set (f := (fun (e : SetRegMreg.elt) (s : EdgeSet.t) =>
      EdgeSet.add (Regs.reg_to_Reg (fst e), Regs.mreg_to_Reg (snd e), None) s)) in *.
rewrite SetRegMreg.fold_1.
set (f' := fun a e => f e a) in *.
generalize SetRegMreg.elements_1. intro HH.
generalize (HH (interf_reg_mreg g) (x,y) H). clear HH. intro HH.
induction (SetRegMreg.elements (interf_reg_mreg g)). simpl.
inversion HH.
rewrite MEdgeFacts.fold_left_assoc.
set (tmp := fold_left f' l EdgeSet.empty) in *.
unfold f', f.
inversion HH; subst.
apply EdgeSet.add_1. destruct H1. simpl in *. subst. apply Edge.eq_refl.
apply EdgeSet.add_2. apply IHl. auto.
unfold f', f. intros.
apply RegRegProps.add_add.

unfold f', f. intros.
apply RegRegProps.Dec.F.add_m. apply E.eq_refl. auto.
Qed.

Lemma regreg_IE_translation : forall x y,
SetRegReg.In (x,y) (interf_reg_reg g) ->
EdgeSet.In (Regs.P x,Regs.P y,None) (IE graph_translation).

Proof.
intros.
unfold graph_translation. unfold IE. simpl.
rewrite (edgemap_to_edgeset_charac _ _ _ _ sym_imap).
apply set2map_charac_2.
left. exists None.
unfold interfgraph_interference_edges. apply EdgeSet.union_2.
rewrite edge_comm. apply regreg_IE. auto.
Qed.

Lemma regmreg_IE_translation : forall x y,
SetRegMreg.In (x,y) (interf_reg_mreg g) ->
EdgeSet.In (Regs.P x,Regs.M y,None) (IE graph_translation).

Proof.
intros.
unfold graph_translation. unfold IE. simpl.
rewrite (edgemap_to_edgeset_charac _ _ _ _ sym_imap).
apply set2map_charac_2.
left. exists None.
unfold interfgraph_interference_edges. apply EdgeSet.union_3.
rewrite edge_comm. apply regmreg_IE. auto.
Qed.

End Translation.
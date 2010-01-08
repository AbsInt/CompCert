Require Import IRC.
Require Import IRCColoring.
Require Import Graph_translation.
Require Import MyRegisters.
Require Import Locations.
Require Import RTLtyping.
Require Import ZArith.
Require Import AST.
Require Import Typed_interfgraphs.
Require Import Edges.
Require Import Graph_Facts.
Require Import Interference_adjacency.
Require Import InterfGraph.
Require Import Conventions.
Require Import Palettes.
Require Import InterfGraph_Construction.
Require Import WS.
Require Import Conservative_criteria.
Require Import IRC_graph.
Require Import IRC_Graph_Functions.
Require Import InterfGraphMapImp.
Require Import Registers.

Import Props Edge RegFacts.

Module ColFacts := FMapFacts.Facts ColorMap.

Definition graph_coloring_aux x int_map float_map env :=
match (Regs.get_type (Regs.P x) env) with
| Tint => match (map_to_coloring int_map (Regs.P x)) with 
          | Some (Regs.P z)  => S (Local Z0 Tint)
          | Some (Regs.M z) => R z
          | None => S (Local (Zpos x) Tint)
          end
| Tfloat => match (map_to_coloring float_map (Regs.P x)) with
            | Some (Regs.P z) => S (Local Z0 Tfloat)
            | Some (Regs.M z) => R z
            | None => S (Local (Zpos x) Tfloat)
            end
end.

Definition reg_translation s :=
Regset.fold (fun v s => VertexSet.add (Regs.reg_to_Reg v) s) s VertexSet.empty.

Definition mreg_translation s :=
MRegset.fold (fun v s => VertexSet.add (Regs.mreg_to_Reg v) s) s VertexSet.empty.

Definition Typed_interfgraphs g env  :=
let regreg_interf_partition :=
regreg_edge_type_partition (interf_reg_reg g) env in
let int_regreg_interf_edge := rr1 regreg_interf_partition in
let float_regreg_interf_edge := rr2 regreg_interf_partition in
let int_regreg_interf_reg := rr3 regreg_interf_partition in
let float_regreg_interf_reg := rr4 regreg_interf_partition in
let regmreg_interf_partition :=
regmreg_edge_type_partition (interf_reg_mreg g) env in
let int_regmreg_interf_edge := rm1 regmreg_interf_partition in
let float_regmreg_interf_edge := rm2 regmreg_interf_partition in
let int_regmreg_interf_reg := rm3 regmreg_interf_partition in
let float_regmreg_interf_reg := rm4 regmreg_interf_partition in
let int_regmreg_interf_mreg := rm5 regmreg_interf_partition in
let float_regmreg_interf_mreg := rm6 regmreg_interf_partition in
let regreg_pref_partition :=
regreg_edge_type_partition (pref_reg_reg g) env in
let int_regreg_pref_edge := rr1 regreg_pref_partition in
let float_regreg_pref_edge := rr2 regreg_pref_partition in
let int_regreg_pref_reg := rr3 regreg_pref_partition in
let float_regreg_pref_reg := rr4 regreg_pref_partition in
let regmreg_pref_partition :=
regmreg_edge_type_partition (pref_reg_mreg g) env in
let int_regmreg_pref_edge := rm1 regmreg_pref_partition in
let float_regmreg_pref_edge := rm2 regmreg_pref_partition in
let int_regmreg_pref_reg := rm3 regmreg_pref_partition in
let float_regmreg_pref_reg := rm4 regmreg_pref_partition in
let int_regmreg_pref_mreg := rm5 regmreg_pref_partition in
let float_regmreg_pref_mreg := rm6 regmreg_pref_partition in
let int_regs := Regset.union int_regreg_interf_reg 
                            (Regset.union int_regmreg_interf_reg
                              (Regset.union int_regreg_pref_reg int_regmreg_pref_reg)) in
let float_regs := Regset.union float_regreg_interf_reg 
                            (Regset.union float_regmreg_interf_reg
                              (Regset.union float_regreg_pref_reg float_regmreg_pref_reg)) in
let int_mregs := MRegset.union int_regmreg_interf_mreg int_regmreg_pref_mreg in
let float_mregs := MRegset.union float_regmreg_interf_mreg float_regmreg_pref_mreg in
let int_Regs := VertexSet.union (reg_translation int_regs) (mreg_translation int_mregs) in
let float_Regs := VertexSet.union (reg_translation float_regs) (mreg_translation float_mregs) in
(int_Regs,
mkgraph int_regreg_interf_edge   int_regmreg_interf_edge   int_regreg_pref_edge   int_regmreg_pref_edge,
float_Regs,
mkgraph float_regreg_interf_edge float_regmreg_interf_edge float_regreg_pref_edge float_regmreg_pref_edge).

Lemma extremities_int_interf_graph : forall g env,
forall e, EdgeSet.In e (interfgraph_affinity_edges (snd (fst (fst (Typed_interfgraphs g env))))) \/
             EdgeSet.In e (interfgraph_interference_edges (snd (fst (fst (Typed_interfgraphs g env))))) ->
             VertexSet.In (fst_ext e) (fst (fst (fst (Typed_interfgraphs g env)))) /\
             VertexSet.In (snd_ext e) (fst (fst (fst (Typed_interfgraphs g env)))).

Proof.
Admitted.

Lemma extremities_float_interf_graph : forall g env,
forall e, EdgeSet.In e (interfgraph_affinity_edges (snd (Typed_interfgraphs g env))) \/
             EdgeSet.In e (interfgraph_interference_edges (snd (Typed_interfgraphs g env))) ->
             VertexSet.In (fst_ext e) (snd (fst (Typed_interfgraphs g env))) /\
             VertexSet.In (snd_ext e) (snd (fst (Typed_interfgraphs g env))).

Proof.
Admitted.

Definition my_graph_coloring g env :=
let typed_graphs := Typed_interfgraphs g env in
let intR := fst (fst (fst typed_graphs)) in
let intG := snd (fst (fst typed_graphs)) in
let floatR := snd (fst typed_graphs) in
let floatG := snd typed_graphs in
let int_graph := graph_translation intG intR (extremities_int_interf_graph g env) in
let float_graph := graph_translation floatG floatR (extremities_float_interf_graph g env) in
let int_map := (IRC_map (graph_to_IRC_graph int_graph int_palette)) in
let float_map := (IRC_map (graph_to_IRC_graph float_graph float_palette)) in
fun x => graph_coloring_aux x int_map float_map env.

Section Coloring_to_allocation.

Variable g : graph.
Variable env : regenv.
Definition typed_graphs := Typed_interfgraphs g env.
Definition intR := fst (fst (fst typed_graphs)).
Definition intG := snd (fst (fst typed_graphs)).
Definition floatR := snd (fst typed_graphs).
Definition floatG := snd typed_graphs.
Definition int_graph := graph_translation intG intR (extremities_int_interf_graph g env).
Definition float_graph := graph_translation floatG floatR (extremities_float_interf_graph g env).
Definition int_map := (IRC_map (graph_to_IRC_graph int_graph int_palette)).
Definition float_map := (IRC_map (graph_to_IRC_graph float_graph float_palette)).
Definition int_coloring := map_to_coloring int_map.
Definition float_coloring := map_to_coloring float_map.

Hypothesis temporaries_out : forall x,
In_graph (Regs.M x) int_graph -> ~List.In (R x) temporaries.

Hypothesis correct_palette_int : forall x,
VertexSet.In x (precolored int_graph) -> VertexSet.In x int_palette.

Hypothesis correct_palette_float : forall x,
VertexSet.In x (precolored float_graph) -> VertexSet.In x float_palette.

Lemma proper_coloring_int : proper_coloring int_coloring int_graph int_palette.

Proof.
intros. apply proper_coloring_IRC_aux.
intro. apply correct_palette_int.
Qed.

Lemma proper_coloring_float : proper_coloring float_coloring float_graph float_palette.

Proof.
intros. apply proper_coloring_IRC_aux.
intro. apply correct_palette_float.
Qed.

Import SetoidList.

Lemma exists_refl : forall x,
exists y, Regs.M x = Regs.M y.

Proof.
intro x. exists x. auto.
Qed.

Lemma mreg_int_palette : forall x,
VertexSet.In x int_palette ->
exists y, x = Regs.M y.

Proof.
unfold int_palette. intros x H.
repeat (destruct (proj1 (Props.Dec.F.add_iff _ _ _) H);
        [inversion H0;subst; apply exists_refl|generalize H0; clear H H0; intro H]).
elim (VertexSet.empty_1 H).
Qed.

Lemma mreg_float_palette : forall x,
VertexSet.In x float_palette ->
exists y, x = Regs.M y.

Proof.
unfold float_palette. intros x H.
repeat (destruct (proj1 (Props.Dec.F.add_iff _ _ _) H);
        [inversion H0;subst; apply exists_refl|generalize H0; clear H H0; intro H]).
elim (VertexSet.empty_1 H).
Qed.

Lemma register_heuristic_mreg : forall x r,
(IRC int_graph int_palette) x = Some r ->
exists y, r = Regs.M y.

Proof.
intros x r H.
apply mreg_int_palette.
generalize (proper_coloring_IRC_aux int_graph int_palette correct_palette_int).
intro H0.
unfold proper_coloring in H0.
unfold proper_coloring_3 in H0.
do 2 destruct H0 as [_ H0].
apply H0 with (x := x).
rewrite H. apply OptionReg.eq_refl.
Qed.

Lemma register_heuristic_mreg_float : forall x r,
(IRC float_graph float_palette) x = Some r ->
exists y, r = Regs.M y.

Proof.
intros x r H.
apply mreg_float_palette.
generalize (proper_coloring_IRC_aux float_graph float_palette correct_palette_float).
intro H0.
unfold proper_coloring in H0.
unfold proper_coloring_3 in H0.
do 2 destruct H0 as [_ H0].
apply H0 with (x := x).
rewrite H. apply OptionReg.eq_refl.
Qed.

Lemma int_palette_type : forall x,
VertexSet.In x int_palette ->
Regs.get_type x env = Tint.

Proof.
unfold int_palette. intros x H.
repeat (destruct (proj1 (Props.Dec.F.add_iff _ _ _) H);
        [inversion H0;subst; auto|generalize H0; clear H H0; intro H]).
elim (VertexSet.empty_1 H).
Qed.

Lemma float_palette_type : forall x,
VertexSet.In x float_palette ->
Regs.get_type x env = Tfloat.

Proof.
unfold float_palette. intros x H.
repeat (destruct (proj1 (Props.Dec.F.add_iff _ _ _) H);
        [inversion H0;subst; auto|generalize H0; clear H H0; intro H]).
elim (VertexSet.empty_1 H).
Qed.

Lemma register_heuristic_type_int : forall x r,
IRC int_graph int_palette x = Some r ->
Regs.get_type r env = Tint.

Proof.
intros x r H.
apply int_palette_type.
generalize (proper_coloring_IRC_aux int_graph int_palette (correct_palette_int)).
intro H0.
unfold proper_coloring in H0. do 2 destruct H0 as [_ H0].
unfold proper_coloring_3 in H0.
apply (H0 x r).
rewrite H. apply OptionReg.eq_refl.
Qed.

Lemma register_heuristic_type_float : forall x r,
IRC float_graph float_palette x = Some r ->
Regs.get_type r env = Tfloat.

Proof.
intros x r H.
apply float_palette_type.
generalize (proper_coloring_IRC_aux float_graph float_palette correct_palette_float).
intro H0.
unfold proper_coloring in H0. do 2 destruct H0 as [_ H0].
unfold proper_coloring_3 in H0.
apply (H0 x r).
rewrite H. apply OptionReg.eq_refl.
Qed.

Lemma Loc_reg_eq_type : forall x,
Regs.get_type (Regs.P x) env = Loc.type (my_graph_coloring g env x).

Proof.
intro x.
unfold my_graph_coloring.
change (snd (fst (fst (Typed_interfgraphs g env)))) with intG.
change (fst (fst (fst (Typed_interfgraphs g env)))) with intR.
change (snd (fst (Typed_interfgraphs g env))) with floatR.
change (snd (Typed_interfgraphs g env)) with floatG.
fold int_graph; fold float_graph.
unfold graph_coloring_aux.
case_eq (Regs.get_type (Regs.P x) env); intros HH.
change (map_to_coloring (IRC_map (graph_to_IRC_graph int_graph int_palette))) with
             (IRC int_graph int_palette).
case_eq (IRC int_graph int_palette (Regs.P x)); intros.
generalize (register_heuristic_mreg _ _ H). intro. destruct H0. rewrite H0.
generalize (register_heuristic_type_int _ _ H).
unfold Regs.get_type. rewrite H0. simpl. auto.
simpl. auto.
change (map_to_coloring (IRC_map (graph_to_IRC_graph float_graph float_palette))) with
             (IRC float_graph float_palette).
case_eq (IRC float_graph float_palette (Regs.P x)); intros.
generalize (register_heuristic_mreg_float _ _ H). intro. destruct H0. rewrite H0.
generalize (register_heuristic_type_float _ _ H).
unfold Regs.get_type. rewrite H0. simpl. auto.
simpl. auto.
Qed.

Lemma regreg_in_fst_partition : forall e s,
SetRegReg.In e s ->
env (fst e) = Tint ->
env (snd e) = Tint ->
SetRegReg.In e (rr1 (regreg_edge_type_partition s env)).

Proof.
intros.
unfold regreg_edge_type_partition.
set (f:=(fun (e0 : SetRegReg.elt) (s0 : regregpartition) =>
         match env (fst e0) with
         | Tint =>
             match env (snd e0) with
             | Tint =>
                 (SetRegReg.add e0 (rr1 s0), rr2 s0,
                 Regset.add (fst e0) (Regset.add (snd e0) (rr3 s0)), 
                 rr4 s0)
             | Tfloat =>
                 (rr1 s0, rr2 s0, Regset.add (fst e0) (rr3 s0),
                 Regset.add (snd e0) (rr4 s0))
             end
         | Tfloat =>
             match env (snd e0) with
             | Tint =>
                 (rr1 s0, rr2 s0, Regset.add (snd e0) (rr3 s0),
                 Regset.add (fst e0) (rr4 s0))
             | Tfloat =>
                 (rr1 s0, SetRegReg.add e0 (rr2 s0), rr3 s0,
                 Regset.add (fst e0) (Regset.add (snd e0) (rr4 s0)))
             end
         end)).
unfold regregpartition in *. fold f.

generalize (SetRegReg.empty,SetRegReg.empty, Regset.empty, Regset.empty).
generalize SetRegReg.elements_1. intro HH.
generalize (HH s e H). clear H HH. intro HH.
intro p. rewrite SetRegReg.fold_1. generalize p. clear p.
induction (SetRegReg.elements s).
inversion HH.
inversion HH.
 subst. intro p. do 3 destruct p. simpl.

assert (f a (t2,t3,t1,t0) = (SetRegReg.add a t2, t3, Regset.add (fst a) (Regset.add (snd a) t1),t0)).
unfold f.

destruct H2. rewrite H in *. rewrite H2 in *. rewrite H0. rewrite H1. simpl. reflexivity.
rewrite H.
destruct H2.

assert (forall x s1 s2 s3 s4, SetRegReg.In x s1 ->
                        SetRegReg.In x (rr1 (fold_left
                            (fun (a0 : SetRegReg.t*SetRegReg.t*Regset.t*Regset.t) (e0 : SetRegReg.elt) => f e0 a0)
                            l (s1, s2, s3, s4)))).

clear H H0 H1 H2 HH IHl.

induction l. 
simpl. auto.
intros x s1 s2 s3 s4 H2.
simpl.

assert (f a0 (s1,s2,s3,s4) = (SetRegReg.add a0 s1, s2,Regset.add (fst a0) (Regset.add (snd a0) s3), s4) \/
        f a0 (s1,s2,s3,s4) = (s1, SetRegReg.add a0 s2, s3, Regset.add (fst a0)(Regset.add (snd a0) s4)) \/
        f a0 (s1,s2,s3,s4) = (s1,s2,Regset.add (fst a0) s3, Regset.add (snd a0) s4)\/
        f a0 (s1,s2,s3,s4) = (s1,s2,Regset.add (snd a0) s3, Regset.add (fst a0) s4)).

unfold f.
destruct (env (fst a0)); destruct (env (snd a0));
unfold rr1,rr2,rr3,rr4; simpl; auto.

destruct H.

rewrite H. apply IHl. apply SetRegReg.add_2. assumption.

destruct H. 
rewrite H.
apply IHl. assumption.
destruct H; rewrite H.
apply IHl. assumption.
apply IHl. assumption.

apply H4. apply SetRegReg.add_1. intuition.

subst. simpl. intro p. apply IHl. assumption.
Qed.

Lemma regreg_in_snd_partition : forall e s,
SetRegReg.In e s ->
env (fst e) = Tfloat ->
env (snd e) = Tfloat ->
SetRegReg.In e (rr2 (regreg_edge_type_partition s env)).

Proof.
intros.
unfold regreg_edge_type_partition.
set (f:=(fun (e0 : SetRegReg.elt) (s0 : regregpartition) =>
         match env (fst e0) with
         | Tint =>
             match env (snd e0) with
             | Tint =>
                 (SetRegReg.add e0 (rr1 s0), rr2 s0,
                 Regset.add (fst e0) (Regset.add (snd e0) (rr3 s0)), 
                 rr4 s0)
             | Tfloat =>
                 (rr1 s0, rr2 s0, Regset.add (fst e0) (rr3 s0),
                 Regset.add (snd e0) (rr4 s0))
             end
         | Tfloat =>
             match env (snd e0) with
             | Tint =>
                 (rr1 s0, rr2 s0, Regset.add (snd e0) (rr3 s0),
                 Regset.add (fst e0) (rr4 s0))
             | Tfloat =>
                 (rr1 s0, SetRegReg.add e0 (rr2 s0), rr3 s0,
                 Regset.add (fst e0) (Regset.add (snd e0) (rr4 s0)))
             end
         end)).
unfold regregpartition in *. fold f.

generalize (SetRegReg.empty,SetRegReg.empty, Regset.empty, Regset.empty).
generalize SetRegReg.elements_1. intro HH.
generalize (HH s e H). clear H HH. intro HH.
intro p. rewrite SetRegReg.fold_1. generalize p. clear p.
induction (SetRegReg.elements s).
inversion HH.
inversion HH.
 subst. intro p. do 3 destruct p. simpl.

assert (f a (t2,t3,t1,t0) = (t2, SetRegReg.add a t3, t1, Regset.add (fst a) (Regset.add (snd a) t0))).
unfold f.

destruct H2. rewrite H in *. rewrite H2 in *. rewrite H0. rewrite H1. simpl. reflexivity.
rewrite H.
destruct H2.

assert (forall x s1 s2 s3 s4, SetRegReg.In x s2 ->
                        SetRegReg.In x (rr2 (fold_left
                            (fun (a0 : SetRegReg.t*SetRegReg.t*Regset.t*Regset.t) (e0 : SetRegReg.elt) => f e0 a0)
                            l (s1, s2, s3, s4)))).

clear H H0 H1 H2 HH IHl.

induction l. 
simpl. auto.
intros x s1 s2 s3 s4 H2.
simpl.

assert (f a0 (s1,s2,s3,s4) = (SetRegReg.add a0 s1, s2,Regset.add (fst a0) (Regset.add (snd a0) s3), s4) \/
        f a0 (s1,s2,s3,s4) = (s1, SetRegReg.add a0 s2, s3, Regset.add (fst a0)(Regset.add (snd a0) s4)) \/
        f a0 (s1,s2,s3,s4) = (s1,s2,Regset.add (fst a0) s3, Regset.add (snd a0) s4)\/
        f a0 (s1,s2,s3,s4) = (s1,s2,Regset.add (snd a0) s3, Regset.add (fst a0) s4)).

unfold f.
destruct (env (fst a0)); destruct (env (snd a0));
unfold rr1,rr2,rr3,rr4; simpl; auto.

destruct H.

rewrite H. apply IHl. assumption.

destruct H. 
rewrite H.
apply IHl. apply SetRegReg.add_2. assumption.
destruct H; rewrite H.
apply IHl. assumption.
apply IHl. assumption.

apply H4. apply SetRegReg.add_1. intuition.

subst. simpl. intro p. apply IHl. assumption.
Qed.

Lemma interf_int_regreg_translation :
        interf_reg_reg (snd (fst (fst (Typed_interfgraphs g env)))) =
        rr1 (regreg_edge_type_partition (interf_reg_reg g) env).

Proof.
unfold Typed_interfgraphs.
case_eq (regreg_edge_type_partition (interf_reg_reg g) env); intros.
case_eq (regreg_edge_type_partition (pref_reg_reg g) env); intros.
case_eq (regmreg_edge_type_partition (interf_reg_mreg g) env); intros.
case_eq (regmreg_edge_type_partition (pref_reg_mreg g) env); intros.
simpl. reflexivity.
Qed.

Lemma interf_float_regreg_translation :
        interf_reg_reg (snd (Typed_interfgraphs g env)) =
        rr2 (regreg_edge_type_partition (interf_reg_reg g) env).

Proof.
unfold Typed_interfgraphs.
case_eq (regreg_edge_type_partition (interf_reg_reg g) env); intros.
case_eq (regreg_edge_type_partition (pref_reg_reg g) env); intros.
case_eq (regmreg_edge_type_partition (interf_reg_mreg g) env); intros.
case_eq (regmreg_edge_type_partition (pref_reg_mreg g) env); intros.
simpl. reflexivity.
Qed.

Lemma correct_alloc_1 : check_coloring_1 g (my_graph_coloring g env) = true.

Proof.
unfold check_coloring_1.
apply SetRegReg.for_all_1.

unfold compat_bool.
intros x y H. destruct H as [H H0].
rewrite H. rewrite H0. reflexivity.

unfold SetRegReg.For_all.
intros x H.
generalize (Loc_reg_eq_type (fst x)). generalize (Loc_reg_eq_type (snd x)).
unfold my_graph_coloring in *.
change (snd (fst (fst (Typed_interfgraphs g env)))) with intG.
change (fst (fst (fst (Typed_interfgraphs g env)))) with intR.
change (snd (fst (Typed_interfgraphs g env))) with floatR.
change (snd (Typed_interfgraphs g env)) with floatG.
fold int_graph; fold float_graph.
unfold graph_coloring_aux.
change (map_to_coloring (IRC_map (graph_to_IRC_graph int_graph int_palette))) with
             (IRC int_graph int_palette).
change (map_to_coloring (IRC_map (graph_to_IRC_graph float_graph float_palette))) with
             (IRC float_graph float_palette).
intros Locty1 Locty2.
case_eq (Regs.get_type (Regs.P (fst x)) env); intros HH.
case_eq (Regs.get_type (Regs.P (snd x)) env); intros HH0.
case_eq (IRC int_graph int_palette (Regs.P (fst x))); intros.
destruct (register_heuristic_mreg (Regs.P (fst x)) t0 H0). rewrite H1. simpl.
case_eq (IRC int_graph int_palette (Regs.P (snd x))); intros.
destruct (register_heuristic_mreg (Regs.P (snd x)) t1 H2). rewrite H3.

generalize (proper_coloring_IRC_aux int_graph int_palette (correct_palette_int)).
intro H4. unfold proper_coloring in H4.
destruct H4 as [H4 _].
unfold proper_coloring_1 in H4.
assert (~Regs.eq (Regs.M x0) (Regs.M x1)).
apply (H4 (Regs.P (fst x), Regs.P (snd x), None)).
unfold Edge.interf_edge. auto.
unfold int_graph.
right. simpl.
apply regreg_IE_translation. unfold intG, typed_graphs.
rewrite interf_int_regreg_translation.
apply regreg_in_fst_partition. destruct x. auto. auto. auto.
change_rewrite. rewrite H0. rewrite H1. apply OptionReg.eq_refl.
change_rewrite. rewrite H2. rewrite H3. apply OptionReg.eq_refl.
destruct (Loc.eq (R x0) (R x1)). subst.
elim H5. inversion e. auto.
reflexivity.
destruct (Loc.eq (R x0) (S (Local (Zpos (snd x)) Tint))). 
inversion e.
reflexivity.
case_eq (IRC int_graph int_palette (Regs.P (snd x))); intros.
destruct (register_heuristic_mreg (Regs.P (snd x)) t0 H1). rewrite H2.
destruct (Loc.eq (S (Local (Zpos (fst x)) Tint)) (R x0)).
inversion e.
reflexivity.
destruct (Loc.eq (S (Local (Zpos (fst x)) Tint)) (S (Local (Zpos (snd x)) Tint))).
inversion e.
elim (set_reg_reg_diff_ext _ _ (or_introl _ H) H3).
reflexivity.

rewrite HH in *. rewrite HH0 in *.
set (l1 := match IRC int_graph int_palette (Regs.P (fst x)) with
      | Some (Regs.P _) => S (Local 0 Tint)
      | Some (Regs.M z) => R z
      | None => S (Local (Zpos (fst x)) Tint)
      end) in *.
set (l2 :=  match IRC float_graph float_palette (Regs.P (snd x)) with
      | Some (Regs.P _) => S (Local 0 Tfloat)
      | Some (Regs.M z) => R z
      | None => S (Local (Zpos (snd x)) Tfloat)
      end) in *.
destruct (Loc.eq l1 l2). rewrite e in Locty2. rewrite <-Locty1 in Locty2. congruence.
reflexivity.

case_eq (Regs.get_type (Regs.P (snd x)) env); intros HH0.

rewrite HH in *. rewrite HH0 in *.
set (l1 :=match IRC float_graph float_palette (Regs.P (fst x)) with
      | Some (Regs.P _) => S (Local 0 Tfloat)
      | Some (Regs.M z) => R z
      | None => S (Local (Zpos (fst x)) Tfloat)
      end ) in *.
set (l2 :=  match IRC int_graph int_palette (Regs.P (snd x)) with
      | Some (Regs.P _) => S (Local 0 Tint)
      | Some (Regs.M z) => R z
      | None => S (Local (Zpos (snd x)) Tint)
      end) in *.
destruct (Loc.eq l1 l2). rewrite e in Locty2. rewrite <-Locty1 in Locty2. congruence.
reflexivity.

case_eq (IRC float_graph float_palette (Regs.P (fst x))); intros.
destruct (register_heuristic_mreg_float (Regs.P (fst x)) t0 H0). rewrite H1. simpl.
case_eq (IRC float_graph float_palette (Regs.P (snd x))); intros.
destruct (register_heuristic_mreg_float (Regs.P (snd x)) t1 H2). rewrite H3.

generalize (proper_coloring_IRC_aux float_graph float_palette (correct_palette_float)).
intro H4. unfold proper_coloring in H4.
destruct H4 as [H4 _].
unfold proper_coloring_1 in H4.
assert (~Regs.eq (Regs.M x0) (Regs.M x1)).
apply (H4 (Regs.P (fst x), Regs.P (snd x), None)).
unfold Edge.interf_edge. auto.
unfold float_graph.
right. simpl.
apply regreg_IE_translation. unfold floatG, typed_graphs.
rewrite interf_float_regreg_translation.
apply regreg_in_snd_partition. destruct x. auto. auto. auto.
change_rewrite. rewrite H0. rewrite H1. apply OptionReg.eq_refl.
change_rewrite. rewrite H2. rewrite H3. apply OptionReg.eq_refl.
destruct (Loc.eq (R x0) (R x1)). subst.
elim H5. inversion e. auto.
reflexivity.
destruct (Loc.eq (R x0) (S (Local (Zpos (snd x)) Tfloat))). 
inversion e.
reflexivity.
case_eq (IRC float_graph float_palette (Regs.P (snd x))); intros.
destruct (register_heuristic_mreg_float (Regs.P (snd x)) t0 H1). rewrite H2.
destruct (Loc.eq (S (Local (Zpos (fst x)) Tfloat)) (R x0)).
inversion e.
reflexivity.
destruct (Loc.eq (S (Local (Zpos (fst x)) Tfloat)) (S (Local (Zpos (snd x)) Tfloat))).
inversion e.
elim (set_reg_reg_diff_ext _ _ (or_introl _ H) H3).
reflexivity.
Qed.

Lemma interf_int_regmreg_translation :
        interf_reg_mreg (snd (fst (fst (Typed_interfgraphs g env)))) =
        rm1 (regmreg_edge_type_partition (interf_reg_mreg g) env).

Proof.
unfold Typed_interfgraphs.
case_eq (regreg_edge_type_partition (interf_reg_reg g) env); intros.
case_eq (regreg_edge_type_partition (pref_reg_reg g) env); intros.
case_eq (regmreg_edge_type_partition (interf_reg_mreg g) env); intros.
case_eq (regmreg_edge_type_partition (pref_reg_mreg g) env); intros.
simpl. reflexivity.
Qed.

Lemma interf_float_regmreg_translation :
        interf_reg_mreg (snd (Typed_interfgraphs g env)) =
        rm2 (regmreg_edge_type_partition (interf_reg_mreg g) env).

Proof.
unfold Typed_interfgraphs.
case_eq (regreg_edge_type_partition (interf_reg_reg g) env); intros.
case_eq (regreg_edge_type_partition (pref_reg_reg g) env); intros.
case_eq (regmreg_edge_type_partition (interf_reg_mreg g) env); intros.
case_eq (regmreg_edge_type_partition (pref_reg_mreg g) env); intros.
simpl. reflexivity.
Qed.

Lemma regmreg_in_fst_partition : forall e s,
SetRegMreg.In e s ->
env (fst e) = Tint ->
mreg_type (snd e) = Tint ->
SetRegMreg.In e (rm1 (regmreg_edge_type_partition s env)).

Proof.
intros.
unfold regmreg_edge_type_partition.
set (f := (fun (e0 : SetRegMreg.elt) (s0 : regmregpartition) =>
         match env (fst e0) with
         | Tint =>
             match mreg_type (snd e0) with
             | Tint =>
                 (SetRegMreg.add e0 (rm1 s0), rm2 s0,
                 Regset.add (fst e0) (rm3 s0), rm4 s0,
                 MRegset.add (snd e0) (rm5 s0), rm6 s0)
             | Tfloat =>
                 (rm1 s0, rm2 s0, Regset.add (fst e0) (rm3 s0), rm4 s0,
                 rm5 s0, MRegset.add (snd e0) (rm6 s0))
             end
         | Tfloat =>
             match mreg_type (snd e0) with
             | Tint =>
                 (rm1 s0, rm2 s0, rm3 s0, Regset.add (fst e0) (rm4 s0),
                 MRegset.add (snd e0) (rm5 s0), rm6 s0)
             | Tfloat =>
                 (rm1 s0, SetRegMreg.add e0 (rm2 s0), rm3 s0,
                 Regset.add (fst e0) (rm4 s0), rm5 s0,
                 MRegset.add (snd e0) (rm6 s0))
             end
         end)).
unfold regmregpartition in *. fold f.

generalize (SetRegMreg.empty, SetRegMreg.empty, Regset.empty, Regset.empty, MRegset.empty, MRegset.empty).
generalize SetRegMreg.elements_1. intro HH.
generalize (HH s e H). clear H HH. intro HH.
intro p. rewrite SetRegMreg.fold_1. generalize p. clear p.
induction (SetRegMreg.elements s).
inversion HH.
inversion HH.
 subst. intro p. do 5 destruct p.  simpl.

assert (f a (t4,t5,t3,t2,t1,t0) = (SetRegMreg.add a t4, t5, Regset.add (fst a) t3, t2, MRegset.add (snd a) t1, t0)).
unfold f.

destruct H2. rewrite H in *. rewrite H2 in *. rewrite H0. rewrite H1. simpl. reflexivity.
rewrite H.
destruct H2.

assert (forall x s1 s2 s3 s4 s5 s6, SetRegMreg.In x s1 ->
                        SetRegMreg.In x (rm1 (fold_left
                            (fun (a0 : SetRegMreg.t * SetRegMreg.t * Regset.t * Regset.t *MRegset.t * MRegset.t)
                                    (e0 : SetRegMreg.elt) => f e0 a0)
                            l (s1, s2, s3, s4, s5, s6)))).

clear H H0 H1 H2 HH IHl.

induction l. 
simpl. auto.
intros x s1 s2 s3 s4 s5 s6 H2.
simpl.

assert (f a0 (s1,s2, s3, s4, s5, s6) = (SetRegMreg.add a0 s1, s2, Regset.add (fst a0) s3, s4, MRegset.add (snd a0) s5, s6) \/
        f a0 (s1,s2,s3,s4,s5,s6) = (s1, SetRegMreg.add a0 s2, s3, Regset.add (fst a0) s4, s5, MRegset.add (snd a0) s6) \/
        f a0 (s1,s2,s3,s4,s5,s6) = (s1,s2,Regset.add (fst a0) s3, s4,s5,MRegset.add (snd a0) s6) \/
        f a0 (s1,s2,s3,s4,s5,s6) = (s1,s2,s3, Regset.add (fst a0) s4, MRegset.add (snd a0) s5, s6)).

unfold f.
destruct (env (fst a0)); destruct (mreg_type (snd a0)); auto.

destruct H.

rewrite H. apply IHl. apply SetRegMreg.add_2. assumption.

destruct H. 
rewrite H.
apply IHl. assumption.
destruct H; rewrite H; apply IHl; assumption.

apply H4. apply SetRegMreg.add_1. intuition.

subst. simpl. intro p. apply IHl. assumption.
Qed.

Lemma regmreg_in_snd_partition : forall e s,
SetRegMreg.In e s ->
env (fst e) = Tfloat ->
mreg_type (snd e) = Tfloat ->
SetRegMreg.In e (rm2 (regmreg_edge_type_partition s env)).

Proof.
intros.
unfold regmreg_edge_type_partition.
set (f := (fun (e0 : SetRegMreg.elt) (s0 : regmregpartition) =>
         match env (fst e0) with
         | Tint =>
             match mreg_type (snd e0) with
             | Tint =>
                 (SetRegMreg.add e0 (rm1 s0), rm2 s0,
                 Regset.add (fst e0) (rm3 s0), rm4 s0,
                 MRegset.add (snd e0) (rm5 s0), rm6 s0)
             | Tfloat =>
                 (rm1 s0, rm2 s0, Regset.add (fst e0) (rm3 s0), rm4 s0,
                 rm5 s0, MRegset.add (snd e0) (rm6 s0))
             end
         | Tfloat =>
             match mreg_type (snd e0) with
             | Tint =>
                 (rm1 s0, rm2 s0, rm3 s0, Regset.add (fst e0) (rm4 s0),
                 MRegset.add (snd e0) (rm5 s0), rm6 s0)
             | Tfloat =>
                 (rm1 s0, SetRegMreg.add e0 (rm2 s0), rm3 s0,
                 Regset.add (fst e0) (rm4 s0), rm5 s0,
                 MRegset.add (snd e0) (rm6 s0))
             end
         end)).
unfold regmregpartition in *. fold f.

generalize (SetRegMreg.empty, SetRegMreg.empty, Regset.empty, Regset.empty, MRegset.empty, MRegset.empty).
generalize SetRegMreg.elements_1. intro HH.
generalize (HH s e H). clear H HH. intro HH.
intro p. rewrite SetRegMreg.fold_1. generalize p. clear p.
induction (SetRegMreg.elements s).
inversion HH.
inversion HH.
 subst. intro p. do 5 destruct p.  simpl.

assert (f a (t4,t5,t3,t2,t1,t0) = (t4, SetRegMreg.add a t5, t3, Regset.add (fst a) t2, t1, MRegset.add (snd a) t0)).
unfold f.

destruct H2. rewrite H in *. rewrite H2 in *. rewrite H0. rewrite H1. simpl. reflexivity.
rewrite H.
destruct H2.

assert (forall x s1 s2 s3 s4 s5 s6, SetRegMreg.In x s2 ->
                        SetRegMreg.In x (rm2 (fold_left
                            (fun (a0 : SetRegMreg.t * SetRegMreg.t * Regset.t * Regset.t *MRegset.t * MRegset.t)
                                    (e0 : SetRegMreg.elt) => f e0 a0)
                            l (s1, s2, s3, s4, s5, s6)))).

clear H H0 H1 H2 HH IHl.

induction l. 
simpl. auto.
intros x s1 s2 s3 s4 s5 s6 H2.
simpl.

assert (f a0 (s1,s2, s3, s4, s5, s6) = (SetRegMreg.add a0 s1, s2, Regset.add (fst a0) s3, s4, MRegset.add (snd a0) s5, s6) \/
        f a0 (s1,s2,s3,s4,s5,s6) = (s1, SetRegMreg.add a0 s2, s3, Regset.add (fst a0) s4, s5, MRegset.add (snd a0) s6) \/
        f a0 (s1,s2,s3,s4,s5,s6) = (s1,s2,Regset.add (fst a0) s3, s4,s5,MRegset.add (snd a0) s6) \/
        f a0 (s1,s2,s3,s4,s5,s6) = (s1,s2,s3, Regset.add (fst a0) s4, MRegset.add (snd a0) s5, s6)).

unfold f.
destruct (env (fst a0)); destruct (mreg_type (snd a0)); auto.

destruct H.

rewrite H. apply IHl. assumption.

destruct H.
rewrite H.
apply IHl. apply SetRegMreg.add_2. assumption.
destruct H; rewrite H; apply IHl; assumption.

apply H4. apply SetRegMreg.add_1. intuition.

subst. simpl. intro p. apply IHl. assumption.
Qed.

Section fold_assoc_map.

Variable A : Type.

Lemma fold_left_compat_map : forall (f : ColorMap.t Regs.t -> A -> ColorMap.t Regs.t) l e e',
ColorMap.Equal e e' ->
(forall e1 e2 a, ColorMap.Equal e1 e2 -> ColorMap.Equal (f e1 a) (f e2 a)) ->
ColorMap.Equal (fold_left f l e) (fold_left f l e').

Proof.
intro f;induction l;simpl.
auto.
intros e e' H H0 H1.
apply (IHl (f e a) (f e' a)).
apply H0;assumption.
assumption.
Qed.

Lemma fold_left_assoc_map : forall l (f : ColorMap.t Regs.t -> A -> ColorMap.t Regs.t) x h,
(forall (y z : A) s, ColorMap.Equal (f (f s y) z) (f (f s z) y)) ->
(forall e1 e2 a, ColorMap.Equal e1 e2 -> ColorMap.Equal (f e1 a) (f e2 a)) ->
ColorMap.Equal (fold_left f (h :: l) x) (f (fold_left f l x) h).

Proof.
induction l;simpl;intros f x h H H0.
intuition.
rewrite <-IHl;simpl;try assumption.
apply fold_left_compat_map;[apply H|];auto.
Qed.

End fold_assoc_map.

Lemma mreg_refl_coloring_aux : forall x gpalette,
VertexSet.In x (precolored (irc_g gpalette)) ->
VertexSet.Subset (precolored (irc_g gpalette)) (pal gpalette) ->
OptionReg.eq (map_to_coloring (IRC_map gpalette) x) (Some x).

Proof.
intros. functional induction IRC_map gpalette; simpl in *.

(* simplify *)
generalize (simplify_inv _ _ e). intro.
generalize (simplify_inv2 _ _ e). intro. destruct H2. simpl in *. clear e.
rewrite H2 in *. clear H2. unfold available_coloring.
set (palette := pal g0) in *. set (wl := irc_wl g0) in *. set (g1 := irc_g g0) in *.
case_eq ( VertexSet.choose
         (VertexSet.diff palette
            (forbidden_colors r
               (IRC_map
                  (simplify_irc r g0
                     (VertexSet.choose_1 (s:=get_simplifyWL wl) x0))) g1))).
intros. unfold map_to_coloring.
rewrite ColFacts.add_neq_o.
apply IHt0. unfold simplify_irc. simpl.
rewrite precolored_remove_vertex. apply VertexSet.remove_2.
intro. rewrite <-H3 in H.
generalize (In_simplify_props _ _ _ _ _ _ _ _ (VertexSet.choose_1 H1) (refl_equal _) (HWS_irc g0)). intro.
destruct H4. destruct H5. destruct H6. elim H7. auto. auto.
unfold simplify_irc. simpl. rewrite precolored_remove_vertex.
intro. intro. apply H0. apply (VertexSet.remove_3 H3).
intro. rewrite <-H3 in H.
generalize (In_simplify_props _ _ _ _ _ _ _ _ (VertexSet.choose_1 H1) (refl_equal _) (HWS_irc g0)). intro.
destruct H4. destruct H5. destruct H6. elim H7. auto. intro.
apply IHt0. unfold simplify_irc. simpl.
rewrite precolored_remove_vertex. apply VertexSet.remove_2.
intro. rewrite <-H3 in H.
generalize (In_simplify_props _ _ _ _ _ _ _ _ (VertexSet.choose_1 H1) (refl_equal _) (HWS_irc g0)). intro.
destruct H4. destruct H5. destruct H6. elim H7. auto. auto.
unfold simplify_irc. simpl. rewrite precolored_remove_vertex.
intro. intro. apply H0. apply (VertexSet.remove_3 H3).

(* coalesce *)
assert (forall e', EdgeSet.In e' (get_movesWL (irc_wl g0)) -> In_graph_edge e' (irc_g g0)).
intros.
generalize (In_move_props _ _ _ _ _ _ _ _ H1 (refl_equal _) (HWS_irc g0)).
intuition.
generalize (coalesce_inv _ _ e0). simpl. intro.
generalize (coalesce_inv_2 _ _ e0). intro. destruct H3. destruct H3. simpl in H3. rewrite H3 in *. clear H3.
generalize (any_coalescible_edge_1 _ _ _ _ H1 H2).
intro. destruct H3.
rewrite <-(moves_AE _ _ _ (HWS_irc g0)) in H4.
generalize (proj2 (proj1 (In_graph_aff_edge_in_AE _ _) H4)). intro.
generalize (any_coalescible_edge_2 _ _ _ _ H1 H2). intro.
unfold complete_coloring.
case_eq (ColorMap.find (elt:=Regs.t) (fst_ext e1)
              (IRC_map (merge_irc e1 g0 x0 x1))). 
intros.
unfold map_to_coloring.
rewrite ColFacts.add_neq_o.
apply IHt0.
assert (Edge.aff_edge e1).
rewrite (moves_AE _ _ _ (HWS_irc g0)) in H4.
generalize (In_move_props _ _ _ _ _ _ _ _ H4 (refl_equal _) (HWS_irc g0)).
intuition.
unfold merge_irc. simpl.
rewrite (precolored_merge _ _ H5 H8 _).
apply VertexSet.remove_2. intro. rewrite H9 in H6. elim H6. auto. auto.
unfold VertexSet.Subset in *.
intros. unfold merge_irc in *. simpl in *.
apply H0. rewrite precolored_merge in H8. apply (VertexSet.remove_3 H8).
intro. rewrite H8 in H6. elim H6. auto.
intro.
apply IHt0.
assert (Edge.aff_edge e1).
rewrite (moves_AE _ _ _ (HWS_irc g0)) in H4.
generalize (In_move_props _ _ _ _ _ _ _ _ H4 (refl_equal _) (HWS_irc g0)).
intuition.
unfold merge_irc. simpl.
rewrite (precolored_merge _ _ H5 H8 _).
apply VertexSet.remove_2. intro. rewrite H9 in H6. elim H6. auto. auto.
unfold VertexSet.Subset in *.
intros. unfold merge_irc in *. simpl in *.
apply H0. rewrite precolored_merge in H8. apply (VertexSet.remove_3 H8).

(* freeze *)
generalize (freeze_inv _ _ e1). intro.
generalize (freeze_inv2 _ _ e1). intro. destruct H2. destruct H2. simpl in *. clear e1.
rewrite H2 in *. clear H2. unfold delete_preference_edges_irc2 in *. simpl in *.
apply IHt0.
rewrite precolored_delete_preference_edges. assumption.
unfold VertexSet.Subset in *.
intros. rewrite precolored_delete_preference_edges in H2. auto.

(* spill *)
generalize e2. clear e e0 e1 e2. intro e.
generalize (spill_inv _ _ e). intro.
generalize (spill_inv2 _ _ e). intro. destruct H2. simpl in *. clear e.
rewrite H2 in *. clear H2. unfold available_coloring.
set (palette := pal g0) in *. set (wl := irc_wl g0) in *. set (g1 := irc_g g0) in *.
case_eq ( VertexSet.choose
         (VertexSet.diff palette
            (forbidden_colors r
               (IRC_map
                  (spill_irc r g0
                     (lowest_cost_in r (get_spillWL wl) g1 x0))) g1))).
intros. unfold map_to_coloring.
rewrite ColFacts.add_neq_o.
apply IHt0. unfold spill_irc. simpl.
rewrite precolored_remove_vertex. apply VertexSet.remove_2.
intro. rewrite <-H3 in H.
generalize (In_spill_props _ _ _ _ _ _ _ _ (lowest_cost_in _ _ _ H1) (refl_equal _) (HWS_irc g0)). intro.
destruct H4. destruct H5. elim H6. auto. auto.
unfold spill_irc. simpl. rewrite precolored_remove_vertex.
intro. intro. apply H0. apply (VertexSet.remove_3 H3).
intro. rewrite <-H3 in H.
generalize (In_spill_props _ _ _ _ _ _ _ _ (lowest_cost_in _ _  _ H1) (refl_equal _) (HWS_irc g0)). intro.
destruct H4. destruct H5. elim H6. auto. intro.
apply IHt0. unfold spill_irc. simpl.
rewrite precolored_remove_vertex. apply VertexSet.remove_2.
intro. rewrite <-H3 in H.
generalize (In_spill_props _ _ _ _ _ _ _ _ (lowest_cost_in _ _ _ H1) (refl_equal _) (HWS_irc g0)). intro.
destruct H4. destruct H5. elim H6. auto. auto.
unfold simplify_irc. simpl. rewrite precolored_remove_vertex.
intro. intro. apply H0. apply (VertexSet.remove_3 H3).

(* ending case *)
set (palette := pal g0) in *.
set (g1 := irc_g g0) in *.
assert (map_to_coloring (precoloring_map g1) x = Some x).
unfold precoloring_map.
rewrite VertexSet.fold_1.
generalize VertexSet.elements_1. intro HH.
generalize (HH (precolored g1) x H). clear HH. intro HH.
generalize (NoDupA_elements (precolored g1)). intro HHH.
induction (VertexSet.elements (precolored g1)).
simpl. inversion HH.

unfold map_to_coloring.
rewrite fold_left_assoc_map.
inversion HH. subst.
rewrite ColFacts.add_eq_o.
inversion H2; subst; auto.
apply Regs.eq_sym. auto.
subst.
unfold map_to_coloring in IHl. unfold Regs.t. 
rewrite ColFacts.add_neq_o.
apply IHl. assumption. inversion HHH. assumption.
inversion HHH. subst. intro H6.
elim H4.
inversion H6; subst; auto.

intros.
unfold ColorMap.Equal. 
intro.
destruct (Regs.eq_dec z y0).
rewrite ColFacts.add_eq_o.
destruct (Regs.eq_dec y y0).
rewrite ColFacts.add_eq_o.
inversion e3; inversion e4; subst; rewrite H6; auto.
auto.
rewrite ColFacts.add_neq_o.
rewrite ColFacts.add_eq_o.
reflexivity.
assumption.
assumption.
assumption.
rewrite ColFacts.add_neq_o.
destruct (Regs.eq_dec y y0).
rewrite ColFacts.add_eq_o.
rewrite ColFacts.add_eq_o.
reflexivity.
assumption.
assumption.
rewrite ColFacts.add_neq_o.
rewrite ColFacts.add_neq_o.
rewrite ColFacts.add_neq_o.
reflexivity.
assumption.
assumption.
assumption.
assumption.

intros.
apply ColFacts.add_m.
apply Regs.eq_refl.
reflexivity.
assumption.

rewrite H1. apply OptionReg.eq_refl.
Qed.

Lemma mreg_refl_coloring : forall x g palette,
VertexSet.In x (precolored g) ->
VertexSet.Subset (precolored g) palette ->
OptionReg.eq (IRC g palette x) (Some x).

Proof.
intros.
apply mreg_refl_coloring_aux;
unfold graph_to_IRC_graph; simpl; auto.
Qed.

Lemma loc_type_reg_type_equiv : forall x,
Loc.type (R x) = Regs.get_type (Regs.M x) env.

Proof.
intro x.
unfold Loc.type. unfold Regs.get_type. reflexivity.
Qed.

Lemma correct_alloc_2 : check_coloring_2 g (my_graph_coloring g env) = true.

Proof.
unfold check_coloring_2.
apply SetRegMreg.for_all_1.

unfold compat_bool.
intros x y H. destruct H as [H H0].
rewrite H. rewrite H0. reflexivity.

unfold SetRegMreg.For_all.
intros x H.
generalize (Loc_reg_eq_type (fst x)). generalize (loc_type_reg_type_equiv (snd x)).
unfold my_graph_coloring in *.
change (snd (fst (fst (Typed_interfgraphs g env)))) with intG.
change (fst (fst (fst (Typed_interfgraphs g env)))) with intR.
change (snd (fst (Typed_interfgraphs g env))) with floatR.
change (snd (Typed_interfgraphs g env)) with floatG.
fold int_graph; fold float_graph.
unfold graph_coloring_aux.
change (map_to_coloring (IRC_map (graph_to_IRC_graph int_graph int_palette))) with
             (IRC int_graph int_palette).
change (map_to_coloring (IRC_map (graph_to_IRC_graph float_graph float_palette))) with
             (IRC float_graph float_palette).
intros Locty1 Locty2.
case_eq (Regs.get_type (Regs.P (fst x)) env); intros HH. rewrite HH in *.
case_eq (Regs.get_type (Regs.M (snd x)) env); intros HH0.
case_eq (IRC int_graph int_palette (Regs.P (fst x))); intros. rewrite H0 in *.
destruct (register_heuristic_mreg (Regs.P (fst x)) t0 H0). rewrite H1 in *. simpl.
case_eq (IRC int_graph int_palette (Regs.M (snd x))); intros.
destruct (register_heuristic_mreg (Regs.M (snd x)) t1 H2).

generalize (proper_coloring_IRC_aux int_graph int_palette (correct_palette_int)).
intro H4. unfold proper_coloring in H4.
destruct H4 as [H4 _].
unfold proper_coloring_1 in H4.
assert (~Regs.eq (Regs.M x0) (Regs.M x1)).
apply (H4 (Regs.P (fst x), Regs.M (snd x), None)).
unfold Edge.interf_edge. auto.
unfold int_graph.
right. simpl.
apply regmreg_IE_translation. unfold intG, typed_graphs.
rewrite interf_int_regmreg_translation.
apply regmreg_in_fst_partition. destruct x. auto. auto. auto.
change_rewrite. rewrite H0. apply OptionReg.eq_refl.
change_rewrite. rewrite H2. rewrite H3. apply OptionReg.eq_refl.
destruct (Loc.eq (R x0) (R x1)). subst.
elim H5. inversion e. auto.

destruct (Loc.eq (R x0) (R (snd x))). inversion e. clear e.
generalize (proper_coloring_IRC_aux int_graph int_palette correct_palette_int).
intro H6. unfold proper_coloring in H6.
destruct H6 as [H6 HH5]. destruct HH5 as [HH5 _].
unfold proper_coloring_1 in H6.
assert (~Regs.req t0 (Regs.M (snd x))).
apply (H6 (Regs.P (fst x), Regs.M (snd x), None)).
unfold Edge.interf_edge. auto.
unfold int_graph. unfold intG, typed_graphs.
right. simpl.
apply regmreg_IE_translation. simpl.
apply regmreg_in_fst_partition. destruct x. auto.
auto.
auto.
change_rewrite. rewrite H0. rewrite H1. apply OptionReg.eq_refl.
change_rewrite. apply mreg_refl_coloring. subst.
apply (proj2 (precolored_equiv _ _)).
unfold is_precolored. simpl.
split. auto.

assert (EdgeSet.In (Regs.reg_to_Reg (fst x), Regs.mreg_to_Reg (snd x), None)
                   (IE int_graph)).
unfold int_graph.
apply regmreg_IE_translation. destruct x. simpl.
case_eq (regreg_edge_type_partition (interf_reg_reg g) env); intros.
case_eq (regreg_edge_type_partition (pref_reg_reg g) env); intros.
case_eq (regmreg_edge_type_partition (interf_reg_mreg g) env); intros.
case_eq (regmreg_edge_type_partition (pref_reg_mreg g) env); intros.
simpl. 
replace p2 with (fst (regmreg_edge_type_partition (interf_reg_mreg g) env)).
apply regmreg_in_fst_partition. auto.
assumption.
assumption.
rewrite H7. auto.
apply (proj2 (In_graph_edge_in_ext (Regs.P (fst x), Regs.M (snd x), None)
             _ (or_intror _ H1))).
assumption.

subst. elim H8. apply Regs.eq_refl. reflexivity.

assert (OptionReg.eq (IRC int_graph int_palette (Regs.M (snd x))) (Some (Regs.M (snd x)))) as Hsnd.
apply mreg_refl_coloring. subst.
apply (proj2 (precolored_equiv _ _)).
unfold is_precolored. simpl.
split. auto.

assert (EdgeSet.In (Regs.reg_to_Reg (fst x), Regs.mreg_to_Reg (snd x), None)
                   (IE int_graph)).
unfold int_graph.
apply regmreg_IE_translation. destruct x. simpl.
case_eq (regreg_edge_type_partition (interf_reg_reg g) env); intros.
case_eq (regreg_edge_type_partition (pref_reg_reg g) env); intros.
case_eq (regmreg_edge_type_partition (interf_reg_mreg g) env); intros.
case_eq (regmreg_edge_type_partition (pref_reg_mreg g) env); intros.
simpl. 
replace p2 with (fst (regmreg_edge_type_partition (interf_reg_mreg g) env)).
apply regmreg_in_fst_partition. auto.
assumption.
assumption.
rewrite H4. auto.
apply (proj2 (In_graph_edge_in_ext (Regs.P (fst x), Regs.M (snd x), None)
             _ (or_intror _ H1))).
assumption.

rewrite H2 in Hsnd. inversion Hsnd.

destruct (Loc.eq (S (Local (Zpos (fst x)) Tint)) (R (snd x))). 
inversion e. reflexivity.

case_eq (IRC int_graph int_palette (Regs.P (fst x))); intros. rewrite H0 in Locty2.
case_eq t0; intros; rewrite H1 in *.
destruct (Loc.eq (S (Local 0 Tint)) (R (snd x))).
inversion e. reflexivity.
destruct (Loc.eq (R m) (R (snd x))).
inversion e. subst. unfold Regs.get_type in HH0. unfold Loc.type in Locty2. congruence.
reflexivity.
destruct (Loc.eq (S (Local (Zpos (fst x)) Tint)) (R (snd x))).
inversion e. reflexivity.

case_eq (Regs.get_type (Regs.M (snd x)) env); intros HH0.

case_eq (IRC float_graph float_palette (Regs.P (fst x))); intros. rewrite H0 in Locty2.
case_eq t0; intros; rewrite H1 in *.
destruct (Loc.eq (S (Local 0 Tfloat)) (R (snd x))).
inversion e. reflexivity.
destruct (Loc.eq (R m) (R (snd x))).
inversion e. subst. rewrite HH in Locty2. unfold Regs.get_type in HH0. unfold Loc.type in Locty2. congruence.
reflexivity.
destruct (Loc.eq (S (Local (Zpos (fst x)) Tfloat)) (R (snd x))).
inversion e. reflexivity.

case_eq (IRC float_graph float_palette (Regs.P (fst x))); intros. rewrite H0 in *.
destruct (register_heuristic_mreg_float (Regs.P (fst x)) t0 H0). rewrite H1 in *. simpl.
case_eq (IRC float_graph float_palette (Regs.M (snd x))); intros.
destruct (register_heuristic_mreg_float (Regs.M (snd x)) t1 H2).

generalize (proper_coloring_IRC_aux float_graph float_palette (correct_palette_float)).
intro H4. unfold proper_coloring in H4.
destruct H4 as [H4 _].
unfold proper_coloring_1 in H4.
assert (~Regs.eq (Regs.M x0) (Regs.M x1)).
apply (H4 (Regs.P (fst x), Regs.M (snd x), None)).
unfold Edge.interf_edge. auto.
unfold float_graph.
right. simpl.
apply regmreg_IE_translation. unfold floatG, typed_graphs.
rewrite interf_float_regmreg_translation.
apply regmreg_in_snd_partition. destruct x. auto. auto. auto.
change_rewrite. rewrite H0. apply OptionReg.eq_refl.
change_rewrite. rewrite H2. rewrite H3. apply OptionReg.eq_refl.
destruct (Loc.eq (R x0) (R x1)). subst.
elim H5. inversion e. auto.

destruct (Loc.eq (R x0) (R (snd x))). inversion e. clear e.
generalize (proper_coloring_IRC_aux float_graph float_palette correct_palette_float).
intro H6. unfold proper_coloring in H6.
destruct H6 as [H6 HH5]. destruct HH5 as [HH5 _].
unfold proper_coloring_1 in H6.
assert (~Regs.req t0 (Regs.M (snd x))).
apply (H6 (Regs.P (fst x), Regs.M (snd x), None)).
unfold Edge.interf_edge. auto.
unfold int_graph. unfold floatG, typed_graphs.
right. simpl.
apply regmreg_IE_translation. simpl.
apply regmreg_in_snd_partition. destruct x. auto.
auto.
auto.
change_rewrite. rewrite H0. rewrite H1. apply OptionReg.eq_refl.
change_rewrite. apply mreg_refl_coloring. subst.
apply (proj2 (precolored_equiv _ _)).
unfold is_precolored. simpl.
split. auto.

assert (EdgeSet.In (Regs.reg_to_Reg (fst x), Regs.mreg_to_Reg (snd x), None)
                   (IE float_graph)).
unfold int_graph.
apply regmreg_IE_translation. destruct x. simpl.
case_eq (regreg_edge_type_partition (interf_reg_reg g) env); intros.
case_eq (regreg_edge_type_partition (pref_reg_reg g) env); intros.
case_eq (regmreg_edge_type_partition (interf_reg_mreg g) env); intros.
case_eq (regmreg_edge_type_partition (pref_reg_mreg g) env); intros.
simpl. 
replace p2 with (fst (regmreg_edge_type_partition (interf_reg_mreg g) env)).
apply regmreg_in_snd_partition. auto.
assumption.
assumption.
rewrite H7. auto.
apply (proj2 (In_graph_edge_in_ext (Regs.P (fst x), Regs.M (snd x), None)
             _ (or_intror _ H1))).
assumption.

subst. elim H8. apply Regs.eq_refl. reflexivity.

assert (OptionReg.eq (IRC float_graph float_palette (Regs.M (snd x))) (Some (Regs.M (snd x)))) as Hsnd.
apply mreg_refl_coloring. subst.
apply (proj2 (precolored_equiv _ _)).
unfold is_precolored. simpl.
split. auto.

assert (EdgeSet.In (Regs.reg_to_Reg (fst x), Regs.mreg_to_Reg (snd x), None)
                   (IE float_graph)).
unfold int_graph.
apply regmreg_IE_translation. destruct x. simpl.
case_eq (regreg_edge_type_partition (interf_reg_reg g) env); intros.
case_eq (regreg_edge_type_partition (pref_reg_reg g) env); intros.
case_eq (regmreg_edge_type_partition (interf_reg_mreg g) env); intros.
case_eq (regmreg_edge_type_partition (pref_reg_mreg g) env); intros.
simpl. 
replace p2 with (fst (regmreg_edge_type_partition (interf_reg_mreg g) env)).
apply regmreg_in_snd_partition. auto.
assumption.
assumption.
rewrite H4. auto.
apply (proj2 (In_graph_edge_in_ext (Regs.P (fst x), Regs.M (snd x), None)
             _ (or_intror _ H1))).
assumption.

rewrite H2 in Hsnd. inversion Hsnd.

destruct (Loc.eq (S (Local (Zpos (fst x)) Tfloat)) (R (snd x))). 
inversion e. reflexivity.
Qed.

Import Registers.

Lemma in_palette_not_in_temporaries : forall x,
VertexSet.In (Regs.M x) int_palette ->
~In (R x) temporaries.

Proof.
unfold int_palette. intros x H.
repeat (destruct (proj1 (Props.Dec.F.add_iff _ _ _) H);[
        inversion H0; subst; intro H1; inversion H1;
        [inversion H2| repeat (destruct H2 as [H2|H2];[inversion H2|])];
        assumption
        | generalize H0; clear H H0; intro H]).
elim (VertexSet.empty_1 H).
Qed.

Lemma in_palette_not_in_temporaries_float : forall x,
VertexSet.In (Regs.M x) float_palette ->
~In (R x) temporaries.

Proof.
unfold int_palette. intros x H.
repeat (destruct (proj1 (Props.Dec.F.add_iff _ _ _) H);[
        inversion H0; subst; intro H1; inversion H1;
        [inversion H2| repeat (destruct H2 as [H2|H2];[inversion H2|])];
        assumption
        | generalize H0; clear H H0; intro H]).
elim (VertexSet.empty_1 H).
Qed.

Lemma coloring_acceptable_loc : forall x,
loc_is_acceptable (my_graph_coloring g env x) = true.

Proof.
intro x.
unfold loc_is_acceptable.
unfold my_graph_coloring in *.
change (snd (fst (fst (Typed_interfgraphs g env)))) with intG.
change (fst (fst (fst (Typed_interfgraphs g env)))) with intR.
change (snd (fst (Typed_interfgraphs g env))) with floatR.
change (snd (Typed_interfgraphs g env)) with floatG.
fold int_graph; fold float_graph.
unfold graph_coloring_aux.
change (map_to_coloring (IRC_map (graph_to_IRC_graph int_graph int_palette))) with
             (IRC int_graph int_palette).
change (map_to_coloring (IRC_map (graph_to_IRC_graph float_graph float_palette))) with
             (IRC float_graph float_palette).
case_eq (Regs.get_type (Regs.P x) env); intros.
case_eq (IRC int_graph int_palette (Regs.P x)); intros.
unfold IRC in *.
generalize (register_heuristic_mreg _ _ H0). intro H2.
destruct H2. rewrite H1.
destruct (List.In_dec Loc.eq (R x0) temporaries).
assert (~In (R x0) temporaries).
apply in_palette_not_in_temporaries.
rewrite <-H1.
generalize (proper_coloring_IRC_aux int_graph int_palette
            (correct_palette_int)). intro H3.
unfold proper_coloring in H3.
do 2 destruct H3 as [_ H3].
unfold proper_coloring_3 in H3.
apply (H3 (Regs.P x) t0).
unfold IRC in *. rewrite H0. apply OptionReg.eq_refl.
elim (H2 i).
reflexivity.
unfold IRC in *. auto.
case_eq (IRC float_graph float_palette (Regs.P x)); intros.
unfold IRC in *.
generalize (register_heuristic_mreg_float _ _ H0). intro H2.
destruct H2. rewrite H1.
destruct (List.In_dec Loc.eq (R x0) temporaries).
assert (~In (R x0) temporaries).
apply in_palette_not_in_temporaries_float.
rewrite <-H1.
generalize (proper_coloring_IRC_aux float_graph float_palette
            correct_palette_float). intro H3.
unfold proper_coloring in H3.
do 2 destruct H3 as [_ H3].
unfold proper_coloring_3 in H3.
apply (H3 (Regs.P x) t0).
unfold IRC in *. rewrite H0 in *. apply OptionReg.eq_refl.
elim (H2 i).
reflexivity.
unfold IRC in *. auto.
Qed.

Lemma correct_alloc_3 : check_coloring_3 (all_interf_regs g) env (my_graph_coloring g env) = true.

Proof.
unfold check_coloring_3.
apply Regset.for_all_1.

unfold compat_bool.
intros. subst. reflexivity.

unfold Regset.For_all.
intros x H.
rewrite coloring_acceptable_loc. simpl.
unfold same_typ.
rewrite <-Loc_reg_eq_type.
simpl. destruct (env x); reflexivity.

Qed.

Theorem correct_alloc : check_coloring g env (all_interf_regs g) (my_graph_coloring g env) = true.

Proof.
unfold check_coloring.
rewrite correct_alloc_1.
rewrite correct_alloc_2.
rewrite correct_alloc_3.
auto.
Qed.

End Coloring_to_allocation.

Lemma precolored_sub_int_palette : forall x g env,
VertexSet.In x (precolored (int_graph g env)) -> VertexSet.In x int_palette.

Proof.
Admitted.

Lemma precolored_sub_float_palette : forall x g env,
VertexSet.In x (precolored (float_graph g env)) -> VertexSet.In x float_palette.

Proof.
Admitted.

Theorem allocation_correct : forall g env,
check_coloring g env (all_interf_regs g) (my_graph_coloring g env) = true.

Proof.
intros. apply correct_alloc.
intros. apply (precolored_sub_int_palette x g env). assumption.
intros. apply (precolored_sub_float_palette x g env). assumption.
Qed.
